#include "llvm/IR/Instruction.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Utils/LoopPeel.h"
#include "llvm/Transforms/Utils/LoopSimplify.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/SizeOpts.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopUnrollAnalyzer.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/IRBuilder.h"
#include <algorithm>

using namespace llvm;

struct ScaledInductionInfo {
  llvm::AllocaInst *IdxAlloca = nullptr;
  llvm::Value      *AInit     = nullptr;
  llvm::Value      *InitOffset= nullptr;

  llvm::BasicBlock *Preheader = nullptr;
  llvm::BasicBlock *Header    = nullptr;
  llvm::BasicBlock *Latch     = nullptr;
  llvm::BasicBlock *BodyBB    = nullptr;

  bool Valid = false;

  void reset() {
    IdxAlloca   = nullptr;
    AInit       = nullptr;
    InitOffset  = nullptr;
    Preheader   = nullptr;
    Header      = nullptr;
    Latch       = nullptr;
    BodyBB      = nullptr;
    Valid       = false;
  }
};

namespace {
struct OurLoopReduce : public LoopPass {
  std::vector<BasicBlock *> LoopBasicBlocks;
  std::unordered_map<Value *, Value *> VariablesMap;
  Value *LoopCounter, *LoopBound;
  bool isLoopBoundConst;
  int BoundValue;

  static char ID; // Pass identification, replacement for typeid
  OurLoopReduce() : LoopPass(ID) {}

  Value *stripToBase(Value *V) {
    while (true) {
      if (auto *Cast = dyn_cast<CastInst>(V)) {
        V = Cast->getOperand(0);
        continue;
      }

      if (auto *LI = dyn_cast<LoadInst>(V)) {
        V = LI->getPointerOperand();
        continue;
      }

      break;
    }
    return V;
  }

  void mapVariables(Loop *L) {
    Function *F = L->getHeader()->getParent();

    for (BasicBlock &BB : *F) {
      for (Instruction &I : BB) {

        if (auto *LI = dyn_cast<LoadInst>(&I)) {
          Value *Base = stripToBase(LI);
          VariablesMap[&I] = Base;
          continue;
        }

        if (auto *CI = dyn_cast<CastInst>(&I)) {
          Value *Op = CI->getOperand(0);
          Value *Base = stripToBase(Op);
          VariablesMap[&I] = Base;
          continue;
        }
      }
    }
  }

  void findLoopCounterAndBound(Loop *L)
  {
    for (Instruction &I : *L->getHeader()) {
      if (isa<ICmpInst>(&I)) {
        LoopCounter = VariablesMap[I.getOperand(0)];
        if (ConstantInt *ConstInt = dyn_cast<ConstantInt>(I.getOperand(1))) {
          isLoopBoundConst = true;
          BoundValue = ConstInt->getSExtValue();
        }
      }
    }
  }

  bool canReduceSimpleMul()
  {
    BasicBlock * LoopBodyBB = LoopBasicBlocks[1]; // assuming there is only 1 BB
    if (LoopBodyBB == nullptr) {
      return false;
    }

    Value *Var1, *Var2;

    for (Instruction &I : *LoopBodyBB) {
      if (isa<MulOperator>(&I)) {
        Var1 = VariablesMap[I.getOperand(0)];
        Var2 = VariablesMap[I.getOperand(1)];

        if (Var1 == LoopCounter) {
          return true;
        }
        else if (Var2 == LoopCounter) {
          return true;
        }
      }
    }

    return false;
  }

  void reduceSimpleMul(Loop *L) {
    ScaledInductionInfo Info;
    Info.Preheader = L->getLoopPreheader();
    Info.Header = L->getHeader();
    Info.Latch = L->getLoopLatch();
    if (!Info.Preheader || !Info.Header || !Info.Latch) {
        errs() << "Loop shape unsupported!\n";
        return;
    }

    Info.BodyBB = nullptr;
    for (BasicBlock *BB : L->getBlocks()) {
        if (BB != Info.Header && BB != Info.Latch) {
            Info.BodyBB = BB;
            break;
        }
    }
    if (!Info.BodyBB)
        Info.BodyBB = Info.Header;

    Instruction *MulInstFound = nullptr;
    Value *MulFactorRaw = nullptr;
    for (Instruction &I : Info.BodyBB) {
        if (I.getOpcode() != Instruction::Mul)
            continue;

        Value *Op0 = I.getOperand(0);
        Value *Op1 = I.getOperand(1);

        Value *NormedOp0 = VariablesMap.count(Op0) ? VariablesMap[Op0] : Op0;
        Value *NormedOp1 = VariablesMap.count(Op1) ? VariablesMap[Op1] : Op1;

        if (NormedOp0 == LoopCounter) {
            MulInstFound = &I;
            MulFactorRaw = Op1;
            break;
        }
        if (NormedOp1 == LoopCounter) {
            MulInstFound = &I;
            MulFactorRaw = Op0;
            break;
        }
    }

    if (!MulInstFound || !MulFactorRaw) {
        errs() << "No mul(i,a) pattern found\n";
        return;
    }

    Instruction *AddInstFound = nullptr;
    Value *BSourceRaw = nullptr;
    LoadInst *BSourceLoad = nullptr;
    for (User *U : MulInstFound->users()) {
      Instruction *UserI = dyn_cast<Instruction>(U);
      if (!UserI)
          continue;
      if (UserI->getOpcode() != Instruction::Add)
          continue;

      Value *A0 = UserI->getOperand(0);
      Value *A1 = UserI->getOperand(1);

      if (A0 == MulInstFound) {
          AddInstFound = UserI;
          BSourceRaw = A1;
      }
      else if (A1 == MulInstFound) {
        AddInstFound = UserI;
        BSourceRaw = A0;
      } else {
        continue;
      }

      if (auto *Ld = dyn_cast<LoadInst>(BSourceRaw)) {
        BSourceLoad = Ld;
      }

      break;
    }

    if (!AddInstFound || !BSourceRaw) {
        errs() << "No mul, load, add pattern\n";
        return;
    }

    Value *BPtr = nullptr;
    if (BSourceLoad) {
      BPtr = BSourceLoad->getPointerOperand();
      if (!BPtr) {
        errs() << "Load has no pointer operand\n";
        return;
      }
    }

    Type *IdxTy = nullptr;
    if (auto *AllocaLC = dyn_cast<AllocaInst>(LoopCounter)) {
        IdxTy = AllocaLC->getAllocatedType();
    } else {
        IdxTy = Type::getInt32Ty(Info.Header->getContext());
    }

    Function *F = Info.Header->getParent();
    IRBuilder<> BEntry(&*F->getEntryBlock().getFirstInsertionPt());
    AllocaInst *IdxAlloca = BEntry.CreateAlloca(IdxTy, nullptr, "Idx");

    IRBuilder<> BPre(Info.Preheader->getTerminator());

    Value *InitIV = BPre.CreateLoad(IdxTy, LoopCounter, "iv.init");
    if (!InitIV) {
        errs() << "Can't get init IV\n";
        return;
    }

    Value *AInit = nullptr;
    if (auto *MFLoad = dyn_cast<LoadInst>(MulFactorRaw)) {
        Value *APtr = MFLoad->getPointerOperand();
        if (!APtr) {
            errs() << "MulFactor load has no pointer operand\n";
            return;
        }
        AInit = BPre.CreateLoad(IdxTy, APtr, "a.init");
    } else {
        AInit = MulFactorRaw;
    }

    Value *InitB = nullptr;
    if (BPtr) {
      InitB = BPre.CreateLoad(IdxTy, BPtr, "b.init");
    }
    else {
      InitB = BSourceRaw;
    }

    Value *InitScaled = BPre.CreateMul(InitIV, AInit, "idx.init");
    Value *InitOffset = BPre.CreateAdd(InitScaled, InitB, "idx.offset");
    BPre.CreateStore(InitOffset, IdxAlloca);

    IRBuilder<> BBody(MulInstFound);
    Value *CurrIdx = BBody.CreateLoad(IdxTy, IdxAlloca, "idx.curr");
    AddInstFound->replaceAllUsesWith(CurrIdx);
    AddInstFound->eraseFromParent();
    if (MulInstFound->use_empty())
        MulInstFound->eraseFromParent();

    Instruction *LatchTerm = Info.Latch->getTerminator();
    IRBuilder<> BL(LatchTerm);
    Value *OldIdx = BL.CreateLoad(IdxTy, IdxAlloca, "idx.old");
    Value *NewIdx = BL.CreateAdd(OldIdx, AInit, "idx.next");
    BL.CreateStore(NewIdx, IdxAlloca);

    Info.IdxAlloca = IdxAlloca;
    Info.AInit = AInit;
    Info.InitOffset = InitOffset;
    Info.Valid = true;

    errs() << "Applied strength reduction\n";
  }

  bool canReducePointer()
  {
    BasicBlock * LoopBodyBB = LoopBasicBlocks[1]; // assuming there is only 1 BB
    if (LoopBodyBB == nullptr) {
      return false;
    }

    Value *Var;

    for (Instruction &I : *LoopBodyBB) {
      if (isa<GetElementPtrInst>(&I)) {
        Var = VariablesMap[I.getOperand(2)];

        if (Var == LoopCounter) {
            return true;
        }
      }
    }

    return false;
  }

  void reducePointer(Loop *L) {
    BasicBlock *Preheader = L->getLoopPreheader();
    BasicBlock *Header = L->getHeader();
    BasicBlock *Latch = L->getLoopLatch();

    if (!Preheader || !Header || !Latch) {
        errs() << "Loop shape unsupported\n";
        return;
    }

    BasicBlock *BodyBB = nullptr;
    for (BasicBlock *BB : L->getBlocks()) {
        if (BB != Header && BB != Latch) {
            BodyBB = BB;
            break;
        }
    }
    if (!BodyBB)
        BodyBB = Header;

    // Find pattern:
    // %elem.ptr = getelementptr [N x i32], ptr %arr, i32 0, i64 %idx
    // store i32 %val, ptr %elem.ptr
    GetElementPtrInst *GEPInst = nullptr;
    StoreInst *StoreAfterGEP = nullptr;

    for (Instruction &I : *BodyBB) {
      auto *G = dyn_cast<GetElementPtrInst>(&I);
      if (!G) continue;

      // Next instruction should store in that GEP
      Instruction *Next = I.getNextNode();
      if (!Next) continue;
      auto *S = dyn_cast<StoreInst>(Next);
      if (!S) continue;

      if (S->getPointerOperand() != G)
          continue;

      if (G->getNumOperands() != 3)
          continue;

      auto *ZeroIdx = dyn_cast<ConstantInt>(G->getOperand(1));
      if (!ZeroIdx || !ZeroIdx->isZero())
          continue;

      GEPInst = G;
      StoreAfterGEP = S;
      break;
    }

    if (!GEPInst || !StoreAfterGEP) {
      errs() << "No suitable static-array GEP+store pattern found\n";
      return;
    }

    Value *BasePtr = GEPInst->getPointerOperand();
    Value *StoreVal = StoreAfterGEP->getValueOperand();
    Type *ElementTy = GEPInst->getResultElementType();

    Function *F = Header->getParent();
    LLVMContext &Ctx = Header->getContext();
    IRBuilder<> BEntry(&*F->getEntryBlock().getFirstInsertionPt());
    PointerType *ElementPtrTy = PointerType::getUnqual(ElementTy);
    AllocaInst *PtrAlloca = BEntry.CreateAlloca(ElementPtrTy, nullptr, "p");

    bool CanUseScaledInfo =
       Info.Valid &&
       Info.Preheader == Preheader &&
       Info.Latch == Latch &&
       Info.BodyBB == BodyBB;

    if (CanUseScaledInfo) {
      IRBuilder<> BPre(Preheader->getTerminator());

      Value *PtrInit = BPre.CreateGEP(GEPInst->getSourceElementType(), BasePtr, Info.InitOffset, "p.init");

      BPre.CreateStore(PtrInit, PtrAlloca);
      IRBuilder<> BBody(StoreAfterGEP);
      Value *CurPtr = BBody.CreateLoad(ElementPtrTy, PtrAlloca, "p.cur");
      BBody.CreateStore(StoreVal, CurPtr);

      StoreAfterGEP->eraseFromParent();
      GEPInst->eraseFromParent();

      IRBuilder<> BL(Latch->getTerminator());
      Value *OldPtr = BL.CreateLoad(ElementPtrTy, PtrAlloca, "p.old");
      Value *NextPtr = BL.CreateGEP(ElementTy, OldPtr, Info.AInit, "p.next");
      BL.CreateStore(NextPtr, PtrAlloca);

      errs() << "Applied pointer-based strength reduction (scaled a*i+b)\n";
      return;
    }

    IRBuilder<> BPre(Preheader->getTerminator());
    // we have to make a value for 0 because CreateGEP expects a Value* type
    Value *Zero32 = ConstantInt::get(Type::getInt32Ty(Ctx), 0);
    Value *PInit = BPre.CreateGEP(GEPInst->getSourceElementType(), BasePtr, { Zero32, Zero32 }, "p.init");
    BPre.CreateStore(PInit, PtrAlloca);

    IRBuilder<> BBody(StoreAfterGEP);
    Value *CurPtr = BBody.CreateLoad(ElementPtrTy, PtrAlloca, "p.cur");
    BBody.CreateStore(StoreVal, CurPtr);

    StoreAfterGEP->eraseFromParent();
    GEPInst->eraseFromParent();


    // Incrementing pointer
    Instruction *LatchTerm = Latch->getTerminator();
    IRBuilder<> BL(LatchTerm);

    Value *OldPtr = BL.CreateLoad(ElementPtrTy, PtrAlloca, "p.old");

    // Same as for zeros, we have to make One32
    Value *One32 = ConstantInt::get(Type::getInt32Ty(Ctx), 1);
    Value *NextPtr = BL.CreateGEP(ElementTy, OldPtr, One32, "p.next");

    BL.CreateStore(NextPtr, PtrAlloca);

    errs() << "Applied pointer-based strength reduction (non scaled)\n";
    return;
  }

  bool runOnLoop(Loop *L, LPPassManager &LPM) override {
    mapVariables(L);
    LoopBasicBlocks = L->getBlocksVector();
    findLoopCounterAndBound(L);
    if(canReduceSimpleMul)
      reduceSimpleMul;
    if(canReducePointer)
      reducePointer;
    return true;
  }
};
}

char OurLoopReduce::ID = 0;
static RegisterPass<OurLoopReduce> X("our-loop-reduce", "",
                                              false /* Only looks at CFG */,
                                              false /* Analysis Pass */);

