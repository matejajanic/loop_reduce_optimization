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

namespace {
struct OurLoopReduce : public LoopPass {
  std::vector<BasicBlock *> LoopBasicBlocks;
  std::unordered_map<Value *, Value *> VariablesMap;
  Value *LoopCounter, *LoopBound;
  bool isLoopBoundConst;
  int BoundValue, MulFactor;

  static char ID; // Pass identification, replacement for typeid
  OurLoopReduce() : LoopPass(ID) {}

  void mapVariables(Loop *L)
  {
    Function *F = L->getHeader()->getParent();
    for (BasicBlock &BB : *F) {
      for (Instruction &I : BB) {
        if (isa<LoadInst>(&I)) {
          VariablesMap[&I] = I.getOperand(0);
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

  bool canReduce()
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
          if (ConstantInt *ConstInt = dyn_cast<ConstantInt>(I.getOperand(1))) {
            MulFactor = ConstInt->getSExtValue();
            return true;
          }
        }
        else if (Var2 == LoopCounter) {
          if (ConstantInt *ConstInt = dyn_cast<ConstantInt>(I.getOperand(0))) {
            MulFactor = ConstInt->getSExtValue();
            return true;
          }
        }
      }
    }

    return false;
  }

  void reduce(Loop *L) {
    using namespace llvm;

    BasicBlock *Preheader = L->getLoopPreheader();
    BasicBlock *Header = L->getHeader();
    BasicBlock *Latch = L->getLoopLatch();

    if (!Preheader || !Header || !Latch) {
        errs() << "Loop shape unsupported!\n";
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

    // finding the mul instruction
    Instruction *MulInstFound = nullptr;
    ConstantInt *ConstFound   = nullptr;

    for (Instruction &I : *BodyBB) {
        if (I.getOpcode() != Instruction::Mul)
            continue;

        Value *Op0 = I.getOperand(0);
        Value *Op1 = I.getOperand(1);

        if (VariablesMap.find(Op0) != VariablesMap.end())
            Op0 = VariablesMap[Op0];
        if (VariablesMap.find(Op1) != VariablesMap.end())
            Op1 = VariablesMap[Op1];

        if (Op0 == LoopCounter && isa<ConstantInt>(I.getOperand(1))) {
            MulInstFound = &I;
            ConstFound   = cast<ConstantInt>(I.getOperand(1));
            break;
        }
        if (Op1 == LoopCounter && isa<ConstantInt>(I.getOperand(0))) {
            MulInstFound = &I;
            ConstFound   = cast<ConstantInt>(I.getOperand(0));
            break;
        }
    }

    if (!MulInstFound || !ConstFound) {
        errs() << "No mul pattern found\n";
        return;
    }

    MulFactor = ConstFound->getSExtValue();

    auto *AllocaPtrTy = dyn_cast<PointerType>(LoopCounter->getType());
    if (!AllocaPtrTy) {
        errs() << "[LSR] LoopCounter is not a pointer to scalar, bailing\n";
        return;
    }

    Type *IdxTy = nullptr;
    if (auto *Alloca = dyn_cast<AllocaInst>(LoopCounter))
      IdxTy = Alloca->getAllocatedType();
    else
      IdxTy = Type::getInt32Ty(L->getHeader()->getContext());
    ConstantInt *StepConst = ConstantInt::get(cast<IntegerType>(IdxTy), MulFactor);

    IRBuilder<> BPre(Preheader->getTerminator());

    AllocaInst *IdxAlloca = BPre.CreateAlloca(IdxTy, nullptr, "Idx");

    Value *InitIV = BPre.CreateLoad(IdxTy, LoopCounter, "iv.init");

    Value *InitScaled = BPre.CreateMul(InitIV, StepConst, "idx.init");

    BPre.CreateStore(InitScaled, IdxAlloca);

    //replacing the mul instruction
    IRBuilder<> BBody(MulInstFound);

    Value *CurrIdxScaled =
        BBody.CreateLoad(IdxTy, IdxAlloca, "idx.curr");

    MulInstFound->replaceAllUsesWith(CurrIdxScaled);

    MulInstFound->eraseFromParent();
    

    //updating idx value
    Instruction *LatchTerm = Latch->getTerminator();
    IRBuilder<> BL(LatchTerm);

    Value *OldScaled = BL.CreateLoad(IdxTy, IdxAlloca, "idx.old");

    Value *NewScaled = BL.CreateAdd(OldScaled, StepConst, "idx.next");

    BL.CreateStore(NewScaled, IdxAlloca);

    errs() << "Applied strength reduction\n";
}


  bool runOnLoop(Loop *L, LPPassManager &LPM) override {
    mapVariables(L);
    LoopBasicBlocks = L->getBlocksVector();
    findLoopCounterAndBound(L);
    if (canReduce()) {
      reduce(L);
      errs() << "Reducing can be done!\n";
    }
    else {
      errs() << "No reducing needed!\n";
    }
    return true;
  }
};
}

char OurLoopReduce::ID = 0;
static RegisterPass<OurLoopReduce> X("our-loop-reduce", "",
                                              false /* Only looks at CFG */,
                                              false /* Analysis Pass */);
