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

  void reduce(Loop *L)
  {
    BasicBlock* Preheader = L->getLoopPreheader();
    IRBuilder<> Builder(Preheader->getTerminator());
    AllocaInst* Idx = Builder.CreateAlloca(Builder.getInt32Ty(), nullptr, "Idx");
    Builder.CreateStore(LoopCounter, Idx);

    BasicBlock * LoopBodyBB = LoopBasicBlocks[1]; // assuming there is only 1 BB
    Value *Var1, *Var2;

    for (Instruction &I : *LoopBodyBB) {
      if (isa<MulOperator>(&I)) {
        Var1 = VariablesMap[I.getOperand(0)];
        Var2 = VariablesMap[I.getOperand(1)];


      }
    }
  }

  bool runOnLoop(Loop *L, LPPassManager &LPM) override {
    mapVariables(L);
    LoopBasicBlocks = L->getBlocksVector();
    if (canReduce()) {
      errs() << "Wuhuuu 8 iz ppj!\n";
    }
    else {
      errs() << "Wuhuuu 9 iz ppj!\n";
    }
    return true;
  }
}; // end of struct OurLoopUnswitchingPass
}  // end of anonymous namespace

char OurLoopReduce::ID = 0;
static RegisterPass<OurLoopReduce> X("our-loop-reduce", "",
                                              false /* Only looks at CFG */,
                                              false /* Analysis Pass */);