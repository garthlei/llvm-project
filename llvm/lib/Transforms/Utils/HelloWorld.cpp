//===-- HelloWorld.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/HelloWorld.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/IRBuilder.h"
#include <map>
#include <vector>

using namespace llvm;

/// Add control-flow checking instructions as described in "Control-Flow
/// Checking by Software Signatures."
PreservedAnalyses HelloWorldPass::run(Function &F,
                                      FunctionAnalysisManager &AM) {
  errs() << F.getName() << "\n";

  LLVMContext &Context = F.getType()->getContext();

  // The signatures of basic blocks.
  std::map<BasicBlock *, uint16_t> sig;

  // Signature differences.
  std::map<BasicBlock *, uint16_t> diff;

  // The locations of adjusting signature assignments.
  std::map<BasicBlock *, Instruction *> branchLoc;

  // A temporary accumulator.
  uint16_t acc = 0;

  // The run-time signature
  Instruction *G = nullptr;

  // The run-time adjusting signature
  Instruction *D = nullptr;

  // Initialization IRBuilder
  IRBuilder<> InitBuilder(&F.getEntryBlock(), F.getEntryBlock().getFirstInsertionPt());

  G = InitBuilder.CreateAlloca(IntegerType::getInt16Ty(Context));
  D = InitBuilder.CreateAlloca(IntegerType::getInt16Ty(Context));
  InitBuilder.CreateStore(ConstantInt::get(Context, APInt(16, 0)), G);
  InitBuilder.CreateStore(ConstantInt::get(Context, APInt(16, 0)), D);

  for (BasicBlock &BB : F) {
    // Naïve approach to assign signatures.
    sig[&BB] = acc++;
  }

  for (BasicBlock &BB : F) {
    IRBuilder<> InBlockBuilder(&BB, BB.getFirstInsertionPt());
    BasicBlock *BasePred;
    if (BB.hasNPredecessors(1)) {
      diff[&BB] = sig[BB.getSinglePredecessor()] ^ sig[&BB];
    } else if (BB.hasNPredecessorsOrMore(2)) {
      for (BasicBlock *Pred : predecessors(&BB)) {
        BasePred = Pred;

        break;
      }

      diff[&BB] = sig[BasePred] ^ sig[&BB];

      for (BasicBlock *Pred : predecessors(&BB)) {

        // D[i, m] = s[i, 1] XOR s[i, m]
        StoreInst(
            ConstantInt::get(Context, APInt(16, sig[Pred] ^ sig[BasePred])),
            D, Pred->getFirstNonPHI());

        // Pred->getInstList().push_front(D);
        // branchLoc[*Pred] = D;
      }
    } else {
      diff[&BB] = 0;
    }

    // G1 = load G
    auto G1 = InBlockBuilder.CreateLoad(G);
    auto G2 = InBlockBuilder.CreateXor(G1, diff[&BB]);
    auto sg = InBlockBuilder.CreateStore(G2, G);

    errs() << F.getName() << " left\n";

    if (BB.hasNPredecessorsOrMore(2)) {
      auto D1 = InBlockBuilder.CreateLoad(D);
      auto G3 = InBlockBuilder.CreateLoad(G);
      auto G4 = InBlockBuilder.CreateXor(G3, D1);
      InBlockBuilder.CreateStore(G4, G);
    }
    errs() << F.getName() << " middle\n";

    // TODO: G5 = load G; br (G5 neq s[j]) error

    BB.getInstList().push_front(G);

    errs() << F.getName() << " right\n";
  }

  errs() << F.getName() << " completed\n";

  return PreservedAnalyses::all();
}
