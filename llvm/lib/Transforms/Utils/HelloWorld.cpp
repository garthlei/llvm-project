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
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
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

  // Instructions where we add branches.
  std::vector<Instruction *> branchLoc;

  // A temporary accumulator.
  uint16_t acc = 0;

  // The run-time signature
  Instruction *G = nullptr;

  // The run-time adjusting signature
  Instruction *D = nullptr;

  // Initialization IRBuilder
  IRBuilder<> InitBuilder(&F.getEntryBlock(),
                          F.getEntryBlock().getFirstInsertionPt());

  // Adjusting signature values.
  std::map<BasicBlock *, uint16_t> Dmap;

  G = InitBuilder.CreateAlloca(IntegerType::getInt16Ty(Context), nullptr, "G");
  D = InitBuilder.CreateAlloca(IntegerType::getInt16Ty(Context), nullptr, "D");
  InitBuilder.CreateStore(ConstantInt::get(Context, APInt(16, 0)), G);
  auto StoreD =
      InitBuilder.CreateStore(ConstantInt::get(Context, APInt(16, 0)), D);

  auto newBB = BasicBlock::Create(Context, "", &F);
  IRBuilder<> DivBuilder(newBB, newBB->getFirstInsertionPt());

  // Trigger the divide-by-zero exception.
  DivBuilder.CreateUDiv(
      DivBuilder.CreateLoad(IntegerType::getInt16Ty(Context), G),
      ConstantInt::get(Context, APInt(16, 0)));
  DivBuilder.CreateBr(newBB);

  for (BasicBlock &BB : F) {
    // Naïve approach to assign signatures.
    sig[&BB] = acc++;
  }

  for (BasicBlock &BB : F) {
    if (BB.hasNPredecessors(1)) {
      diff[&BB] = sig[BB.getSinglePredecessor()] ^ sig[&BB];
    } else if (BB.hasNPredecessorsOrMore(2)) {
      BasicBlock *BasePred = nullptr;
      for (BasicBlock *Pred : predecessors(&BB)) {
        BasePred = Pred;
        break;
      }

      diff[&BB] = sig[BasePred] ^ sig[&BB];

      for (BasicBlock *Pred : predecessors(&BB)) {
        // D[i, m] = s[i, 1] XOR s[i, m]
        Dmap[Pred] = sig[Pred] ^ sig[BasePred];
      }
    } else {
      diff[&BB] = 0;
    }
  }

  for (BasicBlock &BB : F) {
    IRBuilder<> InBlockBuilder(&BB, &BB == &F.getEntryBlock()
                                        ? InitBuilder.GetInsertPoint()
                                        : BB.getFirstInsertionPt());

    auto G1 = InBlockBuilder.CreateLoad(IntegerType::getInt16Ty(Context), G);
    auto G2 = InBlockBuilder.CreateXor(G1, diff[&BB]);
    InBlockBuilder.CreateStore(G2, G);

    if (BB.hasNPredecessorsOrMore(2)) {
      auto D1 = InBlockBuilder.CreateLoad(IntegerType::getInt16Ty(Context), D);
      auto G3 = InBlockBuilder.CreateLoad(IntegerType::getInt16Ty(Context), G);
      auto G4 = InBlockBuilder.CreateXor(G3, D1);
      InBlockBuilder.CreateStore(G4, G);
    }

    auto G5 = InBlockBuilder.CreateLoad(IntegerType::getInt16Ty(Context), G);
    ICmpInst *neq = static_cast<ICmpInst *>(InBlockBuilder.CreateICmpNE(
        G5, ConstantInt::get(Context, APInt(16, sig[&BB]))));
    if (Dmap.find(&BB) != Dmap.end())
      InBlockBuilder.CreateStore(
          ConstantInt::get(Context, APInt(16, Dmap[&BB])), D);

    branchLoc.push_back(neq);
  }

  for (auto neq : branchLoc)
    SplitBlockAndInsertIfThen(neq, neq->getNextNode(), false, nullptr,
                              static_cast<DomTreeUpdater *>(nullptr), nullptr,
                              newBB);

  return PreservedAnalyses::none();
}
