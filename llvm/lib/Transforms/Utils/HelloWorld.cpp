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
PreservedAnalyses HelloWorldPass::run(Module &M, ModuleAnalysisManager &AM) {
  errs() << M.getName() << "\n";

  LLVMContext &Context = M.getContext();

  // The signatures of basic blocks.
  std::map<BasicBlock *, uint16_t> sig;

  // Signature differences.
  std::map<BasicBlock *, uint16_t> diff;

  // Error-handling blocks.
  std::map<Function *, BasicBlock *> ErrBlks;

  // Instructions where we add branches.
  std::vector<Instruction *> branchLoc;

  // Procedure call-related predecessors.
  std::multimap<BasicBlock *, BasicBlock *> PredSet;

  // Call sites
  std::vector<CallBase *> CallSites;

  // A temporary accumulator.
  uint16_t acc = 0;

  // The run-time signature
  GlobalVariable *G =
      new GlobalVariable(M, IntegerType::getInt16Ty(Context), false,
                         GlobalValue::LinkageTypes::InternalLinkage,
                         ConstantInt::get(Context, APInt(16, 0)), "G");
  // Instruction *G = nullptr;

  // The run-time adjusting signature
  // Instruction *D = nullptr;
  GlobalVariable *D =
      new GlobalVariable(M, IntegerType::getInt16Ty(Context), false,
                         GlobalValue::LinkageTypes::InternalLinkage,
                         ConstantInt::get(Context, APInt(16, 0)), "D");

  // Adjusting signature values.
  std::map<BasicBlock *, uint16_t> Dmap;

  for (Function &F : M)
    for (BasicBlock &BB : F)
      for (Instruction &I : BB) {
        auto CB = dyn_cast<CallBase>(&I);
        if (CB != nullptr && !CB->getCalledFunction()->isDeclaration()) {
          PredSet.insert(
              std::make_pair(&CB->getCalledFunction()->getEntryBlock(), &BB));

          // Splitting the basic block now can affect the iteration, so we
          // choose to move the splitting part outside.
          CallSites.push_back(CB);
        }
      }

  for (auto CallSite : CallSites) {
    auto NewBlk = SplitBlock(CallSite->getParent(), CallSite->getNextNode());

    for (BasicBlock &B : *CallSite->getCalledFunction())
      for (Instruction &I : B)
        if (isa<ReturnInst>(&I))
          PredSet.insert(std::make_pair(NewBlk, &B));
  }

  for (Function &F : M)
    for (BasicBlock &BB : F) {
      // Naïve approach to assign signatures.
      sig[&BB] = acc++;
    }

  for (Function &F : M)
    for (BasicBlock &BB : F) {
      size_t PredSetLen = PredSet.count(&BB);
      auto PredSetRange = PredSet.equal_range(&BB);

      if (PredSetLen == 1) {
        diff[&BB] = sig[PredSetRange.first->second] ^ sig[&BB];
      } else if (BB.hasNPredecessors(1)) {
        diff[&BB] = sig[BB.getSinglePredecessor()] ^ sig[&BB];
      } else if (PredSetLen >= 2) {
        BasicBlock *BasePred = PredSetRange.first->second;

        diff[&BB] = sig[BasePred] ^ sig[&BB];

        for (auto i = PredSetRange.first; i != PredSetRange.second; ++i) {
          // D[i, m] = s[i, 1] XOR s[i, m]
          Dmap[i->second] = sig[i->second] ^ sig[BasePred];
        }
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

  for (Function &F : M)
    for (BasicBlock &BB : F) {
      IRBuilder<> InBlockBuilder(&BB, BB.getFirstInsertionPt());

      auto G1 = InBlockBuilder.CreateLoad(IntegerType::getInt16Ty(Context), G);
      auto G2 = InBlockBuilder.CreateXor(G1, diff[&BB]);
      InBlockBuilder.CreateStore(G2, G);

      if (BB.hasNPredecessorsOrMore(2)) {
        auto D1 =
            InBlockBuilder.CreateLoad(IntegerType::getInt16Ty(Context), D);
        auto G3 =
            InBlockBuilder.CreateLoad(IntegerType::getInt16Ty(Context), G);
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

  for (Function &F : M) {
    if (F.isDeclaration())
      continue;
    auto newBB = BasicBlock::Create(Context, "", &F);
    IRBuilder<> ErrHdlBuilder(newBB, newBB->getFirstInsertionPt());

    // Simply branch to itself.
    ErrHdlBuilder.CreateBr(newBB);

    ErrBlks.insert(std::make_pair(&F, newBB));
  }

  for (auto neq : branchLoc)
    SplitBlockAndInsertIfThen(neq, neq->getNextNode(), false, nullptr,
                              static_cast<DomTreeUpdater *>(nullptr), nullptr,
                              ErrBlks[neq->getFunction()]);

  return PreservedAnalyses::none();
}
