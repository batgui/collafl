/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   Copyright 2015, 2016 Google Inc. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.

 */

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <vector>
#include <set>
#include <map>
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/DenseSet.h>
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
/* singleBBS: an array of BBs with single precedent 
    multiBBS: an array of BBs with multiple precedents
    preds: store precedent information of each basic block
    solv: solvable blocks
    unsolv:  unsolvable blocks
    keys: assigns unique random keys to each basic block */
using namespace llvm;
using namespace std;
using xyz = std::array<int, 3>;
using cur_pre = std::array<unsigned int, 2>;
set<unsigned int> hashes, tmpHashSet;
vector< BasicBlock *> singleBBS, multiBBS, solv, unsolv;
map<  BasicBlock*  ,  vector< BasicBlock* >> preds;
map<  BasicBlock*  , unsigned int> keys;
map<  BasicBlock*, xyz> params;
map<cur_pre, unsigned int> hashMap;
map<unsigned int, unsigned int> singleMap;

static bool disjoint(set<unsigned int>& hashes, set<unsigned int>& tmpHashSet)  {
  for (auto hash : hashes){
    for (auto tmpHash : tmpHashSet)
      if (hash == tmpHash)
        return false;
  }
  return true;
    
}
/* search parameters for blocks with multiple precedents */
static void calcFmul() {
  //sizeof(unsol) < delta or unsolv/BBSet  < sigma
  int delta =  10;
  double min = 1;
  double sigma = 0.001;
  int i = 1;
  for (int y = 1; y < MAP_SIZE_POW2; y++ ) {
    //make set or map to empty
    hashes.clear();
    params.clear();
    solv.clear();
    unsolv.clear();
    for (auto BB : multiBBS) {
      // search parameters for BB
      for (int x = 1; x < MAP_SIZE_POW2; x++ ) {
        for (int z = 1; z < MAP_SIZE_POW2; z++ ) {
          tmpHashSet.clear();
          auto cur = keys[BB];
          // hashes for all incoming edges 
          for (auto p : preds[BB]) {
            auto edgeHash = (cur >> x) ^ (keys[p] >> y) + z;
            tmpHashSet.insert(edgeHash);
          }
          // find a solution for BB if no collision
          if (tmpHashSet.size() == preds[BB].size() && disjoint(tmpHashSet, hashes)) {
            i++;
            solv.push_back(BB);
            params[BB] = xyz({x, y, z});
            hashes.insert(tmpHashSet.begin(), tmpHashSet.end());
          }
        }
      }
          
      unsolv.push_back(BB);
    }
    auto sizeofUnsolv = unsolv.size();
    auto sizeofSolv = solv.size();
    auto _min = (double)sizeofUnsolv / (sizeofUnsolv + sizeofSolv);
    if (_min < min) min = _min;
    if(sizeofUnsolv < delta || _min < sigma) {
      errs() << "I'm going to break. " << '\n';
      break;
    }
    
  }
  errs() << "min：" <<　min << '\n';
  errs() << "i: " << i << '\n';
}

/* build the hash table for unsolvable blocksUnsol */

static void calcFhash() {
  hashMap.clear();
  for (auto BB : unsolv) {
    
    auto cur = keys[BB];
    for (auto p : preds[BB]) {
      
      auto pre = keys[p];
      for (int i = 0; i < MAP_SIZE; i++) {
        //errs() << hashes.size() << '\n';
        if (!hashes.count(i)) {
          hashMap[cur_pre({cur, pre})] = i;
          hashes.insert(i);
          break;
        }
      }
      
    }
  }
}

/* build the hash table for blocks with single precedent */

static void calcSingle() {
  singleMap.clear();
  for (auto BB : singleBBS) {
    
    auto cur = keys[BB];
      for (int i = 0; i < MAP_SIZE; i++) {
        
        if (!hashes.count(i)) {
          
          singleMap[cur] = i;
          hashes.insert(i);
          break;
        }
      }
       
  }
}



namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

}

char AFLCoverage::ID = 0;


bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Instrument all the things! */

  int inst_blocks = 0;
  int i = 1;
  for (auto &F : M) 
    for (Function::iterator b = F.begin(), be = F.end(); b != be; ++b) {
      //BasicBlock* BB = b;
      
      i++;
      BasicBlock* BB = &*b;
      TerminatorInst *TInst = BB->getTerminator();
      unsigned NSucc = TInst->getNumSuccessors();
      if(NSucc == 1) {
        //errs() << "single" << '\n';
        singleBBS.push_back(BB);
      }
      else if(NSucc > 1) {
        //errs() << "multiple" << '\n';
        multiBBS.push_back(BB);
  
        }
        for (unsigned I = 0; I < NSucc; ++I) {
          BasicBlock *Succ = TInst->getSuccessor(I);
          preds[BB].push_back(Succ);
      }
      if (AFL_R(100) >= inst_ratio) continue;

      /* Make up cur_loc */

      unsigned int cur_loc = AFL_R(MAP_SIZE);
      keys[BB] = cur_loc;


    }

  
  errs() << "singleBSS size: " << singleBBS.size() << '\n';
  errs() << "multiBSS size: " << multiBBS.size() << '\n';
  // calc hashes for blocks
  calcFmul();
  calcFhash();
  calcSingle();
  errs() << "solv size: " << solv.size() << '\n';
  errs() << "unsolv size: " << unsolv.size() << '\n';
  errs() << "singleMap size: " << singleMap.size() << '\n';
  errs() << "hashMap size: " << hashMap.size() << '\n';
  errs() << "keys size: " << keys.size() << '\n';
  errs() << "params size: " << params.size() << '\n';
  errs() << "preds size: " << preds.size() << '\n';
  for (auto &F : M) 
    for (Function::iterator b = F.begin(), be = F.end(); b != be; ++b) {
           BasicBlock* BB = &*b;
      BasicBlock::iterator IP = BB->getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));
      if (!keys.count(BB)) {
        errs() << "BB not in keys" << '\n';
        continue;
      }
      auto cur_loc = keys[BB];
      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      // BBS with one precedent
      int X = 0;
      int Y = 1;
      int Z = 1;
      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());      
      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc >> X);
      Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

      if (singleMap.count(cur_loc)) {
        ConstantInt *CurLoc = ConstantInt::get(Int32Ty, singleMap[cur_loc]);
        Value *MapPtrIdx =
        IRB.CreateGEP(MapPtr, CurLoc);
        //errs() << "singleMap.count(cur_loc) " << *CurLoc << " MapPtrIdx: "　<< *MapPtrIdx << '\n';
      }
      else if (params.count(BB)) {
       
        auto XYZ = params[BB];
        
        X = XYZ[0];
        Y = XYZ[1];
        Z = XYZ[2];
        errs() << "X: " << X << " Y: " << Y << " Z: " << Z << '\n';
        ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc >> X);
      
       /* Load prev_loc */


        auto XorCurPre = IRB.CreateXor(PrevLocCasted, CurLoc);
        auto XorPlusZ = IRB.CreateAdd(XorCurPre, ConstantInt::get(Int32Ty, Z));
        Value *MapPtrIdx =
        IRB.CreateGEP(MapPtr, XorPlusZ);
        //errs() << "params.count(BB): " << *XorPlusZ << " MapPtrIdx: " << *MapPtrIdx  << '\n';
      }
      else {
        
            //auto pre = (unsigned int)dyn_cast<ConstantInt>((AFLPrevLoc)->getValue());
            // Value* loadedValue = new LoadInst(AFLPrevLoc);
            // auto pre = *ExecutionEngine::getGlobalValueAtAddress(AFLPrevLoc);
            
            // if (hashMap.count(cur_pre({cur_loc, pre}))) {
            //   ConstantInt *CurLoc = ConstantInt::get(Int32Ty, hashMap[cur_pre{cur_loc, pre}]);
            //   Value *MapPtrIdx =
            //   IRB.CreateGEP(MapPtr, CurLoc);
            //   errs() << "else: " << *CurLoc << " MapPtrIdx: " << *MapPtrIdx  << '\n';
            // }

           
        
      }


   /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));

      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Set prev_loc to cur_loc >> Y */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> Y), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      inst_blocks++;
    }

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }

  return true;

  

}
 


// stastic void PassManagerBuilder::populateLTOPassManager(legacy::PassManagerBase &PM) {
//    PM.add(new AFLCoverage());
// }

static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());
  PassManagerBuilder *builder = new PassManagerBuilder();
  // builder.VerifyInput = true;
  builder->populateLTOPassManager(PM);

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_OptimizerLast, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
    
// static RegisterStandardPasses RegisterLTOPass(
//     PassManagerBuilder::EP_OptimizerLast, PassManagerBuilder::populateLTOPassManager);
