#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
using namespace llvm;

namespace {
  struct SGVerifierPass : public FunctionPass {
    static char ID;
    SGVerifierPass() : FunctionPass(ID) { }

    virtual bool runOnFunction(Function& F) {
      errs() << "I saw a function called " << F.getName() << "!\n";
      errs() << "Function body:\n" << F << "\n";
      for (auto& B : F) {
        errs() << "Basic block:\n" << B << "\n";
        for (auto& I : B) {
          errs() << "Instruction: " << I << "\n";
          auto fnCall = dyn_cast<CallInst>(&I);
          if (fnCall) {
            errs() << "*** CallInst with name: " << fnCall->getCalledFunction()->getName() << "\n";
            if (fnCall->getCalledFunction()->getName().equals("llvm.var.annotation")) {
              errs() << "+++ Annotation call\n";
            }
          }
        }
      }
      return false;
    }
  };
}

char SGVerifierPass::ID = 0;

static void registerSGVerifierPass(const PassManagerBuilder &, legacy::PassManagerBase &PM) {
  PM.add(new SGVerifierPass());
}

static RegisterStandardPasses
  RegisterMyPass(PassManagerBuilder::EP_EarlyAsPossible,
  registerSGVerifierPass);

