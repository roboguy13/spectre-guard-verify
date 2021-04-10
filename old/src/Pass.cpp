#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
using namespace llvm;

namespace {
  struct SGVerifierPass : public FunctionPass {
    static char ID;
    SGVerifierPass() : FunctionPass(ID) { }

    virtual bool runOnFunction(Function& F) {
      errs() << "I saw a function called " << F.getName() << "!\n";
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

