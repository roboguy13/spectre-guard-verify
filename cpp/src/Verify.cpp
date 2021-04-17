#include "SetExpr.h"
#include "Z3Gen.h"
#include "ConstraintGen.h"


#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"

/* #include <clang-c/Index.h> */
#include "clang/AST/ASTContext.h"

#include "llvm/Support/CommandLine.h"

using namespace llvm;
using namespace clang;
using namespace clang::tooling;

static llvm::cl::OptionCategory MyToolCategory("sg-verify options");

static cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);

int main(int argc, const char **argv) {
  auto expectedParser = CommonOptionsParser::create(argc, argv, MyToolCategory, llvm::cl::OneOrMore);
  if (!expectedParser) {
    llvm::errs() << expectedParser.takeError();
    return 1;
  }
  CommonOptionsParser& optionsParser = expectedParser.get();
  ClangTool tool(optionsParser.getCompilations(),
                 optionsParser.getSourcePathList());

  ConstraintGenerator gen;

  auto matcher = ast_matchers::functionDecl().bind("functionDecl");
  ast_matchers::MatchFinder finder;


  finder.addMatcher(ast_matchers::traverse(TK_IgnoreUnlessSpelledInSource, matcher), &gen);



  int r = tool.run(newFrontendActionFactory(&finder).get());

  if (r != 0) return r;

  gen.finalizeConstraints();

  llvm::errs() << pprSetConstraints(gen.getConstraints());

  try {
    Z3Gen z3Gen(gen.getVarIdGen(), gen.getNodeIdGen(), gen.getSPairs(), gen.getTNodes());

    auto exprs = z3Gen.generate(gen.getConstraints());

    std::cout << "\nGenerated Z3 expressions:\n";
    for (auto it = exprs.begin(); it != exprs.end(); ++it) {
      std::cout << *it << "\n";
    }
  } catch (z3::exception e) {
    std::cerr << "Z3 exception: " << e.msg() << std::endl;
    return 1;
  }


  return r;
  /* return Tool.run(newFrontendActionFactory<clang::SyntaxOnlyAction>().get()); */
}

