#include "ConstraintGen.h"
#include "SetExpr.h"

#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"

/* #include <clang-c/Index.h> */
#include "clang/AST/ASTContext.h"

#include "llvm/Support/CommandLine.h"


#include <clang-c/Index.h>
#include <clang-c/Platform.h>

#include <string>
#include <iostream>

using std::cout;
using std::cerr;
using std::endl;
using std::string;

using namespace clang::tooling;
using namespace clang;
using namespace llvm;

template<typename T>
NodeId ConstraintGenerator::node(const T* x) {
  return nodeIdGen.getId(x->getBeginLoc());
}

template<typename T>
VarId ConstraintGenerator::var(const T* x) {
  return varIdGen.getId(x->getSourceRange().getBegin());
}

void ConstraintGenerator::pushConstraint(SetExpr* lhs, SetExpr* rhs) {
  constraints.push_back(new SetConstraint(lhs, rhs));
}

void ConstraintGenerator::handle(const Stmt* stmt) {
  if (!stmt) return;

  if (CompoundStmt::classof(stmt)) {
    handle(static_cast<const CompoundStmt*>(stmt));
  } else if (IfStmt::classof(stmt)) {
    handle(static_cast<const IfStmt*>(stmt));
  } else if (BinaryOperator::classof(stmt)) {
    handle(static_cast<const BinaryOperator*>(stmt));
  } else if (DeclStmt::classof(stmt)) {
    handle(static_cast<const DeclStmt*>(stmt));
  } else {
    NodeId n = node(stmt);

    pushConstraint(new C_Exit(n), new C_Entry(n));
  }
}

void ConstraintGenerator::handle(const BinaryOperator* b) {
  if (!b) return;
}

void ConstraintGenerator::handle(const IfStmt* stmt) {
  if (!stmt) return;
}

void ConstraintGenerator::handle(const CompoundStmt* cs) {
  if (!cs) return;

  if (const Stmt* last = *(cs->body_begin())) {
    handle(last);
    for (auto it = cs->body_begin()+1; it != cs->body_end(); ++it) {
      pushConstraint(new C_Entry(node(*it)), new C_Exit(node(last)));
      handle(*it);
      last = *it;
    }
  }
}

void ConstraintGenerator::handle(const DeclStmt* d) {
  for (auto it = d->decl_begin(); it != d->decl_end(); ++it) {
    if (VarDecl::classof(*it)) {
      handle(static_cast<const VarDecl*>(*it));
    }
  }
}

void ConstraintGenerator::handle(const VarDecl* d) {
  auto n = node(d);
  auto v = var(d);

  for (auto it = d->getAttrs().begin(); it != d->getAttrs().end(); ++it) {
    if (string((*it)->getSpelling()) == "nospec") {
      pushConstraint(new C_Exit(n), new SetUnionPair(new C_Entry(n), v, SECRET));
      return;
    }
  }

  pushConstraint(new C_Exit(n), new SetUnionPair(new C_Entry(n), v, PUBLIC));
}

ConstraintGenerator::ConstraintGenerator() {
}

void ConstraintGenerator::run(const clang::ast_matchers::MatchFinder::MatchResult &result) {
  if (const FunctionDecl* f = result.Nodes.getNodeAs<FunctionDecl>("functionDecl")) {
    handle(f->getBody());
  }
}

void ConstraintGenerator::finalizeConstraints() {
  auto n = nodeIdGen.getIdByUniq(0);
  pushConstraint(new C_Entry(n), new EmptySet());
}

SetConstraints ConstraintGenerator::getConstraints() const { return constraints; }

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

  llvm::errs() << "plugin output\n";
  ConstraintGenerator gen;

  auto matcher = ast_matchers::functionDecl().bind("functionDecl");
  ast_matchers::MatchFinder finder;

  finder.addMatcher(matcher, &gen);


  int r = tool.run(newFrontendActionFactory(&finder).get());
  gen.finalizeConstraints();

  llvm::errs() << pprSetConstraints(gen.getConstraints());

  return r;
  /* return Tool.run(newFrontendActionFactory<clang::SyntaxOnlyAction>().get()); */
}

