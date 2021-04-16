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
  return nodeIdGen.getNodeId(x->getBeginLoc());
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

ConstraintGenerator::ConstraintGenerator() {
}

void ConstraintGenerator::run(const clang::ast_matchers::MatchFinder::MatchResult &result) {
  if (const FunctionDecl* f = result.Nodes.getNodeAs<FunctionDecl>("functionDecl")) {
    handle(f->getBody());
  }
}

void ConstraintGenerator::finalizeConstraints() {
  auto n = nodeIdGen.getNodeIdByUniq(0);
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


/*
SetConstraints ConstraintGenerator::genConstraintsForFile(string fileName) {
  CXIndex index = clang_createIndex(0, 1);
  CXTranslationUnit tUnit = clang_parseTranslationUnit(index, fileName.c_str(), nullptr, 0,
    nullptr, 0,
    CXTranslationUnit_None);

  if (!tUnit) {
    cerr << "Cannot create translation unit for " << fileName << endl;
  }

  CXCursor topCursor = clang_getTranslationUnitCursor(tUnit);
  clang_visitChildren(topCursor, ConstraintGenerator::cursorVisitor, this);

  clang_disposeTranslationUnit(tUnit);
  clang_disposeIndex(index);

  return constraints;
}


CXChildVisitResult ConstraintGenerator::cursorVisitor(CXCursor cursor, CXCursor parent, CXClientData clientData) {
  switch (cursor.kind) {
    case CXCursor_FunctionDecl:
      clang_visitChildren(cursor, ConstraintGenerator::funcDeclVisitor, clientData);
      return CXChildVisit_Continue;

    case CXCursor_VarDecl:
      clang_visitChildren(cursor, ConstraintGenerator::varDeclVisitor, clientData);
      return CXChildVisit_Continue;

    default:
      break;
  }

  return CXChildVisit_Recurse;
}

CXChildVisitResult ConstraintGenerator::funcDeclVisitor(CXCursor cursor, CXCursor parent, CXClientData clientData) {

  switch (cursor.kind) {
    case CXCursor_CompoundStmt:
      clang_visitChildren(cursor, ConstraintGenerator::compoundStmtVisitor, clientData);
      break;

    case CXCursor_VarDecl:
      clang_visitChildren(cursor, ConstraintGenerator::varDeclVisitor, clientData);
      break;

    default:
      break;
  }
  return CXChildVisit_Continue;
}

CXChildVisitResult ConstraintGenerator::compoundStmtVisitor(CXCursor cursor, CXCursor parent, CXClientData clientData) {
  std::cout << "compound stmt: " << clang_getCString(clang_getCursorSpelling(cursor)) << endl;

  switch (cursor.kind) {
    case CXCursor_CompoundStmt:
      return CXChildVisit_Recurse;


    case CXCursor_VarDecl:
    case CXCursor_DeclStmt:
      clang_visitChildren(cursor, ConstraintGenerator::varDeclVisitor, clientData);
      return CXChildVisit_Continue;

    case CXCursor_BinaryOperator:
      clang_visitChildren(cursor, ConstraintGenerator::binaryOpVisitor, clientData);
      return CXChildVisit_Continue;

    default:
      return CXChildVisit_Continue;
  }

  return CXChildVisit_Continue;
}

CXChildVisitResult ConstraintGenerator::varDeclVisitor(CXCursor cursor, CXCursor parent, CXClientData clientData) {
  std::cout << "var decl" << endl;
  return CXChildVisit_Continue;
}

CXChildVisitResult ConstraintGenerator::binaryOpVisitor(CXCursor cursor, CXCursor parent, CXClientData clientData) {
  std::cout << "bin op: " << clang_getCString(clang_getCursorSpelling(cursor)) << endl;
  std::cout << "^--> parent bin op: " << clang_getCString(clang_getCursorSpelling(parent)) << endl;

  switch (cursor.kind) {
    case CXCursor_FirstExpr:
      std::cout << "first expr\n";
      return CXChildVisit_Recurse;
    case CXCursor_LastExpr:
      std::cout << "last expr\n";
      return CXChildVisit_Recurse;
    case CXCursor_BinaryOperator:
      return CXChildVisit_Recurse;
    default:
      return CXChildVisit_Continue;
  }
}

int main() {
  ConstraintGenerator gen;
  gen.genConstraintsForFile("../../test.c");
  return 0;
}
*/


