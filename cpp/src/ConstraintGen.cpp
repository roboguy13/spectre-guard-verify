#include "ConstraintGen.h"
#include "SetExpr.h"

/* #include <clang-c/Index.h> */
#include "clang/AST/ASTContext.h"



#include <clang-c/Index.h>
#include <clang-c/Platform.h>

#include <string>
#include <iostream>
using std::cerr;
using std::endl;
using std::string;

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
  /* std::cout << "cursor: " << clang_getCString(clang_getCursorSpelling(cursor)) << endl; */

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


