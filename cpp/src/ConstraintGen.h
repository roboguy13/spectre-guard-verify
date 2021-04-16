#ifndef CONSTRAINT_GEN_H
#define CONSTRAINT_GEN_H

#include "SetExpr.h"

#include <string>

class ConstraintGenerator
{
  SetConstraints constraints;
  NodeIdGenerator nIdGen;


  static CXChildVisitResult cursorVisitor(CXCursor cursor, CXCursor parent, CXClientData clientData);
  static CXChildVisitResult funcDeclVisitor(CXCursor cursor, CXCursor parent, CXClientData clientData);
  static CXChildVisitResult compoundStmtVisitor(CXCursor cursor, CXCursor parent, CXClientData clientData);
  static CXChildVisitResult varDeclVisitor(CXCursor cursor, CXCursor parent, CXClientData clientData);
  static CXChildVisitResult binaryOpVisitor(CXCursor cursor, CXCursor parent, CXClientData clientData);

public:
  SetConstraints genConstraintsForFile(std::string fileName);
};

#endif

