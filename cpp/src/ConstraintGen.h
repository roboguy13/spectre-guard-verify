#ifndef CONSTRAINT_GEN_H
#define CONSTRAINT_GEN_H

#include "SetExpr.h"

#include <string>

#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"

#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"

class ConstraintGenerator : public clang::ast_matchers::MatchFinder::MatchCallback
{
  SetConstraints constraints;
  IdGenerator<NodeId> nodeIdGen;
  IdGenerator<VarId>  varIdGen;

  void pushConstraint(SetExpr*, SetExpr*);

  template<typename T>
  NodeId node(const T* t);

  template<typename T>
  VarId var(const T* t);

  void handle(const clang::IfStmt* stmt);
  void handle(const clang::Stmt* stmt);
  void handle(const clang::CompoundStmt* cs);
  void handle(const clang::BinaryOperator* b);
  void handle(const clang::DeclStmt*);
  void handle(const clang::VarDecl*);
public:
  ConstraintGenerator();

  void run(const clang::ast_matchers::MatchFinder::MatchResult &Result);

  SetConstraints getConstraints() const;

  void finalizeConstraints();
};

#endif

