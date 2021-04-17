#ifndef CONSTRAINT_GEN_H
#define CONSTRAINT_GEN_H

#include "SetExpr.h"

#include <string>
#include <vector>

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

  std::vector<NodeId> entryNodes;

  void pushConstraint(SetExprAtom*, SetExpr*);

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
  void handle(const clang::Expr* e);
  void handle(const clang::ImplicitCastExpr* e);
  void handle(const clang::DeclRefExpr* dre);

  template<typename S, typename T>
  void handleCasted(const T* x);

  std::vector< std::pair<NodeId, NodeId> > sPairs;
  std::vector<NodeId> tNodes;

  void connect(NodeId x, NodeId y);
  void nop(NodeId x);
  void merge(NodeId x, NodeId y);

  const clang::ast_matchers::MatchFinder::MatchResult* result;
public:
  /* ConstraintGenerator(); */

  void run(const clang::ast_matchers::MatchFinder::MatchResult &Result);

  const SetConstraints& getConstraints() const;

  void finalizeConstraints();

  const IdGenerator<NodeId>& getNodeIdGen() const;
  const IdGenerator<VarId>& getVarIdGen() const;

  const std::vector< std::pair<NodeId, NodeId> >& getSPairs() const;
  const std::vector<NodeId>& getTNodes() const;
};

#endif

