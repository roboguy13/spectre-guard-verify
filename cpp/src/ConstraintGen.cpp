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
  return nodeIdGen.getId(x->getID());
}

template<typename T>
NodeId ConstraintGenerator::node1(const T* x) {
  return nodeIdGen.getId(x->getID(*result->Context));
}

template<typename T>
VarId ConstraintGenerator::var(const T* x) {
  return varIdGen.getId(x->getID());
}

void ConstraintGenerator::pushConstraint(SetExprAtom* lhs, SetExpr* rhs) {
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
    NodeId n = node1(stmt);

    pushConstraint(new C_Exit(n), new C_Entry(n));
  }
}

void ConstraintGenerator::handle(const ImplicitCastExpr* e) {
  auto e2 = e->getSubExprAsWritten();
  pushConstraint(new E_Family(node1(e)), new E_Family(node1(e2)));
  handle(e2);
}

void ConstraintGenerator::handle(const BinaryOperator* b) {
  if (!b) return;

  auto lhs = b->getLHS();
  auto n = node1(b);
  auto m = node1(b->getRHS());

  if (b->isAssignmentOp()) {

    if (DeclRefExpr::classof(lhs)) {

      auto v = var(static_cast<const DeclRefExpr*>(lhs)->getFoundDecl());

      pushConstraint(new C_Exit(n), new SetIfThenElse(new PairIn(v, PUBLIC, new C_Entry(n)),
                                                      new SetUnionPair(new C_Entry(n), v, new SensT(m)),
                                                      new C_Entry(n)));
      tNodes.push_back(m);
    }
  } else {
    pushConstraint(new E_Family(n), new SetUnion(new E_Family(node1(b->getLHS())), new E_Family(node1(b->getRHS()))));
  }
  handle(b->getRHS());
  handle(b->getLHS());
}

void ConstraintGenerator::handle(const IfStmt* stmt) {
  if (!stmt) return;
}

void ConstraintGenerator::handle(const CompoundStmt* cs) {
  if (!cs) return;

  if (!cs->body_empty()) {
    if (const Stmt* last = *(cs->body_begin())) {
      handle(last);
      for (auto it = cs->body_begin()+1; it != cs->body_end(); ++it) {
        pushConstraint(new C_Entry(node1(*it)), new C_Exit(node1(last)));
        handle(*it);
        last = *it;
      }
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
  LangOptions langOpts;


  for (auto it = d->getAttrs().begin(); it != d->getAttrs().end(); ++it) {
    string attr = Lexer::getSourceText(CharSourceRange::getTokenRange((*it)->getRange()), d->getASTContext().getSourceManager(), langOpts).str();

    if (attr == "annotate(\"nospec\")") {
      pushConstraint(new C_Exit(n), new SetUnionPair(new C_Entry(n), v, new SensAtom(SECRET)));
      return;
    }
  }

  pushConstraint(new C_Exit(n), new SetUnionPair(new C_Entry(n), v, new SensAtom(PUBLIC)));
}

void ConstraintGenerator::handle(const Expr* e) {
  auto n = node1(e);

  if (BinaryOperator::classof(e)) {
    handle(static_cast<const BinaryOperator*>(e));
  } else if (DeclRefExpr::classof(e)) {
    auto v = var(static_cast<const DeclRefExpr*>(e)->getFoundDecl());

    pushConstraint(new E_Family(n), new SingleVar(v));
  } else if (ImplicitCastExpr::classof(e)) {
    handle(static_cast<const ImplicitCastExpr*>(e));
  } else {
    std::cerr << "handle else\n";
  }
}

/* ConstraintGenerator::ConstraintGenerator(ASTContext& context) : context(context) { */
/* } */

void ConstraintGenerator::run(const clang::ast_matchers::MatchFinder::MatchResult &result) {
  this->result = &result;
  if (const FunctionDecl* f = result.Nodes.getNodeAs<FunctionDecl>("functionDecl")) {
    if (f->hasBody()) {
      entryNodes.push_back(node(f));
    }
    handle(f->getBody());
  }
}

void ConstraintGenerator::finalizeConstraints() {
  for (auto it = entryNodes.begin(); it != entryNodes.end(); ++it) {
    pushConstraint(new C_Entry(*it), new EmptySet());
  }
  /* auto n = nodeIdGen.getId(0); */
  /* pushConstraint(new C_Entry(n), new EmptySet()); */
}

const SetConstraints& ConstraintGenerator::getConstraints() const { return constraints; }

const IdGenerator<NodeId>& ConstraintGenerator::getNodeIdGen() const { return nodeIdGen; }
const IdGenerator<VarId>& ConstraintGenerator::getVarIdGen() const { return varIdGen; }

const std::vector< std::pair<NodeId, NodeId> >& ConstraintGenerator::getSPairs() const { return sPairs; }
const std::vector<NodeId>& ConstraintGenerator::getTNodes() const { return tNodes; }

