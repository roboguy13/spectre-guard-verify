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
  return nodeIdGen.getId(x->getID(*result->Context));
}

template<>
NodeId ConstraintGenerator::node<VarDecl>(const VarDecl* x) {
  return nodeIdGen.getId(x->getID());
}

template<>
NodeId ConstraintGenerator::node<Decl>(const Decl* x) {
  return nodeIdGen.getId(x->getID());
}

template<>
NodeId ConstraintGenerator::node<FunctionDecl>(const FunctionDecl* x) {
  return nodeIdGen.getId(x->getID());
}

template<typename T>
VarId ConstraintGenerator::var(const T* x) {
  return varIdGen.getId(x->getID());
}

template<typename S, typename T>
void ConstraintGenerator::handleCasted(const T* x) {
  NodeId n1 = node(x);
  NodeId n2 = node(static_cast<const S*>(x));
  handle(static_cast<const S*>(x));
  if (n1.id != n2.id) {
    connect(n2, n1);
  }
}

void ConstraintGenerator::connect(NodeId x, NodeId y) {
  /* cerr << "\t" << x.id << " -----> " << y.id << "\n"; */
  pushConstraint(new C_Entry(y), new C_Exit(x));
}

void ConstraintGenerator::nop(NodeId x) {
  pushConstraint(new C_Exit(x), new C_Entry(x));
}

void ConstraintGenerator::pushConstraint(SetExprAtom* lhs, SetExpr* rhs) {
  constraints.push_back(new SetConstraint(lhs, rhs));
}

void ConstraintGenerator::handle(const Stmt* stmt) {
  if (!stmt) return;

  if (CompoundStmt::classof(stmt)) {
    /* handle(static_cast<const CompoundStmt*>(stmt)); */
    handleCasted<CompoundStmt>(stmt);
  } else if (IfStmt::classof(stmt)) {
    /* handle(static_cast<const IfStmt*>(stmt)); */
    handleCasted<IfStmt>(stmt);
  } else if (BinaryOperator::classof(stmt)) {
    /* handle(static_cast<const BinaryOperator*>(stmt)); */
    handleCasted<BinaryOperator>(stmt);
  } else if (DeclStmt::classof(stmt)) {
    /* handle(static_cast<const DeclStmt*>(stmt)); */
    handleCasted<DeclStmt>(stmt);
  } else {
    NodeId n = node(stmt);

    /* pushConstraint(new C_Exit(n), new C_Entry(n)); */
  }
}

void ConstraintGenerator::handle(const ImplicitCastExpr* e) {
  auto e2 = e->getSubExprAsWritten();
  pushConstraint(new E_Family(node(e)), new E_Family(node(e2)));

  connect(node(e), node(e2));

  handle(e2);
}

void ConstraintGenerator::handle(const BinaryOperator* b) {
  if (!b) return;

  auto lhs = b->getLHS();
  auto n = node(b);
  auto m = node(b->getRHS());

  if (b->isAssignmentOp()) {

    if (DeclRefExpr::classof(lhs)) {

      handleCasted<DeclRefExpr>(lhs);

      auto v = var(static_cast<const DeclRefExpr*>(lhs)->getFoundDecl());

      pushConstraint(new C_Exit(n), new SetIfThenElse(new PairIn(v, PUBLIC, new C_Entry(n)),
                                                      new SetUnionPair(new C_Entry(n), v, new SensT(m)),
                                                      new C_Entry(n)));
      tNodes.push_back(m);
    }
  } else {
    pushConstraint(new E_Family(n), new SetUnion(new E_Family(node(b->getLHS())), new E_Family(node(b->getRHS()))));
    handle(b->getLHS());
  }
  handle(b->getRHS());
  /* handle(b->getLHS()); */
}

void ConstraintGenerator::handle(const IfStmt* stmt) {
  if (!stmt) return;
}

void ConstraintGenerator::handle(const DeclRefExpr* dre) {
  connect(node(dre), node(dre));
}

void ConstraintGenerator::handle(const CompoundStmt* cs) {
  if (!cs) return;

  if (!cs->body_empty()) {
    if (const Stmt* last = *(cs->body_begin())) {
      nop(node(cs));

      connect(node(cs), node(last));

      handle(last);

      for (auto it = cs->body_begin()+1; it != cs->body_end(); ++it) {
        /* cerr << "\t" << node(last).id << " -----> " << node(*it).id << "\n"; */
        connect(node(last), node(*it));
        handle(*it);
        last = *it;
      }
      /* pushConstraint(new C_Exit(node(cs)), new C_Exit(node(last))); */
    }
  } else {
    /* pushConstraint(new C_Exit(node(cs)), new C_Entry(node(cs))); */
  }
}

void ConstraintGenerator::handle(const DeclStmt* d) {
  auto last = *(d->decl_begin());
  if (VarDecl::classof(last)) {
    std::cerr << "node ids: " << node(d).id << ", " << node(static_cast<const VarDecl*>(last)).id << std::endl;
    std::cerr << "^---> node ids: " << node(d).id << ", " << node(static_cast<const VarDecl*>(last)).id << std::endl;
    handleCasted<VarDecl>(last);
    connect(node(d), node(static_cast<const VarDecl*>(last))); //, node(d));
  } else {
    /* std::cerr << "not VarDecl ????\n"; */
  }
  for (auto it = d->decl_begin()+1; it != d->decl_end(); ++it) {
    if (VarDecl::classof(*it)) {
      /* handle(static_cast<const VarDecl*>(*it)); */
      handleCasted<VarDecl>(*it);
    }
    /* pushConstraint(new C_Entry(node(*it)), new C_Entry(node(last))); */
    connect(node(last), node(*it));
    last = *it;
  }
  /* pushConstraint(new C_Exit(node(d)), new C_Exit(node(last))); */
  /* pushConstraint(new C_Exit(node(d)), new C_Entry(node(d))); */
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
  auto n = node(e);

  if (BinaryOperator::classof(e)) {
    /* handle(static_cast<const BinaryOperator*>(e)); */
    handleCasted<BinaryOperator>(e);
  } else if (DeclRefExpr::classof(e)) {
    auto v = var(static_cast<const DeclRefExpr*>(e)->getFoundDecl());

    pushConstraint(new E_Family(n), new SingleVar(v));
    handleCasted<DeclRefExpr>(e);
  } else if (ImplicitCastExpr::classof(e)) {
    /* handle(static_cast<const ImplicitCastExpr*>(e)); */
    handleCasted<ImplicitCastExpr>(e);
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
      pushConstraint(new C_Entry(node(f)), new EmptySet());
      pushConstraint(new C_Exit(node(f)), new C_Entry(node(f)));
      pushConstraint(new C_Entry(node(f->getBody())), new C_Exit(node(f)));
      handle(f->getBody());
    }
  }
}

void ConstraintGenerator::finalizeConstraints() {
  /* for (auto it = entryNodes.begin(); it != entryNodes.end(); ++it) { */
  /*   pushConstraint(new C_Entry(*it), new EmptySet()); */
  /* } */
  /* auto n = nodeIdGen.getId(0); */
  /* pushConstraint(new C_Entry(n), new EmptySet()); */
}

const SetConstraints& ConstraintGenerator::getConstraints() const { return constraints; }

const IdGenerator<NodeId>& ConstraintGenerator::getNodeIdGen() const { return nodeIdGen; }
const IdGenerator<VarId>& ConstraintGenerator::getVarIdGen() const { return varIdGen; }

const std::vector< std::pair<NodeId, NodeId> >& ConstraintGenerator::getSPairs() const { return sPairs; }
const std::vector<NodeId>& ConstraintGenerator::getTNodes() const { return tNodes; }

