#include "SetExpr.h"

#include <set>
#include <string>
#include <algorithm>
#include <iterator>
#include <iostream>

using std::set;
using std::string;
using std::cerr;

bool operator==(const NodeId x, const NodeId y) { return x.id == y.id; }
bool operator<(const NodeId x, const NodeId y) { return x.id < y.id; }

bool operator==(const VarId x, const VarId y) { return x.id == y.id; }
bool operator<(const VarId x, const VarId y) { return x.id < y.id; }

//
// EmptySet //
//

set<NodeId> EmptySet::getNodeIds() const { return set<NodeId>(); }
string EmptySet::ppr() const { return "{}"; }
void EmptySet::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }

//
// SetConstraint //
//

SetConstraint::SetConstraint(SetExpr* lhs, SetExpr* rhs) : lhs(lhs), rhs(rhs) { }

SetExpr* SetConstraint::getLHS() const { return lhs; }
SetExpr* SetConstraint::getRHS() const { return rhs; }

set<NodeId> SetConstraint::getNodeIds() const {
  set<NodeId> r(lhs->getNodeIds());

  r.insert(rhs->getNodeIds().begin(), rhs->getNodeIds().end());

  return r;
}

string SetConstraint::ppr() const {
  return lhs->ppr() + " = " + rhs->ppr();
}


//
// SensAtom //
//

SensAtom::SensAtom(Sensitivity sens) : sens(sens) { }

set<NodeId> SensAtom::getNodeIds() const { return set<NodeId>(); }

string SensAtom::ppr() const {
  switch (sens) {
    case SECRET:
      return "secret";
    case PUBLIC:
      return "public";
    default:
      cerr << "SensAtom::ppr(): invalid sens";
      return "<error>";
  }
}

void SensAtom::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }

//
// SensT //
//

SensT::SensT(NodeId node) : node(node) { }

NodeId SensT::getArg() const { return node; }

set<NodeId> SensT::getNodeIds() const { return set<NodeId>({node}); }

string SensT::ppr() const {
  return "T(" + std::to_string(node.id) + ")";
}

void SensT::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }

//
// SetUnion //
//

SetUnion::SetUnion(SetExpr* lhs, SetExpr* rhs) : lhs(lhs), rhs(rhs) { }

SetExpr* SetUnion::getLHS() const { return lhs; }
SetExpr* SetUnion::getRHS() const { return rhs; }

set<NodeId> SetUnion::getNodeIds() const {
  set<NodeId> r(lhs->getNodeIds());

  r.insert(rhs->getNodeIds().begin(), rhs->getNodeIds().end());

  return r;
}

string SetUnion::ppr() const {
  return lhs->ppr() + " U " + rhs->ppr();
}

void SetUnion::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }


//
// SetUnionPair //
//


SetUnionPair::SetUnionPair(SetExpr* lhs, VarId var, Sensitivity sens) : lhs(lhs), var(var), sens(sens) { }

SetExpr* SetUnionPair::getLHS() const { return lhs; }
VarId SetUnionPair::getVar() const { return var; }
Sensitivity SetUnionPair::getSens() const { return sens; }

std::string SetUnionPair::ppr() const { return lhs->ppr() + " U {(" + std::to_string(var.id) + ", " + SensAtom(sens).ppr() + "(}"; }
void SetUnionPair::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }

//
// SensEqual //
//

SensEqual::SensEqual(SensExpr* lhs, SensExpr* rhs) : lhs(lhs), rhs(rhs) { }

SensExpr* SensEqual::getLhs() const { return lhs; }
SensExpr* SensEqual::getRhs() const { return rhs; }

string SensEqual::ppr() const { return lhs->ppr() + " = " + rhs->ppr(); }
void SensEqual::accept(ConditionVisitor& visitor) const { visitor.visit(*this); }

//
// PairIn //
//

PairIn::PairIn(VarId var, Sensitivity sens, SetExpr* expr) : var(var), sens(sens), expr(expr) { }

VarId PairIn::getVar() const { return var; }
Sensitivity PairIn::getSens() const { return sens; }
SetExpr* PairIn::getExpr() const { return expr; }

string PairIn::ppr() const { return "(" + std::to_string(var.id) + ", " + SensAtom(sens).ppr() + ") in " + expr->ppr(); }
void PairIn::accept(ConditionVisitor& visitor) const { visitor.visit(*this); }

//
// SetIfThenElse //
//

SetIfThenElse::SetIfThenElse(Condition* cond, SetExpr* thenBranch, SetExpr* elseBranch) : cond(cond), thenBranch(thenBranch), elseBranch(elseBranch) { }

Condition* SetIfThenElse::getCond() const { return cond; }
SetExpr* SetIfThenElse::getThen() const { return thenBranch; }
SetExpr* SetIfThenElse::getElse() const { return elseBranch; }

string SetIfThenElse::ppr() const { return "if " + cond->ppr() + " then " + thenBranch->ppr() + " else " + elseBranch->ppr(); }
void SetIfThenElse::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }

