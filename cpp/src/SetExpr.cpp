#include "SetExpr.h"

#include <set>
#include <string>
#include <algorithm>
#include <iterator>
#include <iostream>

using std::set;
using std::string;
using std::cerr;
using namespace clang;

bool operator==(const NodeId x, const NodeId y) { return x.id == y.id; }
bool operator<(const NodeId x, const NodeId y) { return x.id < y.id; }

bool operator==(const VarId x, const VarId y) { return x.id == y.id; }
bool operator<(const VarId x, const VarId y) { return x.id < y.id; }

//
// NodeIdGenerator
//


//
// EmptySet //
//

string EmptySet::ppr() const { return "{}"; }
void EmptySet::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }

//
// SetConstraint //
//

SetConstraint::SetConstraint(SetExpr* lhs, SetExpr* rhs) : lhs(lhs), rhs(rhs) { }

SetExpr* SetConstraint::getLHS() const { return lhs; }
SetExpr* SetConstraint::getRHS() const { return rhs; }

string SetConstraint::ppr() const {
  return lhs->ppr() + " = " + rhs->ppr();
}


//
// SensAtom //
//

SensAtom::SensAtom(Sensitivity sens) : sens(sens) { }

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


string SensT::ppr() const {
  return "T(" + std::to_string(node.id) + ")";
}

void SensT::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }

//
// C_Entry
//

C_Entry::C_Entry(NodeId arg) : arg(arg) { }

NodeId C_Entry::getArg() const { return arg; }

string C_Entry::ppr() const { return "C_entry(" + std::to_string(arg.id) + ")"; }
void C_Entry::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }

//
// C_Exit
//

C_Exit::C_Exit(NodeId arg) : arg(arg) { }

NodeId C_Exit::getArg() const { return arg; }

string C_Exit::ppr() const { return "C_exit(" + std::to_string(arg.id) + ")"; }
void C_Exit::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }

//
// S_Family
//

S_Family::S_Family(NodeId first, NodeId second) : first(first), second(second) { }

NodeId S_Family::getFirst() const { return first; }
NodeId S_Family::getSecond() const { return second; }

string S_Family::ppr() const { return "S(" + std::to_string(first.id) + ", " + std::to_string(second.id) + ")"; }
void S_Family::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }

//
// E_Family
//

E_Family::E_Family(NodeId arg) : arg(arg) { }

NodeId E_Family::getArg() const { return arg; }

string E_Family::ppr() const { return "E(" + std::to_string(arg.id) + ")"; }

void E_Family::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }

//
// SetUnion //
//

SetUnion::SetUnion(SetExpr* lhs, SetExpr* rhs) : lhs(lhs), rhs(rhs) { }

SetExpr* SetUnion::getLHS() const { return lhs; }
SetExpr* SetUnion::getRHS() const { return rhs; }

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

string pprSetConstraints(SetConstraints cs) {
  string r = "";
  for (auto it = cs.begin(); it != cs.end(); ++it) {
    r += (*it)->ppr() + "\n";
  }
  return r;
}

