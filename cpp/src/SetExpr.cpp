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

string NodeId::ppr() const { return "n" + std::to_string(id); }
string VarId::ppr() const { return std::to_string(id); }

bool SetExpr::isEmptySet() const { return false; }
bool SetExpr::isSingleVar() const { return false; }
bool SetExpr::isAtom() const { return false; }

bool SetExprAtom::isEmptySet() const { return false; }
bool SetExprAtom::isAtom() const { return true; }

//
// EmptySet //
//

string EmptySet::ppr() const { return "{}"; }
void EmptySet::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }
bool EmptySet::isEmptySet() const { return true; }

//
// SetConstraint //
//

SetConstraint::SetConstraint(SetExprAtom* lhs, SetExpr* rhs) : lhs(lhs), rhs(rhs) { }

SetExprAtom* SetConstraint::getLHS() const { return lhs; }
SetExpr* SetConstraint::getRHS() const { return rhs; }

string SetConstraint::ppr() const {
  return lhs->ppr() + " = " + rhs->ppr();
}


//
// SensAtom //
//

SensAtom::SensAtom(Sensitivity sens) : sens(sens) { }

Sensitivity SensAtom::getSens() const { return sens; }

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
bool SensAtom::isEmptySet() const { return false; }

//
// SensT //
//

SensT::SensT(NodeId node) : node(node) { }

NodeId SensT::getArg() const { return node; }


string SensT::ppr() const {
  return "T(" + node.ppr() + ")";
}

void SensT::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }
bool SensT::isEmptySet() const { return false; }

//
// C_Entry
//

C_Entry::C_Entry(NodeId arg) : arg(arg) { }

NodeId C_Entry::getArg() const { return arg; }

string C_Entry::ppr() const { return "C_entry(" + arg.ppr() + ")"; }
void C_Entry::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }

SetExprAtomKind C_Entry::getKind() const { return SF_C_ENTRY; }

//
// C_Exit
//

C_Exit::C_Exit(NodeId arg) : arg(arg) { }

NodeId C_Exit::getArg() const { return arg; }

string C_Exit::ppr() const { return "C_exit(" + arg.ppr() + ")"; }
void C_Exit::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }

SetExprAtomKind C_Exit::getKind() const { return SF_C_EXIT; }
//
// S_Family
//

S_Family::S_Family(NodeId first, NodeId second) : first(first), second(second) { }

NodeId S_Family::getFirst() const { return first; }
NodeId S_Family::getSecond() const { return second; }

string S_Family::ppr() const { return "S(" + first.ppr() + ", " + second.ppr() + ")"; }
void S_Family::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }
SetExprAtomKind S_Family::getKind() const { return SF_S; }

//
// E_Family
//

E_Family::E_Family(NodeId arg) : arg(arg) { }

NodeId E_Family::getArg() const { return arg; }

string E_Family::ppr() const { return "E(" + arg.ppr() + ")"; }

void E_Family::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }
SetExprAtomKind E_Family::getKind() const { return SF_E; }

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


SetUnionPair::SetUnionPair(SetExpr* lhs, VarId var, SensExpr* sens) : lhs(lhs), var(var), sens(sens) { }

SetExpr* SetUnionPair::getLHS() const { return lhs; }
VarId SetUnionPair::getVar() const { return var; }
SensExpr* SetUnionPair::getSens() const { return sens; }

std::string SetUnionPair::ppr() const { return lhs->ppr() + " U {(" + var.ppr() + ", " + sens->ppr() + ")}"; }
void SetUnionPair::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }

//
// SingleVar
//
SingleVar::SingleVar(VarId v) : v(v) { }

VarId SingleVar::getVarId() const {
  return v;
}

std::string SingleVar::ppr() const {
  return "{" + std::to_string(v.id) + "}";
}

void SingleVar::accept(SetExprVisitor& visitor) const { visitor.visit(*this); }

bool SingleVar::isSingleVar() const { return true; }

//
// SensEqual //
//

SensEqual::SensEqual(SensExpr* lhs, SensExpr* rhs) : lhs(lhs), rhs(rhs) { }

SensExpr* SensEqual::getLHS() const { return lhs; }
SensExpr* SensEqual::getRHS() const { return rhs; }

string SensEqual::ppr() const { return lhs->ppr() + " = " + rhs->ppr(); }
void SensEqual::accept(ConditionVisitor& visitor) const { visitor.visit(*this); }
ConditionKind SensEqual::getKind() const { return SENS_EQUAL; }

//
// PairIn //
//

PairIn::PairIn(VarId var, Sensitivity sens, SetExpr* expr) : var(var), sens(sens), expr(expr) { }

VarId PairIn::getVar() const { return var; } Sensitivity PairIn::getSens() const { return sens; }
SetExpr* PairIn::getExpr() const { return expr; }

string PairIn::ppr() const { return "(" + var.ppr() + ", " + SensAtom(sens).ppr() + ") in " + expr->ppr(); }
void PairIn::accept(ConditionVisitor& visitor) const { visitor.visit(*this); }
ConditionKind PairIn::getKind() const { return PAIR_IN; }

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

