#ifndef SET_EXPR_H
#define SET_EXPR_H

#include <set>
#include <vector>
#include <string>
#include <map>

#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"

enum Sensitivity
{
  PUBLIC,
  SECRET
};

enum SetExprAtomKind
{
  SINGLE_VAR,
  SF_BASE,
  SF_C_ENTRY,
  SF_C_EXIT,
  SF_S,
  SF_E
};

struct NodeId
{
  clang::SourceLocation srcLoc;
  int id;
};

struct VarId {
  clang::SourceLocation srcLoc;
  int id;
};

bool operator==(const NodeId x, const NodeId y);
bool operator<(const NodeId x, const NodeId y);

bool operator==(const VarId x, const VarId y);
bool operator<(const VarId x, const VarId y);

template<typename T>
class IdGenerator
{
  int uniq;
  std::map<clang::SourceLocation, T> ids;
public:
  IdGenerator();

  T getId(clang::SourceLocation);
  T getIdByUniq(int id);
};

class SetExprVisitor;

class SetExpr
{
public:
  virtual std::string ppr() const=0;

  virtual void accept(SetExprVisitor& visitor) const=0;
};

class SetExprAtom : public SetExpr
{
public:
  const SetExprAtomKind kind = SF_BASE;
};

class C_Entry : public SetExprAtom
{
  NodeId arg;
public:
  const SetExprAtomKind kind = SF_C_ENTRY;

  C_Entry(NodeId arg);

  NodeId getArg() const;

  std::string ppr() const;

  void accept(SetExprVisitor& visitor) const;
};

class C_Exit : public SetExprAtom
{
  NodeId arg;
public:
  const SetExprAtomKind kind = SF_C_ENTRY;

  C_Exit(NodeId arg);

  NodeId getArg() const;

  std::string ppr() const;

  void accept(SetExprVisitor& visitor) const;
};

class S_Family : public SetExprAtom
{
  NodeId first, second;
public:
  const SetExprAtomKind kind = SF_S;

  S_Family(NodeId, NodeId);

  NodeId getFirst() const;
  NodeId getSecond() const;

  std::string ppr() const;

  void accept(SetExprVisitor& visitor) const;
};

class E_Family : public SetExprAtom
{
  NodeId arg;
public:
  const SetExprAtomKind kind = SF_E;

  E_Family(NodeId);

  NodeId getArg() const;

  std::string ppr() const;

  void accept(SetExprVisitor& visitor) const;
};



class EmptySet : public SetExpr
{
public:
  std::string ppr() const;

  void accept(SetExprVisitor& visitor) const;
};

class SetConstraint
{
  SetExpr* lhs;
  SetExpr* rhs;
public:
  SetConstraint(SetExpr* lhs, SetExpr* rhs);

  SetExpr* getLHS() const;
  SetExpr* getRHS() const;

  std::string ppr() const;
};

typedef std::vector<SetConstraint*> SetConstraints;

class SensExpr : public SetExpr
{
};

class SensAtom : public SensExpr
{
  Sensitivity sens;
public:
  SensAtom(Sensitivity sens);

  Sensitivity getSens() const;

  std::string ppr() const;
  void accept(SetExprVisitor& visitor) const;
};

class SensT : public SensExpr
{
  NodeId node;
public:
  SensT(NodeId node);

  NodeId getArg() const;

  std::string ppr() const;
  void accept(SetExprVisitor& visitor) const;
};

class SetUnion : public SetExpr
{
  SetExpr* lhs;
  SetExpr* rhs;
public:
  SetUnion(SetExpr* lhs, SetExpr* rhs);

  SetExpr* getLHS() const;
  SetExpr* getRHS() const;

  std::string ppr() const;
  void accept(SetExprVisitor& visitor) const;
};

// Union a singleton set containing one variable/sensitivity pair
class SetUnionPair : public SetExpr
{
  SetExpr* lhs;
  VarId var;
  Sensitivity sens;
public:
  SetUnionPair(SetExpr*, VarId, Sensitivity);

  SetExpr* getLHS() const;
  VarId getVar() const;
  Sensitivity getSens() const;

  std::string ppr() const;
  void accept(SetExprVisitor& visitor) const;
};

class ConditionVisitor;

struct Condition
{
  virtual std::string ppr() const=0;
  virtual void accept(ConditionVisitor&) const=0;
};

class SensEqual : public Condition
{
  SensExpr* lhs;
  SensExpr* rhs;
public:
  SensEqual(SensExpr*, SensExpr*);

  SensExpr* getLhs() const;
  SensExpr* getRhs() const;

  std::string ppr() const;
  void accept(ConditionVisitor& visitor) const;
};

class PairIn : public Condition
{
  SetExpr* expr;
  VarId var;
  Sensitivity sens;
public:
  PairIn(VarId, Sensitivity, SetExpr*);

  VarId getVar() const;
  Sensitivity getSens() const;
  SetExpr* getExpr() const;

  std::string ppr() const;
  void accept(ConditionVisitor& visitor) const;
};

class SetIfThenElse : public SetExpr
{
  Condition* cond;
  SetExpr* thenBranch;
  SetExpr* elseBranch;
public:
  SetIfThenElse(Condition*, SetExpr*, SetExpr*);

  Condition* getCond() const;
  SetExpr* getThen() const;
  SetExpr* getElse() const;

  std::string ppr() const;
  void accept(SetExprVisitor& visitor) const;
};

struct SetExprVisitor
{
  virtual void visit(const EmptySet&)=0;
  virtual void visit(const SensAtom&)=0;
  virtual void visit(const SensT&)=0;
  virtual void visit(const SetUnion&)=0;
  virtual void visit(const SetUnionPair&)=0;
  virtual void visit(const SetIfThenElse&)=0;

  virtual void visit(const C_Entry&)=0;
  virtual void visit(const C_Exit&)=0;
  virtual void visit(const S_Family&)=0;
  virtual void visit(const E_Family&)=0;
};

struct ConditionVisitor
{
  virtual void visit(const SensEqual&)=0;
  virtual void visit(const PairIn&)=0;
};

std::string pprSetConstraints(SetConstraints cs);

template<typename T>
IdGenerator<T>::IdGenerator() : uniq(0) { }

template<typename T>
T IdGenerator<T>::getId(clang::SourceLocation srcLoc) {
  auto it = ids.find(srcLoc);
  T id;

  if (it == ids.end()) {
    id.srcLoc = srcLoc;
    id.id = uniq;

    ids[srcLoc] = id;
    ++uniq;
  } else {
    id = it->second;
  }

  return id;
}

template<typename T>
T IdGenerator<T>::getIdByUniq(int id) {
  for (auto it = ids.begin(); it != ids.end(); ++it) {
    if (it->second.id == id) {
      return it->second;
    }
  }
}

#endif

