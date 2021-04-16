#ifndef SET_EXPR_H
#define SET_EXPR_H

#include <set>
#include <vector>
#include <string>
#include <map>

#include <clang-c/Index.h>

enum Sensitivity
{
  PUBLIC,
  SECRET
};

struct NodeId
{
  CXCursor cursor;
  int id;
};

struct VarId {
  int id;
};

bool operator==(const NodeId x, const NodeId y);
bool operator<(const NodeId x, const NodeId y);

bool operator==(const VarId x, const VarId y);
bool operator<(const VarId x, const VarId y);

class NodeIdGenerator
{
  int uniq;
  std::map<int, NodeId> nodeIds;
public:
  NodeIdGenerator();

  NodeId getNodeId(CXCursor);
};

class SetExprVisitor;

class SetExpr
{
public:
  virtual std::set<NodeId> getNodeIds() const=0;
  virtual std::string ppr() const=0;

  virtual void accept(SetExprVisitor& visitor) const=0;
};

class EmptySet : public SetExpr
{
  std::set<NodeId> getNodeIds() const;
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

  std::set<NodeId> getNodeIds() const;

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

  std::set<NodeId> getNodeIds() const;
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
  std::set<NodeId> getNodeIds() const;

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

  std::set<NodeId> getNodeIds() const;

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
};

struct ConditionVisitor
{
  virtual void visit(const SensEqual&)=0;
  virtual void visit(const PairIn&)=0;
};

#endif

