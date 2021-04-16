#ifndef Z3GEN_H
#define Z3GEN_H

#include "SetExpr.h"

#include <vector>
#include <functional>
#include <z3++.h>

class Z3Gen
{
  std::vector<VarId> vars;
  std::vector<NodeId> nodeIds;

  z3::context context;

  z3::sort varSort, nodeIdSort, sensSort;

  z3::func_decl_vector var_cs, nodeId_cs, sens_cs;

  z3::func_decl t_decl, s_decl, c_entry_decl, c_exit_decl;

  template<typename T, typename F>
  z3::sort toEnumSort(char const* sortName, std::string prefix, std::vector<T>& ids, F toStr, z3::func_decl_vector& cs);
public:
  Z3Gen(const IdGenerator<VarId>& varGen, const IdGenerator<NodeId>& nodeGen);

  z3::sort getVarSort() const;
  z3::sort getNodeIdSort() const;
  z3::sort getSensSort() const;

  z3::expr generate(const SetConstraint& c);

  std::vector<z3::expr> generate(const SetConstraints& cs);

  z3::func_decl getVarFuncDecl(VarId v) const;
  z3::func_decl getNodeIdFuncDecl(NodeId n) const;
  z3::func_decl getSensFuncDecl(Sensitivity s) const;

  z3::expr node(NodeId n) const;
  z3::expr var(VarId v) const;
  z3::expr sens(Sensitivity s) const;

  z3::func_decl getTFuncDecl() const;
  z3::func_decl getSFuncDecl() const;
  z3::func_decl getCEntryFuncDecl() const;
  z3::func_decl getCExitFuncDecl() const;

  z3::context* getContext();
};

class Z3SetExprVisitor : public SetExprVisitor
{
  z3::expr expr;
  Z3Gen& z3Gen;

  z3::expr v;
  z3::expr s;
public:
  Z3SetExprVisitor(Z3Gen& z3Gen, z3::expr expr, z3::expr v, z3::expr s);
  Z3SetExprVisitor(Z3SetExprVisitor& v);

  z3::expr getExpr() const;

  void visit(const EmptySet&);
  void visit(const SensAtom&);
  void visit(const SensT&);
  void visit(const SetUnion&);
  void visit(const SetUnionPair&);
  void visit(const SetIfThenElse&);

  void visit(const C_Entry&);
  void visit(const C_Exit&);
  void visit(const S_Family&);
  void visit(const E_Family&);
};

#endif

