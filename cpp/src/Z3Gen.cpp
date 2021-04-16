#include "Z3Gen.h"
#include <z3.h>

#include <array>
#include <string>

#include <iostream>
using std::cerr;

template<typename T, typename F>
z3::sort Z3Gen::toEnumSort(char const* sortName, std::string prefix, std::vector<T>& ids, F toStr, z3::func_decl_vector& cs) {
  char** names = new char*[ids.size()];

  for (int i = 0; i < ids.size(); ++i) {
    std::string name = prefix + toStr(ids[i]);//std::to_string(ids[i].id);
    names[i] = new char[name.size()];
    strcpy(names[i], name.c_str());
  }

  /* z3::func_decl_vector cs(context); */
  z3::func_decl_vector ts(context);

  auto r = context.enumeration_sort(sortName, ids.size(), names, cs, ts);
  return r;
}

Z3Gen::Z3Gen(IdGenerator<VarId>& varGen, IdGenerator<NodeId>& nodeGen) : varSort(context), nodeIdSort(context), sensSort(context), var_cs(context), nodeId_cs(context), sens_cs(context)
 , s_decl(context), t_decl(context), c_entry_decl(context), c_exit_decl(context) {
  vars = varGen.getIds();
  nodeIds = nodeGen.getIds();

  // TODO: Are these sorts necessary?
  std::sort(vars.begin(), vars.end());
  std::sort(nodeIds.begin(), nodeIds.end());

  std::vector<std::string> sensNames = {"Public", "Secret"};

  varSort = toEnumSort("Var", "v", vars, [](auto v) { return std::to_string(v.id); }, var_cs);
  nodeIdSort = toEnumSort("Node", "n", nodeIds, [](auto n) { return std::to_string(n.id); }, nodeId_cs);
  sensSort = toEnumSort("Sensitivity", "", sensNames, [](auto s) { return s; }, sens_cs);

  auto boolSort = z3::to_sort(context, Z3_mk_bool_sort(context));

  z3::sort s_sorts[4] = { nodeIdSort, nodeIdSort, varSort, sensSort };
  z3::sort t_sorts[1] = { nodeIdSort };

  s_decl = context.function("S", 4, s_sorts, boolSort);
  t_decl = context.function("T", 1, t_sorts, sensSort);


  z3::sort c_entry_sorts[3] = { nodeIdSort, varSort, sensSort };
  c_entry_decl = context.function("C_Entry", 3, c_entry_sorts, boolSort);
  c_exit_decl = context.function("C_Exit", 3, c_entry_sorts, boolSort);
}

z3::sort Z3Gen::getVarSort() const { return varSort; }
z3::sort Z3Gen::getNodeIdSort() const { return nodeIdSort; }
z3::sort Z3Gen::getSensSort() const { return sensSort; }


z3::func_decl Z3Gen::getVarFuncDecl(VarId v) const {
  return var_cs[v.id];
}

z3::func_decl Z3Gen::getNodeIdFuncDecl(NodeId n) const {
  return nodeId_cs[n.id];
}

z3::func_decl Z3Gen::getSensFuncDecl(Sensitivity s) const {
  switch (s) {
    case PUBLIC:
      return sens_cs[0];
    case SECRET:
      return sens_cs[1];
  }
}

z3::expr Z3Gen::node(NodeId n) const {
  return getNodeIdFuncDecl(n)();
}
z3::expr Z3Gen::var(VarId v) const {
  return getVarFuncDecl(v)();
}
z3::expr Z3Gen::sens(Sensitivity s) const {
  return getSensFuncDecl(s)();
}

z3::func_decl Z3Gen::getTFuncDecl() const { return t_decl; }
z3::func_decl Z3Gen::getSFuncDecl() const { return s_decl; }
z3::func_decl Z3Gen::getCEntryFuncDecl() const { return c_entry_decl; }
z3::func_decl Z3Gen::getCExitFuncDecl() const { return c_exit_decl; }

z3::context* Z3Gen::getContext() { return &context; }

Z3SetExprVisitor::Z3SetExprVisitor(Z3Gen& z3Gen, z3::expr expr, NodeId n, VarId v, Sensitivity s) : expr(expr), z3Gen(z3Gen), n(n), v(v), s(s) { }

void Z3SetExprVisitor::visit(const EmptySet&) { cerr << "*** error: visit: EmptySet\n"; }

void Z3SetExprVisitor::visit(const SensAtom& sa) {
  expr = z3Gen.sens(sa.getSens());
}

void Z3SetExprVisitor::visit(const SensT& t) {
  expr = z3Gen.getTFuncDecl()(z3Gen.node(t.getArg()));
}

void Z3SetExprVisitor::visit(const SetUnion& u) {
  u.getLHS()->accept(*this);
  auto lhsExpr = expr;

  u.getRHS()->accept(*this);
  auto rhsExpr = expr;

  expr = lhsExpr || rhsExpr;
}

void Z3SetExprVisitor::visit(const SetUnionPair& u) {
  u.getLHS()->accept(*this);
  auto lhsExpr = expr;

  auto varExpr = z3Gen.var(u.getVar());

  u.getSens()->accept(*this);
  auto sensExpr = expr;

  expr = lhsExpr || (z3Gen.var(v) == varExpr && z3Gen.sens(s) == sensExpr);
}

void Z3SetExprVisitor::visit(const SetIfThenElse&) {
}

void Z3SetExprVisitor::visit(const C_Entry&) { }
void Z3SetExprVisitor::visit(const C_Exit&) { }
void Z3SetExprVisitor::visit(const S_Family&) { }
void Z3SetExprVisitor::visit(const E_Family&) { }

