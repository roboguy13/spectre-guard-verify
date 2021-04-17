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

void Z3Gen::generateSs(std::vector<z3::expr>& vec) {
  
}

void Z3Gen::generateTs(std::vector<z3::expr>& vec) {
  /* z3::expr e; */

  auto v = context.constant("v", varSort);
  auto v2 = context.constant("v2", varSort);

  for (auto it = tNodes.begin(); it != tNodes.end(); ++it) {
    auto condExpr = (z3::forall(v, !e_decl(node(*it), v)))
                        ||
                    (z3::forall(v2, implies(e_decl(node(*it), v2), c_entry_decl(node(*it), v2, sens(PUBLIC)))));

    auto e = z3::ite(condExpr, t_decl(node(*it)) == sens(PUBLIC), t_decl(node(*it)) == sens(SECRET));
    vec.push_back(e);
  }
}

void Z3Gen::generateCorrectnessCondition(std::vector<z3::expr>& vec) {
  auto n = context.constant("n", nodeIdSort);
  auto v = context.constant("v", varSort);
  auto s = context.constant("s", sensSort);
  auto s2 = context.constant("s2", sensSort);


  auto cond = c_exit_decl(n, v, s) && c_exit_decl(n, v, s2);

  auto e = z3::forall(n, z3::forall(v, s, s2,
      z3::implies(
        cond,
        s == s2
      )
    )
  );

  vec.push_back(e);
}


Z3Gen::Z3Gen(const IdGenerator<VarId>& varGen, const IdGenerator<NodeId>& nodeGen, std::vector< std::pair<NodeId, NodeId> > sPairs, std::vector<NodeId> tNodes) : varSort(context), nodeIdSort(context), sensSort(context), var_cs(context), nodeId_cs(context), sens_cs(context)
 , s_decl(context), t_decl(context), e_decl(context), c_entry_decl(context), c_exit_decl(context), sPairs(sPairs), tNodes(tNodes) {
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
  z3::sort e_sorts[2] = { nodeIdSort, varSort };

  s_decl = context.function("S", 4, s_sorts, boolSort);
  t_decl = context.function("T", 1, t_sorts, sensSort);
  e_decl = context.function("E", 2, e_sorts, boolSort);


  z3::sort c_entry_sorts[3] = { nodeIdSort, varSort, sensSort };
  c_entry_decl = context.function("C_Entry", 3, c_entry_sorts, boolSort);
  c_exit_decl = context.function("C_Exit", 3, c_entry_sorts, boolSort);
}

z3::sort Z3Gen::getVarSort() const { return varSort; }
z3::sort Z3Gen::getNodeIdSort() const { return nodeIdSort; }
z3::sort Z3Gen::getSensSort() const { return sensSort; }

z3::expr Z3Gen::generate(SetConstraint c) {
  auto trueExpr = context.bool_val(true);

  switch (c.getLHS()->getKind()) {
    case SF_C_ENTRY:
    case SF_C_EXIT:
    case SF_S:
      {
        auto v = context.constant("v", varSort);
        auto s = context.constant("s", sensSort);

        Z3SetExprVisitor visitorLHS(*this, trueExpr, v, s);
        c.getLHS()->accept(visitorLHS);

        if (c.getRHS()->isEmptySet()) {
          return z3::forall(v, s, !visitorLHS.getExpr());
        } else {
          Z3SetExprVisitor visitorRHS(*this, trueExpr, v, s);

          c.getRHS()->accept(visitorRHS);

          return z3::forall(v, s, visitorLHS.getExpr() == visitorRHS.getExpr());
        }
      }
    case SF_E:
      {
        auto v = context.constant("v", varSort);
        auto n = node(static_cast<const E_Family*>(c.getLHS())->getArg());
        auto s_ = context.constant("s_", sensSort);


        Z3SetExprVisitor visitorLHS(*this, n, v, s_);
        c.getLHS()->accept(visitorLHS);

        if (c.getRHS()->isSingleVar()) {
          return z3::forall(v,
            z3::ite(v == var(static_cast<const SingleVar*>(c.getRHS())->getVarId()),
              visitorLHS.getExpr(),
              !visitorLHS.getExpr()
            )
          );
        } else if (c.getRHS()->isAtom() && static_cast<const SetExprAtom*>(c.getRHS())->getKind() == SF_E) {
          /* auto m = node(static_cast<const E_Family*>(c.getRHS())->getArg()); */

          /* Z3SetExprVisitor visitorRHS(*this, m, v, s_); */
          Z3SetExprVisitor visitorRHS(*this, n, v, s_);
          c.getRHS()->accept(visitorRHS);
          auto rhsExpr = visitorRHS.getExpr();
          return z3::forall(v, e_decl(n, v) == rhsExpr);
        } else {
          Z3SetExprVisitor visitorRHS(*this, n, v, s_);
          c.getRHS()->accept(visitorRHS);
          auto rhsExpr = visitorRHS.getExpr();
          return z3::forall(v, e_decl(n, v) == rhsExpr);
          /* std::cerr << "*** rhs not SF_E" << std::endl; */
          /* throw std::exception(); */
          /* exit(2); */
        }

        /* auto r = z3::forall(v, e_decl(n, v) == rhsExpr); */
        /* cerr << "r = " << r << "\n"; */
        /* return r; */
      }
    default:
      std::cerr << "*** error: Z3Gen::generate: Unrecognize LHS of kind " << c.getLHS()->getKind() << std::endl;
      exit(1);
  }
}

std::vector<z3::expr> Z3Gen::generate(SetConstraints cs) {
  std::vector<z3::expr> r;

  for (auto it = cs.begin(); it != cs.end(); ++it) {
    r.push_back(generate(*(*it)));
  }

  generateSs(r);
  generateTs(r);
  generateCorrectnessCondition(r);

  return r;
}

void Z3Gen::assertExprs(const std::vector<z3::expr>& es) {
  z3::solver solver(context);

  for (auto it = es.begin(); it != es.end(); ++it) {
    solver.add(*it);
  }

  auto result = solver.check();
  switch (result) {
    case z3::unsat:
      std::cout << "Solver: Unsat\n";
      break;
    case z3::sat:
      std::cout << "Solver: Sat\n";
      std::cout << "--- Model ---\n";
      std::cout << solver.get_model() << "\n";
      break;
    case z3::unknown:
      std::cout << "Solver: Unknown\n";
      break;
  }
}


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
z3::func_decl Z3Gen::getEFuncDecl() const { return e_decl; }

z3::context* Z3Gen::getContext() { return &context; }

Z3SetExprVisitor::Z3SetExprVisitor(Z3Gen& z3Gen, z3::expr expr, z3::expr v, z3::expr s) : expr(expr), z3Gen(z3Gen), v(v), s(s) { }

Z3SetExprVisitor::Z3SetExprVisitor(Z3SetExprVisitor& visitor)
  : expr(visitor.expr), z3Gen(visitor.z3Gen), v(visitor.v), s(visitor.s) { }

void Z3SetExprVisitor::visit(const EmptySet&) { cerr << "*** error: visit: EmptySet\n"; }

void Z3SetExprVisitor::visit(const SensAtom& sa) {
  expr = z3Gen.sens(sa.getSens());
}

void Z3SetExprVisitor::visit(const SensT& t) {
  expr = z3Gen.getTFuncDecl()(z3Gen.node(t.getArg()));
}

void Z3SetExprVisitor::visit(const SetUnion& u) {
  auto oldExpr = expr;

  u.getLHS()->accept(*this);
  auto lhsExpr = expr;

  expr = oldExpr;

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

  expr = lhsExpr || (v == varExpr && s == sensExpr);
}

void Z3SetExprVisitor::visit(const SetIfThenElse& ite) {
  switch (ite.getCond()->getKind()) {
    case SENS_EQUAL:
      {
        SensEqual* eq = static_cast<SensEqual*>(ite.getCond());

        eq->getLHS()->accept(*this);
        auto eqX = expr;

        eq->getRHS()->accept(*this);
        auto eqY = expr;

        ite.getThen()->accept(*this);
        auto thenExpr = expr;

        ite.getElse()->accept(*this);
        auto elseExpr = expr;

        expr = z3::ite(eqX == eqY, thenExpr, elseExpr);
        break;
      }
    case PAIR_IN:
      {
        PairIn* pairIn = static_cast<PairIn*>(ite.getCond());

        Z3SetExprVisitor visitor(*this);
        visitor.v = z3Gen.var(pairIn->getVar());
        visitor.s = z3Gen.sens(pairIn->getSens());
        pairIn->getExpr()->accept(visitor);


        ite.getThen()->accept(*this);
        auto thenExpr = expr;

        ite.getElse()->accept(*this);
        auto elseExpr = expr;

        expr = z3::ite(visitor.expr, thenExpr, elseExpr);
        break;
      }
  }
}

void Z3SetExprVisitor::visit(const C_Entry& e) {
  expr = z3Gen.getCEntryFuncDecl()(z3Gen.node(e.getArg()), v, s);
}
void Z3SetExprVisitor::visit(const C_Exit& e) {
  expr = z3Gen.getCExitFuncDecl()(z3Gen.node(e.getArg()), v, s);
}
void Z3SetExprVisitor::visit(const S_Family& sf) {
  auto firstExpr = z3Gen.node(sf.getFirst());
  auto secondExpr = z3Gen.node(sf.getSecond());

  expr = z3Gen.getSFuncDecl()(firstExpr, secondExpr, v, s);
}
void Z3SetExprVisitor::visit(const E_Family& ef) {
  expr = z3Gen.getEFuncDecl()(expr, v);
  /* std::cerr << "*** error: Z3SetExprVisitor::visit: called on E_Family\n"; */
}
void Z3SetExprVisitor::visit(const SingleVar& sv) {
  expr = z3Gen.var(sv.getVarId());
}

z3::expr Z3SetExprVisitor::getExpr() const { return expr; }

