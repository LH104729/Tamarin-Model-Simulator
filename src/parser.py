from tree_sitter import Node
from .base_types import Fact, Formula, FormulaType, RewriteRule, Sort, Term, Restriction


def walk(node: Node, indent: int = 0, max_depth: int = -1):
  if max_depth == 0:
    return
  print("  " * indent + f"{node.type}: {node.text.decode()}")
  for child in node.children:
    walk(child, indent + 1, max_depth - 1 if max_depth > 0 else -1)


def parse_ident(node: Node) -> str:
  assert node.type == "ident"
  return node.text.decode()


def parse_var(node: Node) -> Term:
  name = None
  for child in node.children:
    if child.type == "ident":
      name = child.text.decode()
  if node.type == "pub_var":
    return Term(name, [], Sort.PUB)
  elif node.type == "pub_name":
    return Term(node.text.decode(), [], Sort.PUB, is_constant=True)
  elif node.type == "fresh_var":
    return Term(name, [], Sort.FRESH)
  elif node.type == "nat_var":
    return Term(name, [], Sort.NAT)
  elif node.type == "msg_var_or_nullary_fun":
    return Term(name, [], Sort.MSG)
  elif node.type == "temporal_var":
    return Term(name, [], Sort.TEMPORAL)


def parse_term(node: Node) -> Term:
  if node.type in ["mset_term", "nat_term", "xor_term", "mul_term", "exp_term"]:
    if node.child_count == 1:
      return parse_term(node.children[0])
    if node.type not in ["nat_term"]:
      raise NotImplementedError(f"Unsupported term type: {node.type}")
    subterms = []
    for term_node in node.children:
      if term_node.type in ["++", "+", "%+", "XOR", "⊕", "*", "^"]:
        continue
      subterms.append(parse_term(term_node))
    node_name = node.type[:-5]

    const_1_count = 0
    i = 0
    while i < len(subterms):
      if subterms[i].name == node_name:
        subterms = subterms[:i] + subterms[i].subterm + subterms[i + 1 :]
      elif subterms[i].name == "1" and subterms[i].sort == Sort.NAT:
        const_1_count += 1
        subterms.pop(i)
      else:
        i = i + 1

    subterms = [
      Term("1", [], Sort.NAT, is_constant=True) for _ in range(const_1_count)
    ] + subterms
    while len(subterms) > 2:
      right = subterms.pop()
      left = subterms.pop()
      subterms.append(Term(node_name, [left, right], Sort.NAT))
    return Term(node_name, subterms, Sort.NAT)
  if node.type in [
    "pub_var",
    "fresh_var",
    "msg_var_or_nullary_fun",
    "nat_var",
    "pub_name",
  ]:
    return parse_var(node)
  if node.type == "tuple_term":
    assert node.child_count >= 2
    assert node.children[0].type == "<"
    assert node.children[-1].type == ">"
    subterms = []
    for term_node in node.children[1:-1]:
      if term_node.type == ",":
        continue
      subterms.append(parse_term(term_node))
    while len(subterms) > 2:
      right = subterms.pop()
      left = subterms.pop()
      subterms.append(Term("pair", [left, right]))
    return Term("pair", subterms)
  if node.type == "nary_app":
    func_name = parse_ident(node.children[0])
    assert node.children[1].type == "("
    assert node.children[2].type == "arguments"
    assert node.children[3].type == ")"
    subterms = parse_arguments(node.children[2])
    return Term(func_name, subterms)
  return Term(node.text.decode(), [])


def parse_arguments(node: Node) -> list[Term]:
  terms = []
  for term_node in node.children:
    if term_node.type == ",":
      continue
    terms.append(parse_term(term_node))
  return terms


def parse_fact(node: Node) -> Fact:
  is_presistent = node.type == "persistent_fact"
  name = parse_ident(node.children[0])
  assert node.children[1].type == "("
  assert node.children[-1].type == ")"
  assert node.child_count == 3 or node.child_count == 4
  terms = []
  if node.child_count == 4:
    assert node.children[2].type == "arguments"
    terms = parse_arguments(node.children[2])
  return Fact(name, terms, is_presistent)


def parse_rule(node: Node) -> RewriteRule:
  assert node.type == "rule"
  assert node.children[0].type == "simple_rule"
  rule = node.children[0]
  name = None
  premises = []
  actions = []
  conclusion = []
  renaming_map: dict[Term, Term] = {}
  for child in rule.children:
    if child.type == "ident":
      name = child.text.decode()
    elif child.type == "rule_let_block":
      for let_term in child.children[1:-1]:
        left = parse_term(let_term.children[0])
        right = parse_term(let_term.children[2])
        renaming_map[left] = right.rename(renaming_map)
    elif child.type == "premise":
      assert child.child_count >= 2
      assert child.children[0].type == "["
      assert child.children[-1].type == "]"
      for fact_node in child.children[1:-1]:
        if fact_node.type in [",", "!"]:
          continue
        premises.append(parse_fact(fact_node).rename(renaming_map))
    elif child.type == "action_fact":
      assert child.child_count >= 2
      assert child.children[0].type == "--["
      assert child.children[-1].type == "]->"
      for fact_node in child.children[1:-1]:
        if fact_node.type in [",", "!"]:
          continue
        actions.append(parse_fact(fact_node).rename(renaming_map))
    elif child.type == "conclusion":
      assert child.child_count >= 2
      assert child.children[0].type == "["
      assert child.children[-1].type == "]"
      for fact_node in child.children[1:-1]:
        if fact_node.type in [",", "!"]:
          continue
        conclusion.append(parse_fact(fact_node).rename(renaming_map))

  return RewriteRule(name, premises, actions, conclusion)


def parse_formula(node: Node) -> Formula:
  if node.type in [
    "pub_var",
    "fresh_var",
    "msg_var_or_nullary_fun",
    "nat_var",
    "pub_name",
    "temporal_var",
  ]:
    return parse_var(node)

  formula = Formula()
  if node.type == "imp":
    if node.child_count == 1:
      return parse_formula(node.children[0])
    assert node.child_count == 3
    assert node.children[1].type in ["==>", "⇒"]
    return Formula(
      FormulaType.IMPLICATION,
      [parse_formula(node.children[0]), parse_formula(node.children[2])],
    )
  elif node.type == "nested_formula":
    return parse_formula(node.children[1])
  elif node.type in ["disjunction", "conjunction"]:
    if node.child_count == 1:
      return parse_formula(node.children[0])
    formula.type = (
      FormulaType.DISJUNCTION if node.type == "disjunction" else FormulaType.CONJUNCTION
    )
    formula.subformulas = [
      parse_formula(child)
      for child in node.children
      if child.type not in ["|", "∨", "&", "∧"]
    ]
    return formula
  elif node.type == "quantified_formula":
    formula.type = (
      FormulaType.EXISTS if node.children[0].type in ["Ex", "∃"] else FormulaType.FORALL
    )
    variables = Formula(
      FormulaType.ATOM, [parse_formula(child) for child in node.children[1:-2]]
    )
    subformula = parse_formula(node.children[-1])
    formula.subformulas = [variables, subformula]
    return formula
  elif node.type == "negation":
    return Formula(FormulaType.NEGATION, [parse_formula(node.children[1])])
  elif node.type == "term_eq":
    return Formula(
      FormulaType.TERM_EQ, [parse_term(node.children[0]), parse_term(node.children[2])]
    )
  elif node.type == "subterm_rel":
    return Formula(
      FormulaType.SUBTERM_REL,
      [parse_term(node.children[0]), parse_term(node.children[2])],
    )
  elif node.type == "action_constraint":
    return Formula(
      FormulaType.ATOM, [parse_fact(node.children[0]), parse_var(node.children[2])]
    )
  else:
    raise NotImplementedError(f"Unsupported formula type: {node.type}")
  return formula


def parse_restriction(node: Node) -> Restriction | None:
  assert node.type == "restriction"
  assert node.children[0].type == "restriction"
  restriction_name = node.children[1].text.decode()
  formula: Formula = parse_formula(node.children[-2])

  # Check if formula is of the form "forall xs #t. Fact(xs)@#t => f(xs)"
  if not (
    formula.type == FormulaType.FORALL
    and formula.subformulas[1].type == FormulaType.IMPLICATION
    and formula.subformulas[1].subformulas[0].type == FormulaType.ATOM
  ):
    return None

  fact = formula.subformulas[1].subformulas[0].subformulas[0]

  # Check that f(x) is quantifier-free
  def is_quantifier_free(f: Formula) -> bool:
    if type(f) is Term:
      return True
    if f.type in [FormulaType.EXISTS, FormulaType.FORALL, FormulaType.ATOM]:
      return False
    return all(is_quantifier_free(subf) for subf in f.subformulas)

  if not is_quantifier_free(formula.subformulas[1].subformulas[1]):
    return None

  return Restriction(restriction_name, fact, formula.subformulas[1].subformulas[1])
