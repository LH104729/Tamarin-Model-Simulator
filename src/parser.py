from tree_sitter import Node
from .base_types import Fact, RewriteRule, Sort, Term


def parse_ident(node: Node) -> str:
  assert node.type == "ident"
  return node.text.decode()


def parse_var(node: Node) -> Term:
  if node.type == "pub_var":
    return Term(node.text.decode()[1:], [], Sort.PUB)
  elif node.type == "pub_name":
    return Term(node.text.decode(), [], Sort.PUB, is_constant=True)
  elif node.type == "fresh_var":
    return Term(node.text.decode()[1:], [], Sort.FRESH)
  elif node.type == "nat_var":
    return Term(node.text.decode()[1:], [], Sort.NAT)
  elif node.type == "msg_var_or_nullary_fun":
    return Term(node.text.decode(), [], Sort.MSG)


def parse_term(node: Node) -> Term:
  if node.type in ["mset_term", "nat_term", "xor_term", "mul_term", "exp_term"]:
    if node.child_count == 1:
      return parse_term(node.children[0])
    subterms = []
    for term_node in node.children:
      if term_node.type in ["++", "+", "%+", "XOR", "⊕", "^"]:
        continue
      subterms.append(parse_term(term_node))
    return Term(node.type[:-5], subterms)
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
    return Term("tuple", subterms)
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
