from copy import deepcopy
import tree_sitter_spthy as tsspthy
from tree_sitter import Language, Parser, Node

from src.base_types import Sort, Term, Fact, RewriteRule, Equation, EquationalTheory
from src.parser import parse_rule
from src.default_rules import get_default_rules
from src.default_equations import get_default_equations


class Simulator:
  def __init__(self, rules: list[RewriteRule] = [], equations: list[Equation] = []):
    self.rules: dict[str, RewriteRule] = {rule.name: rule for rule in rules}
    self.trace: list[tuple[Fact, int]] = []
    self.fresh_instance_counter: dict[Term, int] = {}
    self.state: dict[Fact, int] = {}
    self.time: int = 0
    self.equational_theory: EquationalTheory = EquationalTheory(equations)

    for rule in get_default_rules():
      if rule.name not in self.rules:
        self.rules[rule.name] = rule

  def print_state(self):
    print(
      f"[{','.join([fact.__str__() for fact, count in self.state.items() for _ in range(count)])}]"
    )

  def print_trace(self):
    print(f"[{', '.join(f'{time}@{fact}' for fact, time in self.trace)}]")

  def get_rule_possible_values(
    self, rule_name: str, selected_facts: dict[Fact, Fact] = {}
  ) -> dict[Fact, set[Fact]]:
    # Compute the forced terms
    rule = self.rules.get(rule_name)
    restriction: dict[Term, Term] = {}
    possible_facts: dict[Fact, set[Fact]] = {}
    for fact, other_fact in selected_facts.items():
      renaming_map = self.equational_theory.renamable_to(fact, other_fact)
      if renaming_map is None:
        print(f"Selected fact {other_fact} is not compatible with required fact {fact}")
        return {fact: set() for fact in rule.premises}
      for k, v in renaming_map.items():
        if k in restriction:
          if restriction[k] != v:
            print(
              f"Selected facts are not compatible: term {k} is mapped to both {restriction[k]} and {v}"
            )
            return {fact: set() for fact in rule.premises}
        else:
          restriction[k] = v
      possible_facts[fact] = {other_fact}

    prune = False
    new_selected_facts = deepcopy(selected_facts)
    for fact in rule.premises:
      if fact not in possible_facts:
        possible_facts[fact] = set()
        for state_fact in self.state.keys():
          renaming_map = self.equational_theory.renamable_to(
            fact, state_fact, restriction=restriction
          )
          if renaming_map is not None:
            possible_facts[fact].add(state_fact)
        if len(possible_facts[fact]) == 1:
          new_selected_facts[fact] = possible_facts[fact].pop()
          prune = True
    if prune:
      return self.get_rule_possible_values(rule_name, new_selected_facts)
    return possible_facts

  def can_apply_rule(
    self,
    rule_name: str,
    selected_facts: dict[Fact, Fact] = {},
    public_assignment: dict[Term, Term] = {},
  ) -> dict[Term, Term] | None:
    restriction: dict[Term, Term] = deepcopy(public_assignment)
    for fact in self.rules[rule_name].premises:
      if fact.name == "Fr":
        continue
      if fact not in selected_facts:
        return None
      renaming_map = self.equational_theory.renamable_to(fact, selected_facts.get(fact))
      if renaming_map is None:
        return None
      for k, v in renaming_map.items():
        if k in restriction:
          if restriction[k] != v:
            return None
        else:
          restriction[k] = v
    # if not all(term in restriction for term in self.rules[rule_name].atomic_terms):
    #   return None
    return restriction

  def apply_rule(self, rule_name: str, renaming_map: dict[Term, Term]):
    if rule_name not in self.rules:
      raise ValueError(f"Rule {rule_name} not found")
    rule = self.rules.get(rule_name)

    fresh_terms_update: dict[Term, int] = {}
    for fact in rule.premises:
      if fact.name == "Fr":
        assert len(fact.terms) == 1
        t = fact.terms[0]
        if t in renaming_map:
          return False
        fresh_terms_update[t] = self.fresh_instance_counter.get(t, 0) + 1
        renaming_map[t] = Term(f"{t.name}.{fresh_terms_update[t]}", sort=Sort.FRESH)

    # Check if all atomic terms are in the renaming map
    for term in rule.atomic_terms:
      if term not in renaming_map and term not in rule.required_public_terms:
        print(f"Cannot apply rule {rule_name}: term {term} is not in the renaming map")
        return False

    # Compute the required facts
    required_facts: dict[Fact, int] = {}
    for premise in rule.premises:
      required_fact = premise.rename(renaming_map)
      required_facts[required_fact] = required_facts.get(required_fact, 0) + 1

    # Check if all required facts are in the state
    for fact, count in required_facts.items():
      if fact.name == "Fr":
        continue
      elif self.state.get(fact, 0) < count:
        print(f"Cannot apply rule {rule_name}: not enough instances of fact {fact}")
        return False

    # Update the fresh instance counter
    for t, count in fresh_terms_update.items():
      self.fresh_instance_counter[t] = count
    # Remove the required facts from the state
    for fact, count in required_facts.items():
      if fact.name == "Fr":
        continue
      if fact.is_presistent:
        continue
      self.state[fact] -= count
      if self.state[fact] == 0:
        del self.state[fact]

    # Compute the action facts
    self.time += 1
    for action_fact in rule.actions:
      renamed_fact = action_fact.rename(renaming_map)
      self.trace.append((renamed_fact, self.time))

    # Compute the produced facts
    for conclusion_fact in rule.conclusion:
      renamed_fact = self.equational_theory.normal_form(
        conclusion_fact.rename(renaming_map)
      )
      self.state[renamed_fact] = self.state.get(renamed_fact, 0) + 1
    return True


def simulator_from_path(model_file: str) -> Simulator:
  parser = Parser(Language(tsspthy.language()))
  with open(model_file, "r") as f:
    tree = parser.parse(f.read().encode())

  rule_nodes: list[Node] = []
  restriction_nodes: list[Node] = []
  built_ins_nodes: list[Node] = []
  functions_nodes: list[Node] = []
  for child in tree.root_node.children[0].children:
    if child.type == "rule":
      rule_nodes.append(child)
    elif child.type == "restriction":
      restriction_nodes.append(child)
    elif child.type == "built_ins":
      built_ins_nodes.append(child)
    elif child.type == "functions":
      functions_nodes.append(child)

  rules: list[RewriteRule] = []
  for node in rule_nodes:
    rules.append(parse_rule(node))
  equations: list[Equation] = []
  for node in built_ins_nodes:
    for child in node.children:
      if child.type == "built_in":
        equations.extend(get_default_equations(child.text.decode()))
  return Simulator(rules, equations)
