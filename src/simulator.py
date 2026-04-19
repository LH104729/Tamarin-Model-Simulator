from copy import deepcopy
import tree_sitter_spthy as tsspthy
from tree_sitter import Language, Parser, Node

from src.base_types import Sort, Term, Fact, RewriteRule, EquationalTheory
from src.parser import parse_rule
from src.default_rules import get_default_rules
from src.default_equations import get_default_equations


class History:
  trace: list[list[Fact]]
  state: dict[Fact, int]
  fresh_instance_counter: dict[Term, int]
  history: list[tuple[list[Fact], list[Fact]]]
  time: int
  max_time: int

  def __init__(self):
    self.trace = []
    self.state = {}
    self.fresh_instance_counter = {}
    self.history = []

    self.time = 0
    self.max_time = 0

  def add_fact(self, fact: Fact, count: int = 1):
    self.state[fact] = self.state.get(fact, 0) + count

  def remove_fact(self, fact: Fact, count: int = 1):
    if self.state.get(fact, 0) < count:
      raise ValueError(
        f"Cannot remove {count} instances of fact {fact} from the multiset"
      )
    self.state[fact] -= count
    if self.state[fact] == 0:
      del self.state[fact]

  def contains_fact(self, fact: Fact, count: int = 1) -> bool:
    return self.state.get(fact, 0) >= count

  def step(
    self,
    facts_to_remove: dict[Fact, int],
    facts_to_add: dict[Fact, int],
    actions: list[Fact],
  ):
    self.time = self.time + 1
    if self.time <= self.max_time:
      self.history = self.history[: self.time - 1]
      self.trace = self.trace[: self.time - 1]
    self.max_time = self.time

    for fact, count in facts_to_remove:
      self.remove_fact(fact, count)
    for fact, count in facts_to_add:
      self.add_fact(fact, count)
    self.trace.append(actions)
    self.history.append((facts_to_remove, facts_to_add))

  def undo(self):
    if self.time == 0:
      return False
    self.time = self.time - 1
    facts_to_remove, facts_to_add = self.history[self.time]
    for fact, count in facts_to_add:
      self.remove_fact(fact, count)
    for fact, count in facts_to_remove:
      self.add_fact(fact, count)

  def redo(self):
    if self.time >= self.max_time:
      return False
    facts_to_remove, facts_to_add = self.history[self.time]
    for fact, count in facts_to_remove:
      self.remove_fact(fact, count)
    for fact, count in facts_to_add:
      self.add_fact(fact, count)
    self.time = self.time + 1
    return True


class Simulator:
  def __init__(self, rules: list[RewriteRule] = [], built_ins: list[str] = []):
    self.rules: dict[str, RewriteRule] = {rule.name: rule for rule in rules}
    self.rule_names: list[str] = list(self.rules.keys())
    self.attacker_rule_names: list[str] = []
    self.fresh_instance_counter: dict[Term, int] = {}
    self.state: History = History()
    self.equational_theory: EquationalTheory = EquationalTheory()

    for built_in in ["default"] + built_ins:
      attacker_rules = get_default_rules(built_in)
      for rule in attacker_rules:
        if rule.name not in self.rules:
          self.rules[rule.name] = rule
          self.attacker_rule_names.append(rule.name)
      self.equational_theory.add_equations(get_default_equations(built_in))

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
        for state_fact in self.state.state.keys():
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
      if term not in renaming_map:
        if term in rule.required_public_terms:
          renaming_map[term] = Term(
            f"'{term.name}'", deepcopy(term.subterm), sort=Sort.PUB, is_constant=True
          )
        else:
          print(
            f"Cannot apply rule {rule_name}: term {term} is not in the renaming map"
          )
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
      elif not self.state.contains_fact(fact, count):
        print(f"Cannot apply rule {rule_name}: not enough instances of fact {fact}")
        return False

    # Update the fresh instance counter
    for t, count in fresh_terms_update.items():
      self.fresh_instance_counter[t] = count

    facts_to_remove = {
      k: v for k, v in required_facts.items() if not k.is_presistent and k.name != "Fr"
    }
    action_facts = [
      self.equational_theory.normal_form(fact.rename(renaming_map))
      for fact in rule.actions
    ]
    facts_to_add = {
      self.equational_theory.normal_form(fact.rename(renaming_map)): 1
      for fact in rule.conclusion
    }

    self.state.step(facts_to_remove.items(), facts_to_add.items(), action_facts)
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
  built_ins: list[str] = []
  for node in built_ins_nodes:
    for child in node.children:
      if child.type == "built_in":
        built_ins.append(child.text.decode())
  return Simulator(rules, built_ins)
