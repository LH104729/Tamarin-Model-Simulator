from enum import Enum
from copy import deepcopy
from functools import cache

type Equation = tuple[Term, Term]


class Sort(Enum):
  MSG = ""
  FRESH = "~"
  PUB = "$"
  NAT = "%"
  TEMPORAL = "#"

  def __str__(self) -> str:
    return self.value


class Term:
  def __init__(
    self,
    name: str,
    subterm: list["Term"] = [],
    sort: Sort = Sort.MSG,
    is_constant=False,
  ):
    self.name = name
    self.subterm = subterm
    self.sort = sort
    self.is_constant = is_constant
    if self.sort == Sort.NAT and self.name == "1":
      self.is_constant = True

  def __str__(self):
    if self.subterm:
      if self.name == "pair":
        return f"<{', '.join(str(s) for s in self.subterm)}>"
      elif self.name in ["mset", "nat", "xor", "mul", "exp"]:
        op = {"mset": "++", "nat": "%+", "xor": "⊕", "mul": "*", "exp": "^"}[self.name]
        return f" {op} ".join(str(s) for s in self.subterm)
      else:
        return f"{self.name}({', '.join(str(s) for s in self.subterm)})"
    else:
      if self.is_constant and self.sort == Sort.PUB:
        return self.name
      return self.sort.__str__() + self.name

  def __eq__(self, other):
    if not isinstance(other, Term):
      return False
    return (
      self.name == other.name
      and self.subterm == other.subterm
      and self.sort == other.sort
      and self.is_constant == other.is_constant
    )

  def __hash__(self):
    return hash((self.name, tuple(self.subterm), self.sort, self.is_constant))

  def get_minimal_terms(self) -> set["Term"]:
    if self.is_constant:
      return set()
    if not self.subterm:
      return {self}
    else:
      minimal_terms = set()
      for s in self.subterm:
        minimal_terms.update(s.get_minimal_terms())
      return minimal_terms

  def rename(self, renaming_map: dict["Term", "Term"]) -> "Term":
    def __dfs(root: Term) -> Term:
      if root.is_constant:
        return root
      if root in renaming_map:
        return deepcopy(renaming_map[root])
      else:
        if len(root.subterm) == 0:
          return deepcopy(root)
        else:
          new_subterm = [__dfs(s) for s in root.subterm]
          return Term(root.name, new_subterm, root.sort, root.is_constant)

    return __dfs(self)

  def renamable_to(
    self, other: "Term", restriction: dict["Term", "Term"] = {}
  ) -> dict["Term", "Term"] | None:
    # Check if self can be renamed to other.
    # any sort is a subsort of MSG
    if self.sort != other.sort and self.sort != Sort.MSG:
      return None
    if self.is_constant and not self.__eq__(other):
      return None
    if not self.subterm:
      return {self: other}
    if len(self.subterm) != len(other.subterm):
      return None
    renaming_map: dict[Term, Term] = restriction.copy()
    for s1, s2 in zip(self.subterm, other.subterm):
      subterm_renaming_map = s1.renamable_to(s2, restriction=renaming_map)
      if subterm_renaming_map is None:
        return None
      for k, v in subterm_renaming_map.items():
        if k in renaming_map:
          if renaming_map[k] != v:
            return None
        else:
          renaming_map[k] = v
    return renaming_map

  def renamable_to_subterm_of(self, other: "Term") -> dict["Term", "Term"] | None:
    renaming_map = self.renamable_to(other)
    if renaming_map is not None:
      return renaming_map
    for s in other.subterm:
      renaming_map = self.renamable_to_subterm_of(s)
      if renaming_map is not None:
        return renaming_map
    return None


class Fact:
  def __init__(self, name: str, terms: list[Term], is_presistent=False):
    self.name = name
    self.terms = terms
    self.is_presistent = is_presistent

  def __str__(self):
    return f"{'!' if self.is_presistent else ''}{self.name}({', '.join(str(t) for t in self.terms)})"

  def __eq__(self, other):
    if not isinstance(other, Fact):
      return False
    return (
      self.name == other.name
      and self.terms == other.terms
      and self.is_presistent == other.is_presistent
    )

  def __hash__(self):
    return hash((self.name, tuple(self.terms), self.is_presistent))

  def get_minimal_terms(self) -> set[Term]:
    minimal_terms = set()
    for t in self.terms:
      minimal_terms.update(t.get_minimal_terms())
    return minimal_terms

  def rename(self, renaming_map: dict[Term, Term]) -> "Fact":
    new_terms = [t.rename(renaming_map) for t in self.terms]
    return Fact(self.name, new_terms, self.is_presistent)

  def renamable_to(
    self, other: "Fact", restriction: dict[Term, Term] = {}
  ) -> dict[Term, Term] | None:
    if self.name != other.name:
      return None
    if len(self.terms) != len(other.terms):
      return None
    renaming_map: dict[Term, Term] = restriction.copy()
    for t1, t2 in zip(self.terms, other.terms):
      term_renaming_map = t1.renamable_to(t2, restriction=renaming_map)
      if term_renaming_map is None:
        return None
      for k, v in term_renaming_map.items():
        if k in renaming_map:
          if renaming_map[k] != v:
            return None
        else:
          renaming_map[k] = v
    return renaming_map


class RewriteRule:
  def __init__(
    self,
    name: str,
    premises: list[Fact],
    actions: list[Fact],
    conclusion: list[Fact],
  ):
    self.name = name
    self.premises = premises
    self.actions = actions
    self.conclusion = conclusion
    self.atomic_terms: set[Term] = set()
    self.required_public_terms: list[Term] = []

    for fact in premises:
      self.atomic_terms.update(fact.get_minimal_terms())
    for fact in actions:
      for t in fact.get_minimal_terms():
        if t not in self.atomic_terms:
          assert t.sort == Sort.PUB
          self.required_public_terms.append(t)
          self.atomic_terms.add(t)
    for fact in conclusion:
      for t in fact.get_minimal_terms():
        if t not in self.atomic_terms:
          assert t.sort == Sort.PUB
          self.required_public_terms.append(t)
          self.atomic_terms.add(t)

  def __str__(self):
    return f"{self.name}: \n[{', \n'.join(str(p) for p in self.premises)}]\n --[{', \n'.join(str(a) for a in self.actions)}]->\n [{', \n'.join(str(a) for a in self.conclusion)}]"


class EquationalTheory:
  def __init__(self, equations: list[tuple[Term, Term]] = []):
    self.equations = equations

  def add_equations(self, equations: list[Equation] = []):
    self.equations.extend(equations)

  @cache
  def normal_form(self, term: Term | Fact) -> Term | Fact:
    if isinstance(term, Fact):
      new_terms = [self.normal_form(t) for t in term.terms]
      return Fact(term.name, new_terms, term.is_presistent)
    else:
      normalized_term = deepcopy(term)
      applied = True
      while applied:
        applied = False
        for lhs, rhs in self.equations:
          renaming_map = lhs.renamable_to_subterm_of(normalized_term)
          if renaming_map is not None:
            renamed_lhs = lhs.rename(renaming_map)
            renamed_rhs = rhs.rename(renaming_map)
            normalized_term = normalized_term.rename({renamed_lhs: renamed_rhs})
            applied = True
            break
      return normalized_term

  def are_equal(self, t1: Term, t2: Term) -> bool:
    return self.normal_form(t1) == self.normal_form(t2)

  def renamable_to(
    self, t1: Term | Fact, t2: Term | Fact, restriction: dict[Term, Term] = {}
  ) -> dict[Term, Term] | None:
    if isinstance(t1, Term) and isinstance(t2, Term):
      rename_map = self.normal_form(t1).renamable_to(self.normal_form(t2), restriction)
      return rename_map
    elif isinstance(t1, Fact) and isinstance(t2, Fact):
      if t1.name != t2.name or len(t1.terms) != len(t2.terms):
        return None
      if len(t1.terms) != len(t2.terms):
        return None
      renaming_map: dict[Term, Term] = restriction.copy()
      for t1_term, t2_term in zip(t1.terms, t2.terms):
        term_renaming_map = self.renamable_to(
          t1_term, t2_term, restriction=renaming_map
        )
        if term_renaming_map is None:
          return None
        for k, v in term_renaming_map.items():
          if k in renaming_map:
            if renaming_map[k] != v:
              return None
          else:
            renaming_map[k] = v
      return renaming_map
    else:
      raise ValueError("t1 and t2 must be both Term or both Fact")
