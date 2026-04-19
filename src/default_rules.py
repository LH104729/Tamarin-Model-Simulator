from src.base_types import RewriteRule, Fact, Term, Sort
from src.default_equations import BUILTIN_FUNCTIONS, BUILTIN_EQUATIONS

BUILTIN_RULES: dict[str, list[RewriteRule]] = {
  "default": [
    RewriteRule(
      name="irecv_isend",
      premises=[Fact("Out", [Term("x", sort=Sort.MSG)])],
      actions=[
        Fact("KU", [Term("x", sort=Sort.MSG)], is_presistent=True),
        Fact("K", [Term("x", sort=Sort.MSG)]),
      ],
      conclusion=[
        Fact("KD", [Term("x", sort=Sort.MSG)], is_presistent=True),
        Fact("KU", [Term("x", sort=Sort.MSG)], is_presistent=True),
        Fact("In", [Term("x", sort=Sort.MSG)]),
      ],
    ),
    RewriteRule(
      name="irecv",
      premises=[Fact("Out", [Term("x", sort=Sort.MSG)])],
      actions=[],
      conclusion=[Fact("KD", [Term("x", sort=Sort.MSG)], is_presistent=True)],
    ),
    RewriteRule(
      name="isend",
      premises=[Fact("KU", [Term("x", sort=Sort.MSG)], is_presistent=True)],
      actions=[Fact("K", [Term("x", sort=Sort.MSG)])],
      conclusion=[Fact("In", [Term("x", sort=Sort.MSG)])],
    ),
    RewriteRule(
      name="coerce",
      premises=[Fact("KD", [Term("x", sort=Sort.MSG)], is_presistent=True)],
      actions=[Fact("KU", [Term("x", sort=Sort.MSG)], is_presistent=True)],
      conclusion=[Fact("KU", [Term("x", sort=Sort.MSG)], is_presistent=True)],
    ),
    RewriteRule(
      name="pub",
      premises=[],
      actions=[Fact("KU", [Term("x", sort=Sort.PUB)], is_presistent=True)],
      conclusion=[Fact("KU", [Term("x", sort=Sort.PUB)], is_presistent=True)],
    ),
    RewriteRule(
      name="fresh",
      premises=[Fact("Fr", [Term("x", sort=Sort.FRESH)])],
      actions=[Fact("KU", [Term("x", sort=Sort.FRESH)], is_presistent=True)],
      conclusion=[Fact("KU", [Term("x", sort=Sort.FRESH)], is_presistent=True)],
    ),
  ],
  "hashing": [],
  "asymmetric-encryption": [],
  "symmetric-encryption": [],
  "signing": [],
}


def get_default_rules(built_in: str = "default") -> list[RewriteRule]:
  base_rules = BUILTIN_RULES.get(built_in)
  for function_name, arity in BUILTIN_FUNCTIONS.get(built_in, []):
    base_rules.append(
      RewriteRule(
        f"c_{function_name}",
        premises=[
          Fact("KU", [Term(f"x{i}", sort=Sort.MSG)], is_presistent=True)
          for i in range(arity)
        ],
        actions=[
          Fact(
            "KU",
            [
              Term(
                function_name,
                [Term(f"x{i}", sort=Sort.MSG) for i in range(arity)],
                sort=Sort.MSG,
              )
            ],
            is_presistent=True,
          )
        ],
        conclusion=[
          Fact(
            "KU",
            [
              Term(
                function_name,
                [Term(f"x{i}", sort=Sort.MSG) for i in range(arity)],
                sort=Sort.MSG,
              )
            ],
            is_presistent=True,
          )
        ],
      )
    )
  lhs_count = {}
  for lhs, rhs in BUILTIN_EQUATIONS.get(built_in, []):
    if len(lhs.subterm) == 0:
      continue
    base_rules.append(
      RewriteRule(
        f"d_{lhs_count.get(lhs.name, 0)}_{lhs.name}",
        premises=[Fact("KD", [subterm], is_presistent=True) for subterm in lhs.subterm],
        actions=[Fact("KD", [rhs], is_presistent=True)],
        conclusion=[Fact("KD", [rhs], is_presistent=True)],
      )
    )
    lhs_count[lhs.name] = lhs_count.get(lhs.name, 0) + 1
  return base_rules
