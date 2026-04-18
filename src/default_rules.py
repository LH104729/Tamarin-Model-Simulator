from src.base_types import RewriteRule, Fact, Term, Sort

OUT_TO_IN = RewriteRule(
  name="OutToIn",
  premises=[Fact("Out", [Term("M", sort=Sort.MSG)])],
  actions=[],
  conclusion=[Fact("In", [Term("M", sort=Sort.MSG)])],
)


def get_default_rules() -> list[RewriteRule]:
  return [OUT_TO_IN]
