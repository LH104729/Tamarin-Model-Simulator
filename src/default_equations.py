from src.base_types import Term, Equation

BUILTIN_FUNCTIONS: dict[str, list[tuple[str, int]]] = {
  "hashing": [("h", 1)],
  "asymetric-encryption": [("pk", 1), ("aenc", 2), ("adec", 2)],
  "symmetric-encryption": [("senc", 2), ("sdec", 2)],
  "signing": [("true", 0), ("pk", 1), ("sign", 2), ("verify", 3)],
}

BUILTIN_EQUATIONS: dict[str, list[Equation]] = {
  "hashing": [],
  "asymmetric-encryption": [
    (
      Term("adec", [Term("aenc", [Term("m"), Term("pk", [Term("k")])]), Term("k")]),
      Term("m"),
    )
  ],
  "symmetric-encryption": [
    (
      Term("sdec", [Term("senc", [Term("m"), Term("k")]), Term("k")]),
      Term("m"),
    )
  ],
  "signing": [
    (
      Term(
        "verify",
        [Term("sign", [Term("m"), Term("k")]), Term("m"), Term("pk", [Term("k")])],
      ),
      Term("true"),
    )
  ],
}


def get_default_equations(built_in: str) -> list[Equation]:
  return BUILTIN_EQUATIONS.get(built_in, [])
