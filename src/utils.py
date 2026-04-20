def dict_union(d1: dict, d2: dict, dry_run=False) -> bool:
  for k, v in d2.items():
    if k in d1:
      if d1[k] != v:
        return False
    elif not dry_run:
      d1[k] = v
  return True
