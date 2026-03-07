let rec equals2_gen (s : int) : int = if bool_gen () then Err else 5

let[@assert] equals2_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> v == 2 || v == 5 : [%v: int]) [@under])
