let rec gt_five_gen (s : int) : int = if bool_gen () then Err else 7

let[@assert] gt_five_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> v > 5: [%v: int]) [@under])
