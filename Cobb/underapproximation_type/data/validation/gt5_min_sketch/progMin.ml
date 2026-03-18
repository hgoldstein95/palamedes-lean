let rec gt_five_gen (s : int) : int = if Err then Err else Err

let[@assert] gt_five_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> v > 5: [%v: int]) [@under])
