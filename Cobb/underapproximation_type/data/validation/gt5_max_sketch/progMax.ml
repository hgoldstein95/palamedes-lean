let rec gt_five_gen (s : int) : int = Err + 5

let[@assert] gt_five_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> n > 5: [%v: int]) [@under])
