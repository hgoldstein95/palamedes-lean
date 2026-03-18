let rec equals2_gen (s : int) : int = if Err then Err else Err

let[@assert] equals2_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> 2 == v: [%v: int]) [@under])

