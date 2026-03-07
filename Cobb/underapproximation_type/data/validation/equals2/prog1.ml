let rec equals2_gen (s : int) : int = if true then two () else Err

let[@assert] equals2_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> n == 2: [%v: int]) [@under])

