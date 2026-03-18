let rec existsA_gen (s : int) : int = if true then Err else 4

let[@assert] existsA_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((a [@exists]) : int) -> a == 3 && v == a + 1: [%v: int]) [@under])
