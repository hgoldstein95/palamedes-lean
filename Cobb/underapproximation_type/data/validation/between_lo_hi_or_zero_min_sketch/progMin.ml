let rec between_gen (s : int) (lo : int) (hi : int) : int = 
  if Err then Err else 
  if Err then Err else 
  if Err then Err else 
  Err

let[@assert] between_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let lo = ((true : [%v: int]) [@over]) in
  let hi = ((lo < v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> v == 0 || v >= lo && v <= hi : [%v: int]) [@under])
