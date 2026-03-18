let rec between_5_10_gen (s : int) : int = 
  if Err then Err else
  if Err then Err else 
  if Err then Err else 
  if Err then Err else 
  if Err then Err else Err

let[@assert] between_5_10_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> v >= 5 && v <= 10 : [%v: int]) [@under])
