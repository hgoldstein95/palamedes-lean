let rec between_5_10_gen (s : int) : int = 
  if Err then 5 else
  if bool_gen() then 6 else 
  if bool_gen() then 7 else 
  if bool_gen() then 8 else 
  if bool_gen() then 9 else 10

let[@assert] between_5_10_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> v >= 5 && v <= 10 : [%v: int]) [@under])
