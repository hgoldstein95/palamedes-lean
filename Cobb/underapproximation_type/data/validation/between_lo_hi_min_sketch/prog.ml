let rec between_gen (s : int) (lo : int) (hi : int) : int = 
  if bool_gen() then lo else 
  if lo == hi then hi else 
  between_gen s (lo + 1) hi

let[@assert] between_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let lo = ((true : [%v: int]) [@over]) in
  let hi = ((lo < v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> v >= lo && v <= hi : [%v: int]) [@under])
