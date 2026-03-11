let rec len_even_gen (s : int) : int list =
  if sizecheck s then Err else 
    if bool_gen () then [ ]
  else 2 :: 2 :: len_even_gen (subs s)

let[@assert] len_even_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> len v n && n == 2 * s && all_twos v : [%v: int list]) [@under])

