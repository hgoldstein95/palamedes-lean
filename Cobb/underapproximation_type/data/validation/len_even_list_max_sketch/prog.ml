let rec len_even_gen (s : int) : int list =
  if sizecheck s then [ ] else
    if bool_gen () then [ ]
  else (int_gen ()) :: (int_gen ()) :: len_even_gen (subs s)

let[@assert] len_even_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> len v n && n == 2 * s : [%v: int list]) [@under])

