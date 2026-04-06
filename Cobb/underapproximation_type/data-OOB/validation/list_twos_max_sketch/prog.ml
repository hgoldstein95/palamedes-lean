let rec twos_list_gen (s : int) : int list =
  if sizecheck s then [ 2 ]
  else
    
    if bool_gen () then [ 2 ]
  else 2 :: twos_list_gen (subs s)

let[@assert] twos_list_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> len v n && n <= s + 1 && n > 0 && all_twos v
    : [%v: int list])
    [@under])
