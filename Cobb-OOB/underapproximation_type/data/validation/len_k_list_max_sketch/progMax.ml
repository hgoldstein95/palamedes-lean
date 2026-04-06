let rec len_k_gen (s : int) : int list =
  if sizecheck s then Err
  else int_gen () :: len_k_gen (subs s)

let[@assert] len_k_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> len v n && n == s : [%v: int list]) [@under])
