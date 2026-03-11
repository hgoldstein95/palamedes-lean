let rec len_k_gen (s : int) : int list =
  if sizecheck s then Err
  else Err

let[@assert] len_k_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> len v n && n == s && all_twos v : [%v: int list]) [@under])
