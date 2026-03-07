let rec even_list_gen (s : int) : int list =
  if sizecheck s then Err else [ double (int_gen ()) ]

let[@assert] even_list_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> len v n && n <= s + 1 && n > 0 && all_evens v
    : [%v: int list])
    [@under])
