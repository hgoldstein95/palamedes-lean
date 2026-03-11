let rec trues_list_gen (s : int) : bool list =
  if sizecheck s then [ true ]
  else if bool_gen () then [ true ]
  else true :: trues_list_gen (subs s)

let[@assert] trues_list_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> len v n && n <= s + 1 && n > 0 && all_trues v
    : [%v: bool list])
    [@under])
