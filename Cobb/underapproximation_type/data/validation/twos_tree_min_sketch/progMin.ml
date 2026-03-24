let rec twos_tree_gen (d : int) : int tree =
  if sizecheck d then Err else if bool_gen () then Err else Err

let[@assert] twos_tree_gen =
  let d = ((0 <= v : [%v: int]) [@over]) in
  ((all_twos_tree v && fun ((n [@exists]) : int) -> depth v n && n <= d
    : [%v: int tree])
    [@under])
