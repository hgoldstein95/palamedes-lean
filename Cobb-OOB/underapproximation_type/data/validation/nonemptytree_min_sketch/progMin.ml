let rec nonemptytree_gen (s : int) : int tree =
  if sizecheck s then Err
  else if bool_gen () then Err
  else Err

let[@assert] nonemptytree_gen =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((u [@exists]) : int) -> depth v u && u <= s + 1 : [%v: int tree]) [@under]
