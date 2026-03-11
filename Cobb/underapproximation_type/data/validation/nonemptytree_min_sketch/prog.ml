let rec nonemptytree_gen (s : int) : int tree =
  if sizecheck s then Node (int_gen (), Leaf, Leaf)
  else if bool_gen () then Node (int_gen (), Leaf, Leaf)
  else
    let (ss : int) = subs s in
    let (lt : int tree) = nonemptytree_gen ss in
    let (rt : int tree) = nonemptytree_gen ss in
    let (n : int) = int_gen () in
    Node (n, lt, rt)

let[@assert] nonemptytree_gen =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((u [@exists]) : int) -> depth v u && u <= s + 1 : [%v: int tree]) [@under]
