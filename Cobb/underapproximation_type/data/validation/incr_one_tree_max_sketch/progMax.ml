let rec incr_one_tree_gen (s : int) (x : int) : int tree =
  if sizecheck s then Err
  else if bool_gen () then Leaf
  else
    let (ss : int) = subs s in
    let (lt : int tree) = incr_one_tree_gen ss (x + 1) in
    let (rt : int tree) = incr_one_tree_gen ss (x + 1) in
    Node (x, lt, rt)

let[@assert] incr_one_tree_gen =
  let s = (0 <= v : [%v: int]) [@over] in
  let x = ((true : [%v: int]) [@over]) in
  (depth v s && tree_incr_one v &&
   (not (leaf v)) #==> (fun ((u [@exists]) : int) -> root v u && u == x + 1)
    : [%v: int tree]) [@under]
