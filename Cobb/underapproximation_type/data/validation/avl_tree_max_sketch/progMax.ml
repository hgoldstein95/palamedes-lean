let rec avl_tree_gen (d : int) (lo : int) (hi : int) : int tree =
   (* if balance factor is 0 we are a leaf *)
  if sizecheck d then Err
  else if d == 1 then 
    (* if balance factor is 1 we can generate a leaf or a node with leaf children *)
    if bool_gen () then Leaf else 
    let (x : int) = int_range lo hi in
    Node (x, Leaf, Leaf)
  else if incr lo < hi then
    let (x : int) = int_range lo hi in
    let (lt : int tree) = avl_tree_gen (subs d) lo x in
    let (rt : int tree) = avl_tree_gen (subs d) x hi in
    Node (x, lt, rt)
  else Exn

let[@assert] avl_tree_gen =
  let d = ((0 <= v : [%v: int]) [@over]) in
  let lo = ((true : [%v: int]) [@over]) in
  let hi = ((lo < v : [%v: int]) [@over]) in
  ((((not (leaf v))#==>(lower_bound v lo))
    && ((not (leaf v))#==>(upper_bound v hi))
    && bst v 
    && avl_balanced v
    && fun ((n [@exists]) : int) -> depth v n && n <= d
    : [%v: int tree])
    [@under])
