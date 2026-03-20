let rec twos_tree_gen (d : int) : int tree =
  if sizecheck d then Leaf
  else if bool_gen () then
    let (x : int) = two () in
    let (lt : int tree) = twos_tree_gen (subs d) in
    let (rt : int tree) = twos_tree_gen (subs d) in
    Node (x, lt, rt)
  else Leaf 

let[@assert] twos_tree_gen =
  let d = ((0 <= v : [%v: int]) [@over]) in
  ((((not (leaf v))#==>(lower_bound v 2))
    && ((not (leaf v))#==>(upper_bound v 2))
    && fun ((n [@exists]) : int) -> depth v n && n <= d
    : [%v: int tree])
    [@under])
