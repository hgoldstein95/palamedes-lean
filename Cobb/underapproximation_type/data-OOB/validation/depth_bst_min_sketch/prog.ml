let rec size_bst_gen (d : int) (lo : int) (hi : int) : int tree =
  if sizecheck d then Leaf
  else if incr lo < hi then
    let (x : int) = int_range lo hi in
    if bool_gen () then
      let (lt : int tree) = size_bst_gen (subs d) lo x in
      let (rt : int tree) = size_bst_gen (subs d) x hi in
      Node (x, lt, rt)
    else Leaf
  else Leaf

let[@assert] size_bst_gen =
  let d = ((0 <= v : [%v: int]) [@over]) in
  let lo = ((true : [%v: int]) [@over]) in
  let hi = ((lo < v : [%v: int]) [@over]) in
  ((((not (leaf v))#==>(lower_bound v lo))
    && ((not (leaf v))#==>(upper_bound v hi))
    && bst v
    && fun ((n [@exists]) : int) -> depth v n && n <= d
    : [%v: int tree])
    [@under])
