let rec rbtree_gen (inv : int) (color : bool) (h : int) (lo : int) (hi : int) : int rbtree =
  if sizecheck h then Err
  else if incr lo < hi then 
    let (x : int) = int_range lo hi in
    if color then
      let (lt2 : int rbtree) = rbtree_gen (subs inv) false (subs h) lo x in
      let (rt2 : int rbtree) = rbtree_gen (subs inv) false (subs h) x hi in
      Rbtnode (false, lt2, x, rt2)
    else
      let (c : bool) = bool_gen () in
      if c then
        let (lt3 : int rbtree) = rbtree_gen (subs inv) true h lo x in
        let (rt3 : int rbtree) = rbtree_gen (subs inv) true h x hi in
        Rbtnode (true, lt3, x, rt3)
      else
        let (lt4 : int rbtree) = rbtree_gen (subs (subs inv)) false (subs h) lo x in
        let (rt4 : int rbtree) = rbtree_gen (subs (subs inv)) false (subs h) x hi in
        Rbtnode (false, lt4, x, rt4)
    else Exn

let[@assert] rbtree_gen =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let color = (true : [%v: bool]) [@over] in
  let lo = ((true : [%v: int]) [@over]) in
  let hi = ((lo < v : [%v: int]) [@over]) in
  let[@assert] h =
    (v >= 0 && if color then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  (num_black v h && no_red_red v &&
    ((not (rb_leaf v))#==>(rbt_lower_bound v lo))
    && ((not (rb_leaf v))#==>(rbt_upper_bound v hi))
    && rb_bst v 
    && if color then not (rb_root_color v true)
   else (h == 0) #==> (not (rb_root_color v false))
    : [%v: int rbtree])
    [@under]
