let rec rbtree_gen (inv : int) (color : bool) (h : int) : int rbtree =
  if sizecheck h then if color then Err else Err else if color then Err else Err

let[@assert] rbtree_gen =
  let inv = ((v >= 0 : [%v: int]) [@over]) in
  let color = ((true : [%v: bool]) [@over]) in
  let[@assert] h =
    ((v >= 0 && if color then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over])
  in
  ((num_black v h && no_red_red v
    &&
    if color then not (rb_root_color v true)
    else (h == 0)#==>(not (rb_root_color v false))
    : [%v: int rbtree])
    [@under])
