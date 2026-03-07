let[@assert] rty1 =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let color = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if color then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  (fun ((t [@exists]) : int rbtree) ->
     rb_leaf t && rb_root_color v true
     && (not (rb_root_color v false))
     && rb_lch v t && rb_rch v t
    : [%v: int rbtree])
    [@under]

let[@assert] rty2 =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let color = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if color then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  ((not (rb_root_color v false))
   && rb_root_color v true && num_black v 0 && no_red_red v
    : [%v: int rbtree])
    [@under]
