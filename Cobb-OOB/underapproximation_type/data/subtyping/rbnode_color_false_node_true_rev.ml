let[@assert] rty1 =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let color = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if color then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  (fun ((lt3 [@exists]) : int rbtree) ((rt3 [@exists]) : int rbtree)
       ((x_20 [@exists]) : int) ->
     h > 0 && (not color)
     && inv - 1 >= 0
     && inv - 1 < inv
     && h >= 0
     && h + h == inv - 1
     && num_black lt3 h && no_red_red lt3 && num_black rt3 h && no_red_red rt3
     && (not (rb_root_color rt3 true))
     && (not (rb_root_color lt3 true))
     && rb_root v x_20 && rb_lch v lt3 && rb_rch v rt3
     && (not (rb_root_color v false))
     && rb_root_color v true
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
  (h > 0 && (not color) && num_black v h && no_red_red v && rb_root_color v true
   && ((not color) #==> ((h == 0) #==> (not (rb_root_color v false))))
    : [%v: int rbtree])
    [@under]
