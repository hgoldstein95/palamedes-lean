let[@assert] rty1 =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let color = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if color then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  (h > 0 && color
   && fun ((x_13 [@exists]) : int) ->
   inv - 1 >= 0
   && h - 1 >= 0
   && h - 1 + (h - 1) + 1 == inv - 1
   && fun ((lt2 [@exists]) : int rbtree) ->
   no_red_red lt2
   && num_black lt2 (h - 1)
   && ((h - 1 == 0) #==> (not (rb_root_color lt2 false)))
   && inv - 1 < inv
   && h - 1 >= 0
   && h - 1 + (h - 1) + 1 == inv - 1
   && fun ((rt2 [@exists]) : int rbtree) ->
   no_red_red rt2
   && num_black rt2 (h - 1)
   && ((h - 1 == 0) #==> (not (rb_root_color rt2 false)))
   && rb_root_color v false && rb_root v x_13 && rb_lch v lt2 && rb_rch v rt2
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
  (h > 0 && color && num_black v h && no_red_red v
   && (color #==> (not (rb_root_color v true)))
   &&
   if color then not (rb_root_color v true)
   else (h == 0) #==> (not (rb_root_color v false))
    : [%v: int rbtree])
    [@under]
