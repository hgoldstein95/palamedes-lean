let[@assert] rty2 =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let color = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if color then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  (h > 0 && color
   && fun ((inv_1 [@exists]) : int) ->
   inv_1 >= 0 && inv_1 < inv
   && inv_1 == inv - 1
   && fun ((h_0 [@exists]) : int) ->
   h_0 >= 0
   && h_0 + h_0 + 1 == inv_1
   && h_0 == h - 1
   && fun ((lt2 [@exists]) : int rbtree) ->
   num_black lt2 h_0 && no_red_red lt2
   && ((h_0 == 0) #==> (not (rb_root_color lt2 false)))
   && fun ((inv_2 [@exists]) : int) ->
   inv_2 >= 0 && inv_2 < inv
   && inv_2 == inv - 1
   && fun ((h_1 [@exists]) : int) ->
   h_1 >= 0
   && h_1 + h_1 + 1 == inv_2
   && h_1 == h - 1
   && fun ((rt2 [@exists]) : int rbtree) ->
   num_black rt2 h_1 && no_red_red rt2
   && ((h_1 == 0) #==> (not (rb_root_color rt2 false)))
   && fun ((x_13 [@exists]) : int) ->
   rb_root_color v false && rb_root v x_13 && rb_lch v lt2 && rb_rch v rt2
    : [%v: int rbtree])
    [@under]

let[@assert] rty1 =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let color = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if color then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  (h > 0 && color && num_black v h && no_red_red v
   && (color #==> (not (rb_root_color v true)))
    : [%v: int rbtree])
    [@under]
