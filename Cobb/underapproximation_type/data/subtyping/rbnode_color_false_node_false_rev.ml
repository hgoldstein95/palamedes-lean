let[@assert] rty1 =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let color = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if color then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  (fun ((x_0 [@exists]) : bool) ((c [@exists]) : bool) ((h_0 [@exists]) : int)
       ((lt4 [@exists]) : int rbtree) ((rt4 [@exists]) : int rbtree)
       ((inv_1 [@exists]) : int) ((inv_2 [@exists]) : int)
       ((h_1 [@exists]) : int) ((x_13 [@exists]) : int) ((x_24 [@exists]) : int) ->
     h > 0 && (not color) && (not c)
     && inv - 2 >= 0
     && inv - 2 < inv
     && h - 1 >= 0
     && h - 1 + (h - 1) + 1 == inv - 2
     && num_black lt4 (h - 1)
     && no_red_red lt4
     && ((h - 1 == 0) #==> (not (rb_root_color lt4 false)))
     && inv - 2 >= 0
     && inv - 2 < inv
     && h - 1 >= 0
     && h - 1 + (h - 1) + 1 == inv - 2
     && num_black rt4 (h - 1)
     && no_red_red rt4
     && ((h - 1 == 0) #==> (not (rb_root_color rt4 false)))
     && rb_root_color v false && rb_root v x_24 && rb_lch v lt4 && rb_rch v rt4
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
  (h > 0 && (not color) && num_black v h && no_red_red v
   && rb_root_color v false
   (*  && ((not color) #==> ((h == 0) #==> (not (rb_root_color v false)))) *)
    : [%v: int rbtree])
    [@under]
