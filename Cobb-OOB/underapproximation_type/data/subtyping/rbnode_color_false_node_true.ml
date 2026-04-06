let[@assert] rty2 =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let color = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if color then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  (fun ((x_0 [@exists]) : bool) ((c [@exists]) : bool) ((h_0 [@exists]) : int)
       ((lt2 [@exists]) : int rbtree) ((lt3 [@exists]) : int rbtree)
       ((rt2 [@exists]) : int rbtree) ((rt3 [@exists]) : int rbtree)
       ((inv_1 [@exists]) : int) ((inv_2 [@exists]) : int)
       ((inv_3 [@exists]) : int) ((inv_4 [@exists]) : int)
       ((h_1 [@exists]) : int) ((h_2 [@exists]) : int) ((h_3 [@exists]) : int)
       ((x_13 [@exists]) : int) ((x_20 [@exists]) : int) ->
     (* iff x_0 (h == 0)
        && iff (not x_0) *)
     h > 0
     (* x_0
         && ((color && rb_leaf v)
            || (not color) && fun ((x_1 [@exists]) : bool) ->
               (x_1 && rb_leaf v)
               || (not x_1) && fun ((x_2 [@exists]) : int rbtree) ->
                  rb_leaf x_2
                  && fun ((x_3 [@exists]) : int) ((x_4 [@exists]) : int rbtree)
                    ->
                  rb_leaf x_4 && rb_root_color v true && rb_root v x_3
                  && rb_lch v x_4 && rb_rch v x_2)
        || (not x_0)
           && *)
     (* color && inv_1 >= 0 && inv_1 < inv
         && inv_1 == inv - 1
         && h_0 >= 0
         && (false #==> (h_0 + h_0 == inv_1))
         && ((not false) #==> (h_0 + h_0 + 1 == inv_1))
         && h_0 == h - 1
         && num_black lt2 h_0 && no_red_red lt2
         && false #==> not (rb_root_color lt2 true)
         && ((not false) #==> (h_0 == 0 => not (rb_root_color lt2 false)))
         && inv_2 >= 0 && inv_2 < inv
         && inv_2 == inv - 1
         && h_1 >= 0
         && (false #==> (h_1 + h_1 == inv_2))
         && ((not false) #==> (h_1 + h_1 + 1 == inv_2))
         && h_1 == h - 1
         && num_black rt2 h_1 && no_red_red rt2
         && (false #==> (not (rb_root_color rt2 true)))
         && ((not false) #==> ((h_1 == 0) #==> (not (rb_root_color rt2 false))))
         && rb_root_color v false && rb_root v x_13 && rb_lch v lt2
         && rb_rch v rt2
        || *) && (not color)
     && c && inv_3 >= 0 && inv_3 < inv
     && inv_3 == inv - 1
     && h_2 >= 0
     && (true #==> (h_2 + h_2 == inv_3))
     && ((not true) #==> (h_2 + h_2 + 1 == inv_3))
     && h_2 == h && num_black lt3 h_2 && no_red_red lt3
     && (true #==> (not (rb_root_color lt3 true)))
     && ((not true) #==> ((h_2 == 0) #==> (not (rb_root_color lt3 false))))
     && inv_4 >= 0 && inv_4 < inv
     && inv_4 == inv - 1
     && h_3 >= 0
     && (true #==> (h_3 + h_3 == inv_4))
     && ((not true) #==> (h_3 + h_3 + 1 == inv_4))
     && h_3 == h && num_black rt3 h_3 && no_red_red rt3
     && (true #==> (not (rb_root_color rt3 true)))
     && ((not true) #==> ((h_3 == 0) #==> (not (rb_root_color rt3 false))))
     && rb_root_color v true && rb_root v x_20 && rb_lch v lt3 && rb_rch v rt3
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
  (h > 0 && (not color) && num_black v h && no_red_red v

   && rb_root_color v true
   (*    && (color #==> (not (rb_root_color v true))) *)
   && ((not color) #==> ((h == 0) #==> (not (rb_root_color v false))))
    : [%v: int rbtree])
    [@under]
