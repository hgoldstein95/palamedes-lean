let[@assert] rty1 =
  let d = ((0 <= v : [%v: int]) [@over]) in
  let lo = ((true : [%v: int]) [@over]) in
  let hi = ((lo < v : [%v: int]) [@over]) in
  ((fun ((x [@exists]) : int) ->
      (fun ((x_0 [@exists]) : bool) ->
        ((x_0#==>(d == 0)) && ((d == 0)#==>x_0))
        && (((not x_0)#==>(d > 0)) && ((d > 0)#==>(not x_0)))
        && (not x_0)
        && lo + 1 < hi
        && fun ((b_13 [@exists]) : int) ->
        1 + lo < b_13 && b_13 == hi && lo < x && x < b_13)
      (* fun ((x [@exists]) : int) -> *)
      && (fun ((x_0 [@exists]) : bool) ->
        ((x_0#==>(d == 0)) && ((d == 0)#==>x_0))
        && (((not x_0)#==>(d > 0)) && ((d > 0)#==>(not x_0)))
        && (not x_0)
        && lo + 1 < hi
        && fun ((b_13 [@exists]) : int) ->
        1 + lo < b_13 && b_13 == hi && lo < x && x < b_13)
      (* fun ((x [@exists]) : int) -> *)
      && (fun ((x_0 [@exists]) : bool) ->
        ((x_0#==>(d == 0)) && ((d == 0)#==>x_0))
        && (((not x_0)#==>(d > 0)) && ((d > 0)#==>(not x_0)))
        && (not x_0)
        && lo + 1 < hi
        && fun ((b_13 [@exists]) : int) ->
        1 + lo < b_13 && b_13 == hi && lo < x && x < b_13)
      (* fun ((x [@exists]) : int) -> *)
      && (fun ((x_0 [@exists]) : bool) ->
        ((x_0#==>(d == 0)) && ((d == 0)#==>x_0))
        && (((not x_0)#==>(d > 0)) && ((d > 0)#==>(not x_0)))
        && (not x_0)
        && lo + 1 < hi
        && fun ((b_13 [@exists]) : int) ->
        1 + lo < b_13 && b_13 == hi && lo < x && x < b_13)
      && fun ((idx231_13 [@exists]) : int tree) ->
      (fun ((d_9 [@exists]) : int) ->
        0 <= d_9 && d_9 >= 0 && d_9 < d
        && d_9 == d - 1
        && fun ((hi_1 [@exists]) : int) ->
        lo < hi_1 && hi_1 == x
        && fun ((idx231 [@exists]) : int tree) ->
        ((not (leaf idx231))#==>(lower_bound idx231 lo))
        && ((not (leaf idx231))#==>(upper_bound idx231 hi_1))
        && bst idx231
        && (fun ((n [@exists]) : int) -> depth idx231 n && n <= d_9)
        && idx231_13 == idx231)
      (* fun ((x [@exists]) : int) -> *)
      && (fun ((x_0 [@exists]) : bool) ->
        ((x_0#==>(d == 0)) && ((d == 0)#==>x_0))
        && (((not x_0)#==>(d > 0)) && ((d > 0)#==>(not x_0)))
        && (not x_0)
        && lo + 1 < hi
        && fun ((b_13 [@exists]) : int) ->
        1 + lo < b_13 && b_13 == hi && lo < x && x < b_13)
      (* fun ((x [@exists]) : int) -> *)
      && (fun ((x_0 [@exists]) : bool) ->
        ((x_0#==>(d == 0)) && ((d == 0)#==>x_0))
        && (((not x_0)#==>(d > 0)) && ((d > 0)#==>(not x_0)))
        && (not x_0)
        && lo + 1 < hi
        && fun ((b_13 [@exists]) : int) ->
        1 + lo < b_13 && b_13 == hi && lo < x && x < b_13)
      (* fun ((x [@exists]) : int) -> *)
      && (fun ((x_0 [@exists]) : bool) ->
        ((x_0#==>(d == 0)) && ((d == 0)#==>x_0))
        && (((not x_0)#==>(d > 0)) && ((d > 0)#==>(not x_0)))
        && (not x_0)
        && lo + 1 < hi
        && fun ((b_13 [@exists]) : int) ->
        1 + lo < b_13 && b_13 == hi && lo < x && x < b_13)
      && fun ((idx210_10 [@exists]) : int tree) ->
      (fun ((d_2 [@exists]) : int) ->
        0 <= d_2 && d_2 >= 0 && d_2 < d
        && d_2 == d - 1
        && fun ((hi_0 [@exists]) : int) ->
        x < hi_0 && hi_0 == hi
        && fun ((idx210 [@exists]) : int tree) ->
        ((not (leaf idx210))#==>(lower_bound idx210 x))
        && ((not (leaf idx210))#==>(upper_bound idx210 hi_0))
        && bst idx210
        && (fun ((n [@exists]) : int) -> depth idx210 n && n <= d_2)
        && idx210_10 == idx210)
      && fun ((idx1394 [@exists]) : int tree) ->
      root idx1394 x && lch idx1394 idx231_13 && rch idx1394 idx210_10
      && (fun ((nl [@exists]) : int) ->
        fun ((nr [@exists]) : int) ->
         depth idx231_13 nl && depth idx210_10 nr
         && ((nl > nr)#==>(depth idx1394 (nl + 1)))
         && ((nr >= nl)#==>(depth idx1394 (nr + 1))))
      && v == idx1394
    : [%v: int tree])
    [@under])

let[@assert] rty2 =
  let d = ((0 <= v : [%v: int]) [@over]) in
  let lo = ((true : [%v: int]) [@over]) in
  let hi = ((lo < v : [%v: int]) [@over]) in
  ((fun ((x [@exists]) : int) ->
      (fun ((x_0 [@exists]) : bool) ->
        ((x_0#==>(d == 0)) && ((d == 0)#==>x_0))
        && (((not x_0)#==>(d > 0)) && ((d > 0)#==>(not x_0)))
        && (not x_0)
        && lo + 1 < hi
        && fun ((b_13 [@exists]) : int) ->
        1 + lo < b_13 && b_13 == hi && lo < x && x < b_13)
      && d > 0
      && (not (leaf v))
      && (not (leaf v)) #==> (lower_bound v lo)
      && (not (leaf v)) #==> (upper_bound v hi)
      && bst v
      && fun ((n [@exists]) : int) -> depth v n && n <= d
    : [%v: int tree])
    [@under])
