let[@assert] rty1 =
  let d = ((0 <= v : [%v: int]) [@over]) in
  let lo = ((true : [%v: int]) [@over]) in
  let hi = ((lo < v : [%v: int]) [@over]) in
  ((fun ((x_0 [@exists]) : bool) ->
      iff x_0 (d == 0)
      && iff (not x_0) (d > 0)
      && (not x_0)
      && (( lo + 1 < hi && fun ((b_1 [@exists]) : int) ->
            1 + lo < b_1
            && b_1 == hi
            && fun ((x [@exists]) : int) ->
            lo < x && x < b_1
            && fun ((x_4 [@exists]) : bool) ->
            ( x_4 && fun ((d_1 [@exists]) : int) ->
              0 <= d_1 && d_1 >= 0 && d_1 < d
              && d_1 == d - 1
              && fun ((hi_0 [@exists]) : int) ->
              lo < hi_0 && hi_0 == x
              && fun ((lt [@exists]) : int tree) ->
              ((not (leaf lt))#==>(lower_bound lt lo))
              && ((not (leaf lt))#==>(upper_bound lt hi_0))
              && bst lt
              && (fun ((n [@exists]) : int) -> depth lt n && n <= d_1)
              && fun ((d_2 [@exists]) : int) ->
              0 <= d_2 && d_2 >= 0 && d_2 < d
              && d_2 == d - 1
              && fun ((hi_1 [@exists]) : int) ->
              x < hi_1 && hi_1 == hi
              && fun ((rt [@exists]) : int tree) ->
              ((not (leaf rt))#==>(lower_bound rt x))
              && ((not (leaf rt))#==>(upper_bound rt hi_1))
              && bst rt
              && (fun ((n [@exists]) : int) -> depth rt n && n <= d_2)
              && root v x && lch v lt && rch v rt
              && fun ((nl [@exists]) : int) ->
              fun ((nr [@exists]) : int) ->
               depth lt nl && depth rt nr
               && ((nl > nr)#==>(depth v (nl + 1)))
               && ((nr >= nl)#==>(depth v (nr + 1))) )
            || ((not x_4) && leaf v && depth v 0) )
         || ((not (lo + 1 < hi)) && leaf v && depth v 0))
    : [%v: int tree])
    [@under])

let[@assert] rty2 =
  let d = ((0 <= v : [%v: int]) [@over]) in
  let lo = ((true : [%v: int]) [@over]) in
  let hi = ((lo < v : [%v: int]) [@over]) in
  ((d > 0
    && ((not (leaf v))#==>(lower_bound v lo))
    && ((not (leaf v))#==>(upper_bound v hi))
    && bst v
    && fun ((n [@exists]) : int) -> depth v n && n <= d
    : [%v: int tree])
    [@under])
