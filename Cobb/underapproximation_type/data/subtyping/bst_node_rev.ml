let[@assert] rty1 =
  let d = ((0 <= v : [%v: int]) [@over]) in
  let lo = ((true : [%v: int]) [@over]) in
  let hi = ((lo < v : [%v: int]) [@over]) in
  ((fun ((lt [@exists]) : int tree)
      ((rt [@exists]) : int tree)
      ((d_2 [@exists]) : int)
      ((x [@exists]) : int)
    ->
      d > 0
      && lo + 1 < hi
      && lo < x && x < hi
      && 0 <= d - 1
      && d - 1 >= 0
      && d - 1 < d
      && ((not (leaf lt))#==>(lower_bound lt lo))
      && ((not (leaf lt))#==>(upper_bound lt x))
      && bst lt
      && (fun ((n [@exists]) : int) ->
        depth lt n && n <= d - 1)
      && 0 <= d_2 && d_2 >= 0 && d_2 < d
      && d_2 == d - 1
      && x < hi
      && ((not (leaf rt))#==>(lower_bound rt x))
      && ((not (leaf rt))#==>(upper_bound rt hi))
      && bst rt
      && (fun ((n [@exists]) : int) -> depth rt n && n <= d_2 )
      && root v x && lch v lt && rch v rt
      && fun ((nl [@exists]) : int) ((nr [@exists]) : int) ->
      depth lt nl && depth rt nr
      && ((nl > nr)#==>(depth v (nl + 1)))
      && ((nr >= nl)#==>(depth v (nr + 1)))
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
    && (not (leaf v))
    && fun ((n [@exists]) : int) -> depth v n && n <= d
    : [%v: int tree])
    [@under])
