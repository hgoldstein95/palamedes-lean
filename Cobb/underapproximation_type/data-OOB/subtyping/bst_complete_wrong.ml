let[@assert] rty2 =
  let d = (0 <= v : [%v: int]) [@over] in
  let lo = (true : [%v: int]) [@over] in
  let hi = (lo < v : [%v: int]) [@over] in
  (d > 0
   && lo + 1 < hi
   && fun ((x [@exists]) : int) ->
   lo < x && x < hi
   && 0 <= d - 1
   && fun ((lt [@exists]) : int tree) ->
   ((not (leaf lt)) #==> (lower_bound lt lo))
   && ((not (leaf lt)) #==> (upper_bound lt hi))
   && bst lt
   && (fun ((n [@exists]) : int) -> depth lt n && n <= d - 1)
   && 0 <= d - 1
   && fun ((rt [@exists]) : int tree) ->
   ((not (leaf rt)) #==> (lower_bound rt lo))
   && ((not (leaf rt)) #==> (upper_bound rt hi))
   && bst rt
   && (fun ((n [@exists]) : int) -> depth rt n && n <= d - 1)
   && root v x && lch v lt && rch v rt
    : [%v: int tree])
    [@under]

let[@assert] rty1 =
  let d = (0 <= v : [%v: int]) [@over] in
  let lo = (true : [%v: int]) [@over] in
  let hi = (lo < v : [%v: int]) [@over] in
  (d > 0
   && ((not (leaf v)) #==> (lower_bound v lo && upper_bound v hi))
   && (not (leaf v))
   && bst v
   && fun ((n [@exists]) : int) -> depth v n && n <= d
    : [%v: int tree])
    [@under]
