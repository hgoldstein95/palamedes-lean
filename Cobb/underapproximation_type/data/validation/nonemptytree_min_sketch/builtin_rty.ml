let[@library] True = (v : [%v: bool]) [@under]
let[@library] False = (not v : [%v: bool]) [@under]
let[@library] true = (v : [%v: bool]) [@under]
let[@library] false = (not v : [%v: bool]) [@under]

let[@library] Leaf = (leaf v && depth v 0 : [%v: int tree]) [@under]

let[@library] Node =
  let x = ((true : [%v: int]) [@over]) in
  let lt = ((true : [%v: int tree]) [@over]) in
  let rt = ((true : [%v: int tree]) [@over]) in
  ((root v x && lch v lt && rch v rt
    && fun ((nl [@exists]) : int) ((nr [@exists]) : int) ->
    depth lt nl && depth rt nr
    && ((nl > nr)#==>(depth v (nl + 1)))
    && ((nr >= nl)#==>(depth v (nr + 1)))
    : [%v: int tree])
    [@under])

let[@library] bool_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: bool]) [@under]

let[@library] int_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: int]) [@under]

let[@library] hidden_tree_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: int tree]) [@under]

let[@library] sizecheck =
  let x = (true : [%v: int]) [@over] in
  (iff v (x == 0) && iff (not v) (x > 0) : [%v: bool]) [@under]

let[@library] subs =
  let s = (true : [%v: int]) [@over] in
  (v == s - 1 : [%v: int]) [@under]

let[@library] ( < ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (iff v (a < b) : [%v: bool]) [@under]

let[@library] ( > ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (iff v (a > b) : [%v: bool]) [@under]

let[@library] ( <= ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (iff v (a <= b) : [%v: bool]) [@under]

let[@library] ( >= ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (iff v (a >= b) : [%v: bool]) [@under]