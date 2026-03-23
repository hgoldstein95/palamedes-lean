let[@library] True = (v : [%v: bool]) [@under]
let[@library] False = (not v : [%v: bool]) [@under]
let[@library] true = (v : [%v: bool]) [@under]
let[@library] false = (not v : [%v: bool]) [@under]
let[@library] Nil = (emp v : [%v: bool list]) [@under]

let[@library] Cons =
  let x = ((true : [%v: bool]) [@over]) in
  let xs = ((true : [%v: bool list]) [@over]) in
  ((hd v x && tl v xs : [%v: bool list]) [@under])

let[@library] sizecheck =
  let x = ((true : [%v: int]) [@over]) in
  ((iff v (x == 0) && iff (not v) (x > 0) : [%v: bool]) [@under])

let[@library] subs =
  let s = ((true : [%v: int]) [@over]) in
  ((v == s - 1 : [%v: int]) [@under])

let[@library] incr =
  let s = ((true : [%v: int]) [@over]) in
  ((v == s + 1 : [%v: int]) [@under])

let[@library] ( < ) =
  let a = ((true : [%v: int]) [@over]) in
  let b = ((true : [%v: int]) [@over]) in
  ((iff v (a < b) : [%v: bool]) [@under])

let[@library] int_range =
  let a = ((true : [%v: int]) [@over]) in
  let b = ((1 + a < v : [%v: int]) [@over]) in
  ((a < v && v < b : [%v: int]) [@under])
