let[@assert] rty1 =
  let d = ((0 <= v : [%v: int]) [@over]) in
  let lo = ((true : [%v: int]) [@over]) in
  let hi = ((lo < v : [%v: int]) [@over]) in
  ((leaf v && d == 0 && depth v 0 : [%v: int tree]) [@under])

let[@assert] rty2 =
  let d = ((0 <= v : [%v: int]) [@over]) in
  let lo = ((true : [%v: int]) [@over]) in
  let hi = ((lo < v : [%v: int]) [@over]) in
  ((leaf v && d == 0
    && (not (leaf v)) #==> (lower_bound v lo)
    && (not (leaf v)) #==> (upper_bound v hi)
    && bst v
    && fun ((n [@exists]) : int) -> depth v n && n <= d && n >= 0
    : [%v: int tree])
    [@under])