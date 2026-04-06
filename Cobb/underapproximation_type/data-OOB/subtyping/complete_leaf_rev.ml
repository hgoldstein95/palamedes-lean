let[@assert] rty1 =
  let s = ((0 == v : [%v: int]) [@over]) in
  ((leaf v : [%v: int tree]) [@under])

let[@assert] rty2 =
  let s = ((0 == v : [%v: int]) [@over]) in
  ((leaf v && complete v : [%v: int tree]) [@under])
