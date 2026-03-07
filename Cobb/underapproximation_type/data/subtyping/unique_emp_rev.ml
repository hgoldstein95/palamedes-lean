let[@assert] rty1 =
  let s = (0 <= v : [%v: int]) [@over] in
  (emp v : [%v: int list]) [@under]

let[@assert] rty2 =
  let s = (0 <= v : [%v: int]) [@over] in
  (len v 0 && uniq v : [%v: int list]) [@under]
