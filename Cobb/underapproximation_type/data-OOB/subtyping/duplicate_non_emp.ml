let[@assert] rty2 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  ((s > 0
    && (not (emp v))
    && len v s
    && fun (u : int) -> (list_mem v u)#==>(u == x)
    : [%v: int list])
    [@under])

let[@assert] rty1 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  ((fun ((x_2 [@exists]) : int)
      ((_25 [@exists]) : int list)
      ((s_6 [@exists]) : int)
      ((_x28 [@exists]) : int list)
      ((_x68 [@exists]) : int list)
    ->
      s > 0
      && (s_6 >= 0 && s_6 < s
         && s_6 == s - 1
         && len _x28 s_6
         && (fun (u : int) -> (list_mem _x28 u)#==>(u == x))
         && _25 == _x28)
      && hd _x68 x && tl _x68 _25 && v == _x68
    : [%v: int list])
    [@under])
