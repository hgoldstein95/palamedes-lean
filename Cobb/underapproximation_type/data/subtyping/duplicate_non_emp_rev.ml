let[@assert] rty1 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  ((fun ((s1 [@exists]) : int) ((l [@exists]) : int list) ->
      s > 0 && s1 >= 0 && s1 < s
      && s1 == s - 1
      && len l s1
      && (fun (u : int) -> (list_mem l u)#==>(u == x))
      && hd v x && tl v l
    : [%v: int list])
    [@under])

let[@assert] rty2 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  ((s > 0
    && (not (emp v))
    && len v s
    && fun (u : int) -> (list_mem v u)#==>(u == x)
    : [%v: int list])
    [@under])
