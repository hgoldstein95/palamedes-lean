let[@assert] rty1 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  ((emp v && len v s (* && fun (u : int) -> (list_mem v u)#==>(u == x) *)
    : [%v: int list])
    [@under])

let[@assert] rty2 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  ((emp v : [%v: int list]) [@under])
