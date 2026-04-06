let[@assert] rty1 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  (((not (emp v))
    && len v s
    && sorted v (*    && fun (u : int) -> (hd v u) #==> (x <= u) *)
    && (not (emp v)) #==> (fun ((u [@exists]) : int) -> hd v u && x <= u)
    : [%v: int list])
    [@under])

let[@assert] rty2 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  ((fun ((y [@exists]) : int)
      ((s1 [@exists]) : int)
      ((l [@exists]) : int list)
    ->
      s > 0 && x <= y && 0 <= s1 && s1 < s
      && s1 == s - 1
      && len l s1 && sorted l && hd v y && tl v l
      (*    && fun (u : int) -> (hd l u) #==> (y <= u) *)
      && (not (emp l)) #==> (fun ((u [@exists]) : int) -> hd l u && y <= u)
    : [%v: int list])
    [@under])

(* let[@assert] rty1 =
  let s = (0 <= v : [%v: int]) [@over] in
  let x = (true : [%v: int]) [@over] in
  ((not (emp v))
   && len v s && sorted v
   && fun (u : int) -> (hd v u) #==> (x <= u)
    : [%v: int list])
    [@under]

let[@assert] rty2 =
  let s = (0 <= v : [%v: int]) [@over] in
  let x = (true : [%v: int]) [@over] in
  (fun ((y [@exists]) : int) ((s1 [@exists]) : int) ((l [@exists]) : int list) ->
     s > 0 && x <= y && 0 <= s1 && s1 < s
     && s1 == s - 1
     && len l s1 && sorted l && hd v y && tl v l
     && (fun (u : int) -> (hd l u) #==> (y <= u))
    : [%v: int list])
    [@under]
 *)
