let[@assert] rty1 =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((x [@exists]) : int) ((l [@exists]) : int list) ((s_15 [@exists]) : int) ->
     s > 0 && s_15 >= 0 && s_15 < s
     && s_15 == s - 1
     && len l s_15 && uniq l
     && (not (list_mem l x))
     && hd v x && tl v l
    : [%v: int list])
    [@under]

let[@assert] rty2 =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((x [@exists]) : int) ((s_15 [@exists]) : int) ((l [@exists]) : int list) ->
     s > 0 && s_15 >= 0 && s_15 < s
     && s_15 == s - 1
     && len l s_15 && uniq l
     && (not (list_mem l x))
     && (not (emp v))
     && len v s && uniq v
    : [%v: int list])
    [@under]
