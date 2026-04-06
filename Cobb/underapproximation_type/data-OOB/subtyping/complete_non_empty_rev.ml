let[@assert] rty1 =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((_2 [@exists]) : int) ((s_4 [@exists]) : int)
       ((_48 [@exists]) : int tree) ((_46 [@exists]) : int tree) ->
     s > 0 && 0 <= s_4 && s_4 >= 0 && s_4 < s
     && s_4 == s - 1
     && depth _46 s_4 && complete _46 && depth _48 s_4 && complete _48
     && root v _2 && lch v _46 && rch v _48
    : [%v: int tree])
    [@under]

let[@assert] rty2 =
  let s = (0 <= v : [%v: int]) [@over] in
  ((not (leaf v)) && depth v s && complete v : [%v: int tree]) [@under]
