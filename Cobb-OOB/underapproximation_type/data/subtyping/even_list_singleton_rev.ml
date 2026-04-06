let[@assert] rty1 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) ->
      len v n && n <= s + 1 && n > 0 && s == 0 && all_evens v
    : [%v: int list])
    [@under])

let[@assert] rty2 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((s == 0
    &&
    fun ((x [@exists]) : int)
      ((x2 [@exists]) : int)
      ((l2 [@exists]) : int list)
    -> hd v x && x == x2 * 2 && tl v l2 && emp l2
    : [%v: int list])
    [@under])
