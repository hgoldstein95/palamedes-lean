let[@assert] rty1 =
  let num_arr_tau = (v >= 0 : [%v: int]) [@over] in
  let num = (v >= 0 : [%v: int]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (num_arr v num_arr_tau : [%v: stlc_ty]) [@over] in
  (
     num > 0 && num_app v num && is_app v
    : [%v: stlc_term])
    [@under]

let[@assert] rty2 =
  let num_arr_tau = (v >= 0 : [%v: int]) [@over] in
  let num = (v >= 0 : [%v: int]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (num_arr v num_arr_tau : [%v: stlc_ty]) [@over] in
  (num > 0
   && fun ((arg_tau [@exists]) : stlc_ty) ((num_app_func [@exists]) : int) ->
   0 <= num_app_func && num_app_func < num
   && fun ((func [@exists]) : stlc_term) ->
   num_app func num_app_func && fun ((num_2 [@exists]) : int) ->
   num_2 >= 0
   && num_2 == num - num_app_func - 1
   && fun ((arg [@exists]) : stlc_term) ->
   num_app arg num_2 && stlc_app1 v func && stlc_app2 v arg
    : [%v: stlc_term])
    [@under]
