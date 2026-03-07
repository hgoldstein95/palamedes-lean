let[@assert] rty1 =
  let num_arr_tau = (v >= 0 : [%v: int]) [@over] in
  let num = (v >= 0 : [%v: int]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (num_arr v num_arr_tau : [%v: stlc_ty]) [@over] in
  (num > 0 && typing gamma v tau && num_app v num && is_app v
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
   && fun ((func_ty [@exists]) : stlc_ty) ->
   stlc_ty_arr1 func_ty arg_tau
   && stlc_ty_arr2 func_ty tau
   && fun ((num_arr_func_ty [@exists]) : int) ->
   num_arr func_ty num_arr_func_ty
   && num_arr_func_ty >= 0
   && (num_arr_func_ty < num_arr_tau || num_app_func < num)
   && fun ((x_7 [@exists]) : stlc_ty) ->
   stlc_ty_arr1 x_7 arg_tau && stlc_ty_arr2 x_7 tau
   && num_arr x_7 num_arr_func_ty
   && fun ((func [@exists]) : stlc_term) ->
   typing gamma func x_7 && num_app func num_app_func
   && fun ((num_arr_arg_ty [@exists]) : int) ->
   num_arr arg_tau num_arr_arg_ty
   && num_arr_arg_ty >= 0
   && fun ((num_2 [@exists]) : int) ->
   num_2 >= 0 && num_arr_arg_ty >= 0
   && (num_arr_arg_ty < num_arr_tau || num_2 < num)
   && num_2 == num - num_app_func - 1
   && num_arr arg_tau num_arr_arg_ty
   && fun ((arg [@exists]) : stlc_term) ->
   typing gamma arg arg_tau && num_app arg num_2 && stlc_app1 v func
   && stlc_app2 v arg
    : [%v: stlc_term])
    [@under]
