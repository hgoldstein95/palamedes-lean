let[@assert] rty1 =
  let num_arr_tau = (v >= 0 : [%v: int]) [@over] in
  let num = (v >= 0 : [%v: int]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (num_arr v num_arr_tau : [%v: stlc_ty]) [@over] in
  (((is_abs v && (not (is_app v)) && (not (num == 0)) && not (num_arr_tau == 0))
   || (is_abs v && (not (is_app v)) && (not (num == 0)) && num_arr_tau == 0))
   && typing gamma v tau && num_app v num
    : [%v: stlc_term])
    [@under]

let[@assert] rty2 =
  let num_arr_tau = (v >= 0 : [%v: int]) [@over] in
  let num = (v >= 0 : [%v: int]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (num_arr v num_arr_tau : [%v: stlc_ty]) [@over] in
  (num > 0 && fun ((tau1 [@exists]) : stlc_ty) ((tau2 [@exists]) : stlc_ty) ->
   stlc_ty_arr1 tau tau1 && stlc_ty_arr2 tau tau2 && typing gamma v tau
   && num_app v num
   && fun ((body [@exists]) : stlc_term) ->
   stlc_abs_ty v tau1 && stlc_abs_body v body
    : [%v: stlc_term])
    [@under]
