let[@assert] rty1 =
  let num = (v >= 0 : [%v: int]) [@over] in
  let num_arr_tau = (v >= 0 : [%v: int]) [@over] in
  let tau = (num_arr v num_arr_tau : [%v: stlc_ty]) [@over] in

  let tau1 = (true : [%v: stlc_ty]) [@under] in
  let tau2 = (true : [%v: stlc_ty]) [@under] in
  let path_condition =
    ((num > 0)
    && (fun ((x_2 [@exists]) : bool) ->
          (not x_2) && stlc_ty_arr1 tau tau1 && stlc_ty_arr2 tau tau2)
         : [%v: unit])
    [@under]
  in
  let _x10 = (v == tau2 : [%v: stlc_ty]) [@over] in

  let m = (fun ((m [@exists]) : int) -> num_arr _x10 m && v == m : [%v: int]) [@under] in
  (v >= 0 : [%v: int]) [@under]

let[@assert] rty2 =
  let num = (v >= 0 : [%v: int]) [@over] in
  let num_arr_tau = (v >= 0 : [%v: int]) [@over] in
  let tau = (num_arr v num_arr_tau : [%v: stlc_ty]) [@over] in

  let tau1 = (true : [%v: stlc_ty]) [@under] in
  let tau2 = (true : [%v: stlc_ty]) [@under] in
  let path_condition =
    ((num > 0)
    && (fun ((x_2 [@exists]) : bool) ->
          (not x_2) && stlc_ty_arr1 tau tau1 && stlc_ty_arr2 tau tau2)
         : [%v: unit])
    [@under]
  in
  let _x10 = (v == tau2 : [%v: stlc_ty]) [@over] in
  let m = (fun ((x [@exists]) : int) -> num_arr _x10 x && v == x : [%v: int]) [@under] in
  (v == m : [%v: int]) [@under]
