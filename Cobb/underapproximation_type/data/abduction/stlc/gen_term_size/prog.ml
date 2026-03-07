let rec gen_term_size (num_arr_tau : int) (num : int) (gamma : stlc_tyctx)
    (tau : stlc_ty) : stlc_term =
  if sizecheck num then gen_term_no_app gamma tau
  else if bool_gen () then
    let (arg_tau : stlc_ty) = gen_type () in
    let (num_app_func : int) = int_range_inex 0 num in
    let (num_app_arg : int) = int_range_inex 0 (num - num_app_func) in
    let (func_ty : stlc_ty) = Stlc_ty_arr (arg_tau, tau) in
    let (num_arr_func_ty : int) = get_num_arr func_ty in
    let (func : stlc_term) =
      gen_term_size num_arr_func_ty num_app_func gamma
        (Stlc_ty_arr (arg_tau, tau))
    in
    let (num_arr_arg_ty : int) = get_num_arr arg_tau in
    let (arg : stlc_term) =
      gen_term_size num_arr_arg_ty num_app_arg gamma arg_tau
    in
    Stlc_app (func, arg)
  else
    match tau with
    | Stlc_ty_nat -> Err
    | Stlc_ty_arr (tau1, tau2) ->
        let (num_arr_tau2 : int) = get_num_arr tau2 in
        let (body : stlc_term) =
          gen_term_size num_arr_tau2 num (Stlc_tyctx_cons (tau1, gamma)) tau2
        in
        Stlc_abs (tau1, body)

let[@assert] gen_term_size =
  let num_arr_tau = (v >= 0 : [%v: int]) [@over] in
  let num = (v >= 0 : [%v: int]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (num_arr v num_arr_tau : [%v: stlc_ty]) [@over] in
  (typing gamma v tau && num_app v num : [%v: stlc_term]) [@under]
