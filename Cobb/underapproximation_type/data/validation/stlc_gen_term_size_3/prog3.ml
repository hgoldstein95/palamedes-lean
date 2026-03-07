(* val get_num_arr : stlc_ty -> int
   val gen_type : unit -> stlc_ty
   val vars_with_type : stlc_tyctx -> stlc_ty -> stlc_term
   val gen_term_no_app : stlc_tyctx -> stlc_ty -> stlc_term *)

let rec gen_term_size (num_arr_tau : int) (num : int) (gamma : stlc_tyctx)
    (tau : stlc_ty) : stlc_term =
  if sizecheck num then gen_term_no_app gamma tau
  else if bool_gen () then
    let (arg_tau : stlc_ty) = gen_type () in
    if true then
      let (num_app_func : int) = int_range_inex_zero num in
      let (num_app_arg : int) = difference_inex num num_app_func in
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
    else Err
  else match tau with Stlc_ty_nat -> Err | Stlc_ty_arr (tau1, tau2) -> Err
(* let (idx10 : stlc_ty) = tau2 in
        let (idx60_0 : int) = get_num_arr idx10 in
        let (idx570 : int -> stlc_tyctx -> stlc_ty -> stlc_term) =
          gen_term_size idx60_0
        in
        let (idx1 : int) = num in
        let (idx571 : stlc_tyctx -> stlc_ty -> stlc_term) = idx570 idx1 in
        let (idx2 : stlc_tyctx) = gamma in
        let (idx9 : stlc_ty) = tau1 in
        let (idx62_20 : stlc_tyctx) = Stlc_tyctx_cons (idx9, idx2) in
        let (idx572 : stlc_ty -> stlc_term) = idx571 idx62_20 in
        let (idx573_1 : stlc_term) = idx572 idx10 in
        Stlc_abs (idx9, idx573_1) *)

let[@assert] gen_term_size =
  let num_arr_tau = ((v >= 0 : [%v: int]) [@over]) in
  let num = ((v >= 0 : [%v: int]) [@over]) in
  let gamma = ((true : [%v: stlc_tyctx]) [@over]) in
  let tau = ((num_arr v num_arr_tau : [%v: stlc_ty]) [@over]) in
  ((typing gamma v tau && num_app v num : [%v: stlc_term]) [@under])
