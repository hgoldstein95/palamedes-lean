let rec gen_term (num : int) (gamma : stlc_tyctx) : stlc_term =
  (* term with no applications *)
  if sizecheck num then Err
  else if bool_gen () then (* application with n applications *)
    (* num_app_func and num_app_arg sum to num *)
    let (num_app_func : int) = int_range_inex_zero num in
    let (num_app_arg : int) = difference_inex num num_app_func in
    (* generate a term with `num_app_func` applications *)
    let (func : stlc_term) = gen_term num_app_func gamma in
    (* generate a term with `num_app_arg` applications *)
    let (arg : stlc_term) = gen_term num_app_arg gamma in
    Stlc_app (func, arg)
  else (* function with n applications *)
    let (tau : stlc_ty) = gen_type () in
    let (body : stlc_term) =
      gen_term (subs num) (Stlc_tyctx_cons (tau, gamma))
    in
    Stlc_abs (tau, body)

let[@assert] gen_term =
  let num = ((v >= 0 : [%v: int]) [@over]) in
  let gamma = ((true : [%v: stlc_tyctx]) [@over]) in
  ((scoping gamma v && num_app v num : [%v: stlc_term]) [@under])
