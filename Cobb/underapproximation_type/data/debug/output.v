let[@assert] stlc_term_destruct (term: stlc_term) = (exists c, stlc_const term c) \/ (exists id, stlc_id term id) \/ (exists t1 t2, stlc_app1 term t1 && stlc_app2 term t2) \/ (exists ty body, stlc_abs_ty term ty && stlc_abs_body term body)


let[@assert] stlc_typing_abs_tau_destruct (gamma: stlc_tyctx) (v: stlc_term) (tau: stlc_ty) (ty: stlc_ty)=
  typing gamma v tau #==> stlc_abs_ty v ty #==> stlc_ty_arr1 tau ty && exists body_ty, stlc_ty_arr2 tau body_ty


let[@assert] stlc_typing_app_tau_destruct (gamma: stlc_tyctx) (v: stlc_term) (tau: stlc_ty) (t1: stlc_term) (t2: stlc_term)=
  typing gamma v tau #==> stlc_app1 v t1 #==> stlc_app2 v t2 #==>
  exists func_ty arg_ty, stlc_ty_arr1 func_ty arg_ty && stlc_ty_arr2 func_ty tau && typing gamma t1 func_ty && typing gamma t2 arg_ty


let[@assert] stlc_dec_leq_0 (tau: stlc_ty) (dec: int) (num: int) = (dec_pair tau dec num #==> 0 <= dec)



let[@assert] stlc_dec_num_lt_0 (tau: stlc_ty) (dec: int) (num: int)= (dec_pair tau dec num #==> not (num = 0) #==> dec > 0)



let[@assert] stlc_dec_num_arr_body_lt (tau: stlc_ty) (dec: int) (num: int) (body_ty: stlc_ty)=
  (dec_pair tau dec num #==> stlc_ty_arr2 tau body_ty #==> exists dec1, dec_pair body_ty dec1 num && (dec1 < dec))


let[@assert] stlc_dec_num_lt_lt (tau: stlc_ty) (dec: int) (num: int) (tau1: stlc_ty) (m1: int) (tau2: stlc_ty) (m2: int)=
  (dec_pair tau dec num #==> m1 < num #==> m2 < num #==> exists dec1, dec_pair tau1 dec1 m1 && dec_pair tau2 dec1 m2 && (dec1 < dec))


let[@assert] stlc_tyctx_cons (ty: stlc_ty) (gamma: stlc_tyctx)= exists v, stlc_tyctx_hd v ty && stlc_tyctx_tl v gamma


let[@assert] stlc_num_app_geq_0  (v: stlc_term) (n: int) : num_app v n #==> (0 <= n)



let[@assert] stlc_num_app_abs_body_eq (v: stlc_term) (body: stlc_term) (n: int)= stlc_abs_body v body #==> num_app v n #==> num_app body n



let[@assert] stlc_num_app_abs_body_eq_rev (v: stlc_term) (body: stlc_term) (n: int)= stlc_abs_body v body #==> num_app body n #==> num_app v n



let[@assert] stlc_num_app_app_rev (v: stlc_term) (t1: stlc_term) (t2: stlc_term) (n: int)=
  (stlc_app1 v t1 #==> stlc_app2 v t2 #==> num_app v n #==> exists m1 m2, num_app t1 m1 && num_app t2 m2 && (m1 + m2 = n - 1))


let[@assert] stlc_abd_typing_rev (gamma: stlc_tyctx) (v: stlc_term) (tau: stlc_ty) (ty: stlc_ty) (body: stlc_term) (body_ty: stlc_ty) (gamma1: stlc_tyctx) :
  typing gamma v tau #==> stlc_abs_ty v ty #==> stlc_abs_body v body #==> stlc_tyctx_hd gamma1 ty #==> stlc_tyctx_tl gamma1 gamma #==> typing gamma1 body body_ty



let[@assert] stlc_id_is_var (v: stlc_term) (id: int) : stlc_id v id #==> is_var v



let[@assert] stlc_const_is_const (v: stlc_term) (c: int)= stlc_const v c #==> is_const v



let[@assert] stlc_const_typing_nat (gamma: stlc_tyctx) (v: stlc_term) (tau: stlc_ty) (c: int)= stlc_const v c #==> typing gamma v tau #==> stlc_ty_nat tau


