(** STLC *)

(* let[@axiom] stlc_num_arr_exists (tau : stlc_ty) ((n [@exists]) : int) =
   num_arr tau n *)

(* let[@axiom] stlc_num_arr_geq_0 (tau : stlc_ty) (n : int) =
  (num_arr tau n)#==>(n >= 0) *)

let[@axiom] stlc_num_arr_unique (tau : stlc_ty) (n1 : int) (n2 : int) =
  (num_arr tau n1 && num_arr tau n2)#==>(n1 == n2)

(* let[@axiom] stlc_is_abs_num_arr_ge_zero (v : stlc_term) (tau : stlc_ty) (gamma : stlc_tyctx) (n [@exists]: int) =
   (is_abs v && scoping gamma v tau && num_arr tau n ) #==> (n >= 1) *)

(* let[@axiom] stlc_is_abs_num_arr_ge_zero (v : stlc_term) (tau : stlc_ty)
     (gamma : stlc_tyctx) =
   (scoping gamma v tau && num_arr tau 0) #==> (not (is_abs v)) *)

let[@axiom] stlc_num_arr_arr_2_1 (tau : stlc_ty) (tau_body : stlc_ty) (m : int)
    =
  (stlc_ty_arr2 tau tau_body && num_arr tau_body m)#==>(num_arr tau (m + 1))

let[@axiom] stlc_num_arr_2_geq_1 (tau : stlc_ty) (tau_body : stlc_ty) (m : int)
    =
  (stlc_ty_arr2 tau tau_body && num_arr tau m)#==>(m >= 1)

let[@axiom] stlc_num_arr_arr_2_2 (tau : stlc_ty) (tau_body : stlc_ty) (m : int)
    =
  (stlc_ty_arr2 tau tau_body && num_arr tau (m + 1))#==>(num_arr tau_body m)

let[@axiom] stlc_num_arr_arr_1_1 (tau : stlc_ty) (ty : stlc_ty) =
  (stlc_ty_arr1 tau ty)#==>(num_arr ty 0)

(* let[@axiom] stlc_const_num_app_0 (v : stlc_term) =
   (is_const v) #==> (num_app v 0) *)

(* let[@axiom] stlc_var_num_app_0 (v : stlc_term) = (is_var v) #==> (num_app v 0) *)

(* let[@axiom] stlc_num_app_0_is_const_or_var (v : stlc_term) =
   (num_app v 0) #==> (is_const v || is_var v)
*)
let[@axiom] stlc_num_app_non_0_is_app_or_abs (v : stlc_term) (n : int) =
  (num_app v n && n > 0)#==>(is_app v || is_abs v)

(* let[@axiom] stlc_scoping_num_arr (tau : stlc_ty) ((n [@exists]) : int) =
   num_arr tau n *)

(* let[@axiom] stlc_term_4_cases (v : stlc_term) =
     is_const v || is_var v || is_abs v || is_app v

   let[@axiom] stlc_term_disjoint1 (v : stlc_term) = not (is_const v && is_var v)
   let[@axiom] stlc_term_disjoint2 (v : stlc_term) = not (is_const v && is_abs v)
   let[@axiom] stlc_term_disjoint3 (v : stlc_term) = not (is_const v && is_app v)
   let[@axiom] stlc_term_disjoint4 (v : stlc_term) = not (is_var v && is_abs v)
   let[@axiom] stlc_term_disjoint5 (v : stlc_term) = not (is_var v && is_app v)
   let[@axiom] stlc_term_disjoint6 (v : stlc_term) = not (is_abs v && is_app v)
*)

(* let[@axiom] stlc_is_const_disjoint1 (v : stlc_term) =
     (is_const v) #==> (not (is_var v))

   let[@axiom] stlc_is_const_disjoint2 (v : stlc_term) =
     (is_const v) #==> (not (is_abs v))

   let[@axiom] stlc_is_const_disjoint3 (v : stlc_term) =
     (is_const v) #==> (not (is_app v)) *)

(* let[@axiom] stlc_is_var_disjoint1 (v : stlc_term) =
   (is_var v) #==> (not (is_const v)) *)

(* let[@axiom] stlc_is_var_disjoint2 (v : stlc_term) =
   (is_var v) #==> (not (is_abs v)) *)

(* let[@axiom] stlc_is_var_disjoint3 (v : stlc_term) =
   (is_var v) #==> (not (is_app v)) *)

(* let[@axiom] stlc_is_abs_disjoint1 (v : stlc_term) =
     (is_abs v) #==> (not (is_const v))

   let[@axiom] stlc_is_abs_disjoint2 (v : stlc_term) =
     (is_abs v) #==> (not (is_var v)) *)

let[@axiom] stlc_is_abs_disjoint3 (v : stlc_term) =
  (is_abs v)#==>(not (is_app v))

(* let[@axiom] stlc_is_app_disjoint1 (v : stlc_term) =
     (is_app v) #==> (not (is_const v))

   let[@axiom] stlc_is_app_disjoint2 (v : stlc_term) =
     (is_app v) #==> (not (is_var v)) *)

let[@axiom] stlc_is_app_disjoint3 (v : stlc_term) =
  (is_app v)#==>(not (is_abs v))

(* let[@axiom] stlc_term_const_scoping_nat (gamma : stlc_tyctx) (v : stlc_term)
     (tau : stlc_ty) =
   (is_const v && scoping gamma v tau) #==> (stlc_ty_nat tau) *)

(* let[@axiom] stlc_id_is_var (v : stlc_term) (id : int) =
   (stlc_id v id) #==> (is_var v) *)

(* let[@axiom] stlc_const_is_const (v : stlc_term) (c : int) =
   (stlc_const v c) #==> (is_const v) *)

(* let[@axiom] stlc_term_destruct1 (term : stlc_term) ((c [@exists]) : int) =
   (is_const term) #==> (stlc_const term c) *)

(* let[@axiom] stlc_term_destruct2 (term : stlc_term) ((c [@exists]) : int) =
   (is_var term) #==> (stlc_id term c) *)

let[@axiom] stlc_term_destruct3_1 (term : stlc_term)
    ((t1 [@exists]) : stlc_term) =
  (is_app term)#==>(stlc_app1 term t1)

let[@axiom] stlc_term_destruct3_2 (term : stlc_term)
    ((t2 [@exists]) : stlc_term) =
  (is_app term)#==>(stlc_app2 term t2)

let[@axiom] stlc_term_destruct4_ty (term : stlc_term) ((ty [@exists]) : stlc_ty)
    =
  (is_abs term)#==>(stlc_abs_ty term ty)

let[@axiom] stlc_term_destruct4 (term : stlc_term)
    ((body [@exists]) : stlc_term) =
  (is_abs term)#==>(stlc_abs_body term body)

(* let[@axiom] stlc_is_abs_ty (term : stlc_term) (ty : stlc_ty) =
   (stlc_abs_ty term ty) #==> (is_abs term) *)

let[@axiom] stlc_is_abs_body (term : stlc_term) (body : stlc_term) =
  (stlc_abs_body term body)#==>(is_abs term)

let[@axiom] stlc_is_app_1 (term : stlc_term) (t1 : stlc_term) =
  (stlc_app1 term t1)#==>(is_app term)

(* let[@axiom] stlc_is_app_2 (term : stlc_term) (t2 : stlc_term) =
   (stlc_app2 term t2) #==> (is_app term) *)

(* let[@axiom] stlc_term_abs_scoping_arr_1 (gamma : stlc_tyctx) (v : stlc_term)
    (tau : stlc_ty) (ty : stlc_ty) =
  (stlc_abs_ty v ty && scoping gamma v tau)#==>(stlc_ty_arr1 tau ty) *)

(* let[@axiom] stlc_scoping_arr_term_abs_1 (gamma : stlc_tyctx) (v : stlc_term)
     (tau : stlc_ty) (ty : stlc_ty) =
   ((not (is_var v))
   && (not (is_app v))
   && stlc_ty_arr1 tau ty && scoping gamma v tau)
   #==> (stlc_abs_ty v ty) *)

(* let[@axiom] stlc_term_abs_scoping_arr_2 (gamma : stlc_tyctx) (v : stlc_term)
    (tau : stlc_ty) (body : stlc_term) ((body_ty [@exists]) : stlc_ty) =
  (stlc_abs_body v body && scoping gamma v tau)#==>(stlc_ty_arr2 tau body_ty) *)

(* let[@axiom] stlc_scoping_gamma_abd (gamma : stlc_tyctx) (gamma1 : stlc_tyctx)
      (v : stlc_term) (tau : stlc_ty) (tau1 : stlc_ty) (tau2 : stlc_ty)
      (body : stlc_term) =
    (stlc_ty_arr1 tau tau1 && stlc_ty_arr2 tau tau2 && stlc_abs_ty v tau1
   && stlc_abs_body v body && stlc_tyctx_hd gamma1 tau1
   && stlc_tyctx_tl gamma1 gamma && scoping gamma1 body tau2)
    #==> (scoping gamma v tau) *)

let[@axiom] stlc_scoping_app_tau_destruct (gamma : stlc_tyctx) (v : stlc_term)
    (t1 : stlc_term) (t2 : stlc_term) =
  (scoping gamma v && stlc_app1 v t1 && stlc_app2 v t2)#==>(scoping gamma t1
                                                          && scoping gamma t2)

let[@axiom] stlc_scoping_gamma_app (gamma : stlc_tyctx) (v : stlc_term)
    (func : stlc_term) (arg : stlc_term) =
  (stlc_app1 v func && stlc_app2 v arg && scoping gamma func
 && scoping gamma arg)#==>(scoping gamma v)

let[@axiom] stlc_tyctx_cons (ty : stlc_ty) (gamma : stlc_tyctx)
    ((v [@exists]) : stlc_tyctx) =
  stlc_tyctx_hd v ty && stlc_tyctx_tl v gamma

let[@axiom] stlc_num_app_exists (v : stlc_term) ((n [@exists]) : int) =
  num_app v n

let[@axiom] stlc_num_app_geq_0 (v : stlc_term) (n : int) =
  (num_app v n)#==>(0 <= n)

let[@axiom] stlc_num_app_unique (v : stlc_term) (n1 : int) (n2 : int) =
  (num_app v n1 && num_app v n2)#==>(n1 == n2)

(* let[@axiom] stlc_num_app_gt_0_is_abs_or_app (v : stlc_term)
     ((n [@exists]) : int) =
   (is_app v) #==> (num_app v n && n > 0) *)

let[@axiom] stlc_num_app_abs_body_eq (v : stlc_term) (body : stlc_term)
    (n : int) =
  (stlc_abs_body v body && num_app v n)#==>(num_app body n)

(* let[@axiom] stlc_num_app_abs_body_eq_rev (v : stlc_term) (body : stlc_term)
     (n : int) =
   (stlc_abs_body v body && num_app body n) #==> (num_app v n) *)

(* TODO: This is an axiom of concern *)
(* let[@axiom] stlc_num_app_app (v : stlc_term) (t1 : stlc_term) (t2 : stlc_term) =
   (stlc_app1 v t1 && stlc_app2 v t2)
   #==> (fun ((n [@exists]) : int) ((n1 [@exists]) : int) ((n2 [@exists]) : int)
     -> n1 + n2 + 1 == n && num_app t1 n1 && num_app t2 n2 && num_app v n) *)

(* let[@axiom] stlc_num_app_app (v : stlc_term) (t1 : stlc_term) (t2 : stlc_term)
     (n1 : int) (n2 : int) =
   (stlc_app1 v t1 && stlc_app2 v t2 && num_app t1 n1 && num_app t2 n2)
   #==> (num_app v (1 + n1 + n2)) *)

(* let[@axiom] stlc_num_app_app (v : stlc_term) (t1 : stlc_term) (t2 : stlc_term)
     (n1 : int) (n2 : int) =
   (stlc_app1 v t1 && stlc_app2 v t2 && num_app t1 n1 && num_app t2 n2)
   #==> (fun ((n [@exists]) : int) -> n == 1 + n1 + n2 && num_app v n) *)

(* let[@axiom] stlc_num_app_app_rev_1 (v : stlc_term) (t1 : stlc_term)
     (t2 : stlc_term) (n : int) =
   (stlc_app1 v t1 && stlc_app2 v t2 && num_app v n)
   #==> (fun ((m1 [@exists]) : int) ((m2 [@exists]) : int) ->
   num_app t1 m1 && num_app t2 m2 && m1 + m2 == n - 1) *)

(* let[@axiom] stlc_num_app_app_rev (v : stlc_term) (t1 : stlc_term)
      (t2 : stlc_term) (n : int) (m1 : int) (m2 : int) =
    (stlc_app1 v t1 && stlc_app2 v t2 && num_app t1 m1 && num_app t2 m2
   && num_app v n)
    #==> (1 + m1 + m2 == n) *)

let[@axiom] stlc_num_app_app_rev_2 (v : stlc_term) (t1 : stlc_term)
    (t2 : stlc_term) (n : int) (m1 : int) =
  (stlc_app1 v t1 && stlc_app2 v t2 && num_app t1 m1 && num_app v n)#==>(num_app
                                                                           t2
                                                                           (n
                                                                          - m1
                                                                          - 1))

(* let[@axiom] stlc_num_app_app_rev_bounds_1 (v : stlc_term) (t1 : stlc_term)
     (n : int) (m1 : int) =
   (stlc_app1 v t1 && num_app t1 m1 && num_app v n) #==> (m1 < n) *)

(* let[@axiom] stlc_num_app_app_rev_bounds_1 (v : stlc_term) (t1 : stlc_term)
     (n : int) =
   (stlc_app1 v t1 && num_app v n) #==> (fun ((m1 [@exists]) : int) ->
   m1 < n && num_app t1 m1) *)

(* let[@axiom] stlc_num_app_app_rev_bounds_2 (v : stlc_term) (t2 : stlc_term)
     (n : int) (m2 : int) =
   (stlc_app2 v t2 && num_app t2 m2 && num_app v n) #==> (m2 < n) *)

(* let[@axiom] stlc_num_app_app_rev_bounds_2 (v : stlc_term) (t2 : stlc_term)
     (n : int) =
   (stlc_app2 v t2 && num_app v n) #==> (fun ((m2 [@exists]) : int) ->
   m2 < n && num_app t2 m2) *)

let[@axiom] stlc_abd_scoping_rev (gamma : stlc_tyctx) (v : stlc_term)
    (body : stlc_term) (gamma1 : stlc_tyctx) =
  (scoping gamma v && stlc_abs_body v body && stlc_tyctx_tl gamma1 gamma)#==>(scoping
                                                                                gamma1
                                                                                body)

(* TODO: This is an axiom of concern *)
let[@axiom] stlc_abd_scoping (gamma : stlc_tyctx) (v : stlc_term)
    (body : stlc_term) (gamma1 : stlc_tyctx) =
  (scoping gamma1 body && stlc_abs_body v body && stlc_tyctx_tl gamma1 gamma)#==>
                                                                             (scoping
                                                                                gamma
                                                                                v)

(* let[@axiom] stlc_const_num_app_0 (v : stlc_term) (n : int) =
   (is_const v && num_app v n) #==> (n == 0) *)
