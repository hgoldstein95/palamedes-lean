(** int list *)

(** basic *)

let[@axiom] list_emp_no_hd (l : int list) (x : int) = (emp l)#==>(not (hd l x))

let[@axiom] list_emp_no_tl (l : int list) (l1 : int list) =
  (emp l)#==>(not (tl l l1))

let[@axiom] list_no_emp_exists_tl (l : int list) ((l1 [@exists]) : int list) =
  (not (emp l))#==>(tl l l1)

let[@axiom] list_no_emp_exists_hd (l : int list) ((x [@exists]) : int) =
  (not (emp l))#==>(hd l x)

let[@axiom] list_hd_no_emp (l : int list) (x : int) = (hd l x)#==>(not (emp l))

let[@axiom] list_tl_no_emp (l : int list) (l1 : int list) =
  (tl l l1)#==>(not (emp l))

(** len *)

(* let[@axiom] list_len_geq_0 (l : int list) (n : int) = (len l n)#==>(n >= 0) *)
let[@axiom] list_len_0_emp (l : int list) = (emp l)#==>(len l 0)

(* let[@axiom] list_emp_len_0 (l : int list) (n : int) =
  (emp l && len l n)#==>(n == 0) *)

let[@axiom] list_positive_len_is_not_emp (l : int list) (n : int) =
  (len l n && n > 0)#==>(not (emp l))

let[@axiom] list_is_not_emp_positive_len (l : int list) (n : int) =
  (len l n && not (emp l))#==>(n > 0)

let[@axiom] list_tl_len_plus_1 (l : int list) (l1 : int list) (n : int) =
  (tl l l1 && len l1 n)#==>(len l (n + 1))

let[@axiom] list_tl_len_plus_1 (l : int list) (l1 : int list) (n : int) =
  (tl l l1 && len l (n + 1))#==>(len l1 n)

(** incr_one *)

let[@axiom] list_emp_incr_one (l : int list) = (emp l)#==>(incr_one l)
let[@axiom] list_single_incr_one (l : int list) = (len l 1)#==>(incr_one l)

let[@axiom] list_tl_incr_one (l : int list) (l1 : int list) =
  (tl l l1 && incr_one l)#==>(incr_one l1)

let[@axiom] list_hd_incr_one (l : int list) (l1 : int list) (x : int) =
  (tl l l1 && incr_one l)#==>(emp l1 || ((hd l x) #==> hd l1 (x+1)))

let[@axiom] list_incr_one_hd (l : int list) (l1 : int list) (y : int) =

(tl l l1 && incr_one l1 && hd l y && hd l1 (y + 1))#==>(incr_one l)
