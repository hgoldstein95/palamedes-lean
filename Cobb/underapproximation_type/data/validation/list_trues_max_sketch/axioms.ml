let[@axiom] list_emp_no_hd (l : bool list) (x : bool) = (emp l)#==>(not (hd l x))

let[@axiom] list_emp_no_tl (l : bool list) (l1 : bool list) =
  (emp l)#==>(not (tl l l1))

let[@axiom] list_no_emp_exists_tl (l : bool list) ((l1 [@exists]) : bool list) =
  (not (emp l))#==>(tl l l1)

let[@axiom] list_no_emp_exists_hd (l : bool list) ((x [@exists]) : bool) =
  (not (emp l))#==>(hd l x)

let[@axiom] list_hd_no_emp (l : bool list) (x : bool) = (hd l x)#==>(not (emp l))

let[@axiom] list_tl_no_emp (l : bool list) (l1 : bool list) =
  (tl l l1)#==>(not (emp l))

(** len *)

let[@axiom] list_len_geq_0 (l : bool list) (n : int) = (len l n)#==>(n >= 0)
let[@axiom] list_len_0_emp (l : bool list) = (emp l)#==>(len l 0)

let[@axiom] list_emp_len_0 (l : bool list) (n : int) =
  (emp l && len l n)#==>(n == 0)

let[@axiom] list_positive_len_is_not_emp (l : bool list) (n : int) =
  (len l n && n > 0)#==>(not (emp l))

let[@axiom] list_tl_len_plus_1 (l : bool list) (l1 : bool list) (n : int) =
  (tl l l1)#==>(iff (len l1 n) (len l (n + 1)))

(* all_trues *)

let[@axiom] list_emp_is_trues (l : bool list) = (emp l)#==>(all_trues l)

let[@axiom] list_hd_is_true (l : bool list) (l1 : bool list) (x : bool) 
    =
  (tl l l1 && hd l x && all_trues l1 && x)#==>(all_trues l)

let[@axiom] list_is_trues_destruct (l : bool list) (l1 : bool list) (x : bool) =
  (tl l l1 && hd l x && all_trues l)#==>(all_trues l1 && x)

