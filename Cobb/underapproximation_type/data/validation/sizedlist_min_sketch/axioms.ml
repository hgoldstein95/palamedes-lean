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

let[@axiom] list_len_geq_0 (l : int list) (n : int) = (len l n)#==>(n >= 0)
let[@axiom] list_len_0_emp (l : int list) = (emp l)#==>(len l 0)

let[@axiom] list_emp_len_0 (l : int list) (n : int) =
  (emp l && len l n)#==>(n == 0)

let[@axiom] list_positive_len_is_not_emp (l : int list) (n : int) =
  (len l n && n > 0)#==>(not (emp l))

let[@axiom] list_tl_len_plus_1 (l : int list) (l1 : int list) (n : int) =
  (tl l l1)#==>(iff (len l1 n) (len l (n + 1)))