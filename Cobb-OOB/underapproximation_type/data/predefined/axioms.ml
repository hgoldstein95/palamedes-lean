(** int list *)

(** basic *)

let[@axiom] list_emp_no_hd (l : int list) (x : int) =
  (emp l) #==> (not (hd l x))

let[@axiom] list_emp_no_tl (l : int list) (l1 : int list) =
  (emp l) #==> (not (tl l l1))

let[@axiom] list_no_emp_exists_tl (l : int list) ((l1 [@exists]) : int list) =
  (not (emp l)) #==> (tl l l1)

let[@axiom] list_no_emp_exists_hd (l : int list) ((x [@exists]) : int) =
  (not (emp l)) #==> (hd l x)

let[@axiom] list_hd_no_emp (l : int list) (x : int) =
  (hd l x) #==> (not (emp l))

let[@axiom] list_tl_no_emp (l : int list) (l1 : int list) =
  (tl l l1) #==> (not (emp l))

(** len *)

let[@axiom] list_len_geq_0 (l : int list) (n : int) = (len l n) #==> (n >= 0)
let[@axiom] list_len_0_emp (l : int list) = (emp l) #==> (len l 0)

let[@axiom] list_emp_len_0 (l : int list) (n : int) =
  (emp l && len l n) #==> (n == 0)

let[@axiom] list_positive_len_is_not_emp (l : int list) (n : int) =
  (len l n && n > 0) #==> (not (emp l))

let[@axiom] list_tl_len_plus_1 (l : int list) (l1 : int list) (n : int) =
  (tl l l1) #==> (iff (len l1 n) (len l (n + 1)))

(** list_mem *)

let[@axiom] list_hd_leq (l : int list) (x : int) (y : int) =
  (x <= y && hd l y) #==> (fun (u : int) -> (hd l u) #==> (x <= u))

let[@axiom] list_hd_is_mem (l : int list) (u : int) =
  (hd l u) #==> (list_mem l u)

let[@axiom] list_emp_no_mem (l : int list) (u : int) =
  (emp l) #==> (not (list_mem l u))

let[@axiom] list_tl_mem (l : int list) (l1 : int list) (u : int) =
  (tl l l1 && list_mem l1 u) #==> (list_mem l u)

let[@axiom] list_cons_mem (l : int list) (l1 : int list) (u : int) =
  (tl l l1 && list_mem l u) #==> (list_mem l1 u || hd l u)

(** sorted *)

let[@axiom] list_emp_sorted (l : int list) = (emp l) #==> (sorted l)
let[@axiom] list_single_sorted (l : int list) = (len l 1) #==> (sorted l)

let[@axiom] list_tl_sorted (l : int list) (l1 : int list) =
  (tl l l1 && sorted l) #==> (sorted l1)

let[@axiom] list_hd_sorted (l : int list) (l1 : int list) (x : int) (y : int) =
  (tl l l1 && sorted l) #==> (emp l1 || ((hd l1 y && hd l x) #==> (x <= y)))

let[@axiom] list_sorted_hd (l : int list) (l1 : int list) (x : int) (y : int) =
  (tl l l1 && sorted l1 && hd l y && hd l1 x && y <= x) #==> (sorted l)

(** unique *)

let[@axiom] list_emp_unique (l : int list) = (emp l) #==> (uniq l)

let[@axiom] list_tl_unique (l : int list) (l1 : int list) =
  (tl l l1 && uniq l) #==> (uniq l1)

let[@axiom] list_hd_unique (l : int list) (l1 : int list) (x : int) =
  (tl l l1 && uniq l && hd l x) #==> (not (list_mem l1 x))

let[@axiom] list_unique_hd_tl (l : int list) ((l1 [@exists]) : int list)
    ((x [@exists]) : int) =
  (uniq l && not (emp l)) #==> (hd l x && tl l l1 && not (list_mem l1 x))

let[@axiom] list_hd_tl_unique (l : int list) (l1 : int list) (x : int) =
  (tl l l1 && uniq l1 && hd l x && not (list_mem l1 x)) #==> (uniq l)

(** int tree *)

(** basic *)

let[@axiom] tree_leaf_no_root (l : int tree) (x : int) =
  (leaf l) #==> (not (root l x))

let[@axiom] tree_leaf_no_ch (l : int tree) (l1 : int tree) =
  (leaf l) #==> (not (lch l l1 || rch l l1))

let[@axiom] tree_no_leaf_exists_lch (l : int tree) ((l1 [@exists]) : int tree) =
  (not (leaf l)) #==> (lch l l1)

let[@axiom] tree_no_leaf_exists_rch (l : int tree) ((l2 [@exists]) : int tree) =
  (not (leaf l)) #==> (rch l l2)

let[@axiom] tree_no_leaf_exists_root (l : int tree) ((x [@exists]) : int) =
  (not (leaf l)) #==> (root l x)

let[@axiom] tree_root_no_leaf (l : int tree) (x : int) =
  (root l x) #==> (not (leaf l))

let[@axiom] tree_lch_no_leaf (l : int tree) (l1 : int tree) =
  (lch l l1) #==> (not (leaf l))

let[@axiom] tree_rch_no_leaf (l : int tree) (l1 : int tree) =
  (rch l l1) #==> (not (leaf l))

let[@axiom] tree_root_unique (l : int tree) (x : int) (y : int) =
  (root l x && root l y) #==> (x == y)

let[@axiom] tree_lch_unique (l : int tree) (l1 : int tree) (l2 : int tree) =
  (lch l l1 && lch l l2) #==> (l1 == l2)

let[@axiom] tree_rch_unique (l : int tree) (l1 : int tree) (l2 : int tree) =
  (rch l l1 && rch l l2) #==> (l1 == l2)

let[@axiom] tree_leaf_unique (l : int tree) (l1 : int tree) =
  (leaf l && leaf l1) #==> (l == l1)

let[@axiom] tree_leaf_or_root (l : int tree) =
  leaf l || fun ((x [@exists]) : int) -> root l x

(** depth *)

(* let[@axiom] tree_depth_geq_0 (l : int tree) (n : int) = (depth l n) #==> (n >= 0) *)

let[@axiom] tree_leaf_depth_0 (l : int tree) (n : int) =
  (leaf l && depth l n) #==> (n == 0)

let[@axiom] tree_leaf_depth_0_alt (l : int tree) (n : int) =
  (leaf l) #==> (depth l 0)

let[@axiom] tree_positive_depth_is_not_leaf (l : int tree) (n : int) =
  (depth l n && n > 0) #==> (not (leaf l))

(* let[@axiom] tree_depth_exists (l : int tree) ((n [@exists]) : int) = depth l n *)

(* let[@axiom] tree_ch_depth_ex (l : int tree) (l1 : int tree) (n : int)
     ((n1 [@exists]) : int) =
   ((lch l l1 || rch l l1) && depth l n) #==> (depth l1 n1) *)

let[@axiom] tree_lch_depth_minus_1 (l : int tree) (l1 : int tree) (n : int)
    (n1 : int) =
  (lch l l1 && depth l n && depth l1 n1) #==> (n1 <= n - 1)

let[@axiom] tree_rch_depth_minus_1 (l : int tree) (l1 : int tree) (n : int)
    (n1 : int) =
  (rch l l1 && depth l n && depth l1 n1) #==> (n1 <= n - 1)

let[@axiom] tree_lch_depth_minus_1 (l : int tree) (l1 : int tree) (n : int)
    (n1 : int) =
  (lch l l1 && depth l n && depth l1 n1) #==> (n1 <= n - 1)

let[@axiom] tree_lch_depth_minus_1 (l : int tree) (l1 : int tree) (n : int)
    (n1 : int) =
  (lch l l1 && depth l n && n1 <= n - 1 && n1 >= 0) #==> (depth l1 n1)

let[@axiom] tree_rch_depth_minus_1_alt (l : int tree) (l1 : int tree) (n : int)
    (n1 : int) =
  (rch l l1 && depth l n && n1 <= n - 1 && n1 >= 0) #==> (depth l1 n1)

(* let[@axiom] tree_depth_rch (l : int tree) (l1 : int tree) (n : int) (n1 : int) =
     (rch l l1 && depth l1 n1 && depth l n) #==> (n1 < n)

   let[@axiom] tree_depth_lch (l : int tree) (l1 : int tree) (n : int) (n1 : int) =
     (lch l l1 && depth l1 n1 && depth l n) #==> (n1 < n) *)

let[@axiom] tree_depth_0_is_leaf (l : int tree) (n : int) =
  (depth l n && n == 0) #==> (leaf l)

let[@axiom] tree_depth_0_is_leaf_alt (l : int tree) (n : int) =
  (depth l 0) #==> (leaf l)

(* let[@axiom] tree_depth_node (l : int tree) (l1 : int tree) (l2 : int tree)
     (n1 : int) (n2 : int) =
   (depth l1 n1 && depth l2 n2 && lch l l1 && rch l l2)
   #==> (((n1 > n2) #==> (depth l (n1 + 1)))
        && ((n2 >= n1) #==> (depth l (n2 + 1)))) *)

let[@axiom] tree_depth_node_lch (l : int tree) (l1 : int tree) (l2 : int tree)
    (n1 : int) (n2 : int) =
  (depth l1 n1 && depth l2 n2 && lch l l1 && rch l l2 && n1 >= n2)
  #==> (depth l (n1 + 1))

let[@axiom] tree_depth_node_rch (l : int tree) (l1 : int tree) (l2 : int tree)
    (n1 : int) (n2 : int) =
  (depth l1 n1 && depth l2 n2 && lch l l1 && rch l l2 && n2 >= n1)
  #==> (depth l (n2 + 1))

(** tree_mem *)

let[@axiom] tree_leaf_mem (l : int tree) (x : int) =
  (leaf l) #==> (not (tree_mem l x))

let[@axiom] tree_root_mem (l : int tree) (x : int) =
  (root l x) #==> (tree_mem l x)

let[@axiom] tree_mem_lch_mem (l : int tree) (l1 : int tree) (x : int) =
  (lch l l1 && tree_mem l1 x) #==> (tree_mem l x)

let[@axiom] tree_mem_rch_mem (l : int tree) (l1 : int tree) (x : int) =
  (rch l l1 && tree_mem l1 x) #==> (tree_mem l x)

let[@axiom] tree_mem_destruct (l : int tree) (l1 : int tree) (l2 : int tree)
    (x : int) =
  (tree_mem l x && lch l l1 && rch l l2)
  #==> (root l x || tree_mem l1 x || tree_mem l2 x)

(** bst *)

let[@axiom] tree_leaf_bst (l : int tree) = (leaf l) #==> (bst l)

let[@axiom] tree_bst_lch_bst (l : int tree) (l1 : int tree) =
  (lch l l1 && bst l) #==> (bst l1)

let[@axiom] tree_bst_rch_bst (l : int tree) (l1 : int tree) =
  (rch l l1 && bst l) #==> (bst l1)

(* let[@axiom] tree_bst_lch_mem_lt_root (l : int tree) (l1 : int tree) (x : int)
     (y : int) =
   (bst l && lch l l1 && root l x && tree_mem l1 y) #==> (y < x) *)

(* let[@axiom] tree_bst_lch_mem_lt_root_2 (l : int tree) (l1 : int tree)
     ((x [@exists]) : int) =
   (bst l && lch l l1 && fun (y : int) -> (tree_mem l y) #==> (x < y))
   #==> (fun (z : int) -> (tree_mem l1 z) #==> (x < z)) *)

(* let[@axiom] tree_bst_rch_mem_gt_root (l : int tree) (l1 : int tree) (x : int)
     (y : int) =
   (bst l && rch l l1 && root l x && tree_mem l1 y) #==> (x < y) *)

(* let[@axiom] tree_node_bst (l : int tree) (l1 : int tree) (l2 : int tree)
     (x : int) =
   (bst l1 && bst l2 && lch l l1 && rch l l2 && root l x
   && (fun (y1 : int) -> (tree_mem l1 y1) #==> (y1 < x))
   && fun (y2 : int) -> (tree_mem l2 y2) #==> (x < y2))
   #==> (bst l) *)

let[@axiom] tree_node_bst (l : int tree) (l1 : int tree) (l2 : int tree)
    (x : int) =
  (bst l1 && bst l2 && lch l l1 && rch l l2 && root l x
  && ((not (leaf l1)) #==> (upper_bound l1 x))
  && ((not (leaf l2)) #==> (lower_bound l2 x)))
  #==> (bst l)

(** Lower/upper bounds*)

let[@axiom] tree_lower_bound_base (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (bst l && root l x && lch l l1 && leaf l1 && y < x) #==> (lower_bound l y)

let[@axiom] tree_lower_bound_other (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (bst l && root l x && lch l l1 && (not (leaf l1)) && lower_bound l1 y && y < x)
  #==> (lower_bound l y)

let[@axiom] tree_lower_bound_destruct (l : int tree) (l1 : int tree) (x : int) =
  (lower_bound l x && lch l l1 && not (leaf l1)) #==> (lower_bound l1 x)

let[@axiom] tree_lower_bound_destruct_2 (l : int tree) (l1 : int tree) (x : int)
    =
  (bst l && root l x && rch l l1 && not (leaf l1)) #==> (lower_bound l1 x)

let[@axiom] tree_lower_bound_root (l : int tree) (x : int) (y : int) =
  (bst l && root l x && lower_bound l y) #==> (y < x)

let[@axiom] tree_upper_bound_base (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (bst l && root l x && rch l l1 && leaf l1 && y > x) #==> (upper_bound l y)

let[@axiom] tree_upper_bound_other (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (bst l && root l x && rch l l1 && (not (leaf l1)) && upper_bound l1 y && y > x)
  #==> (upper_bound l y)

let[@axiom] tree_upper_bound_destruct (l : int tree) (l1 : int tree) (x : int) =
  (upper_bound l x && rch l l1 && not (leaf l1)) #==> (upper_bound l1 x)

let[@axiom] tree_upper_bound_destruct_2 (l : int tree) (l1 : int tree) (x : int)
    =
  (bst l && root l x && lch l l1 && not (leaf l1)) #==> (upper_bound l1 x)

let[@axiom] tree_upper_bound_root (l : int tree) (x : int) (y : int) =
  (bst l && root l x && upper_bound l y) #==> (y > x)

let[@axiom] upper_lower_separate_by_atleast_one (l : int tree) (x : int)
    (y : int) =
  (bst l && upper_bound l x && lower_bound l y) #==> (y + 1 < x)

(** heap *)

let[@axiom] tree_heap_lch_heap (l : int tree) (l1 : int tree) =
  (lch l l1 && heap l) #==> (heap l1)

let[@axiom] tree_heap_rch_heap (l : int tree) (l1 : int tree) =
  (rch l l1 && heap l) #==> (heap l1)

let[@axiom] tree_heap_root_lt_lch_root (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (heap l && lch l l1 && root l x && root l1 y) #==> (y < x)

let[@axiom] tree_heap_root_rt_rch_root (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (heap l && rch l l1 && root l x && root l1 y) #==> (y < x)

(** complete *)

let[@axiom] tree_complete_leaf (l : int tree) = (leaf l) #==> (complete l)
let[@axiom] tree_depth_leaf (l : int tree) = (leaf l) #==> (depth l 0)

let[@axiom] tree_complete_lch_complete (l : int tree) (l1 : int tree) =
  (lch l l1 && complete l) #==> (complete l1)

let[@axiom] tree_complete_rch_complete (l : int tree) (l1 : int tree) =
  (rch l l1 && complete l) #==> (complete l1)

let[@axiom] tree_complete_node (l : int tree) (l1 : int tree) (l2 : int tree)
    (n : int) =
  (complete l1 && complete l2 && depth l1 n && depth l2 n && lch l l1
 && rch l l2)
  #==> (complete l)

let[@axiom] tree_complete_lch_depth_minus_1 (l : int tree) (l1 : int tree)
    (n : int) =
  (lch l l1 && complete l && depth l n) #==> (depth l1 (n - 1))

let[@axiom] tree_complete_rch_depth_minus_1 (l : int tree) (l1 : int tree)
    (n : int) =
  (rch l l1 && complete l && depth l n) #==> (depth l1 (n - 1))

(** int stream *)

let[@axiom] stream_stream_emp_no_stream_hd (l : int stream) (x : int) =
  (stream_emp l) #==> (not (stream_hd l x))

let[@axiom] stream_stream_emp_no_stream_tl (l : int stream) (l1 : int stream) =
  (stream_emp l) #==> (not (stream_tl l l1))

let[@axiom] stream_no_stream_emp_exists_stream_tl (l : int stream)
    ((l1 [@exists]) : int stream) =
  (not (stream_emp l)) #==> (stream_tl l l1)

let[@axiom] stream_no_stream_emp_exists_stream_hd (l : int stream)
    ((x [@exists]) : int) =
  (not (stream_emp l)) #==> (stream_hd l x)

let[@axiom] stream_stream_hd_no_stream_emp (l : int stream) (x : int) =
  (stream_hd l x) #==> (not (stream_emp l))

let[@axiom] stream_stream_tl_no_stream_emp (l : int stream) (l1 : int stream) =
  (stream_tl l l1) #==> (not (stream_emp l))

(** stream_len *)

let[@axiom] stream_stream_len_geq_0 (l : int stream) (n : int) =
  (stream_len l n) #==> (n >= 0)

let[@axiom] stream_stream_len_leq_0_emp_stream (l : int stream) (n : int) =
  (stream_len l n && n <= 0) #==> (stream_emp l)

let[@axiom] stream_stream_emp_stream_len_0 (l : int stream) (n : int) =
  (stream_emp l && stream_len l n) #==> (n == 0)

let[@axiom] stream_positive_stream_len_is_not_stream_emp (l : int stream)
    (n : int) =
  (stream_len l n && n > 0) #==> (not (stream_emp l))

let[@axiom] stream_stream_tl_stream_len_plus_1 (l : int stream)
    (l1 : int stream) (n : int) =
  (stream_tl l l1) #==> (iff (stream_len l1 n) (stream_len l (n + 1)))

(** bankersq *)

let[@axiom] bankersq_destruct (q : int bankersq) ((lenf [@exists]) : int)
    ((f [@exists]) : int stream) ((lenr [@exists]) : int)
    ((r [@exists]) : int stream) =
  lenr >= 0 && lenr <= lenf && stream_len f lenf && stream_len r lenr
  && bankersq1 q lenf && bankersq2 q f && bankersq3 q lenr && bankersq4 q r

let[@axiom] bankersq1_len (q : int bankersq) (n : int) (m : int) =
  (bankersq1 q n && bankersq_len q m) #==> (n == m)

(** batchedq *)

let[@axiom] batchedq_destruct (q : int batchedq) ((lenf [@exists]) : int)
    ((f [@exists]) : int list) ((lenr [@exists]) : int)
    ((r [@exists]) : int list) =
  batchedq1 q f && batchedq2 q r && lenr >= 0 && len f lenf && len r lenr

let[@axiom] batchedq_f_geq_r (q : int batchedq) (lenf : int) (f : int list)
    (lenr : int) (r : int list) =
  (batchedq1 q f && batchedq2 q r && len f lenf && len r lenr)
  #==> (lenf >= lenr)

let[@axiom] batchedq1_len (q : int batchedq) (f : int list) (n : int) =
  (batchedq1 q f) #==> (iff (batchedq_len q n) (len f n))

(** int leafisthp *)

(** basic *)

let[@axiom] leftisthp_leftisthp_leaf_no_leftisthp_root (l : int leftisthp)
    (x : int) =
  (leftisthp_leaf l) #==> (not (leftisthp_root l x))

let[@axiom] leftisthp_leftisthp_leaf_no_ch (l : int leftisthp)
    (l1 : int leftisthp) =
  (leftisthp_leaf l) #==> (not (leftisthp_lch l l1 || leftisthp_rch l l1))

let[@axiom] leftisthp_no_leftisthp_leaf_exists_ch (l : int leftisthp)
    ((l1 [@exists]) : int leftisthp) ((l2 [@exists]) : int leftisthp)
    ((r [@exists]) : int) =
  (not (leftisthp_leaf l))
  #==> (leftisthp_lch l l1 && leftisthp_rch l l2 && leftisthp_rank l r
       && leftisthp_depth l2 (r - 1)
       && r > 0)

let[@axiom] leftisthp_no_leftisthp_leaf_exists_leftisthp_root
    (l : int leftisthp) ((x [@exists]) : int) =
  (not (leftisthp_leaf l)) #==> (leftisthp_root l x)

let[@axiom] leftisthp_leftisthp_root_no_leftisthp_leaf (l : int leftisthp)
    (x : int) =
  (leftisthp_root l x) #==> (not (leftisthp_leaf l))

let[@axiom] leftisthp_ch_no_leftisthp_leaf (l : int leftisthp)
    (l1 : int leftisthp) =
  (leftisthp_lch l l1 || leftisthp_rch l l1) #==> (not (leftisthp_leaf l))

(** leftisthp_depth *)

let[@axiom] leftisthp_leftisthp_depth_0_leftisthp_leaf (l : int leftisthp) =
  (leftisthp_depth l 0) #==> (leftisthp_leaf l)

let[@axiom] leftisthp_right_depth_leq_depth (l : int leftisthp) (n : int)
    (r : int) =
  (leftisthp_depth l n && leftisthp_rank l r) #==> (r <= n)

let[@axiom] leftisthp_right_depth_leq_depth (l : int leftisthp)
    (l1 : int leftisthp) (r : int) =
  (leftisthp_rch l l1 && leftisthp_rank l r) #==> (leftisthp_depth l1 (r - 1))

let[@axiom] leftisthp_leftisthp_depth_geq_0 (l : int leftisthp) (n : int) =
  (leftisthp_depth l n) #==> (n >= 0)

let[@axiom] leftisthp_leftisthp_leaf_leftisthp_depth_0 (l : int leftisthp)
    (n : int) =
  (leftisthp_leaf l && leftisthp_depth l n) #==> (n == 0)

let[@axiom] leftisthp_positive_leftisthp_depth_is_not_leftisthp_leaf
    (l : int leftisthp) (n : int) =
  (leftisthp_depth l n && not (n == 0)) #==> (not (leftisthp_leaf l))

let[@axiom] leftisthp_leftisthp_depth_ch_leftisthp_depth_minus_1
    (tr : int leftisthp) (tr1 : int leftisthp) (n : int) =
  (leftisthp_lch tr tr1)
  #==> (iff (leftisthp_depth tr (n + 1)) (leftisthp_depth tr1 n))

(** int rbtree *)

(** basic *)

let[@axiom] rbtree_leaf_is_leaf (l : int rbtree) (l2 : int rbtree) =
  (rb_leaf l && rb_leaf l2) #==> (l == l2)

let[@axiom] rbtree_rb_leaf_no_rb_root (l : int rbtree) (x : int) =
  (rb_leaf l) #==> (not (rb_root l x))

let[@axiom] rbtree_rb_leaf_no_rb_root_color (l : int rbtree) (x : bool) =
  (rb_leaf l) #==> (not (rb_root_color l x))

let[@axiom] rbtree_rb_leaf_no_ch (l : int rbtree) (l1 : int rbtree) =
  (rb_leaf l) #==> (not (rb_lch l l1 || rb_rch l l1))

let[@axiom] rbtree_rb_leaf_no_red_red (l : int rbtree) =
  (rb_leaf l) #==> (no_red_red l)

let[@axiom] rbtree_no_rb_leaf_exists_ch (l : int rbtree)
    ((l1 [@exists]) : int rbtree) ((l2 [@exists]) : int rbtree) =
  (not (rb_leaf l)) #==> (rb_lch l l1 && rb_rch l l2)

let[@axiom] rbtree_no_rb_leaf_exists_rb_root (l : int rbtree)
    ((x [@exists]) : int) =
  (not (rb_leaf l)) #==> (rb_root l x)

let[@axiom] rbtree_no_rb_leaf_exists_rb_root_color (l : int rbtree)
    ((x [@exists]) : bool) =
  (not (rb_leaf l)) #==> (rb_root_color l x)

let[@axiom] rbtree_rb_root_no_rb_leaf (l : int rbtree) (x : int) =
  (rb_root l x) #==> (not (rb_leaf l))

let[@axiom] rbtree_rb_root_color_no_rb_leaf (l : int rbtree) (x : bool) =
  (rb_root_color l x) #==> (not (rb_leaf l))

let[@axiom] rbtree_ch_no_rb_leaf (l : int rbtree) (l1 : int rbtree) =
  (rb_lch l l1 || rb_rch l l1) #==> (not (rb_leaf l))

(* let[@axiom] rbtree_root_lch_rch (l : int rbtree) (x : int)
     ((l1 [@exists]) : int rbtree) ((l2 [@exists]) : int rbtree) =
   (rb_root l x) #==> (rb_lch l l1 && rb_rch l l2) *)

(* let[@axiom] rbtree_root_lch (l : int rbtree) (x : int)
       ((l1 [@exists]) : int rbtree) =
     (rb_root l x) #==> (rb_lch l l1)

   let[@axiom] rbtree_root_rch (l : int rbtree) (x : int)
       ((l1 [@exists]) : int rbtree) =
     (rb_root l x) #==> (rb_rch l l1) *)

(** num_black *)

let[@axiom] rbtree_num_black_0_rb_leaf (l : int rbtree) =
  (num_black l 0 && not (rb_root_color l true)) #==> (rb_leaf l)

let[@axiom] rbtree_num_black_geq_0 (l : int rbtree) (n : int) =
  (num_black l n) #==> (n >= 0)

let[@axiom] rbtree_rb_leaf_num_black_0 (l : int rbtree) (n : int) =
  (rb_leaf l && num_black l n) #==> (n == 0)

let[@axiom] rbtree_rb_leaf_num_black_0_second (l : int rbtree) =
  (rb_leaf l) #==> (num_black l 0)

let[@axiom] rbtree_positive_num_black_is_not_rb_leaf (l : int rbtree) (n : int)
    =
  (num_black l n && n > 0) #==> (not (rb_leaf l))

let[@axiom] num_black_root_black_lt_minus_1 (v : int rbtree) (lt : int rbtree)
    (h : int) =
  (rb_root_color v false && num_black v h && rb_lch v lt)
  #==> (num_black lt (h - 1))

let[@axiom] num_black_root_black_rt_minus_1 (v : int rbtree) (rt : int rbtree)
    (h : int) =
  (rb_root_color v false && num_black v h && rb_rch v rt)
  #==> (num_black rt (h - 1))

let[@axiom] num_black_root_red_lt_same (v : int rbtree) (lt : int rbtree)
    (h : int) =
  (rb_root_color v true && num_black v h && rb_lch v lt) #==> (num_black lt h)

let[@axiom] num_black_root_red_rt_same (v : int rbtree) (rt : int rbtree)
    (h : int) =
  (rb_root_color v true && num_black v h && rb_rch v rt) #==> (num_black rt h)

let[@axiom] num_black_root_from_lt_rt (v : int rbtree) (lt : int rbtree)
    (rt : int rbtree) (h : int) =
  (num_black lt h && num_black rt h && rb_rch v rt && rb_lch v lt
 && rb_root_color v true)
  #==> (num_black v h)

let[@axiom] num_black_root_from_lt_rt_plus_1 (v : int rbtree) (lt : int rbtree)
    (rt : int rbtree) (h : int) =
  (num_black lt h && num_black rt h && rb_rch v rt && rb_lch v lt
 && rb_root_color v false)
  #==> (num_black v (h + 1))

let[@axiom] num_black_root_black_0_lt_leaf (v : int rbtree) (lt : int rbtree) =
  (no_red_red v && num_black v 0 && rb_lch v lt) #==> (rb_leaf lt)

let[@axiom] num_black_root_black_0_rt_leaf (v : int rbtree) (rt : int rbtree) =
  (no_red_red v && num_black v 0 && rb_rch v rt) #==> (rb_leaf rt)

(* let[@axiom] num_black_root_red (v : int_rbtree) =
   (num_black v 0 && rb_root_color v true) #==> *)

let[@axiom] num_black_root_black_0_rt_red (v : int rbtree) (rt : int rbtree) =
  (num_black v 0 && rb_rch v rt) #==> (rb_root_color v true)

let[@axiom] no_red_red_lt (v : int rbtree) (lt : int rbtree) =
  (no_red_red v && rb_lch v lt) #==> (no_red_red lt)

let[@axiom] no_red_red_rt (v : int rbtree) (rt : int rbtree) =
  (no_red_red v && rb_rch v rt) #==> (no_red_red rt)

let[@axiom] no_red_red_root_red_lt_not_red (v : int rbtree) (lt : int rbtree) =
  (no_red_red v && rb_lch v lt && rb_root_color v true)
  #==> (not (rb_root_color lt true))

let[@axiom] no_red_red_root_red_rt_not_red (v : int rbtree) (rt : int rbtree) =
  (no_red_red v && rb_rch v rt && rb_root_color v true)
  #==> (not (rb_root_color rt true))

let[@axiom] no_red_red_given_lt_rt_black_root (v : int rbtree) (lt : int rbtree)
    (rt : int rbtree) =
  (no_red_red lt && no_red_red rt && rb_lch v lt && rb_rch v rt
 && rb_root_color v false)
  #==> (no_red_red v)

let[@axiom] no_red_red_given_lt_rt_red_root (v : int rbtree) (lt : int rbtree)
    (rt : int rbtree) =
  (no_red_red lt && no_red_red rt && rb_lch v lt && rb_rch v rt
  && (not (rb_root_color lt true))
  && (not (rb_root_color rt true))
  && rb_root_color v true)
  #==> (no_red_red v)

let[@axiom] black_lt_black_num_black_gt_1 (v : int rbtree) (lt : int rbtree)
    (h : int) =
  (num_black v h && rb_lch v lt && rb_root_color v false
 && rb_root_color lt false)
  #==> (h > 1)

let[@axiom] black_rt_black_num_black_gt_1 (v : int rbtree) (rt : int rbtree)
    (h : int) =
  (num_black v h && rb_rch v rt && rb_root_color v false
 && rb_root_color rt false)
  #==> (h > 1)

(** STLC *)

(* let[@axiom] stlc_num_arr_exists (tau : stlc_ty) ((n [@exists]) : int) =
  num_arr tau n *)

(* let[@axiom] stlc_num_arr_geq_0 (tau : stlc_ty) (n : int) =
  (num_arr tau n) #==> (n >= 0) *)

let[@axiom] stlc_num_arr_unique (tau : stlc_ty) (n1 : int) (n2 : int) =
  (num_arr tau n1 && num_arr tau n2) #==> (n1 == n2)

(* let[@axiom] stlc_is_abs_num_arr_ge_zero (v : stlc_term) (tau : stlc_ty) (gamma : stlc_tyctx) (n [@exists]: int) =
   (is_abs v && typing gamma v tau && num_arr tau n ) #==> (n >= 1) *)

(* let[@axiom] stlc_is_abs_num_arr_ge_zero (v : stlc_term) (tau : stlc_ty)
     (gamma : stlc_tyctx) =
   (typing gamma v tau && num_arr tau 0) #==> (not (is_abs v)) *)

let[@axiom] stlc_num_arr_arr_2_1 (tau : stlc_ty) (tau_body : stlc_ty) (m : int)
    =
  (stlc_ty_arr2 tau tau_body && num_arr tau_body m) #==> (num_arr tau (m + 1))

let[@axiom] stlc_num_arr_2_geq_1 (tau : stlc_ty) (tau_body : stlc_ty) (m : int)
    =
  (stlc_ty_arr2 tau tau_body && num_arr tau m) #==> (m >= 1)

let[@axiom] stlc_num_arr_arr_2_2 (tau : stlc_ty) (tau_body : stlc_ty) (m : int)
    =
  (stlc_ty_arr2 tau tau_body && num_arr tau (m + 1)) #==> (num_arr tau_body m)

let[@axiom] stlc_num_arr_arr_1_1 (tau : stlc_ty) (ty : stlc_ty) =
  (stlc_ty_arr1 tau ty) #==> (num_arr ty 0)

(* let[@axiom] stlc_const_num_app_0 (v : stlc_term) =
  (is_const v) #==> (num_app v 0) *)

(* let[@axiom] stlc_var_num_app_0 (v : stlc_term) = (is_var v) #==> (num_app v 0) *)

(* let[@axiom] stlc_num_app_0_is_const_or_var (v : stlc_term) =
  (num_app v 0) #==> (is_const v || is_var v)
 *)
let[@axiom] stlc_num_app_non_0_is_app_or_abs (v : stlc_term) (n : int) =
  (num_app v n && n > 0) #==> (is_app v || is_abs v)

(* let[@axiom] stlc_typing_num_arr (tau : stlc_ty) ((n [@exists]) : int) =
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
  (is_abs v) #==> (not (is_app v))

(* let[@axiom] stlc_is_app_disjoint1 (v : stlc_term) =
  (is_app v) #==> (not (is_const v))

let[@axiom] stlc_is_app_disjoint2 (v : stlc_term) =
  (is_app v) #==> (not (is_var v)) *)

let[@axiom] stlc_is_app_disjoint3 (v : stlc_term) =
  (is_app v) #==> (not (is_abs v))

(* let[@axiom] stlc_term_const_typing_nat (gamma : stlc_tyctx) (v : stlc_term)
    (tau : stlc_ty) =
  (is_const v && typing gamma v tau) #==> (stlc_ty_nat tau) *)

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
  (is_app term) #==> (stlc_app1 term t1)

let[@axiom] stlc_term_destruct3_2 (term : stlc_term)
    ((t2 [@exists]) : stlc_term) =
  (is_app term) #==> (stlc_app2 term t2)

let[@axiom] stlc_term_destruct4_ty (term : stlc_term) ((ty [@exists]) : stlc_ty)
    =
  (is_abs term) #==> (stlc_abs_ty term ty)

let[@axiom] stlc_term_destruct4 (term : stlc_term)
    ((body [@exists]) : stlc_term) =
  (is_abs term) #==> (stlc_abs_body term body)

(* let[@axiom] stlc_is_abs_ty (term : stlc_term) (ty : stlc_ty) =
  (stlc_abs_ty term ty) #==> (is_abs term) *)

let[@axiom] stlc_is_abs_body (term : stlc_term) (body : stlc_term) =
  (stlc_abs_body term body) #==> (is_abs term)

let[@axiom] stlc_is_app_1 (term : stlc_term) (t1 : stlc_term) =
  (stlc_app1 term t1) #==> (is_app term)

(* let[@axiom] stlc_is_app_2 (term : stlc_term) (t2 : stlc_term) =
  (stlc_app2 term t2) #==> (is_app term) *)

let[@axiom] stlc_term_abs_typing_arr_1 (gamma : stlc_tyctx) (v : stlc_term)
    (tau : stlc_ty) (ty : stlc_ty) =
  (stlc_abs_ty v ty && typing gamma v tau) #==> (stlc_ty_arr1 tau ty)

(* let[@axiom] stlc_typing_arr_term_abs_1 (gamma : stlc_tyctx) (v : stlc_term)
    (tau : stlc_ty) (ty : stlc_ty) =
  ((not (is_var v))
  && (not (is_app v))
  && stlc_ty_arr1 tau ty && typing gamma v tau)
  #==> (stlc_abs_ty v ty) *)

let[@axiom] stlc_term_abs_typing_arr_2 (gamma : stlc_tyctx) (v : stlc_term)
    (tau : stlc_ty) (body : stlc_term) ((body_ty [@exists]) : stlc_ty) =
  (stlc_abs_body v body && typing gamma v tau) #==> (stlc_ty_arr2 tau body_ty)

(* let[@axiom] stlc_typing_gamma_abd (gamma : stlc_tyctx) (gamma1 : stlc_tyctx)
    (v : stlc_term) (tau : stlc_ty) (tau1 : stlc_ty) (tau2 : stlc_ty)
    (body : stlc_term) =
  (stlc_ty_arr1 tau tau1 && stlc_ty_arr2 tau tau2 && stlc_abs_ty v tau1
 && stlc_abs_body v body && stlc_tyctx_hd gamma1 tau1
 && stlc_tyctx_tl gamma1 gamma && typing gamma1 body tau2)
  #==> (typing gamma v tau) *)

let[@axiom] stlc_typing_app_tau_destruct (gamma : stlc_tyctx) (v : stlc_term)
    (tau : stlc_ty) (t1 : stlc_term) (t2 : stlc_term) =
  (typing gamma v tau && stlc_app1 v t1 && stlc_app2 v t2)
  #==> (fun ((func_ty [@exists]) : stlc_ty) ((arg_ty [@exists]) : stlc_ty) ->
  stlc_ty_arr1 func_ty arg_ty
  && stlc_ty_arr2 func_ty tau && typing gamma t1 func_ty
  && typing gamma t2 arg_ty)

let[@axiom] stlc_typing_gamma_app (gamma : stlc_tyctx) (v : stlc_term)
    (tau : stlc_ty) (func : stlc_term) (arg : stlc_term) (func_ty : stlc_ty)
    (arg_ty : stlc_ty) =
  (stlc_app1 v func && stlc_app2 v arg
  && stlc_ty_arr1 func_ty arg_ty
  && stlc_ty_arr2 func_ty tau && typing gamma func func_ty
  && typing gamma arg arg_ty)
  #==> (typing gamma v tau)

let[@axiom] stlc_tyctx_cons (ty : stlc_ty) (gamma : stlc_tyctx)
    ((v [@exists]) : stlc_tyctx) =
  stlc_tyctx_hd v ty && stlc_tyctx_tl v gamma

let[@axiom] stlc_num_app_exists (v : stlc_term) ((n [@exists]) : int) =
   num_app v n

let[@axiom] stlc_num_app_geq_0 (v : stlc_term) (n : int) =
  (num_app v n) #==> (0 <= n)

let[@axiom] stlc_num_app_unique (v : stlc_term) (n1 : int) (n2 : int) =
  (num_app v n1 && num_app v n2) #==> (n1 == n2)

(* let[@axiom] stlc_num_app_gt_0_is_abs_or_app (v : stlc_term)
    ((n [@exists]) : int) =
  (is_app v) #==> (num_app v n && n > 0) *)

let[@axiom] stlc_num_app_abs_body_eq (v : stlc_term) (body : stlc_term)
    (n : int) =
  (stlc_abs_body v body && num_app v n) #==> (num_app body n)

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
  (stlc_app1 v t1 && stlc_app2 v t2 && num_app t1 m1 && num_app v n)
  #==> (num_app t2 (n - m1 - 1))

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

let[@axiom] stlc_abd_typing_rev (gamma : stlc_tyctx) (v : stlc_term)
    (tau : stlc_ty) (ty : stlc_ty) (body : stlc_term) (body_ty : stlc_ty)
    (gamma1 : stlc_tyctx) =
  (typing gamma v tau && stlc_abs_ty v ty && stlc_abs_body v body
 && stlc_tyctx_hd gamma1 ty && stlc_tyctx_tl gamma1 gamma)
  #==> (typing gamma1 body body_ty)

(* TODO: This is an axiom of concern *)
let[@axiom] stlc_abd_typing (gamma : stlc_tyctx) (v : stlc_term) (tau : stlc_ty)
    (ty : stlc_ty) (body : stlc_term) (body_ty : stlc_ty) (gamma1 : stlc_tyctx)
    =
  (typing gamma1 body body_ty && stlc_abs_ty v ty && stlc_abs_body v body
 && stlc_ty_arr1 tau ty && stlc_ty_arr2 tau body_ty && stlc_tyctx_hd gamma1 ty
 && stlc_tyctx_tl gamma1 gamma)
  #==> (typing gamma v tau)

let[@axiom] stlc_const_typing_nat (gamma : stlc_tyctx) (v : stlc_term)
    (tau : stlc_ty) =
  (is_const v && typing gamma v tau) #==> (stlc_ty_nat tau)

(* let[@axiom] stlc_const_num_app_0 (v : stlc_term) (n : int) =
   (is_const v && num_app v n) #==> (n == 0) *)

(** For synthesis *)

let[@axiom] root_color_single (v : int rbtree) =
  not (rb_root_color v false && rb_root_color v true)

let[@axiom] leaf_no_root_color (v : int rbtree) =
  (rb_leaf v) #==> ((not (rb_root_color v false)) && not (rb_root_color v true))
