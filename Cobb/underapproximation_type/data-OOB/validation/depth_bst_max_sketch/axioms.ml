(** int tree *)

(** basic *)

let[@axiom] tree_leaf_no_root (l : int tree) (x : int) =
  (leaf l)#==>(not (root l x))

let[@axiom] tree_leaf_or_root (l : int tree) ((x [@exists]) : int) =
  leaf l || root l x

let[@axiom] tree_leaf_root_discriminate (l : int tree) (x : int) =
  not (leaf l && root l x)

let[@axiom] tree_no_root_leaf (l : int tree) ((x [@exists]) : int) =
  (not (root l x))#==>(leaf l)

let[@axiom] tree_root_no_leaf (l : int tree) (x : int) =
  (root l x)#==>(not (leaf l))

(* let[@axiom] tree_leaf_no_ch (l : int tree) (l1 : int tree) =
  (leaf l)#==>(not (lch l l1 || rch l l1)) *)

let[@axiom] tree_no_leaf_exists_lch (l : int tree) ((l1 [@exists]) : int tree) =
  (not (leaf l))#==>(lch l l1)

(* let[@axiom] tree_leaf_exists_no_lch (l : int tree) (l1 : int tree) =
  (leaf l)#==>(not (lch l l1))

let[@axiom] tree_leaf_exists_no_rch (l : int tree) (l1 : int tree) =
  (leaf l)#==>(not (rch l l1))
 *)

let[@axiom] tree_no_leaf_exists_rch (l : int tree) ((l2 [@exists]) : int tree) =
  (not (leaf l))#==>(rch l l2)

(* let[@axiom] tree_no_leaf_exists_root (l : int tree) ((x [@exists]) : int) =
  (not (leaf l))#==>(root l x) *)

(* let[@axiom] tree_lch_no_leaf (l : int tree) (l1 : int tree) =
  (lch l l1)#==>(not (leaf l)) *)

(* let[@axiom] tree_rch_no_leaf (l : int tree) (l1 : int tree) =
  (rch l l1)#==>(not (leaf l)) *)

let[@axiom] tree_root_unique (l : int tree) (x : int) (y : int) =
  (root l x && root l y)#==>(x == y)

let[@axiom] tree_lch_unique (l : int tree) (l1 : int tree) (l2 : int tree) =
  (lch l l1 && lch l l2)#==>(l1 == l2)

let[@axiom] tree_rch_unique (l : int tree) (l1 : int tree) (l2 : int tree) =
  (rch l l1 && rch l l2)#==>(l1 == l2)

let[@axiom] tree_leaf_unique (l : int tree) (l1 : int tree) =
  (leaf l && leaf l1)#==>(l == l1)

(* let[@axiom] tree_leaf_or_root (l : int tree) =
  leaf l || (fun ((x [@exists]) : int) -> root l x)
 *)

(** depth *)

(* let[@axiom] tree_depth_geq_0 (l : int tree) (n : int) = (depth l n)#==>(n >= 0) *)

let[@axiom] tree_leaf_depth_0 (l : int tree) (n : int) =
  (leaf l && depth l n)#==>(n == 0)

let[@axiom] tree_leaf_depth_0_disjoint (l : int tree) ((n [@exists]) : int) =
  (depth l n && n == 0 && leaf l) || (depth l n && n > 0 && not (leaf l))

let[@axiom] tree_leaf_depth_0_alt (l : int tree) (n : int) =
  (leaf l)#==>(depth l 0)

(* let[@axiom] tree_leaf_depth_0_alt (l : int tree) (n : int) =
  (depth l 0)#==>(leaf l) *)

let[@axiom] tree_positive_depth_is_not_leaf (l : int tree) (n : int) =
  (depth l n && n > 0)#==>(not (leaf l))

let[@axiom] tree_depth_exists (l : int tree) ((n [@exists]) : int) =
  depth l n (* && n >= 0 *)

let[@axiom] tree_depth_unique (l : int tree) (n : int) (m : int) =
  (depth l n && depth l m)#==>(n == m)

(* let[@axiom] tree_ch_depth_ex (l : int tree) (l1 : int tree) (n : int)
     ((n1 [@exists]) : int) =
   ((lch l l1 || rch l l1) && depth l n) #==> (depth l1 n1) *)

(* let[@axiom] tree_lch_depth_minus_1 (l : int tree) (l1 : int tree) (n : int)
    (n1 : int) =
  (lch l l1 && depth l n && depth l1 n1)#==>(n1 <= n - 1) *)

(* let[@axiom] tree_rch_depth_minus_1 (l : int tree) (l1 : int tree) (n : int)
    (n1 : int) =
  (rch l l1 && depth l n && depth l1 n1)#==>(n1 <= n - 1) *)
(*
let[@axiom] tree_lch_depth_minus_1 (l : int tree) (l1 : int tree) (n : int)
    (n1 : int) =
  (lch l l1 && depth l n && depth l1 n1) #==> (n1 <= n - 1) *)

(* let[@axiom] tree_lch_depth_minus_1_alt (l : int tree) (l1 : int tree) (n : int)
    ((n1 [@exists]) : int) =
  (lch l l1 && depth l n)#==>(depth l1 n1 && n1 <= n - 1 && n1 >= 0)

let[@axiom] tree_rch_depth_minus_1_alt (l : int tree) (l1 : int tree) (n : int)
    ((n1 [@exists]) : int) =
  (rch l l1 && depth l n)#==>(depth l1 n1 && n1 <= n - 1 && n1 >= 0)

let[@axiom] tree_depth_rch (l : int tree) (l1 : int tree) (n : int) (n1 : int) =
     (rch l l1 && depth l1 n1 && depth l n) #==> (n1 < n)

   let[@axiom] tree_depth_lch (l : int tree) (l1 : int tree) (n : int) (n1 : int) =
     (lch l l1 && depth l1 n1 && depth l n) #==> (n1 < n) *)

(* let[@axiom] tree_depth_0_is_leaf (l : int tree) (n : int) =
  (depth l n && n == 0)#==>(leaf l) *)

let[@axiom] tree_depth_0_is_leaf_alt (l : int tree) (n : int) =
  (depth l 0)#==>(leaf l)

(* let[@axiom] tree_depth_rch (l : int tree) (l1 : int tree) (n : int) (n1 : int) =
  (rch l l1 && depth l1 n1 && depth l n)#==>(n1 < n)

let[@axiom] tree_depth_lch (l : int tree) (l1 : int tree) (n : int) (n1 : int) =
  (lch l l1 && depth l1 n1 && depth l n)#==>(n1 < n) *)

(* let[@axiom] tree_depth_node (l : int tree) (l1 : int tree) (l2 : int tree)
     (n1 : int) (n2 : int) =
   (depth l1 n1 && depth l2 n2 && lch l l1 && rch l l2)
   #==> (((n1 > n2) #==> (depth l (n1 + 1)))
        && ((n2 >= n1) #==> (depth l (n2 + 1)))) *)


let[@axiom] tree_depth_node (l : int tree) (l1 : int tree) (l2 : int tree)
    (n1 : int) (n2 : int) (___weight : bool) =
  (depth l1 n1 && depth l2 n2 && lch l l1 && rch l l2)#==>(depth l ((ite (n1 >= n2) n1 n2) + 1))


(* let[@axiom] tree_depth_node_lch (l : int tree) (l1 : int tree) (l2 : int tree)
    (n1 : int) (n2 : int) =
  (depth l1 n1 && depth l2 n2 && lch l l1 && rch l l2 && n1 >= n2)#==>(depth l
                                                                         (n1 + 1))

let[@axiom] tree_depth_node_rch (l : int tree) (l1 : int tree) (l2 : int tree)
    (n1 : int) (n2 : int) =
  (depth l1 n1 && depth l2 n2 && lch l l1 && rch l l2 && n2 >= n1)#==>(depth l
                                                                         (n2 + 1)) *)

(* let[@axiom] tree_depth_node_lch (l : int tree) (l1 : int tree) (n1 : int)
    (n : int) =
  (depth l n && depth l1 n1 && lch l l1)#==>(n1 < n)

let[@axiom] tree_depth_node_rch (l : int tree) (l1 : int tree) (n1 : int)
    (n : int) =
  (depth l n && depth l1 n1 && rch l l1)#==>(n1 < n) *)

(** bst *)

let[@axiom] tree_leaf_bst (l : int tree) = (leaf l)#==>(bst l)

let[@axiom] tree_bst_lch_bst (l : int tree) (l1 : int tree) =
  (lch l l1 && bst l)#==>(bst l1)

let[@axiom] tree_bst_rch_bst (l : int tree) (l1 : int tree) =
  (rch l l1 && bst l)#==>(bst l1)

let[@axiom] tree_node_bst (l : int tree) (l1 : int tree) (l2 : int tree)
    (x : int) =
  (bst l1 && bst l2 && lch l l1 && rch l l2 && root l x
  && ((not (leaf l1))#==>(upper_bound l1 x))
  && ((not (leaf l2))#==>(lower_bound l2 x)))#==>(bst l)

(** Lower/upper bounds*)

let[@axiom] tree_lower_bound_base (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (bst l && root l x && lch l l1 && leaf l1 && y < x)#==>(lower_bound l y)

let[@axiom] tree_lower_bound_other (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (bst l && root l x && lch l l1 && (not (leaf l1)) && lower_bound l1 y && y < x)
  #==>(lower_bound l y)

let[@axiom] tree_lower_bound_destruct (l : int tree) (l1 : int tree) (x : int) =
  (lower_bound l x && lch l l1 && not (leaf l1))#==>(lower_bound l1 x)

let[@axiom] tree_lower_bound_destruct_2 (l : int tree) (l1 : int tree) (x : int)
    =
  (bst l && root l x && rch l l1 && not (leaf l1))#==>(lower_bound l1 x)

let[@axiom] tree_lower_bound_root (l : int tree) (x : int) (y : int) =
  (bst l && root l x && lower_bound l y)#==>(y < x)

let[@axiom] tree_upper_bound_base (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (bst l && root l x && rch l l1 && leaf l1 && y > x)#==>(upper_bound l y)

let[@axiom] tree_upper_bound_other (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (bst l && root l x && rch l l1 && (not (leaf l1)) && upper_bound l1 y && y > x)
  #==>(upper_bound l y)

let[@axiom] tree_upper_bound_destruct (l : int tree) (l1 : int tree) (x : int) =
  (upper_bound l x && rch l l1 && not (leaf l1))#==>(upper_bound l1 x)

let[@axiom] tree_upper_bound_destruct_2 (l : int tree) (l1 : int tree) (x : int)
    =
  (bst l && root l x && lch l l1 && not (leaf l1))#==>(upper_bound l1 x)

let[@axiom] tree_upper_bound_root (l : int tree) (x : int) (y : int) =
  (bst l && root l x && upper_bound l y)#==>(y > x)
