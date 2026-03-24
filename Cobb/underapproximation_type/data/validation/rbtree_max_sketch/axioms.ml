(** int rbtree *)

(** basic *)

let[@axiom] rbtree_leaf_is_leaf (l : int rbtree) (l2 : int rbtree) =
  (rb_leaf l && rb_leaf l2)#==>(l == l2)

let[@axiom] rbtree_rb_leaf_no_rb_root (l : int rbtree) (x : int) =
  (rb_leaf l)#==>(not (rb_root l x))

let[@axiom] rbtree_rb_leaf_no_rb_root_color (l : int rbtree) (x : bool) =
  (rb_leaf l)#==>(not (rb_root_color l x))

let[@axiom] rbtree_rb_leaf_no_ch (l : int rbtree) (l1 : int rbtree) =
  (rb_leaf l)#==>(not (rb_lch l l1 || rb_rch l l1))

let[@axiom] rbtree_rb_leaf_no_red_red (l : int rbtree) =
  (rb_leaf l)#==>(no_red_red l)

let[@axiom] rbtree_no_rb_leaf_exists_ch (l : int rbtree)
    ((l1 [@exists]) : int rbtree) ((l2 [@exists]) : int rbtree) =
  (not (rb_leaf l))#==>(rb_lch l l1 && rb_rch l l2)

let[@axiom] rbtree_no_rb_leaf_exists_rb_root (l : int rbtree)
    ((x [@exists]) : int) =
  (not (rb_leaf l))#==>(rb_root l x)

let[@axiom] rbtree_no_rb_leaf_exists_rb_root_color (l : int rbtree)
    ((x [@exists]) : bool) =
  (not (rb_leaf l))#==>(rb_root_color l x)

let[@axiom] rbtree_rb_root_no_rb_leaf (l : int rbtree) (x : int) =
  (rb_root l x)#==>(not (rb_leaf l))

let[@axiom] rbtree_rb_root_color_no_rb_leaf (l : int rbtree) (x : bool) =
  (rb_root_color l x)#==>(not (rb_leaf l))

let[@axiom] rbtree_ch_no_rb_leaf (l : int rbtree) (l1 : int rbtree) =
  (rb_lch l l1 || rb_rch l l1)#==>(not (rb_leaf l))

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
  (num_black l 0 && not (rb_root_color l true))#==>(rb_leaf l)

let[@axiom] rbtree_num_black_geq_0 (l : int rbtree) (n : int) =
  (num_black l n)#==>(n >= 0)

let[@axiom] rbtree_rb_leaf_num_black_0 (l : int rbtree) (n : int) =
  (rb_leaf l && num_black l n)#==>(n == 0)

let[@axiom] rbtree_rb_leaf_num_black_0_second (l : int rbtree) =
  (rb_leaf l)#==>(num_black l 0)

let[@axiom] rbtree_positive_num_black_is_not_rb_leaf (l : int rbtree) (n : int)
    =
  (num_black l n && n > 0)#==>(not (rb_leaf l))

let[@axiom] num_black_root_black_lt_minus_1 (v : int rbtree) (lt : int rbtree)
    (h : int) =
  (rb_root_color v false && num_black v h && rb_lch v lt)#==>(num_black lt
                                                                (h - 1))

let[@axiom] num_black_root_black_rt_minus_1 (v : int rbtree) (rt : int rbtree)
    (h : int) =
  (rb_root_color v false && num_black v h && rb_rch v rt)#==>(num_black rt
                                                                (h - 1))

let[@axiom] num_black_root_red_lt_same (v : int rbtree) (lt : int rbtree)
    (h : int) =
  (rb_root_color v true && num_black v h && rb_lch v lt)#==>(num_black lt h)

let[@axiom] num_black_root_red_rt_same (v : int rbtree) (rt : int rbtree)
    (h : int) =
  (rb_root_color v true && num_black v h && rb_rch v rt)#==>(num_black rt h)

let[@axiom] num_black_root_from_lt_rt (v : int rbtree) (lt : int rbtree)
    (rt : int rbtree) (h : int) =
  (num_black lt h && num_black rt h && rb_rch v rt && rb_lch v lt
 && rb_root_color v true)#==>(num_black v h)

let[@axiom] num_black_root_from_lt_rt_plus_1 (v : int rbtree) (lt : int rbtree)
    (rt : int rbtree) (h : int) =
  (num_black lt h && num_black rt h && rb_rch v rt && rb_lch v lt
 && rb_root_color v false)#==>(num_black v (h + 1))

let[@axiom] num_black_root_black_0_lt_leaf (v : int rbtree) (lt : int rbtree) =
  (no_red_red v && num_black v 0 && rb_lch v lt)#==>(rb_leaf lt)

let[@axiom] num_black_root_black_0_rt_leaf (v : int rbtree) (rt : int rbtree) =
  (no_red_red v && num_black v 0 && rb_rch v rt)#==>(rb_leaf rt)

(* let[@axiom] num_black_root_red (v : int_rbtree) =
   (num_black v 0 && rb_root_color v true) #==> *)

let[@axiom] num_black_root_black_0_rt_red (v : int rbtree) (rt : int rbtree) =
  (num_black v 0 && rb_rch v rt)#==>(rb_root_color v true)

let[@axiom] no_red_red_lt (v : int rbtree) (lt : int rbtree) =
  (no_red_red v && rb_lch v lt)#==>(no_red_red lt)

let[@axiom] no_red_red_rt (v : int rbtree) (rt : int rbtree) =
  (no_red_red v && rb_rch v rt)#==>(no_red_red rt)

let[@axiom] no_red_red_root_red_lt_not_red (v : int rbtree) (lt : int rbtree) =
  (no_red_red v && rb_lch v lt && rb_root_color v true)#==>(not
                                                              (rb_root_color lt
                                                                 true))

let[@axiom] no_red_red_root_red_rt_not_red (v : int rbtree) (rt : int rbtree) =
  (no_red_red v && rb_rch v rt && rb_root_color v true)#==>(not
                                                              (rb_root_color rt
                                                                 true))

let[@axiom] no_red_red_given_lt_rt_black_root (v : int rbtree) (lt : int rbtree)
    (rt : int rbtree) =
  (no_red_red lt && no_red_red rt && rb_lch v lt && rb_rch v rt
 && rb_root_color v false)#==>(no_red_red v)

let[@axiom] no_red_red_given_lt_rt_red_root (v : int rbtree) (lt : int rbtree)
    (rt : int rbtree) =
  (no_red_red lt && no_red_red rt && rb_lch v lt && rb_rch v rt
  && (not (rb_root_color lt true))
  && (not (rb_root_color rt true))
  && rb_root_color v true)#==>(no_red_red v)

let[@axiom] black_lt_black_num_black_gt_1 (v : int rbtree) (lt : int rbtree)
    (h : int) =
  (num_black v h && rb_lch v lt && rb_root_color v false
 && rb_root_color lt false)#==>(h > 1)

let[@axiom] black_rt_black_num_black_gt_1 (v : int rbtree) (rt : int rbtree)
    (h : int) =
  (num_black v h && rb_rch v rt && rb_root_color v false
 && rb_root_color rt false)#==>(h > 1)

let[@axiom] root_color_single (v : int rbtree) =
  not (rb_root_color v false && rb_root_color v true)

let[@axiom] leaf_no_root_color (v : int rbtree) =
  (rb_leaf v)#==>((not (rb_root_color v false)) && not (rb_root_color v true))

(** bst *)

let[@axiom] rbtree_leaf_bst (l : int rbtree) = (rb_leaf l)#==>(rb_bst l)

let[@axiom] rbtree_bst_lch_bst (l : int rbtree) (l1 : int rbtree) =
  (rb_lch l l1 && rb_bst l)#==>(rb_bst l1)

let[@axiom] rbtree_bst_rch_bst (l : int rbtree) (l1 : int rbtree) =
  (rb_rch l l1 && rb_bst l)#==>(rb_bst l1)

let[@axiom] rbtree_node_bst (l : int rbtree) (l1 : int rbtree) (l2 : int rbtree)
    (x : int) =
  (rb_bst l1 && rb_bst l2 && rb_lch l l1 && rb_rch l l2 && rb_root l x
  && ((not (rb_leaf l1))#==>(rbt_upper_bound l1 x))
  && ((not (rb_leaf l2))#==>(rbt_lower_bound l2 x)))#==>(rb_bst l)

(** Lower/upper bounds*)

let[@axiom] rbtree_lower_bound_base (l : int rbtree) (l1 : int rbtree) (x : int)
    (y : int) =
  (rb_bst l && rb_root l x && rb_lch l l1 && rb_leaf l1 && y < x)#==>(rbt_lower_bound
                                                                        l y)

let[@axiom] rbtree_lower_bound_other (l : int rbtree) (l1 : int rbtree)
    (x : int) (y : int) =
  (rb_bst l && rb_root l x && rb_lch l l1
  && (not (rb_leaf l1))
  && rbt_lower_bound l1 y && y < x)#==>(rbt_lower_bound l y)

let[@axiom] rbtree_lower_bound_destruct (l : int rbtree) (l1 : int rbtree)
    (x : int) =
  (rbt_lower_bound l x && rb_lch l l1 && not (rb_leaf l1))#==>(rbt_lower_bound
                                                                 l1 x)

let[@axiom] rbtree_lower_bound_destruct_2 (l : int rbtree) (l1 : int rbtree)
    (x : int) =
  (rb_bst l && rb_root l x && rb_rch l l1 && not (rb_leaf l1))#==>(rbt_lower_bound
                                                                     l1 x)

let[@axiom] rbtree_lower_bound_root (l : int rbtree) (x : int) (y : int) =
  (rb_bst l && rb_root l x && rbt_lower_bound l y)#==>(y < x)

let[@axiom] rbtree_upper_bound_base (l : int rbtree) (l1 : int rbtree) (x : int)
    (y : int) =
  (rb_bst l && rb_root l x && rb_rch l l1 && rb_leaf l1 && y > x)#==>(rbt_upper_bound
                                                                        l y)

let[@axiom] rbtree_upper_bound_other (l : int rbtree) (l1 : int rbtree)
    (x : int) (y : int) =
  (rb_bst l && rb_root l x && rb_rch l l1
  && (not (rb_leaf l1))
  && rbt_upper_bound l1 y && y > x)#==>(rbt_upper_bound l y)

let[@axiom] rbtree_upper_bound_destruct (l : int rbtree) (l1 : int rbtree)
    (x : int) =
  (rbt_upper_bound l x && rb_rch l l1 && not (rb_leaf l1))#==>(rbt_upper_bound
                                                                 l1 x)

let[@axiom] rbtree_upper_bound_destruct_2 (l : int rbtree) (l1 : int rbtree)
    (x : int) =
  (rb_bst l && rb_root l x && rb_lch l l1 && not (rb_leaf l1))#==>(rbt_upper_bound
                                                                     l1 x)

let[@axiom] rbtree_upper_bound_root (l : int rbtree) (x : int) (y : int) =
  (rb_bst l && rb_root l x && rbt_upper_bound l y)#==>(y > x)
