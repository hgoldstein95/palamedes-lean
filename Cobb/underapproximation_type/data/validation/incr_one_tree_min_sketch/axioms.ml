(* int tree *)

(* basic *)

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

let[@axiom] tree_leaf_exists_no_lch (l : int tree) (l1 : int tree) =
  (leaf l)#==>(not (lch l l1))

let[@axiom] tree_no_leaf_exists_rch (l : int tree) ((l2 [@exists]) : int tree) =
  (not (leaf l))#==>(rch l l2)

let[@axiom] tree_no_leaf_exists_root (l : int tree) ((x [@exists]) : int) =
  (not (leaf l))#==>(root l x)

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

let[@axiom] tree_leaf_depth_0_disjoint (l : int tree) ((n [@exists]) : int) =
  (depth l n && n == 0 && leaf l) || (depth l n && n > 0 && not (leaf l))

let[@axiom] tree_leaf_unique (l : int tree) (l1 : int tree) =
  (leaf l && leaf l1)#==>(l == l1)

let[@axiom] tree_no_leaf_depth (l : int tree) ((n [@exists]) : int) =
  (not (leaf l))#==>(depth l n && n > 0)

let[@axiom] tree_positive_depth_is_not_leaf (l : int tree) (n : int) =
  (depth l n && n > 0)#==>(not (leaf l))

let[@axiom] tree_leaf_depth (l : int tree) ((n [@exists]) : int) =
  (leaf l)#==>(depth l 0)

let[@axiom] tree_depth_0_is_leaf_alt (l : int tree) (n : int) =
  (depth l 0)#==>(leaf l)

let[@axiom] tree_leaf_depth_0_alt (l : int tree) (n : int) =
  (leaf l && depth l n)#==>(n == 0)

let[@axiom] tree_depth_unique (l : int tree) (n1 : int) (n2 : int) =
  (depth l n1 && depth l n2)#==>(n1 == n2)

let[@axiom] tree_depth_node_lch (l : int tree) (l1 : int tree) (l2 : int tree)
    (n1 : int) (n2 : int) =
  (depth l1 n1 && depth l2 n2 && lch l l1 && rch l l2 && n1 >= n2)#==>(depth l
                                                                         (n1 + 1))

let[@axiom] tree_depth_node_rch (l : int tree) (l1 : int tree) (l2 : int tree)
    (n1 : int) (n2 : int) =
  (depth l1 n1 && depth l2 n2 && lch l l1 && rch l l2 && n2 >= n1)#==>(depth l
                                                                         (n2 + 1))

let[@axiom] tree_depth_node (l : int tree) (l1 : int tree) (l2 : int tree)
    (n1 : int) (n2 : int) (___weight : bool) =
  (depth l1 n1 && depth l2 n2 && lch l l1 && rch l l2)#==>(depth l
                                                             (ite (n1 >= n2) n1
                                                                n2
                                                             + 1))

let[@axiom] tree_depth_positive_not_leaf (l : int tree) (n : int) =
  (depth l n && n > 0)#==>(not (leaf l))

(* all_twos_tree *)

let[@axiom] incr_one_leaf (l : int tree) = (leaf l)#==>(tree_incr_one l)
let[@axiom] incr_one_depth_one (l : int tree) = (depth l 1)#==>(tree_incr_one l)

let[@axiom] incr_one_lch (l : int tree) (l1 : int tree) =
  (lch l l1 && tree_incr_one l)#==>(tree_incr_one l1)

let[@axiom] incr_one_rch (l : int tree) (l1 : int tree) =
  (rch l l1 && tree_incr_one l)#==>(tree_incr_one l1)

let[@axiom] tree_incr_one_tree_node (l : int tree) (l1 : int tree)
    (l2 : int tree) (x : int) (y : int) =
  (tree_incr_one l1 && tree_incr_one l2 && lch l l1 && rch l l2 && root l1 y
 && root l2 y && root l x
  && y == x + 1)#==>(tree_incr_one l)

let[@axiom] tree_incr_one_tree_node_leaves (l : int tree) (l1 : int tree)
    (l2 : int tree) =
  (leaf l1 && leaf l2 && lch l l1 && rch l l2)#==>(tree_incr_one l)

let[@axiom] tree_incr_one_tree_node_left (l : int tree) (l1 : int tree)
    (l2 : int tree) (x : int) (y : int) =
  (tree_incr_one l1 && leaf l2 && lch l l1 && rch l l2 && root l1 y && root l x
  && y == x + 1)#==>(tree_incr_one l)

let[@axiom] tree_incr_one_tree_node_right (l : int tree) (l1 : int tree)
    (l2 : int tree) (x : int) (y : int) =
  (leaf l1 && tree_incr_one l2 && lch l l1 && rch l l2 && root l2 y && root l x
  && y == x + 1)#==>(tree_incr_one l)

let[@axiom] tree_incr_one_root_lch (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (tree_incr_one l && lch l l1)#==>(leaf l1
                                   || ((root l x)#==>(root l1 y && y == x + 1))
                                   )

let[@axiom] tree_incr_one_root_rch (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (tree_incr_one l && rch l l1)#==>(leaf l1
                                   || ((root l x)#==>(root l1 y && y == x + 1))
                                   )
