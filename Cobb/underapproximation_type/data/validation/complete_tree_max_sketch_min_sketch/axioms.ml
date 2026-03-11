(* int tree *)

(* basic *)

let[@axiom] tree_leaf_no_root (l : int tree) (x : int) =
  (leaf l)#==>(not (root l x))

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

let[@axiom] tree_leaf_unique (l : int tree) (l1 : int tree) =
  (leaf l && leaf l1)#==>(l == l1)

let[@axiom] tree_no_leaf_depth (l : int tree) ((n [@exists]) : int) =
  (not (leaf l))#==>(depth l n && n > 0)

let[@axiom] tree_leaf_depth (l : int tree) ((n [@exists]) : int) =
  (leaf l)#==>(depth l 0)

let[@axiom] tree_depth_unique (l : int tree) (n1 : int) (n2 : int) =
  (depth l n1 && depth l n2)#==>(n1 == n2)
(*
let[@axiom] tree_depth_node_lch (l : int tree) (l1 : int tree) (l2 : int tree)
    (n1 : int) (n2 : int) =
  (depth l1 n1 && depth l2 n2 && lch l l1 && rch l l2 && n1 >= n2)#==>(depth l
                                                                         (n1 + 1))

let[@axiom] tree_depth_node_rch (l : int tree) (l1 : int tree) (l2 : int tree)
    (n1 : int) (n2 : int) =
  (depth l1 n1 && depth l2 n2 && lch l l1 && rch l l2 && n2 >= n1)#==>(depth l
                                                                         (n2 + 1))
 *)
(* complete *)

let[@axiom] tree_complete_leaf (l : int tree) = (leaf l)#==>(complete l)

let[@axiom] tree_complete_lch_complete (l : int tree) (l1 : int tree) =
  (lch l l1 && complete l)#==>(complete l1)

let[@axiom] tree_complete_rch_complete (l : int tree) (l1 : int tree) =
  (rch l l1 && complete l)#==>(complete l1)

let[@axiom] tree_complete_node (l : int tree) (l1 : int tree) (l2 : int tree)
    (n : int) =
  (complete l1 && complete l2 && depth l1 n && depth l2 n && lch l l1
 && rch l l2)#==>(complete l)

let[@axiom] tree_complete_lch_depth_minus_1 (l : int tree) (l1 : int tree)
    (n : int) =
  (lch l l1 && complete l && depth l n)#==>(depth l1 (n - 1))

let[@axiom] tree_complete_rch_depth_minus_1 (l : int tree) (l1 : int tree)
    (n : int) =
  (rch l l1 && complete l && depth l n)#==>(depth l1 (n - 1))
