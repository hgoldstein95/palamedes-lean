import Palamedes.Data.List
import Palamedes.Data.Stack.Stack
import Palamedes.Data.STLC.Ty
import Palamedes.Data.STLC.Term
import Palamedes.Data.Tree
import Palamedes.Data.Nat
import Palamedes.Support

macro "optimality" : tactic =>
  `(tactic|
    repeat'
      first
        | rfl
        | (intro)
        | rw [support_assume_pick]
        | rw [support_pick_assume]
        | rw [support_assume_bind]
        | rw [support_pure_bind]
        | rw [support_bind_bind]
        | apply Term.support_unfold_congr
        | apply Tree.support_unfold_congr
        | apply List.support_unfold_congr
        | apply Stack.support_unfold_congr
        | apply Ty.support_unfold_congr
        | apply Gen.support_caseTy_congr
        | apply support_arbLabel
        | apply support_bind_congr
        | apply support_pick_congr
        | apply support_if_congr
        | apply support_assume_congr
        | simp only [dite_true, dite_false, *]
        | rw [← support_pick_bind]
        | rw [← support_if_bind]
        | split
        | simp_all
        | aesop)
