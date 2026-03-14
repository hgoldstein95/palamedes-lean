import Palamedes.Data.List
import Palamedes.Data.Stack.Stack
import Palamedes.Data.STLC.Ty
import Palamedes.Data.STLC.Term
import Palamedes.Data.Tree
import Palamedes.Data.Nat
import Palamedes.Total

open Gen Total

macro "totality" : tactic =>
  `(tactic|
    -- NOTE: This is the old version. I think it mostly does the same thing, although it does have
    -- the advantage of using Aesop's rule_set mechanism.

    -- aesop
    --   (rule_sets := [-default, -builtin, totality])
    --   (config := {enableSimp := false})
    --   (add safe (by intro))
    --   (add 5% (by split))
    --   (add 5% (by simp)))
    repeat'
      first
        | (intro)
        | apply total_pure
        | apply total_bind
        | apply total_pick
        | apply total_assume
        | apply total_indexed
        | apply total_map
        | apply total_dite
        | apply total_arbBool
        | apply total_Bool_rec
        | apply total_arbColor
        | apply total_arbNat
        | apply total_choose
        | apply total_gt
        | apply total_lt
        | apply Tree.total_unfold
        | apply Stack.total_unfold
        | apply total_arbLabel
        | apply total_elements
        | apply total_arbTy
        | apply total_Ty_caseTy
        | apply Term.total_unfold
        | apply List.total_unfold
        | split
        | simp (config := {singlePass := true}))
