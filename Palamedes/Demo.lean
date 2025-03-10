import Palamedes.Free
import Palamedes.Support
import Palamedes.Synth
import Palamedes.Util
import Ssreflect.Lang

attribute [simp] guard
attribute [-simp] Prod.forall

#print CGen

example : CGen (λ x => x = 1 ∨ x = 2) := by
  apply synth_or
  . apply synth_pure
  . apply synth_pure

abbrev genOneOrTwo : CGen (λ x => x = 1 ∨ x = 2) := by
  apply synth_or <;> apply synth_pure

#eval traceConstWithTransparency .reducible ``genOneOrTwo

def isAllTwos (xs : List Nat) : Option Unit :=
  List.foldrM
    (λ x () => guard (x == 2))
    ()
    xs

def genAllTwos' : CGen (λ xs => isAllTwos xs = Option.some ()) := by
  apply synth_unfoldM=>b
  simp_all only [guard, beq_iff_eq, ite, failure, Option.pure_def, deforest_decidable_eq, reduceCtorEq, decidable_or,
    and_false, and_true, false_or, ListF_or, true_and, exists_and_right, exists_eq_right]
  apply synth_or
  . apply synth_pure
  . apply synth_bind_arb=>a; apply synth_pure

#eval traceConstWithTransparency .reducible ``genAllTwos'
