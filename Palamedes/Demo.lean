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

abbrev genAllTwos' : CGen (λ xs => isAllTwos xs = Option.some ()) := by
  apply synth_unfoldM=>[]//==
  constructor=>//=ls <;> constructor=>//
  elim: ls=>//=a b->{a}
  -- I'm not an expety by this goal seems false.
  sorry


#eval traceConstWithTransparency .reducible ``genAllTwos'
