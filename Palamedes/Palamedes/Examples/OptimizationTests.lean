import Lean
import Palamedes.Optimizer

open Lean Elab Command Term Meta Gen

syntax (name := assertOptimizes) "#assert_optimizes! " term " goes_to " term : command

@[command_elab assertOptimizes]
def expandAssertOptimizes : CommandElab := fun stx =>
  match stx with
  | `(#assert_optimizes! $t1:term goes_to $t2:term) => do
    liftTermElabM do
      let mα ← mkFreshExprMVar none
      let e1 ← elabTerm t1 (some (.app (.const ``Gen []) mα))
      let e2 ← elabTerm t2 (some (.app (.const ``Gen []) mα))
      let e1' ← optimizeGen e1
      unless ← isDefEq e1' e2 do
        throwError "{e1}\n~~>\n{e1'}\n!=\n{e2}"

      let thm ← mkEq (← mkAppM ``support #[e1]) (← mkAppM ``support #[e1'])
      let g ← mkFreshExprMVar thm
      let [] ←
        try
          Tactic.run g.mvarId! (Tactic.evalTactic (← `(tactic|aesop)))
        catch e =>
          throwError "could not prove: {thm}\n{e.toMessageData}"
        | throwError "could not prove: {thm}\ngoals remain"
  | _ => throwError "invalid syntax {stx}"

private axiom g : Gen Nat
private axiom f : Nat → Gen Nat

#assert_optimizes!
  (pure 5 : Gen Nat) >>= fun x => pure (x + 1)
  goes_to
  (fun x => pure (x + 1)) 5

#assert_optimizes!
  (g >>= fun x => pure (x + 1)) >>= fun x => pure (x + 2)
  goes_to
  g >>= (fun x => pure ((x + 1) + 2))

#assert_optimizes!
  pick (assume ((2 : Nat) == 2) (fun _ => (pure 3 : Gen Nat))) (pure 4)
  goes_to
  if _ : (2 == 2) then pick (pure 3) (pure 4) else pure 4

-- TODO: Can we do better? Ideally we could apply a heuristic here to try to figure out which one is
-- easier to satisfy...
#assert_optimizes!
  pick (assume ((2 : Nat) == 2) (fun _ => (pure 2 : Gen Nat))) (assume ((3 : Nat) == 3) (fun _ => pure 3))
  goes_to
  if ((2 : Nat) == 2) then if ((3 : Nat) == 3) then pick (pure 2) (pure 3) else pure 2 else assume ((3 : Nat) == 3) (fun _ => pure 3)

#assert_optimizes!
  (assume ((2 : Nat) == 2) (fun _ => pure 3)) >>= f
  goes_to
  assume ((2 : Nat) == 2) (fun _ => f 3)

#assert_optimizes!
  g >>= (fun x => assume ((2 : Nat) == 2) (fun _ => pure (x + 1)))
  goes_to
  assume ((2 : Nat) == 2) (fun h => g >>= fun x => (fun _ => pure (x + 1)) h)

#assert_optimizes!
  pick (pure 4 : Gen Nat) (assume ((2 : Nat) == 2) (fun _ => pure 3))
  goes_to
  if _ : ((2 : Nat) == 2) then pick (pure 4) (pure 3) else pure 4
