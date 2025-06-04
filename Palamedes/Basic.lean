import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Data.Tree
import Mathlib.Tactic.Convert
import Lean.Elab.Tactic.NormCast
/-
Simple examples using palamedes.
-/

set_option maxHeartbeats 1000000

#set_up_palamedes_simp

def genTwo : CGen (λ v => v = 2) := by
  palamedes

def genTwo' : CGen (2 = .) := by
  palamedes

def genTwoOrThree : CGen (λ v => v = 2 ∨ v = 3) := by
  palamedes

def getMoreThanThree : CGen (λ v => v > 3) := by
  palamedes

def genTwoOrThreeOrFour : CGen (λ v => v = 2 ∨ v = 3 ∨ v = 4) := by
  palamedes

def genTwoAndThree : CGen (λ (v : Int × Int) => v.fst = 2 ∧ v.snd = 3) := by
  palamedes

def genTwoAndThree' : CGen (λ (v : Nat × Nat) => ∃ a, ∃ b, a = 2 ∧ b = 3 ∧ v = (a, b)) := by
  palamedes

def genThreeAndTwo : CGen (λ (v : Int × Int) => v.snd = 3 ∧ v.fst = 2) := by
  palamedes

def genThreeAndTwo' : CGen (λ (v : Int × Int) => ∃ a, ∃ b, b = 3 ∧ a = 2 ∧ v = (a, b)) := by
  palamedes

@[aesop simp (rule_sets := [palamedes])]
def allTwos : List Nat → Bool
  | [] => true
  | x :: xs => x == 2 && allTwos xs

-- TODO
-- def genAllTwos : CGen (λ v => allTwos v = true) := by
--   palamedes

def genInRange : CGen (λ v => 10 ≤ v ∧ v ≤ 20) := by
  palamedes

def genTwoInRange : CGen (λ (v : Nat × Nat) => 0 ≤ v.1 ∧ v.1 ≤ v.2 ∧ v.2 ≤ 100) := by
  apply synth_tuple
  on_goal 2 =>
    apply synth_between
  on_goal 4 =>
    intro x
    apply synth_between
  on_goal 1 =>
    intro v
    apply Iff.intro
    on_goal 1 =>
      rintro ⟨⟨h1, h2⟩, h3, h4⟩
      apply And.intro
      on_goal 1 =>
        assumption
      on_goal 1 =>
        apply And.intro
        on_goal 2 => assumption
    on_goal 2 =>
      rintro⟨h1, h2, h3⟩
      apply And.intro
      on_goal 1 =>
        apply And.intro
        on_goal 1 => simp
      on_goal 2 =>
        apply And.intro
        on_goal 2 => assumption
  on_goal 2 =>
    exact Nat.le_trans h2 h3
  on_goal 2 =>
    have : id v.fst ≤ v.snd := by assumption
    apply this
  assumption

def genOneGtOther: CGen (λ (v : Nat × Nat) => v.2 < v.1) := by
  palamedes?

def genOneGtOther': CGen (λ (v : Nat × Nat) => v.2 > v.1) := by
  palamedes

def genTupleOneElem: CGen (λ (v: Int × Int) => v.1 > 2) := by
  palamedes?

def genOneGtOther3: CGen (λ (v : Nat × Nat) => ∃ x y, x > y ∧ v = (x,y)) := by
  palamedes? --need rw swap to try different order of exists

theorem tup2exists {v : α × β} (P : α → β → Prop) :
  P v.1 v.2 ↔ ∃ x : α, ∃ y : β, P x y ∧ v = (x,y) :=
  by aesop

theorem tup2exists_fst {v : α × β} (P : α → β → Prop) (Q : α → Prop) :
  P v.1 v.2 ∧ Q v.1 ↔ ∃ x : α, ∃ y : β, P x y ∧ Q x ∧ v = (x,y) :=
  by aesop

theorem tup2exists_snd {v : α × β} (P : α → β → Prop) (Q : β → Prop) :
  P v.1 v.2 ∧ Q v.2 ↔ ∃ x : α, ∃ y : β, P x y ∧ Q y ∧ v = (x,y) :=
  by aesop

theorem tup2exists_ext {v : α × β} (P : α → β → Prop) (Q : α → Prop) (R: β → Prop) :
  P v.1 v.2 ∧ Q v.1 ∧ R v.2 ↔ ∃ x : α, ∃ y : β, P x y ∧ Q x ∧ R y ∧ v = (x,y) :=
  by aesop

theorem swap_e {α β : Type} {P: α → β → Prop} :
  (∃ t: α, ∃ u: β, P t u) ↔ (∃ u: β, ∃ t: α, P t u) := by
    apply Iff.intro
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨w_1, h⟩ := h
      apply Exists.intro
      · apply Exists.intro
        · exact h
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨w_1, h⟩ := h
      apply Exists.intro
      · apply Exists.intro
        · exact h

theorem hoist{α : Type} {P: α → Prop} {Q: Prop}:
  (∃ t: α, Q ∧ P t) ↔ (Q ∧ ∃ t: α, P t) := by
  simp_all only [exists_and_left]

theorem chomp_a {α β : Type} {P: α → Prop} {Q: α → β → Prop} :
  (∃ t: α, ∃ u: β, P t ∧ Q t u) ↔ ∃ t: α, (P t) ∧ ∃ u: β, Q t u := by
  simp_all only [exists_and_left]

theorem chomp_t {α β : Type} {Q: α → β → Prop} :
  (∃ t: α, ∃ u: β, Q t u) ↔ ∃ t: α, True ∧ ∃ u: β, Q t u := by
  simp_all only [true_and]

def genOneGtOther2: CGen (λ (v : Nat × Nat) => v.1 > 2 ∧ v.2 > v.1) := by
  --simp only [tup2exists] --bad, yields CGen fun v => v.fst > 2 ∧ ∃ x y, x < y ∧ v = (x, y)
  --simp only [and_comm,and_assoc,tup2exists_fst]
  --simp only [swap_e] --recursion problem
  --simp only [← and_assoc, and_comm,hoist]
  palamedes --TODO: rewrite 2 into 3



def genOneGtOther3: CGen (λ (v : Nat × Nat) => ∃ x, x > 2 ∧ ∃ y, y > x ∧ v = (x,y)) := by
  palamedes


def genTwoBetweens : CGen (λ (v : Nat × Nat) => ∃ x, (2 ≤ x ∧ x ≤ 6) ∧ ∃ y, (2 ≤ y ∧ y ≤ 100) ∧ v = (x,y)) := by
  apply synth_bind
  · apply synth_between
  · intro a
    obtain ⟨val, property⟩ := a
    obtain ⟨left, right⟩ := property
    simp_all only
    apply synth_bind
    · apply synth_between
    · intro a
      obtain ⟨val_1, property⟩ := a
      obtain ⟨left_1, right_1⟩ := property
      simp_all only
      apply synth_pure


--set_option pp.mvars.delayed true
open Lean Meta Elab Tactic Term in
elab "partResult3" : tactic => do
  let rec get_conjuncts (e: Expr) : TacticM $ (List Expr) := do
    --if let (Expr.app (Expr.app (Expr.const `And _) p) q) := e then
    if e.isAppOf `And then
      let lhs_conjuncts ← get_conjuncts e.getAppArgs[0]!
      let rhs_conjuncts ← get_conjuncts e.getAppArgs[1]!
      return lhs_conjuncts ++ rhs_conjuncts
    else if e.containsConst (λ c => c == `Exists) then
      dbg_trace "contains exists"
      throwUnsupportedSyntax -- TODO: better error
    else
      -- logInfo e.ctorName
      return [e]

  let rec partition (exprs : List Expr) : (List Expr) × (List Expr) :=
      match exprs with
      | .nil => ([],[])
      | .cons e es =>
        let (rest_t,rest_f) := partition es
        if e.hasLooseBVar 1 then
        --if Expr.containsFVar e id then
          (e :: rest_t,rest_f)
        else (rest_t, e :: rest_f)

  let mvarId ← getMainGoal
  mvarId.withContext do
    let mainDecl ← getMainDecl
    let e := mainDecl.type
    logInfo e.ctorName
    if e.isAppOf `Eq then
      --dbg_trace f!"maindecl: {t.isAppOf `CGen}"
      let origOuterLam := e.getAppArgs[2]!
      let (Expr.lam outer_name outer_type t outer_binfo) := origOuterLam | throwUnsupportedSyntax
      -- outer_name is definitely #1!!! otherwise there will be an error due to structure
      if t.isAppOf `Exists then
        let (Expr.lam name type body binfo) := t.getAppArgs[1]! | throwUnsupportedSyntax
        let conjuncts ← get_conjuncts body
        logInfo conjuncts
        -- let (Expr.bvar yidx) := conjuncts[0]!.getAppArgs[3]! | throwUnsupportedSyntax
        -- logInfo f!"yidx: {yidx} {conjuncts[0]!.hasLooseBVar (yidx + 1)}"

        --let id ← outer_name.fvarId!
        let (varIn,varNotIn) := partition conjuncts
        logInfo f!"{varIn}/{varNotIn}"
        if varIn.length < 1 then throwUnsupportedSyntax
        let nameIn := mkAndN $ varIn
        --logInfo nameIn
        let rest := mkAndN $ varNotIn
        --logInfo rest
        let allAnd := mkAnd rest nameIn
        --Reconstruct the exists:
        let newLam := (Expr.lam name type allAnd binfo)
        let newE := mkAppN t.getAppFn #[t.getAppArgs[0]!, newLam]
        logInfo newE
        --Reconstruct the CGen:
        let newOuterLam := Expr.lam outer_name outer_type newE outer_binfo
        --let newCGen := mkAppN e.getAppFn #[e.getAppArgs[0]!, newOuterLam]
        logInfo newOuterLam
        --Change the goal
        let newEMvarId ← mkFreshExprMVar newOuterLam
        --proofterming
        let copyOfNewE ← mkFreshExprMVar newOuterLam
        let simpTheorems ←  #[``and_comm,``and_assoc].foldlM (·.addConst ·) ({} : Meta.SimpTheorems)
        --let ctx ← Simp.mkContext {} #[simpTheorems]
        let (.some resultProof) ← NormCast.proveEqUsing simpTheorems origOuterLam newOuterLam | throwUnsupportedSyntax
        -- let (simpResMV,simpStats) ← simpTarget copyOfNewE.mvarId! ctx
        -- logInfo simpStats.usedTheorems.toArray[2]!.key
        logInfo resultProof.proof?.get!
        logInfo (← inferType resultProof.proof?.get!) --.proof?.get!
        -- let newImpliesOld ← mkArrow newCGen e
        -- let mvarIdImplies ← mkFreshExprMVar newImpliesOld (userName := `helper)
        -- let proofTerm := mkApp mvarIdImplies newEMvarId

        --assign the proof to get things to unify and be done with it?
        mvarId.assign resultProof.proof?.get!

        -- let mNew ← mvarId.replaceTargetEq newCGen resultProof.proof?.get!
        -- replaceMainGoal [mNew]

        --run tauto to eliminate implication
        -- let taut_stx ← `(tactic| tauto)
        -- evalTactic taut_stx
      else throwUnsupportedSyntax
    else throwUnsupportedSyntax

--apply synth_conv (by partResult3) _

open Lean Meta Elab Tactic Term in
elab "partResult4" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let mainDecl ← getMainDecl
    let e := mainDecl.type
    logInfo f!"{e.getAppArgs[2]!}"
    let (Expr.lam outer_name outer_type t outer_binfo) := e.getAppArgs[2]! | throwUnsupportedSyntax
    logInfo t
    logInfo f!"{t.isAppOf `Exists}"
    let (Expr.lam name type body binfo) := t.getAppArgs[1]! | throwUnsupportedSyntax
    logInfo body


def genSomethingTest : CGen (λ (v: Nat × Nat) => ∃ x, 2 ≤ x ∧ x ≤ 6 ∧ v = (2, x)) := by
  apply synth_conv (by
    partResult3
  ) (synth_bind _ _)

def genTwoBetweens2 : CGen (λ (v : Nat × Nat) => ∃ x, (2 ≤ x ∧ x ≤ 6) ∧ ∃ y, 2 ≤ y ∧ y ≤ 100 ∧ v = (x,y)) := by
  apply synth_conv (by partResult3) (synth_bind _ _)
  sorry
  -- · apply synth_between
  -- · intro a
  --   obtain ⟨val, property⟩ := a
  --   obtain ⟨left, right⟩ := property
  --   simp_all only
  --   partResult3
  --   --simp_all only [and_comm,and_assoc]
  --   apply synth_bind
  --   · apply synth_between
  --   · intro a
  --     obtain ⟨val_1, property⟩ := a
  --     obtain ⟨left_1, right_1⟩ := property
  --     simp_all only
  --     apply synth_pure

-- @[aesop simp (rule_sets := [palamedes])]
-- def evenLength : List α → Bool
--   | [] => true
--   | _ :: xs => not (evenLength xs)

-- -- TODO
-- -- def genEvenLength [Arbitrary α] :
-- --     CGen (λ (v : List α) => evenLength v = true) := by
-- --   palamedes

-- -- TODO
-- -- def genLengthK {k : Nat} [Arbitrary α] :
-- --     CGen (λ (v : List α) => List.length v = k) := by
-- --   palamedes

-- -- TODO
-- -- def genEvenLengthTwos :
-- --     CGen (λ (v : List Nat) => List.foldrM (λ x b => do guard (x == 2); pure (not b)) true v = Option.some true) := by
-- --   palamedes

-- -- TODO
-- -- def genLengthKTwos (k : Nat) :
-- --     CGen (λ (v : List Nat) =>
-- --       List.foldr (λ _ l => l + 1) 0 v = k ∧
-- --       List.foldrM (λ x () => guard (x == 2)) () v = Option.some ()) := by
-- --   palamedes

-- @[aesop simp (rule_sets := [palamedes])]
-- def increasingByOne : List Int → Int → Bool := λ xs prev =>
--   match xs with
--   | [] => true
--   | x :: xs => x == prev + 1 && increasingByOne xs x

-- -- TODO
-- -- def genIncreasingByOne : CGen (λ (v : List Int) => increasingByOne v 0) := by
-- --   palamedes

-- def genTreeIncreasingByOne :
--     CGen (λ v =>
--       Tree.accuM (λ x _ => (x, x))
--                  (λ () x () => λ (prev : Int) => do guard (x == prev + 1))
--                  (λ _ => pure ())
--                  v
--                  0 = some ()) := by
--   palamedes

-- def genBetween : CGen (λ v => 3 ≤ v ∧ v ≤ 10) := by
--   palamedes

-- @[aesop simp (rule_sets := [palamedes])]
-- def sortedBetween (hi : Nat) : List Nat → Nat → Bool := λ xs lo =>
--   match xs with
--   | [] => true
--   | x :: xs => lo ≤ x && x ≤ hi && sortedBetween hi xs x

-- -- TODO
-- -- def genSortedBetween
-- --     (lo hi : Nat) :
-- --     CGen (λ v => sortedBetween hi v lo = true) := by
-- --   palamedes
