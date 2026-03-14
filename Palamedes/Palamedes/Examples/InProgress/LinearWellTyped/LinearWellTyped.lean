import Palamedes.Synthesizer

open Gen CorrectGen

namespace LinearWellTyped

/-
Inductive combine : list bool -> list bool -> list bool -> Prop :=
| combine_nil : combine nil nil nil
| combine_cons : forall as1 as2 as3 a1 a2 a3, nand a1 a2 a3
      -> combine as1 as2 as3 -> combine (cons a1 as1) (cons a2 as2) (cons a3 as3).

Inductive var_linear : list bool -> nat -> Prop :=
| zero_lin : forall n, var_linear (true :: falses n) 0
| suc_lin : forall u n, var_linear u n -> var_linear (cons false u) (S n).

Inductive linear : list bool -> Term -> Prop :=
| l_var : forall u_ n_, var_linear u_ n_ -> linear u_ (var n_)
| l_app : forall u1_ u2_ u3_ e1_ e2_, linear u1_ e1_ -> linear u2_ e2_
                                 -> combine u1_ u2_ u3_ -> linear u3_ (app e1_ e2_)
| l_con  : forall len_ n_, linear (falses len_) (const n_)
| l_lam : forall u_ e_, linear (true :: u_) e_ -> linear u_ (lam e_)
-/

-- def combine : List Bool → List Bool → List Bool → Bool := by sorry

-- def var_linear : List Bool → Nat → Bool := by sorry

-- def isLinear (t : Term) (varUsed : List Bool) : Bool :=
--   match t with
--   | .unit => true
--   | .var n => n < varUsed.length && varUsed[n]? == some false
--   | .abs _ t' => isLinear t' (false :: varUsed)
--   | .app t₁ t₂ => combine

-- @[simp]
-- def isLinearAux (t : Term) (varUsedOnce : List Bool) : Option (List Bool) :=
--   match t with
--   | .unit => varUsedOnce
--   | .var n => if varUsedOnce[n] == some false then List.nth
--   | .abs _ t => by sorry
--   | .app t₁ t₂ => by sorry


-- @[simp]
-- def isLinear (t : Term) : Bool :=
--   isLinearAux t []

@[simp]
def isWellScoped (t : Term) (varCap : Nat) : Bool :=
  match t with
  | .unit => true
  | .var n => n < varCap
  | .abs _ t => isWellScoped t (varCap + 1)
  | .app t₁ t₂ => isWellScoped t₁ varCap && isWellScoped t₂ varCap

@[simp]
def getType (t : Term) (Γ : List Ty) : Option Ty :=
  match t with
  | .unit => pure .unit
  | .var n => Γ[n]?
  | .abs τ t => do
    let τ' ← getType t (τ :: Γ)
    pure (.arrow τ τ')
  | .app t₁ t₂ => do
    let τ₁ ← getType t₁ Γ
    let τ₂ ← getType t₂ Γ
    match τ₁ with
    | .arrow τarg τres => do
      guard (τarg == τ₂)
      pure τres
    | .unit => failure

@[simp]
def isWellTyped (Γ : List Ty) (t : Term) : Prop :=
  ∃ (τ : Ty), getType t Γ = τ

set_option maxHeartbeats 5000000

def genLinearWellTyped : Gen Term := by
  generator_search (fun t => isWellScoped t 0 = true)

end LinearWellTyped
