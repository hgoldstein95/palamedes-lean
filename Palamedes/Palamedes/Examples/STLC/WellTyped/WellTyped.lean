import Palamedes.Synthesizer

open Gen CorrectGen

namespace WellTyped

set_option maxHeartbeats 5000000

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

attribute [local simp] Ty.as_or Ty.deforest_eq in
def genWellTyped (Γ : List Ty) : Gen Term := by
  generator_search (fun t => isWellTyped Γ t)

end WellTyped
