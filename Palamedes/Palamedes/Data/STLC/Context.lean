import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Total
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Basic

namespace Gen

def elements (xs : List α) (h : xs.length > 0) : Gen α :=
  match xs with
  | x :: xs =>
    match hxs : xs with
    | [] => pure x
    | _ :: _ => pick (pure x) (elements xs (by rw [hxs]; simp))

@[simp]
theorem support_elements
    {xs : List α} {v : α} {h : xs.length > 0} :
    v ∈ 〚elements xs h〛↔ v ∈ xs := by
  induction xs with
  | nil => simp_all; contradiction
  | cons x xs ih =>
    match hxs : xs with
    | [] =>
      simp_all [elements]
    | _ :: _ =>
      simp [elements] at ih |-
      simp_all

namespace CorrectGen

@[reducible]
def s_elements_partial [DecidableEq α] (xs : List α) : CorrectGen (fun v => List.elem v xs) :=
  Subtype.mk (assume (xs.length > 0) (fun h => elements xs (by aesop))) <| by
    funext v
    simp [support_elements]
    cases xs <;> simp_all

end CorrectGen

namespace Total

@[simp, aesop safe (rule_sets := [totality])]
theorem total_elements :
    (Gen.total (elements xs h)) := by
  induction xs <;> simp at h
  case cons x xs' ih _ =>
    simp [elements]
    cases xs' <;> simp_all

end Total

theorem getElem?_eq_some_iff_indexesOf_getElem?_eq_some
    [BEq α]
    [LawfulBEq α]
    {xs : List α}
    {i : Nat}
    {a : α} :
    xs[i]? = some a ↔ i ∈ (xs.indexesOf a) := by
  induction xs generalizing a i with
  | nil => simp [List.indexesOf_nil]
  | cons x xs ih =>
    simp [List.indexesOf_cons, List.getElem?_cons]
    apply Iff.intro
    . intro h
      match i with
      | 0 => simp_all
      | i' + 1 =>
        simp_all
        by_cases hxa : x == a
        . simp_all
        . have : (x == a) = false := by aesop
          simpa [this]
    . intro h
      by_cases hxa : x == a
      . simp_all
        match h with
        | .inl h => simp_all
        | .inr h =>
          simp_all
          intro h'
          aesop
      . simp_all
        aesop

end Gen
