import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Total
import Palamedes.Util

section BaseFunctor

inductive ListF (α β : Type) where
  | nil : ListF α β
  | cons : (a : α) → (b : β) → ListF α β

theorem ListF_or
    {α β : Type}
    {P : Prop}
    {Q : α → β → Prop}
    {t : ListF α β} :
    ListF.rec P Q t ↔ (P ∧ t = .nil) ∨ (∃ x b, t = .cons x b ∧ Q x b) := by
  match t with
  | .nil => simp
  | .cons x b => aesop

end BaseFunctor

section RecursionSchemes


def List.fold {α β: Type} (f : α → β → β) (z : β) (xs : List α) :=
  List.foldr f z xs

@[simp]
theorem List.fold_nil : List.fold f z .nil = z := rfl

@[simp]
theorem List.fold_cons
    {xs : List α}
    {f : α → β → β} :
    List.fold f z (.cons x xs) = f x (List.fold f z xs) :=
  rfl

def List.accuM
    [Monad m]
    {α β σ : Type}
    (st : α → σ → σ)
    (f : α → β → σ → m β)
    (z : σ → m β)
    (xs : List α)
    (s : σ) :
    m β :=
  match xs with
  | [] => z s
  | x :: xs => do f x (← List.accuM st f z xs (st x s)) s


@[simp]
theorem List.accuM_nil
    [Monad m]
    {st : α → σ → σ}
    {f : α → β → σ → m β}
    {z : σ → m β}
    {i : σ} :
    List.accuM st f z .nil i = z i :=
  rfl

@[simp]
theorem List.accuM_cons
    [Monad m]
    {st : α → σ → σ}
    {f : α → β → σ → m β}
    {z : σ → m β}
    {i : σ}
    {x: α}
    {xs : List α} :
    List.accuM st f z (.cons x xs) i = (do f x (← List.accuM st f z xs (st x i)) i) :=
  rfl

end RecursionSchemes

section Unfold

open Gen

private def List.unfold_aux (n : Nat) (f : β → Gen (ListF α β)) (b : β) : Gen (Option (List α)) :=
  match n with
  | 0 => pure none
  | n + 1 => do
    match (← f b) with
    | .nil => pure (some [])
    | .cons x b' => do
      let xs ← List.unfold_aux n f b'
      pure (do x :: (← xs))

theorem List.unfold_aux_monotonic :
    some v ∈ 〚List.unfold_aux n f b〛 →
    some v ∈ 〚List.unfold_aux (n + 1) f b〛 := by
  induction n generalizing v f b
  case zero =>
    simp [List.unfold_aux]
  case succ n' ih =>
    unfold List.unfold_aux
    simp
    intro l hl hv
    exists l
    apply And.intro hl
    cases l <;> simp_all
    have ⟨w, ⟨hl, hr⟩⟩ := hv
    exists w
    cases w <;> simp_all

@[irreducible]
def List.unfold (f : β → Gen (ListF α β)) (b : β) : Gen (List α) :=
  indexed (fun n => List.unfold_aux n f b)

-- TODO: I wish I had a better naming convention for this.
@[simp]
def List.unfold_support (P : β → ListF α β → Prop) (b : β) (xs : List α) : Prop :=
  match xs with
  | [] => P b .nil
  | x :: xs => ∃ b', P b (.cons x b') ∧ List.unfold_support P b' xs

@[simp]
theorem List.support_unfold :
    support (List.unfold f b) = List.unfold_support (fun b' => support (f b')) b := by
  unfold List.unfold
  funext xs
  simp_all
  induction xs generalizing b with
  | nil =>
    apply Iff.intro
    . intro ⟨n, h⟩
      cases n <;> simp_all [List.unfold_aux]
      have ⟨v', hv'1, hv'2⟩ := h
      cases v' <;> simp_all [List.unfold_aux]
      have ⟨v'', hv''⟩ := hv'2
      cases v'' <;> simp_all
    . simp
      intro h
      exists 1
      simp [List.unfold_aux]
      exists ListF.nil
  | cons x xs ih =>
    apply Iff.intro
    . intro ⟨n, h⟩
      cases n <;> simp_all [List.unfold_aux]; case succ n =>
      have ⟨v', hv'1, hv'2⟩ := h
      cases v' <;> simp_all
      case cons _ b'' =>
      have ⟨v'', hv''⟩ := hv'2
      cases v'' <;> simp_all
      obtain ⟨hv'', rfl, rfl⟩ := hv''
      exists b''
      apply And.intro hv'1
      apply (@ih b'').mp
      exists n
    . intro ⟨b', hx, hxs⟩
      have ⟨n, h⟩ := ih.mpr hxs
      exists n + 1
      simp_all
      exists ListF.cons x b'
      simp_all
      exists some xs

theorem List.support_unfold_congr
    {hf : ∀ {b}, support (f b) = support (f' b)} :
    support (List.unfold f b) = support (List.unfold f' b) := by
  aesop

end Unfold

section FoldConversions

theorem List.fold_accu_Option_basic
    {α β : Type}
    {v : β}
    {xs : List α}
    {z : β}
    {f : α → β → β} :
    List.fold f z xs = v ↔
    List.accuM
      (fun _ _ => ())
      (fun x xs _ => some (f x xs))
      (fun _ => some z)
      xs
      () = some v := by
  induction xs generalizing v <;> simp_all [List.fold, List.accuM]
  case cons x xs' ih =>
    replace ih := @ih (List.fold f z xs')
    simp_all [List.fold, List.accuM]

theorem List.fold_accu_Option_true
    {α : Type}
    {xs : List α}
    {g : α → Bool}
    {f :  α → Bool → Bool}
    (h : ∀ x acc, f x acc = (g x && acc)) :
    List.fold f true xs = true ↔
    List.accuM
      (fun _ _ => ())
      (fun x _ _ => guard (g x))
      (fun _ => some ())
      xs
      () = some () := by
  induction xs <;> simp_all [List.fold, List.accuM]
  case cons x xs' ih =>
    apply Iff.intro <;> intro hf
    . generalize hv : fold f true xs' = v
      cases v <;>
        simp_all [List.fold, List.accuM, guard]
    . rw [Option.bind_eq_some_iff] at hf
      replace ⟨ v, hf ⟩ := hf
      simp_all [List.fold, List.accuM, guard]

theorem List.fold_accu_Option_function
    {α β σ : Type}
    {i : σ}
    {v : β}
    {xs : List α}
    {z : (σ → β)}
    {f : α → (σ → β) → (σ → β)}
    {g : α → β → σ → Option β}
    {st :  α → σ → σ}
    (h : ∀ x acc s w, f x acc s = w ↔ (do g x (← acc (st x s)) s) = some w) :
    List.fold f z xs i = v ↔
    List.accuM
      st
      g
      (fun s => some (z s))
      xs
      i = some v := by
  induction xs generalizing v i <;> simp_all [List.fold, List.accuM, Option.bind_eq_some_iff]
  case cons x xs' ih =>
    apply Iff.intro <;> intro hg
    . exists (foldr f z xs' (st x i))
      simp_all
      rw [← ih]
    . replace ⟨w, ⟨hgw, hg⟩⟩ := hg
      rw [← ih] at hgw
      rw [hgw]
      apply hg

theorem List.fold_accu_Option_function_true
    {α σ : Type}
    {i : σ}
    {xs : List α}
    {f : α → (σ → Bool) → (σ → Bool)}
    {g : α → σ → Bool}
    {st :  α → σ → σ}
    (h : ∀ x acc s,
      f x acc s = true ↔ (do (return (g x s) && (← acc (st x s)))) = some true)
    :
    List.fold f (fun _ => true) xs i = true ↔
    List.accuM
      st
      (fun x _ s => guard $ g x s)
      (fun _ => some ())
      xs
      i = some () := by
    induction xs generalizing i <;> simp_all [List.fold, List.accuM, Option.bind_eq_some_iff, guard]
    case cons x xs' ih =>
      apply Iff.intro <;> intro hg <;> simp_all
      replace ⟨⟨v, hv ⟩ , hg⟩ := hg <;> simp_all


theorem bind_false (b : Bool) :
  (some b).bind (fun _ => some false) = some false := by
  aesop

theorem List.fold_accu_cond_bool {α : Type} {xs : List α} [BEq α] (flag : α) b :
  some (List.fold
    (fun c acc s =>
      if c == flag then !s && acc true else acc false)
    (fun _ => true)
    xs
    b) =
  List.accuM (fun x _ => x == flag)
              (fun x acc s =>
                if x == flag then (return !s && acc) else return acc)
              (fun _ => true)
              xs
              b := by
  induction xs generalizing b <;> simp
  case cons head tail ih =>
    cases (head == flag) <;> simp
    . apply ih
    . specialize ih true
      cases b <;> simp_all
      rw [← ih, bind_false]

theorem List.fold_accu_cond_nat {α : Type} [BEq α] {xs : List α} flag i base_i :
  some (List.fold
    (fun c acc i => if c == flag then acc i else i > 0 && acc (i - 1))
    (fun i => i == base_i)
    xs
    i) =
  List.accuM (fun x i => if x == flag then i else (i - 1))
            (fun x acc i =>
              if x == flag then (return acc) else return i > 0 && acc)
            (fun i => i == base_i)
            xs
            i := by
    induction xs generalizing i <;> simp
    case cons head tail ih =>
      cases (head == flag) <;> simp
      specialize ih (i - 1)
      . cases (decide (0 < i)) <;> simp_all
        rw [← ih, bind_false]
      . apply ih

/-
theorem conv_cond_fold_accu_bool
  {α σ : Type}
  {i : σ}
  {st_true st_false : α -> σ -> σ}
  {cond_true cond_false : σ -> Bool}
  {xs : List α}
  {cond_guard : α -> Bool} :
  some (List.fold
    (fun c acc s => if cond_guard c then
                      cond_true s && acc (st_true c s) else
                      cond_false s && acc (st_false c s))
    (fun _ => true)
    xs
    i) =
  List.accuM
    (fun x s => if cond_guard x then st_true x s else st_false x s)
    (fun x (acc : Bool) s =>
      if cond_guard x then return cond_true s && acc else return cond_false s && acc)
    (fun _ => true)
    (xs : List α)
    i := by
  induction xs generalizing i <;> simp
  case cons head tail ih =>
    cases (cond_guard head) <;> simp_all
    . cases (cond_false i) <;> simp_all
      rw [← ih, bind_false]
    . cases (cond_true i) <;> simp_all
      rw [← ih, bind_false]

theorem conv_cond_fold_accu_iff
  {α σ : Type}
  {i : σ}
  {st_true st_false : α -> σ -> σ}
  {cond_true cond_false : σ -> Bool}
  {xs : List α}
  {cond_guard : α -> Bool} :
  List.fold
    (fun c acc s => if cond_guard c then
                      cond_true s && acc (st_true c s) else
                      cond_false s && acc (st_false c s))
    (fun _ => true)
    xs
    i = true ↔
  List.accuM
    (fun x s => if cond_guard x then st_true x s else st_false x s)
    (fun x (acc : Bool) s =>
      if cond_guard x then return cond_true s && acc else return cond_false s && acc)
    (fun _ => true)
    (xs : List α)
    i = some true := by
  rw [← conv_cond_fold_accu_bool]
  simp
-/

end FoldConversions

section FoldCoercion

theorem List.coerce_to_fold
    {xs : List α}
    {f : List α → β}
    {z : β}
    {g : α → β → β}
    (h1 : f [] = z := by rflm)
    (h2 : ∀ x xs, f (x :: xs) = g x (f xs)
      := by intros; simp_all [- Bool.not_eq_eq_eq_not]; rflm) :
    f xs = xs.fold g z := by
  induction xs <;> simp_all

end FoldCoercion

section FoldMerging

theorem List.merge_accuM
    {xs : List α}
    {st₁ : α → σ₁ → σ₁}
    {st₂ : α → σ₂ → σ₂}
    {f₁ : α → β₁ → σ₁ → Option β₁}
    {f₂ : α → β₂ → σ₂ → Option β₂}
    {s₁ : σ₁} {s₂ : σ₂}
    {z₁ : σ₁ → Option β₁} {z₂ : σ₂ → Option β₂}
    {b₁ : β₁} {b₂ : β₂} :
    (xs.accuM st₁ f₁ z₁ s₁ = some b₁ ∧ xs.accuM st₂ f₂ z₂ s₂ = some b₂)
    ↔
    (xs.accuM
      (fun x (s₁, s₂) => (st₁ x s₁, st₂ x s₂))
      (fun x (b₁, b₂) (s₁, s₂) => do (← f₁ x b₁ s₁, ← f₂ x b₂ s₂))
      (fun (s₁, s₂) => do (← z₁ s₁, ← z₂ s₂))
      (s₁, s₂) = some (b₁, b₂)) := by
  induction xs generalizing st₁ st₂ f₁ f₂ s₁ s₂ z₁ z₂ b₁ b₂
  case nil => simp_all [List.accuM, Option.bind_eq_some_iff]
  case cons y ys ih =>
    simp_all [List.accuM, Option.bind_eq_some_iff]
    apply Iff.intro
    . -- (->)
      intro ⟨ ⟨ v₁, ⟨ hv1h, hv1tl ⟩ ⟩ , ⟨ v₂, ⟨ hv2h, hv2tl ⟩ ⟩ ⟩
      exists v₁, v₂
      replace ih := @ih st₁ st₂ f₁ f₂ (st₁ y s₁) (st₂ y s₂) z₁ z₂ v₁ v₂
      simp_all [List.accuM, Option.bind_eq_some_iff]
    . -- (<-)
      intro ⟨ v₁, v₂, h, h1, h2 ⟩
      replace ih := @ih st₁ st₂ f₁ f₂ (st₁ y s₁) (st₂ y s₂) z₁ z₂ v₁ v₂
      apply And.intro
      . exists v₁
        simp_all [List.accuM, Option.bind_eq_some_iff]
      . exists v₂
        simp_all [List.accuM, Option.bind_eq_some_iff]

end FoldMerging

namespace Gen

namespace CorrectGen

@[reducible]
def List.s_unfold
    {α β σ : Type}
    {st : α → σ → σ}
    {f : α → β → σ → Option β}
    {z : σ → Option β}
    {s : σ}
    {b : β}
    (g : (b : β) → (s : σ) → CorrectGen
      (fun (t : ListF α β) =>
        (z s = some b ∧ t = .nil) ∨
        (∃ a b', f a b' s = some b ∧ t = .cons a b'))) :
    CorrectGen (fun v => List.accuM st f z v s = some b) :=
  Subtype.mk
    (List.unfold (fun (b, s) => do
      match (← (g b s).val) with
      | .nil => pure .nil
      | .cons x b' => pure (.cons x (b', st x s))) (b, s)) <| by
    rw [List.support_unfold]
    funext xs
    induction xs generalizing b s <;> simp_all
    case nil =>
      apply Iff.intro <;> intro h
      . replace ⟨ ys, ⟨ hys, h ⟩ ⟩ := h
        cases ys <;> simp_all [(g b s).property]
      . exists ListF.nil
        simp_all [(g b s).property]
    case cons x xs ih =>
      apply Iff.intro <;> intro h
      . replace ⟨ b', ⟨ s', ⟨ ⟨ ys, ⟨ hys, h ⟩ ⟩ , h' ⟩ ⟩ ⟩ := h
        cases ys <;> simp_all [(g b s).property]
      . rw [Option.bind_eq_some_iff] at h
        replace ⟨ b', ⟨ hxs, h ⟩ ⟩ := h
        exists b', st x s
        apply And.intro
        . exists ListF.cons x b'
          simp_all [(g b s).property]
        . assumption

end CorrectGen

namespace Total

@[simp, aesop safe (rule_sets := [totality])]
def List.total_unfold
    (h : ∀ b, total (g b)) :
    total (List.unfold g b) := by
  simp [List.unfold]
  apply total_indexed
  intro n
  induction n generalizing b with
  | zero => simp [List.unfold_aux]
  | succ n' ih =>
    simp [List.unfold_aux]
    apply total_bind <;> try apply h
    intro t h
    cases t <;> simp [ih]

end Total

end Gen
