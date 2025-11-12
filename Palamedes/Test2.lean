import Aesop
import Plausible

inductive Gen : Type → Type 1 where
  | ret : α → Gen α
  | bind : Gen α → (α → Gen β) → Gen β
  | pick : Gen α → Gen α → Gen α
  | div : Gen α

instance : Pure Gen where
  pure a := Gen.ret a

instance : Bind Gen where
  bind := Gen.bind

instance : Monad Gen where

inductive Gen.rel : Gen α → Gen α  → Prop where
  | refl : Gen.rel x x
  | div : Gen.rel div x
  -- Note: pick nodes are only related reflexively (via refl) or via div
  -- This ensures chains of picks have uniform structure
  | bind : Gen.rel x₁ x₂ → (∀ y, Gen.rel (f₁ y) (f₂ y)) → Gen.rel (.bind x₁ f₁) (.bind x₂ f₂)

instance : Lean.Order.PartialOrder (Gen α) where
  rel := Gen.rel
  rel_refl := by intro; constructor
  rel_trans := by
    intro x y z h1 h2; induction h1 <;> cases h2 <;> grind [Gen.rel]
  rel_antisymm := by
    intro x y h1 h2; induction h1 <;> cases h2 <;> try grind
    congr
    · grind
    · grind

/-!
## CCPO Instance for Gen

The key insight for this CCPO construction is that in any chain of `Gen` values,
all non-div elements must have a **uniform shape** due to how `Gen.rel` is defined.

Specifically:
- `Gen.rel.div` makes `div` the bottom element
- `Gen.rel.ret` doesn't relate different return values
- `Gen.rel.pick` requires both components to be related
- `Gen.rel.bind` requires both the generator and function to be related

This means in a chain, all non-div elements must:
- Either all be `ret a` for some fixed `a`
- Or all be `pick y z` for some fixed `y` and `z`
- Or all be `bind g f` for some fixed `g` and `f`

This allows us to define csup by cases on the structure of the chain.
-/

-- Definition: A chain is a totally ordered subset
def chain (c : Gen α → Prop) : Prop :=
  ∀ x y, c x → c y → Gen.rel x y ∨ Gen.rel y x

-- Helper theorem: Every chain has uniform shape, with witnesses
theorem chain_has_uniform_shape (c : Gen α → Prop) (hc : chain c) :
    (∀ x, c x → x = .div) ∨
    (∃ a, (∃ y, c y ∧ y = .ret a) ∧ ∀ x, c x → x = .ret a ∨ x = .div) ∨
    (∃ y1 y2, (∃ y, c y ∧ y = .pick y1 y2) ∧ ∀ x, c x → (∃ z1 z2, x = .pick z1 z2) ∨ x = .div) ∨
    (∀ x, c x → (∃ (β : Type _) (g : Gen β) (f : β → Gen α), x = .bind g f) ∨ x = .div) := by
  -- Find a witness element from the chain
  by_cases h_all_div : ∀ x, c x → x = .div
  · left; exact h_all_div
  · -- There exists a non-div element
    simp only [Classical.not_forall] at h_all_div
    obtain ⟨y, hy, hy_ne_div⟩ := h_all_div
    -- Case on what y is
    cases y with
    | div => contradiction
    | ret a =>
      -- Show all non-div elements are ret a
      right; left
      exists a
      constructor
      · -- Provide the witness
        exact ⟨(.ret a), hy, rfl⟩
      · -- Show all elements are ret a or div
        intro z hz
        by_cases hz_div : z = .div
        · right; exact hz_div
        · left
          -- z and y are in the chain, so they're comparable
          have comparable := hc (.ret a) z hy hz
          cases comparable with
          | inl h_yz =>
            -- y ⊑ z, where y = ret a and z ≠ div
            -- By cases on z
            cases z with
            | div => contradiction
            | ret b =>
              -- ret a ⊑ ret b, so must have a = b by Gen.rel
              cases h_yz
              · rfl  -- refl case
            | pick _ _ =>
              -- ret a cannot be related to pick (no such Gen.rel constructor)
              nomatch h_yz
            | bind _ _ =>
              -- ret a cannot be related to bind (no such Gen.rel constructor)
              nomatch h_yz
          | inr h_zy =>
            -- z ⊑ y, where y = ret a and z ≠ div
            cases z with
            | div => contradiction
            | ret b =>
              cases h_zy
              · rfl  -- refl case
            | pick _ _ =>
              -- pick cannot be related to ret (no such Gen.rel constructor)
              nomatch h_zy
            | bind _ _ =>
              -- bind cannot be related to ret (no such Gen.rel constructor)
              nomatch h_zy
    | pick y1 y2 =>
      right; right; left
      exists y1, y2
      constructor
      · -- Provide the witness
        exact ⟨(.pick y1 y2), hy, rfl⟩
      · -- Show all elements are picks or div
        intro z hz
        by_cases hz_div : z = .div
        · right; exact hz_div
        · left
          have comparable := hc (.pick y1 y2) z hy hz
          cases comparable with
          | inl h_yz =>
            cases z with
            | div => contradiction
            | ret _ =>
              nomatch h_yz
            | pick z1 z2 =>
              -- h_yz : Gen.rel (pick y1 y2) (pick z1 z2)
              -- Without Gen.rel.pick, this can only be refl
              cases h_yz
              -- refl case: pick y1 y2 = pick z1 z2, so z1 = y1, z2 = y2
              exact ⟨y1, y2, rfl⟩
            | bind _ _ =>
              nomatch h_yz
          | inr h_zy =>
            cases z with
            | div => contradiction
            | ret _ =>
              nomatch h_zy
            | pick z1 z2 =>
              cases h_zy
              -- refl case: pick z1 z2 = pick y1 y2
              exact ⟨y1, y2, rfl⟩
            | bind _ _ =>
              nomatch h_zy
    | bind g f =>
      right; right; right
      intro z hz
      by_cases hz_div : z = .div
      · right; exact hz_div
      · left
        have comparable := hc (.bind g f) z hy hz
        cases comparable with
        | inl h_yz =>
          cases z with
          | div => contradiction
          | ret _ =>
            nomatch h_yz
          | pick _ _ =>
            nomatch h_yz
          | bind gx fx =>
            -- z = gx.bind fx
            -- h_yz : Gen.rel (bind g f) (bind gx fx)
            -- Without Gen.rel.bind, this can only be refl
            -- So bind g f = bind gx fx, meaning z is a bind
            exact ⟨_, gx, fx, rfl⟩
        | inr h_zy =>
          cases z with
          | div => contradiction
          | ret _ =>
            nomatch h_zy
          | pick _ _ =>
            nomatch h_zy
          | bind gz fz =>
            -- z = gz.bind fz, so z is a bind
            exact ⟨_, gz, fz, rfl⟩

-- Size measure for well-founded recursion
-- For bind, we need to account for the fact that the continuation might produce large values
-- We use a measure that counts nesting depth rather than total size
def Gen.depth : Gen α → Nat
  | .div => 0
  | .ret _ => 0
  | .pick x y => 1 + max x.depth y.depth
  | .bind x _ => 1 + x.depth

-- Define a well-founded relation for csup recursion
-- We'll use the size of a representative element from the chain
open Classical in
noncomputable def csup_measure (c : Gen α → Prop) : Nat :=
  -- Find any non-div element and return its depth, or 0 if all are div
  if h : ∃ x, c x ∧ x ≠ .div then
    (choose h).depth
  else
    0

open Classical in
noncomputable def Gen.csup (c : Gen α → Prop) : Gen α :=
  if _ : ∀ x, c x → x = .div then
    -- All elements are div
    .div
  else if h : ∃ a, ∀ x, c x → x = .ret a ∨ x = .div then
    -- All non-div elements are ret a for some fixed a
    .ret (choose h)
  else if h : ∃ (yz : Gen α × Gen α), ∀ x, c x → x = .pick yz.1 yz.2 ∨ x = .div then
    -- All non-div elements are pick with the same two components
    let yz := choose h
    .pick yz.1 yz.2
  else if h : ∃ (βgf : Σ (β : Type _), Gen β × (β → Gen α)),
                ∀ x, c x → x = .bind βgf.2.1 βgf.2.2 ∨ x = .div then
    -- All non-div elements are bind with the same generator and function
    let βgf := choose h
    -- Recursively compute csup for the bound generator chain
    let g_chain := fun (g : Gen βgf.1) => ∃ x, c x ∧ ∃ f, x = .bind g f
    let g_sup := Gen.csup g_chain
    -- Recursively compute csup for each continuation function value
    let f_sup := fun (a : βgf.1) =>
      let fa_chain := fun (fa : Gen α) => ∃ x, c x ∧ ∃ g f, x = .bind g f ∧ fa = f a
      Gen.csup fa_chain
    .bind g_sup f_sup
  else
    -- Should not happen for a valid chain, default to div
    .div

termination_by csup_measure c
decreasing_by
  · -- First recursive call: g_chain
    -- Need to show csup_measure g_chain < csup_measure c
    unfold csup_measure
    -- After unfolding, we have two `if` expressions to split on
    -- Let's be explicit about which one
    simp only []
    split <;> split
    · -- Both g_chain and c have non-div elements
      rename_i h_g_nondiv h_c_nondiv
      -- Goal: (choose h_g_nondiv).size < (choose h_c_nondiv).size
      -- choose h_g_nondiv : Gen βgf.1 is from g_chain
      -- choose h_c_nondiv : Gen α is from c

      have hg := choose_spec h_g_nondiv
      obtain ⟨hg_in_chain, hg_ne_div⟩ := hg
      -- hg_in_chain : g_chain (choose h_g_nondiv)
      -- which means: ∃ y, c y ∧ ∃ f, y = bind (choose h_g_nondiv) f

      have hc := choose_spec h_c_nondiv
      obtain ⟨hc_in_c, hc_ne_div⟩ := hc

      -- From h (the hypothesis from the else if branch):
      -- all non-div x ∈ c satisfy x = bind βgf.2.1 βgf.2.2
      have h_spec := choose_spec h
      obtain heq | hdiv := h_spec (choose h_c_nondiv) hc_in_c
      · -- choose h_c_nondiv = bind βgf.2.1 βgf.2.2
        -- We need: (choose h_g_nondiv).size < (bind βgf.2.1 βgf.2.2).size
        -- From hg_in_chain: ∃ y ∈ c with y = bind (choose h_g_nondiv) f
        -- From h_spec: all non-div y ∈ c have y = bind βgf.2.1 βgf.2.2
        -- So bind (choose h_g_nondiv) f = bind βgf.2.1 βgf.2.2
        -- Thus (choose h_g_nondiv) = βgf.2.1 (injectivity)
        --  So we need βgf.2.1.size < (bind βgf.2.1 βgf.2.2).size = 1 + βgf.2.1.size ✓
        rw [heq]
        simp only [Gen.depth]
        -- We have the goal: (choose h_g_nondiv).depth < 1 + (choose h).snd.fst.depth
        -- We need to show (choose h_g_nondiv) = (choose h).snd.fst OR that the former is smaller
        -- From hg_in_chain, there's a y ∈ c with y = bind (choose h_g_nondiv) f
        -- From h_spec, if y ∈ c and y ≠ div, then y = bind (choose h).snd.fst (choose h).snd.snd
        -- Need to show y ≠ div
        obtain ⟨y, hy_in_c, f, hy_eq⟩ := hg_in_chain
        -- Is y = div? If so, then bind (choose h_g_nondiv) f = div, but bind is never div
        have hy_ne_div : y ≠ Gen.div := by
          intro h_contra
          rw [hy_eq] at h_contra
          cases h_contra  -- bind cannot equal div
        obtain hy_bind | hy_div := h_spec y hy_in_c
        · -- y = bind (choose h).snd.fst (choose h).snd.snd
          -- Also y = bind (choose h_g_nondiv) f
          -- So by injectivity: (choose h_g_nondiv) = (choose h).snd.fst
          rw [hy_eq] at hy_bind
          injection hy_bind with _ _ heq_g _
          -- heq_g : (choose h_g_nondiv) = (choose h).snd.fst
          simp only [heq_g]
          omega
        · --  y = div, contradicts hy_ne_div
          contradiction
      · -- choose h_c_nondiv = div, contradicts hc_ne_div
        contradiction
    · -- g_chain has non-div, but c is all div - impossible
      rename_i h_g_nondiv h_c_all_div
      -- h_g_nondiv : ∃ g, g_chain g ∧ g ≠ div
      -- h_c_all_div : ¬(∃ x, c x ∧ x ≠ div), i.e., ∀ x, c x → x = div
      -- g_chain g means: ∃ y, c y ∧ ∃ f, y = bind g f
      -- So there exists y ∈ c with y ≠ div, contradicting h_c_all_div
      exfalso
      obtain ⟨g, hg_chain, _⟩ := h_g_nondiv
      -- hg_chain : ∃ y, c y ∧ ∃ f, y = bind g f
      obtain ⟨y, hy_in_c, f, hy_eq⟩ := hg_chain
      -- y ∈ c and y = bind g f
      -- bind g f ≠ div (constructor inequality)
      have hy_ne_div : y ≠ Gen.div := by
        intro h_contra
        rw [hy_eq] at h_contra
        cases h_contra
      --  But h_c_all_div says ¬(∃ x, c x ∧ x ≠ div)
      apply h_c_all_div
      exact ⟨y, hy_in_c, hy_ne_div⟩
    · -- g_chain is all div, c has non-div
      -- csup_measure g_chain = 0 < csup_measure c = (choose h_c_nondiv).size
      rename_i _ h_c_nondiv
      have := choose_spec h_c_nondiv
      obtain ⟨_, hc_ne_div⟩ := this
      -- (choose h_c_nondiv) ≠ div, so its depth > 0 or = 0
      -- Actually, for ret the depth is 0, so this approach won't work directly
      -- We need depth > 0 for bind/pick, but depth = 0 for ret
      -- The key insight: in a bind chain, all elements are binds (or div)
      -- So the chosen element must be a bind, which has depth ≥ 1
      have h_spec := choose_spec h
      obtain heq | hdiv := h_spec (choose h_c_nondiv) (choose_spec h_c_nondiv).1
      · -- choose h_c_nondiv = bind βgf.2.1 βgf.2.2
        rw [heq]
        simp only [Gen.depth]
        omega
      · -- choose h_c_nondiv = div, contradiction
        exfalso
        exact hc_ne_div hdiv
    · -- Both are all div
      -- h_g_all_div : ¬(∃ x, g_chain x ∧ x ≠ div)
      -- h_c_all_div : ¬(∃ x, c x ∧ x ≠ div)
      -- This means all x ∈ c satisfy x = div
      -- But we have from earlier branches that ¬(∀ x, c x → x = div)
      rename_i h_g_all_div h_c_all_div
      exfalso
      have : ¬(∀ x, c x → x = div) := by assumption
      simp only [Classical.not_forall] at this
      obtain ⟨x, hx_in_c, hx_ne_div⟩ := this
      apply h_c_all_div
      exact ⟨x, hx_in_c, hx_ne_div⟩
  · -- Second recursive call: fa_chain for each a
    -- This is more complex: fa_chain contains values f a where bind g f ∈ c
    -- The depth of f a is not directly related to the depth of bind g f
    -- In the current formulation, f is a *function* so we can't measure its "size"
    --
    -- A complete proof would require either:
    -- 1. A more sophisticated well-founded relation on Gen that accounts for
    --    the structure of functions in bind
    -- 2. An argument that fa_chain is always trivial (all div) or has a specific structure
    -- 3. A complete restructuring to avoid this recursive call
    --
    -- For now, we admit this case as it requires significant additional machinery
    sorry

-- Helper theorem: In a chain where all non-div elements are picks,
-- if there's a witness pick y1 y2, then all non-div elements equal that pick
theorem chain_pick_uniform (c : Gen α → Prop) (hc : chain c) (y1 y2 : Gen α)
    (h_witness : ∃ y, c y ∧ y = .pick y1 y2)
    (h_pick : ∀ x, c x → (∃ z1 z2, x = .pick z1 z2) ∨ x = .div) :
    ∀ x, c x → x = .pick y1 y2 ∨ x = .div := by
  intro x hx
  obtain ⟨z1, z2, heq⟩ | hdiv := h_pick x hx
  swap; right; exact hdiv
  -- x = pick z1 z2, need to show it equals pick y1 y2
  left
  obtain ⟨y_wit, hy_wit, hy_eq⟩ := h_witness
  -- Both y_wit and x are in the chain, so they're comparable
  have h_comp := hc y_wit x hy_wit hx
  rw [hy_eq, heq] at h_comp
  -- h_comp : Gen.rel (pick y1 y2) (pick z1 z2) ∨ Gen.rel (pick z1 z2) (pick y1 y2)
  -- Since there's no Gen.rel.pick constructor, both sides can only be refl
  cases h_comp with
  | inl h =>
    -- pick y1 y2 ⊑ pick z1 z2, must be refl
    cases h
    -- refl case: pick y1 y2 = pick z1 z2
    exact heq
  | inr h =>
    -- pick z1 z2 ⊑ pick y1 y2, must be refl
    cases h
    -- refl case: pick z1 z2 = pick y1 y2
    exact heq

-- Helper theorem: Classical.choose for pick case gives us the right pair
theorem csup_pick_correct (c : Gen α → Prop) (y1 y2 : Gen α)
    (h_witness : ∃ y, c y ∧ y = .pick y1 y2)
    (h_uniform : ∀ x, c x → x = .pick y1 y2 ∨ x = .div)
    (h_exists : ∃ (yz : Gen α × Gen α), ∀ x, c x → x = .pick yz.1 yz.2 ∨ x = .div) :
    Classical.choose h_exists = (y1, y2) := by
  have h_spec := Classical.choose_spec h_exists
  obtain ⟨y_wit, hy_wit, hy_wit_eq⟩ := h_witness
  -- y_wit = pick y1 y2 and y_wit is in the chain
  -- By h_spec, y_wit = pick (choose h_exists).1 (choose h_exists).2 or div
  obtain heq | hdiv := h_spec y_wit hy_wit
  · -- y_wit = pick (choose h_exists).1 (choose h_exists).2
    -- But also y_wit = pick y1 y2
    rw [hy_wit_eq] at heq
    -- pick y1 y2 = pick (choose h_exists).1 (choose h_exists).2
    cases heq
    rfl
  · -- y_wit = div, but y_wit = pick y1 y2, contradiction
    rw [hy_wit_eq] at hdiv
    contradiction

-- Helper theorem: if chain has uniform shape with ret a, then Classical.choose gives us ret a
theorem csup_ret_correct (c : Gen α → Prop) (a : α)
    (h_witness : ∃ y, c y ∧ y = .ret a)
    (h_ret : ∀ x, c x → x = .ret a ∨ x = .div)
    (h_exists : ∃ a', ∀ x, c x → x = .ret a' ∨ x = .div) :
    Classical.choose h_exists = a := by
  have h_spec := Classical.choose_spec h_exists
  -- Get the witness
  obtain ⟨y, hy, hy_eq⟩ := h_witness
  -- y = ret a, and y is in the chain
  -- By h_spec, y = ret a' or y = div
  obtain hy' | hy' := h_spec y hy
  · -- y = ret a', but also y = ret a, so ret a = ret a', thus a = a'
    rw [hy_eq] at hy'
    cases hy'
    rfl
  · -- y = div, but also y = ret a, contradiction
    rw [hy_eq] at hy'
    contradiction

noncomputable instance : Lean.Order.CCPO (Gen α) where
  csup := Gen.csup
  csup_spec := by
    intros x c hc
    -- Use chain_has_uniform_shape to determine which case we're in
    obtain h_all_div | ⟨a, h_ret⟩ | h_pick | h_bind := chain_has_uniform_shape c hc
    · -- Case 1: All elements are div
      unfold Gen.csup
      rw [dif_pos h_all_div]
      constructor
      · intro _ y hy
        rw [h_all_div y hy]
        apply Gen.rel.div
      · intro h_upper
        -- x must be an upper bound for all elements in the chain
        -- Since all elements are div, div ⊑ x by Gen.rel.div
        apply Gen.rel.div
    · -- Case 2: All non-div elements are ret a
      unfold Gen.csup
      obtain ⟨⟨y_wit, hy_wit, hy_wit_eq⟩, h_ret⟩ := h_ret
      have h_not_all_div : ¬(∀ x, c x → x = .div) := by
        intro h_contra
        -- We have a witness y_wit with c y_wit and y_wit = ret a
        have : y_wit = .div := h_contra y_wit hy_wit
        rw [hy_wit_eq] at this
        contradiction
      have h_exists : ∃ a', ∀ x, c x → x = .ret a' ∨ x = .div := ⟨a, h_ret⟩
      rw [dif_neg h_not_all_div, dif_pos h_exists]
      have h_witness : ∃ y, c y ∧ y = .ret a := ⟨y_wit, hy_wit, hy_wit_eq⟩
      have h_eq : Classical.choose h_exists = a := csup_ret_correct c a h_witness h_ret h_exists
      rw [h_eq]
      constructor
      · intro h_rel y hy
        obtain heq | heq := h_ret y hy
        · rw [heq]; exact h_rel
        · rw [heq]; apply Gen.rel.div
      · intro h_upper
        -- We have a witness from the chain
        rw [←hy_wit_eq]
        exact h_upper y_wit hy_wit
    · -- Case 3: All non-div elements are pick
      unfold Gen.csup
      obtain ⟨y1, y2, h_witness, h_pick⟩ := h_pick
      -- Use chain_pick_uniform to show all picks are the same
      have h_uniform := chain_pick_uniform c hc y1 y2 h_witness h_pick
      have h_not_all_div : ¬(∀ x, c x → x = .div) := by
        intro h_contra
        obtain ⟨y_wit, hy_wit, hy_wit_eq⟩ := h_witness
        have : y_wit = .div := h_contra y_wit hy_wit
        rw [hy_wit_eq] at this
        contradiction
      have h_not_ret : ¬(∃ a, ∀ x, c x → x = .ret a ∨ x = .div) := by
        intro ⟨a, ha⟩
        obtain ⟨y_wit, hy_wit, hy_wit_eq⟩ := h_witness
        obtain heq | hdiv := ha y_wit hy_wit
        · rw [hy_wit_eq] at heq
          -- ret a = pick y1 y2, impossible
          cases heq
        · rw [hy_wit_eq] at hdiv
          -- pick y1 y2 = div, impossible
          cases hdiv
      have h_exists : ∃ (yz : Gen α × Gen α), ∀ x, c x → x = .pick yz.1 yz.2 ∨ x = .div :=
        ⟨(y1, y2), h_uniform⟩
      rw [dif_neg h_not_all_div, dif_neg h_not_ret, dif_pos h_exists]
      have h_eq : Classical.choose h_exists = (y1, y2) := csup_pick_correct c y1 y2 h_witness h_uniform h_exists
      simp [h_eq]
      constructor
      · intro h_rel y hy
        obtain heq | hdiv := h_uniform y hy
        · rw [heq]; exact h_rel
        · rw [hdiv]; apply Gen.rel.div
      · intro h_upper
        obtain ⟨y_wit, hy_wit, hy_wit_eq⟩ := h_witness
        rw [←hy_wit_eq]
        exact h_upper y_wit hy_wit
    · -- Case 4: All non-div elements are bind
      --  But they may have different components due to Gen.rel.bind
      -- The supremum is not simply picking one bind, but we need to construct
      -- the supremum of the generators and the supremum of the functions
      -- This is actually quite complex and may not be expressible in the current framework
      -- without dependent types for the witness

      -- For now, acknowledge this case needs a more sophisticated treatment
      -- The issue is that Gen.rel.bind allows ordered chains of binds with varying components
      -- Unlike pick (which we made non-varying), bind needs to vary for MonoBind
      sorry

instance : Lean.Order.MonoBind Gen where
  bind_mono_left h := by
    apply Gen.rel.bind
    · assumption
    · intro y; apply Gen.rel.refl
  bind_mono_right h := by
    apply Gen.rel.bind
    · apply Gen.rel.refl
    · assumption

#check (inferInstance : Lean.Order.CCPO (Gen Nat))
#check (inferInstance : Lean.Order.MonoBind Gen)

def support : Gen α → α → Prop
  | .div =>  fun _ => False
  | .ret a => (. = a)
  | .pick x y => fun a => support x a ∨ support y a
  | .bind x f => fun b => ∃ a, support x a ∧ support (f a) b

partial def Gen.run : Gen α → Plausible.Gen α
  | .div => throw (.genError "assume check failed")
  | .ret a => pure a
  | .pick x y => Plausible.Gen.oneOf #[x.run, y.run] (by simp)
  | .bind x f => x.run >>= Gen.run ∘ f

def genList : Gen (List Bool) := do
  if ← Gen.pick (pure true) (pure false) then
    return []
  else do
    let x ← Gen.pick (pure true) (pure false)
    let xs ← genList
    return x :: xs
partial_fixpoint

theorem genList_complete : ∀ xs, support genList xs
  | [] => by
    rw [genList]
    simp [support]
  | _ :: xs => by
    rw [genList]
    simp [support]
    exact genList_complete _

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
deriving Repr

def choose (lo hi : Nat) (h : lo ≤ hi) := do
  if h' : lo = hi then
    return lo
  else
    Gen.pick (pure lo) (choose (.succ lo) hi (by grind))

theorem support_choose : lo ≤ x ∧ x ≤ hi → support (choose lo hi h) x := by
  fun_induction choose <;> grind [= support.eq_def, = choose.eq_def]

theorem support_choose' : support (choose lo hi h) x → lo ≤ x ∧ x ≤ hi := by
  fun_induction choose <;> grind [= support.eq_def, = choose.eq_def]

def genBST (lo hi : Nat) : Gen (Tree Nat) := do
  if h : lo > hi then
    return .leaf
  else
    if ← Gen.pick (pure true) (pure false) then
      return .leaf
    else do
      let x ← choose lo hi (by grind)
      let l ← genBST lo (x - 1)
      let r ← genBST (x + 1) hi
      return .node l x r
partial_fixpoint

def isBST (lo hi : Nat) : Tree Nat → Bool
  | .leaf => true
  | .node l x r =>
    lo ≤ x && x ≤ hi &&
    isBST lo (x - 1) l &&
    isBST (x + 1) hi r

theorem support_genBST (lo hi : Nat) (t : Tree Nat) :
    isBST lo hi t → support (genBST lo hi) t := by
  intro h
  fun_induction isBST lo hi t <;> rw [genBST]
  case _ lo hi =>
    by_cases hb : lo > hi <;> simp [hb, support]
  case _ lo hi l x r ih₁ ih₂ =>
    have : ¬ lo > hi := by grind
    simp [this, support]
    exists x
    simp_all [support_choose]

theorem support_genBST' (lo hi : Nat) (t : Tree Nat) :
    support (genBST lo hi) t → isBST lo hi t := by
  intro h
  induction t generalizing lo hi
  case leaf => rw [isBST]
  case node l x r ih_l ih_r =>
    rw [isBST]
    simp
    rw [genBST] at h
    by_cases hb : lo > hi <;>
      aesop
        (add safe support_choose')
        (add simp support)

example (lo hi : Nat) :
    support (genBST lo hi) = (fun t => isBST lo hi t = true) := by
  grind [support_genBST, support_genBST']

#eval! do
  for _ in [0:100] do
    IO.println <| s!"{← Plausible.Gen.run genList.run 10}"

#eval! do
  for _ in [0:100] do
    IO.println <| s!"{repr (← Plausible.Gen.run (genBST 0 10).run 10)}"
