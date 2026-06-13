import Palamedes.Gen
import Palamedes.OptimizeCongr

open Gen

theorem support_assume_pick :
    support (if h : b then pick (x h) y else y) = support (pick (assume b x) y) := by
  aesop

theorem support_pick_assume :
    support (if h : b then pick x (y h) else x) = support (pick x (assume b y)) := by
  aesop

theorem support_assume_bind :
    support (assume b (fun h => x h >>= f)) = support (assume b x >>= f) := by
  aesop

theorem support_pick_bind :
    support (pick (x >>= f) (y >>= f)) = support (pick x y >>= f) := by
  aesop

theorem support_if_bind
    {x : b = true → Gen α}
    {y : ¬ (b = true) → Gen α} :
    support (if h : b then x h >>= f else y h >>= f) = support ((if h : b then x h else y h) >>= f) := by
  aesop

theorem support_pure_bind :
    support (pure a >>= f) = support (f a) := by
  aesop

theorem support_bind_bind :
    support ((x >>= f) >>= g) = support (x >>= (fun a => f a >>= g)) := by
  aesop

@[gen_congr]
theorem support_bind_congr
    (hx : support x = support x')
    (hf : ∀ {a}, support (f a) = support (f' a)) :
    support (x >>= f) = support (x' >>= f') := by
  aesop

@[gen_congr]
theorem support_pick_congr
    (hx : support x = support x')
    (hy : support y = support y') :
    support (pick x y) = support (pick x' y') := by
  aesop

@[gen_congr]
theorem support_if_congr
    {P : Prop}
    [Decidable P]
    {x x' : P → Gen α}
    {y y' : ¬ P → Gen α}
    (hx : ∀ {h}, support (x h) = support (x' h))
    (hy : ∀ {h}, support (y h) = support (y' h)) :
    support (if h : P then x h else y h) = support (if h : P then x' h else y' h) := by
  aesop

/-- Non-dependent `if`-congruence. The dependent twin (`support_if_congr`) does not cover the plain
`ite` nodes the optimizer produces via `support_ite_bind`, so without this the optimizer could not
descend into `ite` branches. -/
@[gen_congr]
theorem support_ite_congr
    {P : Prop}
    [Decidable P]
    {x x' y y' : Gen α}
    (hx : support x = support x')
    (hy : support y = support y') :
    support (if P then x else y) = support (if P then x' else y') := by
  split <;> simp_all

@[gen_congr]
theorem support_assume_congr
    {f f' : b = true → Gen α}
    (hf : ∀ h, support (f h) = support (f' h)) :
    support (assume b f) = support (assume b f') := by
  aesop

@[gen_congr]
theorem support_indexed_congr
    {f f' : Nat → Gen (Option α)}
    (hf : ∀ n, support (f n) = support (f' n)) :
    support (indexed f) = support (indexed f') := by
  simp only [Gen.Support.support_indexed, hf]

theorem support_ite_bind
    {P : Prop} [Decidable P] {a b : Gen α} {f : α → Gen β} :
    support ((if P then a else b) >>= f) = support (if P then a >>= f else b >>= f) := by
  split <;> rfl

theorem support_bind_assume
    {x : Gen α} {b : Bool} {g : α → b = true → Gen β} :
    support (x >>= fun a => assume b (g a))
      = support (assume b fun h => x >>= fun a => g a h) := by
  aesop

theorem support_pick_assume_same
    {b : Bool} {f g : b = true → Gen α} :
    support (pick (assume b f) (assume b g))
      = support (assume b fun h => pick (f h) (g h)) := by
  aesop
