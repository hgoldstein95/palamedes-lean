import Palamedes.Gen

open Gen

theorem support_assume_pick :
    support (if h : b then pick l (x h) r y else y) = support (pick l (assume b x) r y) := by
  aesop

theorem support_pick_assume :
    support (if h : b then pick l x r (y h) else x) = support (pick l x r (assume b y)) := by
  aesop

theorem support_assume_bind :
    support (assume b (fun h => x h >>= f)) = support (assume b x >>= f) := by
  aesop

theorem support_pick_bind :
    support (pick l (x >>= f) r (y >>= f)) = support (pick l x r y >>= f) := by
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

theorem support_bind_congr
    (hx : support x = support x')
    (hf : ∀ {a}, support (f a) = support (f' a)) :
    support (x >>= f) = support (x' >>= f') := by
  aesop

theorem support_pick_congr
    (hx : support x = support x')
    (hy : support y = support y') :
    support (pick x y w) = support (pick x' y' w) := by
  aesop

theorem support_if_congr
    {P : Prop}
    [Decidable P]
    {x x' : P → Gen α}
    {y y' : ¬ P → Gen α}
    (hx : ∀ {h}, support (x h) = support (x' h))
    (hy : ∀ {h}, support (y h) = support (y' h)) :
    support (if h : P then x h else y h) = support (if h : P then x' h else y' h) := by
  aesop

theorem support_assume_congr :
    (assume b f).support = (f h).support := by
  aesop
