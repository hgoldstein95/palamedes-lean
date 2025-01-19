import Aesop

inductive Gen : Type → Type 1 where
  | ret : α → Gen α
  | bind : Gen α → (α → Gen β) → Gen β
  | pick : (w : Nat × Nat) → Gen α → Gen α → Gen α
  | choose : (lo : Nat) → (hi : Nat) → lo ≤ hi → Gen Nat
  | sized : (Nat → Gen (Option α)) → Gen α
  | guardIn : (P : Prop) → Decidable P → (P → Gen α) → Gen α

-- def optBind : Gen α → (α → Gen β) → Gen β
--   | .ret v, f => f v
--   | .bind x g, f => .bind x (λ y => optBind (g y) f)
--   | .guardIn P inst g, f => .guardIn P inst (λ h => optBind (g h) f)
--   | x, f => .bind x f

@[simp]
def genMeasure : Gen α → Nat
  | .guardIn P _ f => if hp : P then 1 + genMeasure (f hp) else 0
  | _ => 0

instance : Monad Gen where
  pure := .ret
  bind := .bind

def pick (x y : Gen α) : Gen α := .pick (1, 1) x y

def wpick (w : Nat × Nat) (x y : Gen α) : Gen α := .pick w x y

def choose (lo hi : Nat) (h : lo ≤ hi := by simp) : Gen Nat :=
  .choose lo hi h
