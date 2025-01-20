import Aesop

inductive Gen : Type → Type 1 where
  | ret : α → Gen α
  | bind : (Unit → Gen α) → (α → Gen β) → Gen β
  | pick : (w : Nat × Nat) → (Unit → Gen α) → (Unit → Gen α) → Gen α
  | choose : (lo : Nat) → (hi : Nat) → lo ≤ hi → Gen Nat
  | sized : (Nat → Gen (Option α)) → Gen α
  | guardIn : (P : Prop) → Decidable P → (P → Gen α) → Gen α

def optBind : Gen α → (α → Gen β) → Gen β
  | .ret v, f => f v
  | .bind x g, f => .bind x (λ y => optBind (g y) f)
  | .guardIn P inst g, f => .guardIn P inst (λ h => optBind (g h) f)
  | x, f => .bind (λ () => x) f

@[simp]
def genMeasure : Gen α → Nat
  | .guardIn P _ f => if hp : P then 1 + genMeasure (f hp) else 0
  | _ => 0

def optPick (w : Nat × Nat) : Gen α → Gen α → Gen α
  | .guardIn P _ f, y => if h : P then optPick w (f h) y else y
  | x, .guardIn Q _ g => if h : Q then optPick w x (g h) else x
  | x, y => .pick w (λ () => x) (λ () => y)
  termination_by x y => genMeasure x + genMeasure y
  decreasing_by
    . by_cases P
      . simp_all [ite]
      . contradiction
    . by_cases Q
      . simp_all [ite]
      . contradiction

instance : Monad Gen where
  pure := .ret
  bind := optBind

def pick (x y : Gen α) : Gen α := optPick (1, 1) x y

def wpick (w : Nat × Nat) (x y : Gen α) : Gen α := optPick w x y

def choose (lo hi : Nat) (h : lo ≤ hi := by simp) : Gen Nat :=
  .choose lo hi h
