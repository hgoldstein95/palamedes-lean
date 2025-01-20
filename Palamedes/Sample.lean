import Palamedes.Free
import Plausible.Random

def replicateM [Monad m] (n : Nat) (mx : m α) : m (List α) :=
  match n with
  | 0 => pure []
  | n + 1 => do
    let x ← mx
    let xs ← replicateM n mx
    pure (x :: xs)

mutual
partial def sampleSized (tries : Nat) (n : Nat) (f : Nat → Gen (Option α)) : Plausible.RandT IO α := do
  -- match (← sampleRand (f n)) with
  -- | .none => sampleSized (2 * n) f
  -- | .some v => pure v
  match (← sampleRand (f n)) with
  | .none =>
    if tries == 0
      then StateT.lift (throw (IO.userError "ran out of fuel"))
      else sampleSized (tries - 1) n f
  | .some v => pure v

partial def sampleRand : Gen α → Plausible.RandT IO α
  | .ret v' => pure v'
  | .pick (w₁, w₂) x y =>
    Plausible.Random.randBound Nat 0 (w₁ + w₁ - 1) (by simp) >>= λ ⟨b, _⟩ =>
      if b < w₁ then sampleRand (x ()) else sampleRand (y ())
  | .choose lo hi pf => Plausible.Random.randBound Nat lo hi pf
  | .sized f => sampleSized 10 100 f
  | .bind x f => sampleRand (x ()) >>= sampleRand ∘ f
  | .guardIn p _ f =>
    if h : p
      then sampleRand (f h)
      else StateT.lift (throw (IO.userError "failed to generate value"))
end

partial def sample : Gen α → IO α := Plausible.runRand ∘ sampleRand

partial def sampleN (n : Nat) : Gen α → IO (List α) := replicateM n ∘ Plausible.runRand ∘ sampleRand
