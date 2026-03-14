import Palamedes.Synthesizer

open Gen CorrectGen

def genOneOrInRange (lo hi : Nat) : Gen Nat :=
  if h : decide (lo <= hi) = true then
    pick (pure 0) (choose lo hi (s_between_partial._proof_1 h))
  else
    pure 0

/-
Differences:
- Simplify proof for choose.
-/
def genOneOrInRange_manual (lo hi : Nat) : Gen Nat :=
  if h : lo <= hi then
    pick (pure 0) (choose lo hi (by omega))
  else
    pure 0

def genCompleteTree (n : Nat) : Gen (Tree Nat) :=
  Tree.unfold
    (fun x =>
      if x.snd = 0 then pure TreeF.leaf
      else do
        let a <- arbNat
        pure (TreeF.node ((), x.2 - 1) a ((), x.2 - 1)))
    ((), n)

/-
Differences:
- Remove extra unit in collector.
-/
def genComplete_manual (n : Nat) : Gen (Tree Nat) :=
  Tree.unfold
    (fun height =>
      if height = 0 then
        pure TreeF.leaf
      else do
        let a <- arbNat
        pure (TreeF.node (height - 1) a (height - 1)))
    n

def genSortedBetween (lo hi : Nat) : Gen (List Nat) :=
  List.unfold
    (fun x =>
      if h : decide (x.snd.fst <= x.snd.snd) = true then
        pick (pure ListF.nil) do
          let a <- choose x.2.1 x.2.2 (s_between_partial._proof_1 h)
          pure (ListF.cons a (PUnit.unit, a, x.2.2))
      else
        pure ListF.nil)
    (PUnit.unit, lo, hi)

/-
Differences:
- Simplify proof for choose.
- Remove extra unit in collector.
-/
def genSortedBetween_manual (lo hi : Nat) : Gen (List Nat) :=
  List.unfold
    (fun (lo, hi) =>
      if h : lo <= hi then
        pick
          (pure ListF.nil)
          (do
            let a <- choose lo hi (by omega)
            pure (ListF.cons a (a, hi)))
      else
        pure ListF.nil)
    (lo, hi)

def genLengthKAllTwos (k : Nat): Gen (List Nat) :=
  List.unfold
    (fun x =>
      if x.fst.fst = 0 then pure ListF.nil
      else pure (ListF.cons 2 ((Nat.pred x.1.1, PUnit.unit), PUnit.unit, PUnit.unit)))
    ((k, PUnit.unit), PUnit.unit, PUnit.unit)

/-
Differences:
- Remove two extra units in collector.
-/
def genLengthKAllTwos_manual (k : Nat): Gen (List Nat) :=
  List.unfold
    (fun len =>
      if len = 0 then
        pure ListF.nil
      else
        pure (ListF.cons 2 (len - 1)))
    k

def genAVL (height lo hi : Nat) : Gen (Tree Nat) :=
  Tree.unfold
    (fun x => do
      let __do_lift <-
        if x.snd.snd = 0 then pure TreeF.leaf
          else
            if Nat.pred x.snd.snd = 0 then
              if h : decide (x.snd.fst.fst <= x.snd.fst.snd) = true then
                pick (pure TreeF.leaf) do
                  let a <- choose x.2.1.1 x.2.1.2 (s_between_partial._proof_1 h)
                  pure (TreeF.node (PUnit.unit, PUnit.unit) a (PUnit.unit, PUnit.unit))
              else pure TreeF.leaf
            else
              assume (decide (x.snd.fst.fst <= x.snd.fst.snd)) fun h => do
                let a <- choose x.2.1.1 x.2.1.2 (s_between_partial._proof_1 h)
                pure (TreeF.node (PUnit.unit, PUnit.unit) a (PUnit.unit, PUnit.unit))
      match __do_lift with
        | TreeF.leaf => pure TreeF.leaf
        | TreeF.node bl x_1 br =>
          pure
            (TreeF.node (bl, (x.2.1.1, x_1 - 1), x.2.2 - 1) x_1
              (br, (x_1 + 1, x.2.1.2), x.2.2 - 1)))
    ((PUnit.unit, PUnit.unit), (lo, hi), height)

/-
Differences:
- Remove two extra units in collector.
- Nicer match on height to reduce some duplication.
-/
def genAVL_manual (height lo hi : Nat) : Gen (Tree Nat) :=
  Tree.unfold
    (fun (lo, hi, height) => do
      match height with
      | 0 => pure TreeF.leaf
      | 1 =>
        if h : lo > hi then
          pure TreeF.leaf
        else do
          pick
            (pure TreeF.leaf)
            (do
              let a <- choose lo hi (by aesop)
              pure (TreeF.node (lo, a - 1, height - 1) a (a + 1, hi, height - 1)))
      | height' + 1 => do
        -- We cannot guarantee that lo <= hi at this stage.
        assume (lo <= hi) fun h => do
          let a <- choose lo hi (by aesop)
          pure (TreeF.node (lo, a - 1, height - 1) a (a + 1, hi, height - 1)))
    (lo, hi, height)

/-
Differences:
- Remove two extra units in collector.
- Nicer match on height to reduce some duplication.
- Generator is technically total now; this requires insight about the total number of values that
can appear in a tree of height k.
-/
def genAVL_manual' (height lo hi : Nat) : Gen (Tree Nat) :=
  -- Guarantee that there are enough values in the range, given the height.
  assume (hi - lo > 2 ^ height) fun _ =>
    Tree.unfold
      (fun (lo, hi, height) => do
        match height with
        | 0 => pure TreeF.leaf
        | 1 =>
            pick
              (pure TreeF.leaf)
              (assume (lo <= hi) fun h => do  -- Will always succeed.
                -- Choose values so we never truncate the range to be too small.
                let a <- choose (lo + 2 ^ (height - 1)) (hi - 2 ^ (height - 1)) (by aesop)
                pure (TreeF.node (lo, a - 1, height - 1) a (a + 1, hi, height - 1)))
        | height' + 1 => do
          assume (lo <= hi) fun h => do -- Will always succeed.
            -- Choose values so we never truncate the range to be too small.
            let a <- choose (lo + 2 ^ (height - 1)) (hi - 2 ^ (height - 1)) (by aesop)
            pure (TreeF.node (lo, a - 1, height - 1) a (a + 1, hi, height - 1)))
      (lo, hi, height)
