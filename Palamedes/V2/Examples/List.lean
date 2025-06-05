import Palamedes.V2.Synthesizer

open Gen CorrectGen


def genAllTwosFold : Gen (List Nat) := by
  generator_search fun xs => List.fold (fun x b => x == 2 && b) true xs = true

def genTrueFold : Gen (List Nat) := by
  generator_search (fun (xs : List Nat) => List.fold (fun x b => b) true xs = true)

def genEvenLenFold : Gen (List Nat) := by
  generator_search (fun (xs : List Nat) => List.fold (fun x b => !b) true xs = true)

def genLengthKFold {k : Nat} : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b => b + 1) 0 xs = k)

-- -- TODO
-- def genEvenLenTwosFold : Gen (List Nat) := by
--   -- generator_search (fun xs => some (List.fold (fun x b => sorry) true sorry) = some true)
--   let cg : CorrectGen (fun xs => some (List.fold (fun x b => sorry) true sorry) = some true) := by
--     cgenerator_search
--   let g : Gen (List Nat) := by
--     optimize_gen cg.val
--   let _ : support cg.val = support cg := by
--     optimality
--   let _ : Gen.total g := by
--     totality
--   exact g

-- set_option palamedes.debug true

-- def genLengthKTwosFold (k : Nat) : Gen (List Nat) := by
--   -- generator_search (fun (xs : List Nat) =>
--   --     List.fold (fun _ l => l + 1) 0 v = k ∧
--   --     List.fold (fun x () => guard (x == 2)) () v = Option.some ())
--   sorry

-- -- -- @[aesop simp (rule_sets := [palamedes])]
-- -- def increasingByOne : List Int → Int → Bool := λ xs =>
-- --   match xs with
-- --   | [] => λ _ => true
-- --   | x :: xs => λ prev => x == prev + 1 && increasingByOne xs x

-- -- TODO int
-- def genIncreasingByOneFold : Gen (List Nat) := by
--   -- generator_search (fun xs => (List.fold (fun x b prev => x == prev + 1 && b x) (fun _ => true) xs 0) = true)
--   let cg : CorrectGen (fun (xs : List Nat) => List.fold (fun x b prev => x == prev + 1 && b x) (fun _ => true) xs 0 = true) := by
--     cgenerator_search
--   let g : Gen (List Int) := by
--     optimize_gen cg.val
--   let _ : support cg.val = support cg := by
--     optimality
--   let _ : Gen.total g := by
--     totality
--   exact g


-- def genBetween (lo hi : Nat): Gen Nat := by
--     generator_search (fun n => lo ≤ n ∧ n ≤ hi) allow_partial

-- -- -- @[aesop simp (rule_sets := [palamedes])]
-- -- def sortedBetween (hi : Nat) : List Nat → Nat → Bool := λ xs =>
-- --   match xs with
-- --   | [] => λ _ => true
-- --   | x :: xs => λ lo => lo ≤ x && x ≤ hi && (sortedBetween hi xs) x

-- def genSortedBetween (lo hi : Nat) : Gen (List Nat) := by
--  -- generator_search (fun (xs : List Nat) => List.fold (fun x b s => s ≤ x && x ≤ hi && b x) (fun _ => true) xs lo = true)
--   let cg : CorrectGen (fun (xs : List Nat) => List.fold (fun x b s => s ≤ x && x ≤ hi && b x) (fun _ => true) xs lo = true) := by
--     cgenerator_search
--   let g : Gen (List Nat) := by
--     optimize_gen cg.val
--   let _ : support cg.val = support cg := by
--     optimality
--   let _ : Gen.total g := by
--     totality
--   exact g
