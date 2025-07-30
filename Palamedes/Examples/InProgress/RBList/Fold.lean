import Palamedes.Synthesizer
import Palamedes.Data.Color

/-
Equivalent to
  List.fold
    (fun c acc isRedParent =>
      if c = .red then !isRedParent && acc true else && acc false
    (fun _ => true)
    xs
    false
-/
@[simp]
def rrFoldList (xs : List Color) : Bool :=
  List.fold
    (fun c acc isRedParent =>
      if (c == .red) = true then !isRedParent && acc true else true && acc false)
    (fun _ => true)
    xs
    false

/-
Equivalent to
  List.fold
    (fun c acc h => if c == .red then acc h else h > 0 && acc (h - 1))
    (fun h => h == 1)
    xs
    height
-/
@[simp]
def bhFoldList (xs : List Color) (height : Nat) : Bool :=
  List.fold
    (fun c acc h =>
      if (c == .red) = true
        then true && acc h
        else h > 0 && acc (h - 1))
    (fun h => h == 1)
    xs
    height

open Gen CorrectGen

set_option palamedes.debug true

def genRRFold : Gen (List Color) := by
  generator_search (fun xs => rrFoldList xs = true)

def genBHFold (height : Nat) : Gen (List Color) := by
  generator_search (fun xs => bhFoldList xs height = true)
