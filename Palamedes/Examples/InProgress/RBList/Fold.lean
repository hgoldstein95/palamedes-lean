import Palamedes.Synthesizer
import Palamedes.Data.Color

@[simp]
def rrFoldList (xs : List Color) : Bool :=
  List.fold
    (fun c acc isRedParent =>
      if c == .red then !isRedParent && acc true else acc false)
    (fun _ => true)
    xs
    false

@[simp]
def bhFoldList (xs : List Color) (height : Nat) : Bool :=
  List.fold
    (fun c acc h => if c == .red then acc h else h > 0 && acc (h - 1))
    (fun h => h == 0)
    xs
    height

open Gen CorrectGen

def genRRFold : Gen (List Color) := by
  generator_search (fun xs => rrFoldList xs = true)

def genBHFold (height : Nat) : Gen (List Color) := by
  generator_search (fun xs => bhFoldList xs height = true)
