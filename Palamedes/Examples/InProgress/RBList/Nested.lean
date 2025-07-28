import Palamedes.Synthesizer
import Palamedes.Data.Color

open Gen CorrectGen

namespace RBList

@[simp]
def rrAuxList : List Color → Bool → Bool := λ t isRedChild =>
 match t with
 | .nil => true
 | .cons .red tl => !isRedChild && rrAuxList tl true
 | .cons .black tl => rrAuxList tl false

@[simp]
def rrList : List Color → Bool := λ xs => rrAuxList xs false

@[simp]
def bhList : List Color → Nat → Bool := λ xs height =>
 match xs with
 | .nil => height == 1
 | .cons .red tl => bhList tl height
 | .cons .black tl => height > 0 && bhList tl (height - 1)

open Gen CorrectGen

/- def genRRFold : Gen (List Color) := by
  generator_search (fun xs => rrList xs = true)

def genBHFold (height : Nat) : Gen (List Color) := by
  generator_search (fun xs => bhList xs height = true) -/
