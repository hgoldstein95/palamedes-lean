import Palamedes.Synthesizer
import Palamedes.Data.Color

open Gen CorrectGen

namespace RBList

@[simp]
def isRRListAux : List Color → Bool → Bool := λ t isRedChild =>
 match t with
 | .nil => true
 | .cons c tl => if c == .red then !isRedChild && isRRListAux tl true else isRRListAux tl false

@[simp]
def isRRList : List Color → Bool := λ xs => isRRListAux xs false

@[simp]
def isBHList : List Color → Nat → Bool := λ xs height =>
 match xs with
 | .nil => height == 0
 | .cons h tl => if h == .red then isBHList tl height else height > 0 && isBHList tl (height - 1)

open Gen CorrectGen

def genRRFold : Gen (List Color) := by
  generator_search (fun xs => isRRList xs = true)

def genBHFold (height : Nat) : Gen (List Color) := by
  generator_search (fun xs => isBHList xs height = true)
