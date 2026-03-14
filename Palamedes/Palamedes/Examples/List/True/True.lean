import Palamedes.Synthesizer

open Gen CorrectGen

namespace ConstTrue

@[simp]
def isTrue : List α → Bool
  | [] => true
  | x :: xs => (fun _ => true) x && isTrue xs

def genTrue : Gen (List Nat) := by
  generator_search (fun xs => isTrue xs = true)

end ConstTrue
