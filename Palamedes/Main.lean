import Palamedes.Basic
import Palamedes.Sample

-- #eval replicateM 100 <| sample (WellTyped.genWellTyped [])

-- #eval replicateM 100 <| sample (BST.genBST 0 20)

def main : IO Unit := IO.println "Hello, world!"
