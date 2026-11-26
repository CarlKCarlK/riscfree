import Popcount

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "Usage: lean --run proof/VerifyElf.lean ELF")
  Riscfree.verifyElf path
