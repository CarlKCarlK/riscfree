/-!
# ELF byte verification

GNU binutils supply the ELF symbol and section locations. Compare the raw
bytes at the resulting file offset with the instruction words a proof decoded,
independently of any disassembly.
-/

namespace Riscfree

def columns (line : String) : List String :=
  (line.splitOn " ").filter (· != "")

def hex (part : String) : IO Nat := do
  let mut value := 0
  for digit in part.toList do
    let ascii := digit.toNat
    let nibble ←
      if '0'.toNat ≤ ascii && ascii ≤ '9'.toNat then pure (ascii - '0'.toNat)
      else if 'a'.toNat ≤ ascii && ascii ≤ 'f'.toNat then pure (ascii - 'a'.toNat + 10)
      else throw (IO.userError s!"Invalid hexadecimal value: {part}")
    value := value * 16 + nibble
  return value

def verifyElf (path symbol : String) (words : List (BitVec 32)) : IO Unit := do
  let symbols ← IO.Process.run { cmd := "nm", args := #["-S", "--defined-only", path] }
  let sections ← IO.Process.run { cmd := "objdump", args := #["-h", "-j", ".text", path] }
  let symbolRows := (symbols.splitOn "\n").map columns
  let [[addressText, sizeText, "T", _]] :=
    symbolRows.filter (fun row => row.getLast? == some symbol)
    | throw (IO.userError s!"Expected one {symbol} text symbol")
  let [(_ :: ".text" :: sectionSizeText :: baseText :: _ :: offsetText :: _)] :=
    (sections.splitOn "\n").map columns |>.filter (fun row => row[1]? == some ".text")
    | throw (IO.userError "Expected one .text section")
  let address ← hex addressText
  let size ← hex sizeText
  let sectionSize ← hex sectionSizeText
  let base ← hex baseText
  let offset ← hex offsetText
  unless address % 4 == 0 && base ≤ address && address + size ≤ base + sectionSize do
    throw (IO.userError s!"{symbol} is misaligned or lies outside .text")
  let expected := words.flatMap fun word =>
    (List.range 4).map fun index => UInt8.ofNat (word.toNat >>> (8 * index))
  let startOffset := offset + (address - base)
  let elf ← IO.FS.readBinFile path
  let actual := (elf.extract startOffset (startOffset + size)).data.toList
  unless size == expected.length && actual == expected do
    throw (IO.userError s!"The linked {symbol} bytes differ from the Lean proof")
  IO.println s!"{symbol}: verified all {size} linked bytes"

end Riscfree
