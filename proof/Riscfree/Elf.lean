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

-- Check the bytes and return the symbol's address.
def verifyElfSymbol (path symbol : String) (words : List (BitVec 32)) : IO Nat := do
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
  return address

def verifyElf (path symbol : String) (words : List (BitVec 32)) : IO Unit :=
  discard <| verifyElfSymbol path symbol words

-- Check that the file is a 32-bit little-endian RISC-V ELF whose `e_flags`
-- leave `EF_RISCV_RVC` clear. The linker sets that flag when any input object
-- enables compressed instructions. With it clear, every instruction is a
-- 32-bit word, so every call leaves the word-aligned return address that the
-- theorems' final `ret` needs.
def verifyUncompressed (path : String) : IO Unit := do
  let elf ← IO.FS.readBinFile path
  unless elf.size ≥ 52 do
    throw (IO.userError s!"{path} is too short for an ELF32 header")
  let byte (index : Nat) : Nat := elf[index]!.toNat
  let magic := [byte 0, byte 1, byte 2, byte 3]
  let machine := byte 0x12 + (byte 0x13 <<< 8)
  let flags := byte 0x24 + (byte 0x25 <<< 8) + (byte 0x26 <<< 16) + (byte 0x27 <<< 24)
  unless magic == [0x7f, 0x45, 0x4c, 0x46] && byte 4 == 1 && byte 5 == 1 && machine == 0xf3 do
    throw (IO.userError s!"{path} is not a 32-bit little-endian RISC-V ELF file")
  unless flags &&& 1 == 0 do
    throw (IO.userError s!"{path} may contain compressed instructions (EF_RISCV_RVC is set)")
  IO.println s!"{path}: no compressed instructions (EF_RISCV_RVC clear)"

end Riscfree
