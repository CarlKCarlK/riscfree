import Popcount
import Riscfree.PopcountDecode

namespace Riscfree.Popcount

-- The ELF verifier compares raw bytes against Riscfree.code in little-endian
-- order. This equality uses the same words in the Sail decoder certificate.
theorem decoderUsesVerifiedWords :
    instructions.map (fun entry => entry.1.toNat) = Riscfree.code.toList := by
  rfl

end Riscfree.Popcount
