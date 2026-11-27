"""Write corrupted copies of linked ELF files for the linked-byte negative tests.

    corrupt_elf.py flip <elf> <symbol> <out>   # flip one bit in the symbol's middle byte
    corrupt_elf.py flip-at <elf> <symbol> <offset> <out>  # flip a selected byte
    corrupt_elf.py rvc <elf> <out>             # set EF_RISCV_RVC in the ELF header

`just prove` passes each copy to `scripts/LinkedBytes.lean` as a `reject-...`
check, which must fail for the expected reason.
"""

from pathlib import Path
from subprocess import check_output
import sys


def main():
    match sys.argv[1:]:
        case ["flip", elf, symbol, out]:
            image = bytearray(Path(elf).read_bytes())
            start, size = symbol_bytes(elf, symbol)
            image[start + size // 2] ^= 0x10
            Path(out).write_bytes(image)
        case ["flip-at", elf, symbol, offset, out]:
            image = bytearray(Path(elf).read_bytes())
            start, size = symbol_bytes(elf, symbol)
            offset = int(offset, 0)
            if not 0 <= offset < size:
                sys.exit("Byte offset lies outside the symbol")
            image[start + offset] ^= 0x10
            Path(out).write_bytes(image)
        case ["rvc", elf, out]:
            image = bytearray(Path(elf).read_bytes())
            image[0x24] |= 1
            Path(out).write_bytes(image)
        case _:
            sys.exit(__doc__)


def symbol_bytes(elf, symbol):
    """The file offset and size of a .text symbol, located as check_elf.py does."""
    symbols = check_output(["nm", "-S", "--defined-only", elf], text=True)
    [row] = [line.split() for line in symbols.splitlines() if line.endswith((f" T {symbol}", f" t {symbol}"))]
    address, size = (int(field, 16) for field in row[:2])
    sections = check_output(["objdump", "-h", "-j", ".text", elf], text=True)
    [section] = [fields for line in sections.splitlines() if (fields := line.split())[1:2] == [".text"]]
    _, base, _, offset = (int(field, 16) for field in section[2:6])
    return offset + address - base, size


if __name__ == "__main__":
    main()
