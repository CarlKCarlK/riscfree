"""Compare the linked RawVec symbol's raw ELF bytes with the recorded words.

With --uncompressed, also require that EF_RISCV_RVC is clear in e_flags, so
the linked file contains no compressed instructions.
"""

from argparse import ArgumentParser
from pathlib import Path
from subprocess import check_output
import sys


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--uncompressed", action="store_true")
    args = parser.parse_args()
    elf = args.elf
    if args.uncompressed:
        check_uncompressed(elf)
    symbol = "raw_vec_u32_insert"
    symbols = check_output(["nm", "-S", "--defined-only", elf], text=True)
    [symbol_row] = [row.split() for row in symbols.splitlines() if row.endswith(f" T {symbol}")]
    address, size = (int(field, 16) for field in symbol_row[:2])

    sections = check_output(["objdump", "-h", "-j", ".text", elf], text=True)
    [section_row] = [row for line in sections.splitlines() if (row := line.split())[1:2] == [".text"]]
    section_size, base, _, offset = (int(field, 16) for field in section_row[2:6])

    words = Path(__file__).with_name("raw_vec_u32.words").read_text().split()
    if any(len(word) != 8 or int(word, 16) & 3 != 3 for word in words):
        sys.exit("Expected only 32-bit RISC-V instruction words")
    expected = b"".join(int(word, 16).to_bytes(4, "little") for word in words)
    if address % 4 or address < base or address + size > base + section_size:
        sys.exit(f"{symbol} is misaligned or outside .text")
    start = offset + address - base
    actual = elf.read_bytes()[start : start + size]
    if actual != expected or size != len(expected):
        sys.exit(f"{symbol}: linked bytes differ from the recorded instruction words")
    print(f"{symbol}: verified all {size} linked bytes ({len(words)} instructions)")


def check_uncompressed(elf):
    header = elf.read_bytes()[:52]
    is_riscv32 = header[:6] == b"\x7fELF\x01\x01" and int.from_bytes(header[0x12:0x14], "little") == 0xF3
    if len(header) < 52 or not is_riscv32:
        sys.exit(f"{elf} is not a 32-bit little-endian RISC-V ELF file")
    if int.from_bytes(header[0x24:0x28], "little") & 1:
        sys.exit(f"{elf} may contain compressed instructions (EF_RISCV_RVC is set)")
    print(f"{elf}: no compressed instructions (EF_RISCV_RVC clear)")


if __name__ == "__main__":
    main()
