"""Compare each linked RawVec symbol's raw ELF bytes with its recorded words."""

from pathlib import Path
from subprocess import check_output
import sys

# Each verified routine and the file that records its instruction words.
ROUTINES = [
    ("raw_vec_u32_insert", "raw_vec_u32.words"),
    ("raw_vec_pair_insert", "raw_vec_pair.words"),
]


def main():
    elf = Path(sys.argv[1])
    symbols = check_output(["nm", "-S", "--defined-only", elf], text=True)
    sections = check_output(["objdump", "-h", "-j", ".text", elf], text=True)
    [section_row] = [row for line in sections.splitlines() if (row := line.split())[1:2] == [".text"]]
    section_size, base, _, offset = (int(field, 16) for field in section_row[2:6])
    image = elf.read_bytes()
    for symbol, words_file in ROUTINES:
        check_symbol(symbols, image, section_size, base, offset, symbol, words_file)


def check_symbol(symbols, image, section_size, base, offset, symbol, words_file):
    [symbol_row] = [row.split() for row in symbols.splitlines() if row.endswith(f" T {symbol}")]
    address, size = (int(field, 16) for field in symbol_row[:2])

    words = Path(__file__).with_name(words_file).read_text().split()
    if any(len(word) != 8 or int(word, 16) & 3 != 3 for word in words):
        sys.exit("Expected only 32-bit RISC-V instruction words")
    expected = b"".join(int(word, 16).to_bytes(4, "little") for word in words)
    if address % 4 or address < base or address + size > base + section_size:
        sys.exit(f"{symbol} is misaligned or outside .text")
    start = offset + address - base
    actual = image[start : start + size]
    if actual != expected or size != len(expected):
        sys.exit(f"{symbol}: linked bytes differ from the recorded instruction words")
    print(f"{symbol}: verified all {size} linked bytes ({len(words)} instructions)")


if __name__ == "__main__":
    main()
