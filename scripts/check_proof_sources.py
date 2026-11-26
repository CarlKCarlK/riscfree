"""Reject proof shortcuts in the Lean sources before they are built.

Usage: python3 scripts/check_proof_sources.py

Scans every `.lean` file under `proof/`, plus `lakefile.toml`, with comments and
string literals removed, so prose may still mention a forbidden name. The axiom
audit (`scripts/AxiomAudit.lean`) reads what the kernel recorded; this scan
also catches shortcuts that leave no axiom, such as `#exit` or code that runs
while a file is elaborated.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROOF_DIRECTORY = "proof"

FORBIDDEN = [
    (r"\bsorry\b", "`sorry` leaves a goal unproved"),
    (r"\badmit\b", "`admit` leaves a goal unproved"),
    (r"\bnative_decide\b", "`native_decide` trusts compiled code (Lean.ofReduceBool)"),
    (r"\bbv_decide\b", "`bv_decide` trusts compiled code (Lean.ofReduceBool)"),
    (r"\+native\b|\bnative\s*:=\s*true\b", "native `decide` trusts compiled code"),
    (r"\bofReduceBool\b|\bofReduceNat\b|\btrustCompiler\b", "compiler-trust axiom"),
    (r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*axiom\b", "new axiom"),
    (r"\bimplemented_by\b|@\[\s*extern\b", "compiled code replaces a definition"),
    (r"\bunsafe\b", "`unsafe` code bypasses the kernel"),
    (r"\bskipKernelTC\b|\baddDeclWithoutChecking\b", "skips kernel checking"),
    (r"^\s*#exit\b", "`#exit` skips the rest of the file"),
    (r"\bwarningAsError\s*(?::=|=)\s*false\b", "disables the warnings-as-errors build setting"),
]

FORBIDDEN_IN_LEAN = [
    (r"#eval\b|\brun_cmd\b|\brun_elab\b|\brun_meta\b|\brun_tac\b",
     "code runs during elaboration; keep checks like `verifyElf` in the justfile"),
    (r"^\s*(?:builtin_)?initialize\b", "code runs when the module loads"),
]


def strip_comments_and_strings(text: str) -> str:
    """Blank out Lean comments (nested block comments included) and string literals.

    Newlines are kept, so line numbers still match the file.
    """
    output = []
    index = 0
    depth = 0
    while index < len(text):
        char = text[index]
        pair = text[index : index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                output.append("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                output.append("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif pair == "/-":
            depth = 1
            output.append("  ")
            index += 2
        elif pair == "--":
            end = text.find("\n", index)
            end = len(text) if end == -1 else end
            output.append(" " * (end - index))
            index = end
        elif char == '"':
            end = index + 1
            while end < len(text) and text[end] != '"':
                end += 2 if text[end] == "\\" else 1
            output.append(" " * (end + 1 - index))
            index = end + 1
        elif char == "'" and re.match(r"'(?:\\.|[^\\'\n])'", text[index : index + 4]) and (
            index == 0 or not (text[index - 1].isalnum() or text[index - 1] in "_'!?")
        ):
            # A character literal, not the prime in a name such as `h'`.
            literal = re.match(r"'(?:\\.|[^\\'\n])'", text[index:]).group(0)
            output.append(" " * len(literal))
            index += len(literal)
        else:
            output.append(char)
            index += 1
    return "".join(output)


def main() -> int:
    files = sorted((ROOT / PROOF_DIRECTORY).rglob("*.lean"))
    lakefile = ROOT / "lakefile.toml"
    failures = []
    for path in [*files, lakefile]:
        relative = path.relative_to(ROOT)
        text = path.read_text(encoding="utf-8")
        code = text if path == lakefile else strip_comments_and_strings(text)
        rules = FORBIDDEN if path == lakefile else FORBIDDEN + FORBIDDEN_IN_LEAN
        for line_number, line in enumerate(code.splitlines(), start=1):
            for pattern, reason in rules:
                if re.search(pattern, line):
                    failures.append(f"{relative}:{line_number}: {reason}: {text.splitlines()[line_number - 1].strip()}")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        print(f"proof source check: {len(failures)} forbidden shortcut(s)", file=sys.stderr)
        return 1
    print(f"proof source check: OK: {len(files)} Lean files have no forbidden shortcuts.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
