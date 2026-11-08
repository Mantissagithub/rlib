"""Check the transitive axioms reported by Lean for the public theorems."""

import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
audit = root / "RlibTest/Axioms.lean"
result = subprocess.run(
    ["lake", "env", "lean", str(audit)], cwd=root, text=True, capture_output=True
)
print(result.stdout, end="")
print(result.stderr, end="")
if result.returncode:
    raise SystemExit(result.returncode)

reports = re.findall(r"depends on axioms: \[([^]]*)\]", result.stdout, re.DOTALL)
empty_reports = result.stdout.count("does not depend on any axioms")
expected = audit.read_text().count("#print axioms ")
if len(reports) + empty_reports != expected:
    raise SystemExit("Missing or unrecognized axiom report")

allowed = {"propext", "Classical.choice", "Quot.sound"}
for report in reports:
    unexpected = {name.strip() for name in report.split(",") if name.strip()} - allowed
    if unexpected:
        raise SystemExit(f"Unexpected axioms: {sorted(unexpected)}")
print(f"Axiom audit passed for {expected} theorems.")
