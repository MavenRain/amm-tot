"""Check the swap identity and its rejection controls with a tot executable."""
from pathlib import Path
import hashlib
import os
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_TOT = Path("/Users/oobi/Documents/kan-lang-tot-pin/"
                   "_build/default/bin/tot.exe")
TOT = Path(os.environ.get("TOT", DEFAULT_TOT))
FOUNDATION = (ROOT / "src" / "Foundation.tot").read_text()
FIELD = (ROOT / "src" / "Field.tot").read_text()
INVARIANT = (ROOT / "src" / "Invariant.tot").read_text()
BASE = FOUNDATION + "\n" + FIELD + "\n" + INVARIANT

GOAL = ("  Eq F (fmul (fadd x dx) (fsub y (fdiv (fmul y dx) (fadd x dx))))"
        " (fmul x y) :=\n")
COMMUTED = GOAL.replace("(fmul x y) :=", "(fmul y x) :=")
WRONG_DEN = GOAL.replace("(fdiv (fmul y dx) (fadd x dx))))",
                         "(fdiv (fmul y dx) x)))")
LAST_STEP = """      (trans0 F
        (fsub (fadd (fmul x y) (fmul dx y)) (fmul y dx))
        (fsub (fadd (fmul x y) (fmul dx y)) (fmul dx y))
        (fmul x y)
        (cong0 F F
          (fmul y dx)
          (fmul dx y)
          (fun z => fsub (fadd (fmul x y) (fmul dx y)) z)
          (mulComm y dx))
        (addSubCancelRight (fmul x y) (fmul dx y))))))
"""
NO_LAST_STEP = "        (addSubCancelRight (fmul x y) (fmul dx y)))))\n"

# Each law type of the record, and a weakened replacement for it. The
# text occurs twice in Field.tot: once as the constructor field and once
# as the return type of the projection. Both change together, so the
# projection still checks and swapOutputIdentity is the first def that
# fails.
LAWS = [
    ("addPos",
     "flt fzero (fadd a b)",
     "flt fzero a"),
    ("neOfGt",
     "(0 h : flt fzero a) -> (0 e : Eq F a fzero) -> Empty",
     "(0 h : flt fzero a) -> (0 e : Eq F a a) -> Empty"),
    ("mulSub",
     "Eq F (fmul a (fsub b c)) (fsub (fmul a b) (fmul a c))",
     "Eq F (fmul a (fsub b c)) (fmul a (fsub b c))"),
    ("mulDivAssoc",
     "Eq F (fmul a (fdiv b c)) (fdiv (fmul a b) c)",
     "Eq F (fmul a (fdiv b c)) (fmul a (fdiv b c))"),
    ("mulDivCancelLeft",
     "Eq F (fdiv (fmul a b) a) b",
     "Eq F (fdiv (fmul a b) a) (fdiv (fmul a b) a)"),
    ("addMul",
     "Eq F (fmul (fadd a b) c) (fadd (fmul a c) (fmul b c))",
     "Eq F (fmul (fadd a b) c) (fmul (fadd a b) c)"),
    ("mulComm",
     "Eq F (fmul a b) (fmul b a)",
     "Eq F (fmul a b) (fmul a b)"),
    ("addSubCancelRight",
     "Eq F (fsub (fadd a b) b) a",
     "Eq F (fsub (fadd a b) b) (fsub (fadd a b) b)"),
]

def mutate_invariant(old, new):
    """Return BASE with one exact substring of the invariant replaced."""
    if INVARIANT.count(old) != 1:
        raise SystemExit(f"anchor is not unique in Invariant.tot: {old!r}")
    return FOUNDATION + "\n" + FIELD + "\n" + INVARIANT.replace(old, new)

def mutate_field(old, new, count):
    """Return BASE with every occurrence of a record substring replaced.

    The count is exact. It guards the paired edit of a constructor field
    and the return type of its projection.
    """
    found = FIELD.count(old)
    if found != count:
        raise SystemExit(f"anchor occurs {found} times, not {count}, "
                         f"in Field.tot: {old!r}")
    return FOUNDATION + "\n" + FIELD.replace(old, new) + "\n" + INVARIANT

# A case is (name, full source, expected diagnostic word).
# None: the checker must accept. A string: the checker must exit with
# status 1 and print that string in its diagnostic.
CASES = [
    ("swap-output-identity", BASE, None),
    ("commuted-rhs", mutate_invariant(GOAL, COMMUTED), "mismatch"),
    ("wrong-denominator", mutate_invariant(GOAL, WRONG_DEN), "mismatch"),
    ("dropped-step", mutate_invariant(LAST_STEP, NO_LAST_STEP), "mismatch"),
    ("positivity-misused",
     mutate_invariant("(addPos x dx hx hdx)", "(addPos x dx hx hx)"),
     "mismatch"),
] + [(f"weak-{name}", mutate_field(old, new, 2), "mismatch")
     for name, old, new in LAWS] + [
    ("wrong-projection",
     mutate_field("=> mulComm a b", "=> mulComm b a", 1), "mismatch"),
    ("axiom-rejected",
     BASE + "\naxiom fake : (0 F : Type 0) -> (a : F) -> (b : F) ->"
            " Eq F a b\n", "axiom"),
]

def run_case(directory, name, source):
    path = Path(directory) / f"{name}.tot"
    path.write_text(source)
    return subprocess.run(
        [str(TOT), "check", "--no-prelude", "--no-axioms", str(path)],
        text=True, capture_output=True, timeout=60)

def accepted(result, expected):
    if expected is None:
        return result.returncode == 0
    diagnostic = (result.stdout + result.stderr).lower()
    return result.returncode == 1 and expected in diagnostic

def main():
    if not TOT.is_file():
        raise SystemExit(f"checker not found: {TOT}\n"
                         "Set TOT=/absolute/path/to/tot.exe")
    print(f"checker: {TOT}")
    print(f"checker sha256: {hashlib.sha256(TOT.read_bytes()).hexdigest()}")
    with tempfile.TemporaryDirectory(prefix="amm-tot-") as directory:
        for name, source, expected in CASES:
            result = run_case(directory, name, source)
            if not accepted(result, expected):
                raise SystemExit(f"FAIL {name}: exit {result.returncode}\n"
                                 f"{result.stdout}\n{result.stderr}")
            print(f"PASS {name}")
    print(f"PASS {len(CASES)} of {len(CASES)} cases")

if __name__ == "__main__":
    main()
