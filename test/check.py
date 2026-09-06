"""Check the swap identity, the order and fraction library, and the rejection controls."""
from functools import reduce
from pathlib import Path
import hashlib
import os
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_TOT = Path("/Users/oobi/Documents/kan-lang-tot-pin/"
                   "_build/default/bin/tot.exe")
TOT = Path(os.environ.get("TOT", DEFAULT_TOT))
NAMES = ["Foundation", "Field", "Invariant", "Axioms", "Ring", "Laws",
         "Compose", "Frac", "Order", "Pool", "Basic", "Product", "NoDrain"]
FILES = {name: (ROOT / "src" / f"{name}.tot").read_text() for name in NAMES}
FIELD = FILES["Field"]
INVARIANT = FILES["Invariant"]
AXIOMS = FILES["Axioms"]
LAWS_SRC = FILES["Laws"]
FRAC = FILES["Frac"]
ORDER = FILES["Order"]
POOL = FILES["Pool"]

def concatenate(**changed):
    """Return the thirteen sources in check order, with the named ones replaced."""
    return "\n".join(changed.get(name, FILES[name]) for name in NAMES)

BASE = concatenate()

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

# Each axiom of OrderedField, and a weakened replacement for it. The
# axiom record has no projections, so the text occurs once in
# Axioms.tot. Every proof stays unchanged, and the first def that uses
# the axiom is rejected.
AXIOM_LAWS = [
    ("addComm",
     "Eq F (fadd a b) (fadd b a)",
     "Eq F (fadd a b) (fadd a b)"),
    ("addAssoc",
     "Eq F (fadd (fadd a b) c) (fadd a (fadd b c))",
     "Eq F (fadd (fadd a b) c) (fadd (fadd a b) c)"),
    ("addZero",
     "Eq F (fadd a fzero) a",
     "Eq F (fadd a fzero) (fadd a fzero)"),
    ("addNegCancel",
     "Eq F (fadd a (fneg a)) fzero",
     "Eq F (fadd a (fneg a)) (fadd a (fneg a))"),
    ("mulComm",
     "Eq F (fmul a b) (fmul b a)",
     "Eq F (fmul a b) (fmul a b)"),
    ("mulAssoc",
     "Eq F (fmul (fmul a b) c) (fmul a (fmul b c))",
     "Eq F (fmul (fmul a b) c) (fmul (fmul a b) c)"),
    ("mulOne",
     "Eq F (fmul a fone) a",
     "Eq F (fmul a fone) (fmul a fone)"),
    ("mulAdd",
     "Eq F (fmul a (fadd b c)) (fadd (fmul a b) (fmul a c))",
     "Eq F (fmul a (fadd b c)) (fmul a (fadd b c))"),
    ("subEqAddNeg",
     "Eq F (fsub a b) (fadd a (fneg b))",
     "Eq F (fsub a b) (fsub a b)"),
    ("divEqMulInv",
     "Eq F (fdiv a b) (fmul a (finv b))",
     "Eq F (fdiv a b) (fdiv a b)"),
    ("mulInvCancel",
     "Eq F (fmul a (finv a)) fone",
     "Eq F (fmul a (finv a)) (fmul a (finv a))"),
    ("ltIrrefl",
     "(0 h : flt a a) -> Empty",
     "(0 h : flt a a) -> flt a a"),
    ("ltTrans",
     "(0 h2 : flt b c) -> flt a c",
     "(0 h2 : flt b c) -> flt a b"),
    ("addLtAddLeft",
     "(0 h : flt b c) -> flt (fadd a b) (fadd a c)",
     "(0 h : flt b c) -> flt b c"),
]

DERIVE_ADD_MUL = "(deriveAddMul F fadd fmul fsub fdiv fneg finv fzero fone flt A)"
DERIVE_MUL_COMM = "(deriveMulComm F fadd fmul fsub fdiv fneg finv fzero fone flt A)"

def mutate_invariant(old, new):
    """Return BASE with one exact substring of the invariant replaced."""
    if INVARIANT.count(old) != 1:
        raise SystemExit(f"anchor is not unique in Invariant.tot: {old!r}")
    return concatenate(Invariant=INVARIANT.replace(old, new))

def mutate_field(old, new, count):
    """Return BASE with every occurrence of a record substring replaced.

    The count is exact. It guards the paired edit of a constructor field
    and the return type of its projection.
    """
    found = FIELD.count(old)
    if found != count:
        raise SystemExit(f"anchor occurs {found} times, not {count}, "
                         f"in Field.tot: {old!r}")
    return concatenate(Field=FIELD.replace(old, new))

def mutate_axioms(old, new):
    """Return BASE with one exact substring of the axiom record replaced."""
    if AXIOMS.count(old) != 1:
        raise SystemExit(f"anchor is not unique in Axioms.tot: {old!r}")
    return concatenate(Axioms=AXIOMS.replace(old, new))

def mutate_pool(pairs):
    """Return BASE with paired substrings of src/Pool.tot replaced.

    Each pair is (old, new). The count is exact and it is one, so the
    record field, the result type of the projection and the return motive
    change together. The projection still checks and the first consumer
    of the projection is the def that fails.
    """
    def one(text, pair):
        old, new = pair
        found = text.count(old)
        if found != 1:
            raise SystemExit(f"anchor occurs {found} times, not 1, "
                             f"in Pool.tot: {old!r}")
        return text.replace(old, new)
    changed = reduce(one, pairs, POOL)
    return concatenate(Pool=changed)

def def_span(name, source=None, where="Laws.tot"):
    """Return the span of one def, from its header to its check line."""
    text = LAWS_SRC if source is None else source
    header = re.search(rf"^(?:reducible )?def {name}\b", text, re.MULTILINE)
    if header is None:
        raise SystemExit(f"def not found in {where}: {name}")
    return header.start(), text.index(f"\ncheck {name}\n", header.start())

def mutate_in_def(file_name, def_name, old, new, count=1):
    """Return BASE with one substring inside one def of one file replaced.

    The count is exact. It guards the anchor of every new negative case:
    the anchor ends with the ":=" of the def header, so it matches the
    result type of the def and never a step of its body.
    """
    source = FILES[file_name]
    start, end = def_span(def_name, source, f"{file_name}.tot")
    block = source[start:end]
    found = block.count(old)
    if found != count:
        raise SystemExit(f"anchor occurs {found} times, not {count}, "
                         f"in {file_name}.tot def {def_name}: {old!r}")
    changed = source[:start] + block.replace(old, new) + source[end:]
    return concatenate(**{file_name: changed})

def mutate_laws(name, old, new):
    """Return BASE with one exact substring inside one def of Laws.tot replaced."""
    start, end = def_span(name)
    block = LAWS_SRC[start:end]
    if block.count(old) != 1:
        raise SystemExit(f"anchor is not unique in {name}: {old!r}")
    return concatenate(Laws=LAWS_SRC[:start] + block.replace(old, new)
                       + LAWS_SRC[end:])

def swap_in_laws(name, first, second):
    """Return BASE with two unique substrings inside one def of Laws.tot exchanged."""
    start, end = def_span(name)
    block = LAWS_SRC[start:end]
    if block.count(first) != 1 or block.count(second) != 1:
        raise SystemExit(f"anchors are not unique in {name}: "
                         f"{first!r}, {second!r}")
    swapped = (block.replace(first, "\0").replace(second, first)
               .replace("\0", second))
    return concatenate(Laws=LAWS_SRC[:start] + swapped + LAWS_SRC[end:])

# The abbreviations of the M3b brief, spelled out as the files spell
# them. OPS is the ten operation arguments of a pure def, and PARAMS is
# OPS followed by the axiom record.
OPS = "F fadd fmul fsub fdiv fneg finv fzero fone flt"
RX = "(poolReserveX F fzero flt p)"
RY = "(poolReserveY F fzero flt p)"
LPT = "(poolTotalLP F fzero flt p)"

# The 27 negatives of src/Basic.tot: (case, def, old, new, failing def).
# The first eight change the result type of a theorem and keep the
# proof. The next ten do the same for an obligation. The last nine
# change the body of a pure definition and keep every statement, so the
# first def that unfolds the definition fails.
BASIC_NEGATIVES = [
    ("wrong-constantproduct-pos", "constantProductPos",
     f"flt fzero (constantProduct {OPS} p) :=",
     f"flt (constantProduct {OPS} p) fzero :=",
     "constantProductPos"),
    ("wrong-feecomplement-pos", "feeComplementPos",
     f"flt fzero (feeComplement {OPS} f) :=",
     f"flt (feeComplement {OPS} f) fzero :=",
     "feeComplementPos"),
    ("wrong-feecomplement-ltone", "feeComplementLtOne",
     f"flt (feeComplement {OPS} f) fone :=",
     f"flt fone (feeComplement {OPS} f) :=",
     "feeComplementLtOne"),
    ("wrong-reservex-nezero", "poolReserveXNeZero",
     f"(0 e : Eq F {RX} fzero) -> Empty :=",
     f"(0 e : Eq F fzero {RX}) -> Empty :=",
     "poolReserveXNeZero"),
    ("wrong-reservey-nezero", "poolReserveYNeZero",
     f"(0 e : Eq F {RY} fzero) -> Empty :=",
     f"(0 e : Eq F fzero {RY}) -> Empty :=",
     "poolReserveYNeZero"),
    ("wrong-totallp-nezero", "poolTotalLPNeZero",
     f"(0 e : Eq F {LPT} fzero) -> Empty :=",
     f"(0 e : Eq F fzero {LPT}) -> Empty :=",
     "poolTotalLPNeZero"),
    ("wrong-reservex-add-pos", "reserveXAddPos",
     f"flt fzero (fadd {RX} dx) :=",
     f"flt fzero (fadd dx {RX}) :=",
     "reserveXAddPos"),
    ("wrong-reservex-add-nezero", "reserveXAddNeZero",
     f"(0 e : Eq F (fadd {RX} dx) fzero) -> Empty :=",
     f"(0 e : Eq F (fadd dx {RX}) fzero) -> Empty :=",
     "reserveXAddNeZero"),
    ("wrong-swap-hx", "swapHx",
     f"flt fzero (fadd {RX} dx) :=",
     f"flt fzero (fadd dx {RX}) :=",
     "swapHx"),
    ("wrong-swap-hy", "swapHy",
     f"(fsub {RY}\n      (swapOutput {OPS} p dx)) :=",
     f"(fsub (swapOutput {OPS} p dx)\n      {RY}) :=",
     "swapHy"),
    ("wrong-swapwithfee-hx", "swapWithFeeHx",
     f"flt fzero (fadd {RX} dx) :=",
     f"flt fzero (fadd dx {RX}) :=",
     "swapWithFeeHx"),
    ("wrong-swapwithfee-hy", "swapWithFeeHy",
     f"(fsub {RY}\n    (swapOutputWithFee {OPS} p dx f)) :=",
     f"(fsub (swapOutputWithFee {OPS} p dx f)\n    {RY}) :=",
     "swapWithFeeHy"),
    ("wrong-addliquidity-hx", "addLiquidityHx",
     f"flt fzero (fadd {RX} dx) :=",
     f"flt fzero (fadd dx {RX}) :=",
     "addLiquidityHx"),
    ("wrong-addliquidity-hy", "addLiquidityHy",
     f"(fadd {RY}\n      (fdiv (fmul dx {RY}) {RX})) :=",
     f"(fadd (fdiv (fmul dx {RY}) {RX})\n      {RY}) :=",
     "addLiquidityHy"),
    ("wrong-addliquidity-hlp", "addLiquidityHlp",
     f"(fadd {LPT}\n      (fdiv (fmul dx {LPT}) {RX})) :=",
     f"(fadd (fdiv (fmul dx {LPT}) {RX})\n      {LPT}) :=",
     "addLiquidityHlp"),
    ("wrong-removeliquidity-hx", "removeLiquidityHx",
     f"(fsub {RX}\n    (redeemX {OPS} p lp)) :=",
     f"(fsub (redeemX {OPS} p lp)\n    {RX}) :=",
     "removeLiquidityHx"),
    ("wrong-removeliquidity-hy", "removeLiquidityHy",
     f"(fsub {RY}\n    (redeemY {OPS} p lp)) :=",
     f"(fsub (redeemY {OPS} p lp)\n    {RY}) :=",
     "removeLiquidityHy"),
    ("wrong-removeliquidity-hlp", "removeLiquidityHlp",
     f"flt fzero (fsub {LPT} lp) :=",
     f"flt fzero (fsub lp {LPT}) :=",
     "removeLiquidityHlp"),
    ("wrong-constantproduct", "constantProduct",
     f"fmul {RX} {RY}", f"fmul {RX} {RX}",
     "constantProductPos"),
    ("wrong-swapoutput", "swapOutput",
     f"(fadd {RX} dx)", f"(fadd {RX} {RX})",
     "swapHy"),
    ("wrong-effectiveprice", "effectivePrice",
     "(p : Pool F fzero flt) -> (dx : F) -> F :=",
     "(p : Pool F fzero flt) -> (dx : F) -> Pool F fzero flt :=",
     "effectivePrice"),
    ("wrong-spotprice", "spotPrice",
     "(p : Pool F fzero flt) -> F :=",
     "(p : Pool F fzero flt) -> Pool F fzero flt :=",
     "spotPrice"),
    ("wrong-feecomplement", "feeComplement",
     "fsub fone (feeRateRate F fzero fone flt f)",
     "fsub (feeRateRate F fzero fone flt f) fone",
     "feeComplementPos"),
    ("wrong-effectiveinput", "effectiveInput",
     f"fmul dx (feeComplement {OPS} f)", "fmul dx dx",
     "swapWithFeeHy"),
    ("wrong-swapoutputwithfee", "swapOutputWithFee",
     f"(fadd {RX} (effectiveInput {OPS} dx f))",
     f"(fadd {RX} dx)",
     "swapWithFeeHy"),
    ("wrong-redeemx", "redeemX",
     f"fdiv (fmul lp {RX}) {LPT}", f"fdiv (fmul lp {LPT}) {RX}",
     "removeLiquidityHx"),
    ("wrong-redeemy", "redeemY",
     f"fdiv (fmul lp {RY}) {LPT}", f"fdiv (fmul lp {LPT}) {RY}",
     "removeLiquidityHy"),
]

# The two record negatives. The constructor field, the result type of
# the projection and the return motive change together.
POOL_HX = [
    ("(hx : flt fzero reserveX)", "(hx : flt fzero totalLP)"),
    (f"(p : Pool F fzero flt) -> flt fzero {RX} :=",
     f"(p : Pool F fzero flt) -> flt fzero {LPT} :="),
    ("match p as q return flt fzero (poolReserveX F fzero flt q) with",
     "match p as q return flt fzero (poolTotalLP F fzero flt q) with"),
]
FEERATE_HLT = [
    ("(hlt : flt rate fone)", "(hlt : flt fone rate)"),
    ("(f : FeeRate F fzero fone flt) ->"
     " flt (feeRateRate F fzero fone flt f) fone :=",
     "(f : FeeRate F fzero fone flt) ->"
     " flt fone (feeRateRate F fzero fone flt f) :="),
    ("match f as g return flt (feeRateRate F fzero fone flt g) fone with",
     "match f as g return flt fone (feeRateRate F fzero fone flt g) with"),
]

# The thirteen negatives of src/Product.tot and src/NoDrain.tot that M3c
# adds: (case, file, def, old, new, failing def). The first ten change
# the result type of a theorem and keep the proof, so the def itself
# fails. The last three keep the statement and break the proof: one
# permutes the two reserves, one drops the transport and one drops the
# symmetry step.
M3C_NEGATIVES = [
    ("wrong-swap-preserves-product", "Product", "swapPreservesProduct",
     f"""  Eq F
    (constantProduct {OPS}
      (swap {OPS} A p dx hdx))
    (constantProduct {OPS} p) :=""",
     f"""  Eq F
    (constantProduct {OPS} p)
    (constantProduct {OPS}
      (swap {OPS} A p dx hdx)) :=""",
     "swapPreservesProduct"),
    ("wrong-effectiveinput-lt", "Product", "effectiveInputLt",
     f"  flt (effectiveInput {OPS} dx f) dx :=",
     f"  flt dx (effectiveInput {OPS} dx f) :=",
     "effectiveInputLt"),
    ("wrong-effectiveinput-pos", "Product", "effectiveInputPos",
     f"  flt fzero (effectiveInput {OPS} dx f) :=",
     f"  flt (effectiveInput {OPS} dx f) fzero :=",
     "effectiveInputPos"),
    ("wrong-swapwithfee-increases-product", "Product",
     "swapWithFeeIncreasesProduct",
     f"""  flt
    (constantProduct {OPS} p)
    (constantProduct {OPS}
      (swapWithFee {OPS} A p dx hdx f)) :=""",
     f"""  flt
    (constantProduct {OPS}
      (swapWithFee {OPS} A p dx hdx f))
    (constantProduct {OPS} p) :=""",
     "swapWithFeeIncreasesProduct"),
    ("wrong-swapoutput-lt-reservey", "NoDrain", "swapOutputLtReserveY",
     f"  flt (swapOutput {OPS} p dx) {RY} :=",
     f"  flt {RY} (swapOutput {OPS} p dx) :=",
     "swapOutputLtReserveY"),
    ("wrong-swapoutput-pos", "NoDrain", "swapOutputPos",
     f"  flt fzero (swapOutput {OPS} p dx) :=",
     f"  flt (swapOutput {OPS} p dx) fzero :=",
     "swapOutputPos"),
    ("wrong-swapoutputwithfee-lt-reservey", "NoDrain",
     "swapOutputWithFeeLtReserveY",
     f"""  flt (swapOutputWithFee {OPS} p dx f)
    {RY} :=""",
     f"""  flt {RY}
    (swapOutputWithFee {OPS} p dx f) :=""",
     "swapOutputWithFeeLtReserveY"),
    ("wrong-reservey-pos-after-swap", "NoDrain", "reserveYPosAfterSwap",
     f"""  flt fzero
    (fsub {RY}
      (swapOutput {OPS} p dx)) :=""",
     f"""  flt fzero
    (fsub (swapOutput {OPS} p dx)
      {RY}) :=""",
     "reserveYPosAfterSwap"),
    ("wrong-reservey-pos-after-swapwithfee", "NoDrain",
     "reserveYPosAfterSwapWithFee",
     f"""  flt fzero
    (fsub {RY}
      (swapOutputWithFee {OPS} p dx f)) :=""",
     f"""  flt fzero
    (fsub (swapOutputWithFee {OPS} p dx f)
      {RY}) :=""",
     "reserveYPosAfterSwapWithFee"),
    ("wrong-constantproduct-lowerbound", "NoDrain",
     "constantProductLowerBound",
     f"""  fle F flt
    (constantProduct {OPS} p)
    (constantProduct {OPS}
      (swap {OPS} A p dx hdx)) :=""",
     f"""  fle F flt
    (constantProduct {OPS}
      (swap {OPS} A p dx hdx))
    (constantProduct {OPS} p) :=""",
     "constantProductLowerBound"),
    ("wrong-swap-preserves-product-proof", "Product", "swapPreservesProduct",
     f"      {RX} {RY} dx",
     f"      {RY} {RX} dx",
     "swapPreservesProduct"),
    ("wrong-increases-product-notransport", "Product",
     "swapWithFeeIncreasesProduct",
     f"""      subst0 F
        (fmul
          (fadd {RX}
            (effectiveInput {OPS} dx f))
          (fsub {RY}
            (swapOutputWithFee {OPS} p dx f)))
        (fmul {RX} {RY})
        (fun z =>
          flt z
            (fmul (fadd {RX} dx)
              (fsub {RY}
                (swapOutputWithFee {OPS} p dx f))))
        (swapOutputIdentityOf {OPS} A
          {RX}
          {RY}
          (effectiveInput {OPS} dx f)
          (poolHx F fzero flt p)
          (effectiveInputPos {OPS} A dx hdx f))
""",
     "",
     "swapWithFeeIncreasesProduct"),
    ("wrong-lowerbound-nosym", "NoDrain", "constantProductLowerBound",
     f"""      (sym0 F
        (constantProduct {OPS}
          (swap {OPS} A p dx hdx))
        (constantProduct {OPS} p)
        (swapPreservesProduct {OPS} A p dx hdx))""",
     f"      (swapPreservesProduct {OPS} A p dx hdx)",
     "constantProductLowerBound"),
]

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
] + [(f"weak-axiom-{name}", mutate_axioms(old, new), "mismatch")
     for name, old, new in AXIOM_LAWS] + [
    ("wrong-derive-mulcomm",
     mutate_laws("deriveMulComm", "mulComm a b", "mulComm b a"), "mismatch"),
    ("wrong-field-order",
     swap_in_laws("fieldLawsOf", DERIVE_ADD_MUL, DERIVE_MUL_COMM), "mismatch"),
    ("axiom-rejected",
     BASE + "\naxiom fake : (0 F : Type 0) -> (a : F) -> (b : F) ->"
            " Eq F a b\n", "axiom"),
    # The three axioms that M3a adds, weakened one at a time. Every proof
    # stays unchanged, so the first def that reads the axiom fails.
    ("weak-axiom-mulpos",
     mutate_axioms("flt fzero (fmul a b)", "flt fzero a"), "mismatch"),
    ("weak-axiom-lttrichotomy",
     mutate_axioms(
         "(ltTrichotomy : (a : F) -> (b : F) -> Trichotomy F flt a b)",
         "(ltTrichotomy : (a : F) -> (b : F) -> Trichotomy F flt a a)"),
     "mismatch"),
    ("weak-axiom-zeroneone",
     mutate_axioms("Eq F fzero fone", "Eq F fzero fzero"), "mismatch"),
    # One lemma of the library at a time, with the result type changed and
    # the proof kept. The proof proves the original statement, so the
    # checker reports the mismatch at that def.
    ("wrong-subpos",
     mutate_in_def("Order", "subPosOfLt", "flt fzero (fsub a b) :=",
                   "flt fzero (fsub b a) :="), "mismatch"),
    ("wrong-divdiv",
     mutate_in_def("Frac", "divDiv", "(fdiv a (fmul b c)) :=",
                   "(fdiv a (fmul c b)) :="), "mismatch"),
    ("wrong-invpos",
     mutate_in_def("Order", "invPos", "flt fzero (finv a) :=",
                   "flt (finv a) fzero :="), "mismatch"),
    ("wrong-divltdiv",
     mutate_in_def("Order", "divLtDivOfPosLeft",
                   "flt (fdiv a b) (fdiv a c) :=",
                   "flt (fdiv a c) (fdiv a b) :="), "mismatch"),
    # The 27 negatives of src/Basic.tot and the two record negatives of
    # src/Pool.tot that M3b adds.
] + [(name, mutate_in_def("Basic", def_name, old, new), "mismatch")
     for name, def_name, old, new, _failing in BASIC_NEGATIVES] + [
    ("weak-pool-hx", mutate_pool(POOL_HX), "mismatch"),
    ("weak-feerate-hlt", mutate_pool(FEERATE_HLT), "mismatch"),
    # The ten result-type negatives and the three proof negatives of
    # src/Product.tot and src/NoDrain.tot that M3c adds.
] + [(name, mutate_in_def(file_name, def_name, old, new), "mismatch")
     for name, file_name, def_name, old, new, _failing in M3C_NEGATIVES]

# The def that must fail first, for every case that M3a adds. The name
# comes from the position of the diagnostic, so a mutation that moves the
# rejection to another def is a failure of the case.
FAILING_DEFS = {
    "weak-axiom-mulpos": "zeroLtOne",
    "weak-axiom-lttrichotomy": "ltOfLtOfLe",
    "weak-axiom-zeroneone": "zeroLtOne",
    "wrong-subpos": "subPosOfLt",
    "wrong-divdiv": "divDiv",
    "wrong-invpos": "invPos",
    "wrong-divltdiv": "divLtDivOfPosLeft",
    **{name: failing
       for name, _def_name, _old, _new, failing in BASIC_NEGATIVES},
    "weak-pool-hx": "constantProductPos",
    "weak-feerate-hlt": "feeComplementPos",
    **{name: failing
       for name, _file, _def_name, _old, _new, failing in M3C_NEGATIVES},
}

def failing_def(source, result):
    """Return the def that holds the position of the first diagnostic."""
    position = re.search(r":(\d+):\d+:", result.stdout + result.stderr)
    if position is None:
        return None
    line = int(position.group(1))
    heads = [(number, head.group(1))
             for number, text in enumerate(source.splitlines(), 1)
             for head in [re.match(r"(?:reducible )?def (\w+)", text)]
             if head is not None]
    earlier = [name for number, name in heads if number <= line]
    return earlier[-1] if earlier else None

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
            wanted = FAILING_DEFS.get(name)
            found = None if wanted is None else failing_def(source, result)
            if wanted is not None and found != wanted:
                raise SystemExit(f"FAIL {name}: the first failing def is "
                                 f"{found}, not {wanted}\n"
                                 f"{result.stdout}\n{result.stderr}")
            place = "" if wanted is None else f" (first failing def {wanted})"
            print(f"PASS {name}{place}")
    print(f"PASS {len(CASES)} of {len(CASES)} cases")

if __name__ == "__main__":
    main()
