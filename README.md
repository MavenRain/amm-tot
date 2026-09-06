# The AMM swap identity in tot

A standalone port of one theorem of amm-lean. The theorem is the core
algebraic identity of a constant-product automated market maker with no
fee. The port is verification only. It measures the cost of the same
proof in tot, a language with no fields, no division, no tactics and no
rewrite form.

## Check

```sh
python3 test/check.py
```

Run from this directory. The runner uses the checker named by `TOT` when
that variable is set. Otherwise it uses the pinned checker at
`/Users/oobi/Documents/kan-lang-tot-pin/_build/default/bin/tot.exe` and
stops with a message when that file is absent. The runner concatenates
the foundation, the record file and the proof source in temporary files
and checks with `--no-prelude --no-axioms`. It prints the checker
SHA-256, so validation identifies the binary actually used. No compiler
rebuild is necessary when a built checker exists.

## What is proved

`swapOutputIdentity`: for every carrier `F`, every addition,
multiplication, subtraction and division operation on `F`, every
distinguished element `fzero`, every relation `flt`, and every `x`, `y`
and `dx` in `F`, if the eight supplied laws hold and `flt fzero x` and
`flt fzero dx` hold, then

```
fmul (fadd x dx) (fsub y (fdiv (fmul y dx) (fadd x dx))) = fmul x y
```

The Lean source is `swap_output_identity` in
`/Users/oobi/Documents/amm-lean/AmmLean/Invariant.lean`, lines 56 to 60:

```lean
theorem swap_output_identity (x y dx : F) (hx : 0 < x) (hdx : 0 < dx) :
    (x + dx) * (y - y * dx / (x + dx)) = x * y
```

The Lean version reads the field structure, the order and the lemmas
from instance resolution. The tot version takes each one as an explicit
hypothesis. The eight laws are the fields of the record `FieldLaws` in
`src/Field.tot`. The theorem takes one record `L` and destructures it
once. The record plays the role of the three instances `Field F`,
`LinearOrder F` and `IsStrictOrderedRing F`. The proof is the same six
rewrites of the Lean tactic block, in the same order, written as an
equality chain.

| tot hypothesis or record field | Mathlib source |
| --- | --- |
| `fadd`, `fmul`, `fsub`, `fdiv` | the `Field F` operations |
| `fzero`, `flt` | `0` and `<` from `LinearOrder F` |
| field `addPos` | `add_pos` |
| field `neOfGt` | `ne_of_gt` |
| field `mulSub` | `mul_sub` |
| field `mulDivAssoc` | `mul_div_assoc'` |
| field `mulDivCancelLeft` | `mul_div_cancel_left₀` |
| field `addMul` | `add_mul` |
| field `mulComm` | `mul_comm` |
| field `addSubCancelRight` | `add_sub_cancel_right` |

`neOfGt` states the disequality as a function to `Empty`, because tot has
no `Ne` and no `Prop`.

## Measurement

| Quantity | Lean | tot, pilot | tot, record |
| --- | --- | --- | --- |
| Statement lines | 2 | 14 | 7 |
| Proof lines | 3 | 46 | 48 |
| Statement characters | 119 | 1084 | 390 |
| Proof characters | 162 | 1578 | 1610 |
| Context lambdas written by hand | 0 | 4 | 4 |
| Transitivity steps written by hand | 0 | 5 | 5 |
| Hypotheses in the signature | 5 | 20 | 13 |

The statement is the text from the `def` line, or the `theorem` line, to
the goal line. The proof is the text from the `:=` line to the last body
line. The goal line carries the `:=`, so both spans count it. The
characters are the bytes of those lines after leading spaces are
removed. The Lean statement is `Invariant.lean` lines 56 to 57 and the
Lean proof is lines 58 to 60. The tot statement of the record version is
`src/Invariant.tot` lines 7 to 13, and the tot proof is lines 13 to 60.
The pilot values are the same spans of the pilot file at commit
`860a907`.

The eight law lines left the signature and became the record. One
`match` line and one `end` line entered the proof. The signature falls
from twenty hypotheses to thirteen, and from 1084 to 390 characters. The
proof grows by two lines and by 32 characters, because the chain is one
level deeper. The record file `src/Field.tot` costs 103 lines once. That
file holds the header comment, the record and the eight projections. The
context lambdas and the transitivity steps do not change, because the
chain is the same.

`test/check.py` runs in about 0.15 seconds of wall time on the pinned
checker, for all fifteen cases.

## Scope and trust

The eight laws are hypotheses, not axioms. The record `FieldLaws` is a
hypothesis of the same kind: this repository supplies no inhabitant of
it. The file declares no axiom, and `--no-axioms` rejects any axiom.
Nothing in this repository asserts that a field exists. The signature of
`swapOutputIdentity` therefore has no tot inhabitant that this
repository supplies: a caller must supply the operations and one record
that holds the proofs of the eight laws. The theorem is conditional on
them.

The standalone foundation declares only `Empty` and indexed
propositional `Eq`, with `subst0`, `J0`, `sym0`, `trans0` and `cong0`.
Those seven items are copied verbatim from the tot prelude. There are no
postulates, admitted proofs or placeholder theorems. The default prelude
is excluded, including its unrelated IO-law axioms. Checking trusts
tot's current elaborator and kernel. This project does not establish
their metatheoretic soundness.

The port covers one theorem. The other theorems of amm-lean are not
ported.

## Validation

On 2026-09-06, all fifteen checks passed with checker SHA-256
`30c4524d57f6723e39ba117097222f3ab8ef3e899a8a4af8b7e60c68337842bf` at
`/Users/oobi/Documents/kan-lang-tot-pin/_build/default/bin/tot.exe`,
built from tot commit `8cf0b8b` with a clean tree. Build that commit to
reproduce the reference checker.

The checker reports every rejection in this repository with the word
`mismatch`, except the axiom case, which reports `axiom`.

The fifteen checks:

- The theorem checks without a prelude or axioms.
- The proof is rejected against a commuted right side, `fmul y x`.
- The proof is rejected against a wrong denominator, `x` in place of
  `fadd x dx`.
- The proof is rejected when the fifth step of the chain is removed.
- The proof is rejected when the positivity of `dx` is replaced by a
  second use of the positivity of `x`.
- Eight checks, one for each law. Each check weakens that one law to a
  trivial or wrong statement and leaves the proof unchanged. The weaker
  text replaces the constructor field and the return type of the
  matching projection together, so the projection still checks and the
  rejection lands on `swapOutputIdentity`. Each one is rejected. Every
  law is load bearing.
- One check replaces the result of the `lawMulComm` arm by
  `mulComm b a`. The projection then contradicts its own return type,
  and the checker rejects it.
- A user axiom is rejected.

The negative controls show that specific proof terms are rejected. They
do not show that the false statements are unprovable.

No adjustment to the signature of the brief was necessary. The surface
accepts named binders in the constructor type of `fieldLaws`, so the
field names of the brief are kept. The checker did reject holes in the
erased argument slots of `trans0` and `cong0`, so the proof spells out
every carrier and every endpoint of the chain.

## Next milestones

1. Derive the eight laws from a smaller set of field axioms in tot, and
   build the record once with a def `fieldLawsOf`. The division laws need
   the disequality hypothesis that `mul_div_cancel_left₀` carries.
2. Port the other nineteen theorems of amm-lean against the record.
   Measure whether the per-theorem overhead falls after the bundle.
3. A tot data record bundling the eight field laws checks cleanly when
   the law fields carry quantity w, but fails with an erased-variable-
   used-at-runtime error when the same fields carry quantity 0 and a def
   projects one of them into a w position.
4. The checker rejects the theorem when the record binder L is marked
   quantity 0 because the body still matches on L at a runtime (w)
   position, reporting an erased variable used at runtime error.
5. The checker rejects a Type 0 record whose constructor carries a
   type-valued relation field (F to F to Type 0) at quantity w,
   reporting that the constructor argument lives above the declared
   universe, so the probeStatement written through projections was
   never reached.
6. A later constructor field may mention an earlier one and both Laws2
   and its opAdd2 projection check cleanly, but the lawAddComm2
   projection is rejected with a type mismatch because the declared
   return type stated through opAdd2 applications does not reduce to
   line up with the raw field variables bound inside the match.
7. The carrier type F may live inside the record when the record itself
   is declared at Type 1 and the carrier field F is left at quantity w,
   and the checker accepted carrierOf on the first attempt with no
   fallback to Type 0 or a 0-marked F needed.

Sources: `src/Foundation.tot`, `src/Field.tot`, `src/Invariant.tot`.
