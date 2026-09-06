# The AMM swap identity in tot

A standalone port of one theorem of amm-lean. The theorem is the core
algebraic identity of a constant-product automated market maker with no
fee. The port is verification only. It measures the cost of the same
proof in tot, a language with no fields, no division, no tactics and no
rewrite form. The theorem is proved twice: once against a record of the
eight field laws that the Lean proof cites, and once against a record of
seventeen ordered-field axioms, from which the eight laws are derived.

## Check

```sh
python3 test/check.py
```

Run from this directory. The runner uses the checker named by `TOT` when
that variable is set. Otherwise it uses the pinned checker at
`/Users/oobi/Documents/kan-lang-tot-pin/_build/default/bin/tot.exe` and
stops with a message when that file is absent. The runner concatenates
the nine source files, in the order of the Sources line at the end of
this file, in temporary files and checks with `--no-prelude --no-axioms`. It prints the checker
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

### The same identity from seventeen axioms

`swapOutputIdentityOf` in `src/Compose.tot` states the same identity
against the record `OrderedField` of `src/Axioms.tot`. That record holds
seventeen axioms of an ordered field as w fields, in the same style as
`FieldLaws`. `src/Ring.tot` proves six helper lemmas from the axioms.
`src/Laws.tot` proves each of the eight laws and builds the `FieldLaws`
record once, in the def `fieldLawsOf`. `src/Compose.tot` applies
`swapOutputIdentity` to that record, so its body is one application. The
composed theorem takes sixteen hypotheses: the carrier, eight operations,
the relation, the axiom record, three elements and two positivity proofs.

| field of `OrderedField` | statement | Mathlib source |
| --- | --- | --- |
| `addComm` | `fadd a b` equals `fadd b a` | `add_comm` |
| `addAssoc` | `fadd (fadd a b) c` equals `fadd a (fadd b c)` | `add_assoc` |
| `addZero` | `fadd a fzero` equals `a` | `add_zero` |
| `addNegCancel` | `fadd a (fneg a)` equals `fzero` | `add_neg_cancel` |
| `mulComm` | `fmul a b` equals `fmul b a` | `mul_comm` |
| `mulAssoc` | `fmul (fmul a b) c` equals `fmul a (fmul b c)` | `mul_assoc` |
| `mulOne` | `fmul a fone` equals `a` | `mul_one` |
| `mulAdd` | `fmul a (fadd b c)` equals `fadd (fmul a b) (fmul a c)` | `mul_add` |
| `subEqAddNeg` | `fsub a b` equals `fadd a (fneg b)` | `sub_eq_add_neg` |
| `divEqMulInv` | `fdiv a b` equals `fmul a (finv b)` | `div_eq_mul_inv` |
| `mulInvCancel` | if `a` is not `fzero`, `fmul a (finv a)` equals `fone` | `mul_inv_cancel₀` |
| `ltIrrefl` | `flt a a` gives `Empty` | `lt_irrefl` |
| `ltTrans` | `flt a b` and `flt b c` give `flt a c` | `lt_trans` |
| `addLtAddLeft` | `flt b c` gives `flt (fadd a b) (fadd a c)` | `add_lt_add_left` |
| `mulPos` | `flt fzero a` and `flt fzero b` give `flt fzero (fmul a b)` | `mul_pos` |
| `ltTrichotomy` | `flt a b`, `Eq F a b` or `flt b a` holds | `lt_trichotomy` |
| `zeroNeOne` | `Eq F fzero fone` gives `Empty` | `zero_ne_one` |

The disequality of `mulInvCancel` is a function from the equality to
`Empty`, as in `neOfGt`. The operations `fneg` and `finv` and the
element `fone` are new parameters of the axiom record. The eight
operations and the two elements carry quantity w in every def of the
derivation library, because a def body that is a plain application
checks at quantity w and passes them into w binders. The carrier and the
relation keep quantity 0.

The six helper lemmas of `src/Ring.tot`:

| helper | statement | Mathlib analogue |
| --- | --- | --- |
| `zeroAdd` | `fadd fzero a` equals `a` | `zero_add` |
| `negAddCancel` | `fadd (fneg a) a` equals `fzero` | `neg_add_cancel` |
| `addLeftCancel` | `fadd a b` equals `fadd a c` gives `b` equals `c` | `add_left_cancel` |
| `mulZero` | `fmul a fzero` equals `fzero` | `mul_zero` |
| `negEqOfAddEqZero` | `fadd a b` equals `fzero` gives `b` equals `fneg a` | `neg_eq_of_add_eq_zero_right` |
| `mulNeg` | `fmul a (fneg c)` equals `fneg (fmul a c)` | `mul_neg` |

The eight derived laws of `src/Laws.tot`. Equalities chained counts the
`trans0` applications plus one. The two order laws are one application
of an axiom with one `subst0` transport, so they chain no equality.

| law | Mathlib lemma | equalities chained | `cong0` | `sym0` | `subst0` |
| --- | --- | --- | --- | --- | --- |
| `addPos` | `add_pos` | 0 | 0 | 0 | 1 |
| `neOfGt` | `ne_of_gt` | 0 | 0 | 0 | 1 |
| `mulSub` | `mul_sub` | 4 | 2 | 1 | 0 |
| `mulDivAssoc` | `mul_div_assoc'` | 3 | 1 | 2 | 0 |
| `mulDivCancelLeft` | `mul_div_cancel_left₀` | 5 | 2 | 0 | 0 |
| `addMul` | `add_mul` | 4 | 2 | 0 | 0 |
| `mulComm` | `mul_comm` | 1 | 0 | 0 | 0 |
| `addSubCancelRight` | `add_sub_cancel_right` | 4 | 1 | 0 | 0 |

Each Lean lemma is one Mathlib theorem whose proof instance resolution
supplies. The tot version writes the proof from the axioms.

## The order and fraction library

The thirty structural theorems of amm-lean that this port does not cover
yet cite about thirty Mathlib order and fraction lemmas, among them
`mul_pos`, `sub_pos`, `div_lt_iff₀`, `div_pos`, `div_div` and
`div_eq_div_iff`. None of them follows from the axioms as M2 left the
record, because that record had no multiplication-order axiom, no
totality and no `zero_ne_one`. The record now holds seventeen
axioms, and two files derive every cited lemma from them. The comment in
`src/Compose.tot` still says fourteen axioms, because M3a does not
change that file.

`src/Frac.tot` holds the twelve `Eq` lemmas of the fraction library. It
cites `src/Axioms.tot` and `src/Ring.tot`, and it cites nothing in
`src/Order.tot`. `src/Order.tot` holds `exfalso`, `fle` and the
twenty-four order lemmas. Every def of both files takes the eleven
parameters of the defs of `src/Ring.tot`, then its own arguments, and
destructures the record `A` with one match. Every new proof binder
carries quantity w, so that a later milestone can store such a proof in
a record field, and a w value passes into any 0 slot. Three binders of
these two files stay at quantity 0, and the checker forces each one. The
first is the binder inside `fle`, because the `not_lt` form erases it.
The second is the second hypothesis of `ltAsymm`, because `leOfLt` gives
that erased binder to it. The third is the nonzero hypothesis of a
denominator, which stays at quantity 0 when the body only forwards it
into a 0 slot, and which carries w when the body applies it or gives it
to a w slot.

Two conventions hold in both files. First, `fle F flt a b` is the
`not_lt` form of `a <= b`. It is the type of a function from a proof of
`flt b a` to `Empty`. tot has no `Prop` and no order class, so the
library states `<=` in this way, and `exfalso` eliminates `Empty` into
any type. `fle` and `exfalso` are reducible defs, because a plain def is
opaque to conversion and the statements read their unfoldings. Second,
every fraction lemma takes one nonzero hypothesis for each denominator,
because `inv_zero` is not an axiom of `src/Axioms.tot`, so nothing here
fixes the value of `finv fzero`. M3b discharges the `div_nonneg`
obligations of `addLiquidity` with `divPos` and `leOfLt`.

The `rewrites` column counts the `trans0` applications of the def plus
one, so it is the number of equalities that the def chains. A def whose
body is a plain term, or one application with `subst0` transports,
chains no equality and counts 0. A line that holds two `trans0` counts
twice. The `lines` column counts from the `def` line to the `check`
line.

| tot name | Mathlib name | file | lines | rewrites |
| --- | --- | --- | --- | --- |
| `negNeg` | `neg_neg` | `src/Frac.tot` | 15 | 0 |
| `zeroMul` | `zero_mul` | `src/Frac.tot` | 18 | 2 |
| `negMulNeg` | `neg_mul_neg` | `src/Frac.tot` | 41 | 5 |
| `oneMul` | `one_mul` | `src/Frac.tot` | 18 | 2 |
| `invEqOfMulEqOne` | `inv_eq_of_mul_eq_one_right` | `src/Frac.tot` | 53 | 6 |
| `mulNeZero` | `mul_ne_zero` | `src/Frac.tot` | 60 | 7 |
| `mulInv` | `mul_inv` | `src/Frac.tot` | 81 | 7 |
| `divMulCancel` | `div_mul_cancel₀` | `src/Frac.tot` | 33 | 5 |
| `mulDivCancelRight` | `mul_div_cancel_right₀` | `src/Frac.tot` | 28 | 4 |
| `divDiv` | `div_div` | `src/Frac.tot` | 36 | 5 |
| `mulDivMulRight` | `mul_div_mul_right` | `src/Frac.tot` | 41 | 8 |
| `divEqDivOfMulEq` | `div_eq_div_iff` | `src/Frac.tot` | 82 | 14 |
| `ltAsymm` | `lt_asymm` | `src/Order.tot` | 13 | 0 |
| `leOfLt` | `le_of_lt` | `src/Order.tot` | 13 | 0 |
| `leOfEq` | `le_of_eq` | `src/Order.tot` | 17 | 0 |
| `leRefl` | `le_refl` | `src/Order.tot` | 13 | 0 |
| `ltOfLtOfLe` | `lt_of_lt_of_le` | `src/Order.tot` | 17 | 0 |
| `addLtAddRight` | `add_lt_add_right` | `src/Order.tot` | 23 | 0 |
| `ltOfAddLtAddLeft` | `lt_of_add_lt_add_left` | `src/Order.tot` | 57 | 5 |
| `ltAddOfPosRight` | `lt_add_of_pos_right` | `src/Order.tot` | 18 | 0 |
| `ltAddOfPosLeft` | `lt_add_of_pos_left` | `src/Order.tot` | 18 | 0 |
| `negNegOfPos` | `neg_neg_of_pos` | `src/Order.tot` | 23 | 0 |
| `negPosOfNeg` | `neg_pos` | `src/Order.tot` | 23 | 0 |
| `subPosOfLt` | `sub_pos` | `src/Order.tot` | 26 | 0 |
| `ltOfSubPos` | `sub_pos` | `src/Order.tot` | 58 | 5 |
| `subLtSelf` | `sub_lt_self` | `src/Order.tot` | 27 | 0 |
| `leAddOfNonnegRight` | `le_add_of_nonneg_right` | `src/Order.tot` | 24 | 0 |
| `zeroLtOne` | `zero_lt_one` | `src/Order.tot` | 37 | 2 |
| `mulLtMulOfPosRight` | `mul_lt_mul_of_pos_right` | `src/Order.tot` | 48 | 4 |
| `mulLtMulOfPosLeft` | `mul_lt_mul_of_pos_left` | `src/Order.tot` | 23 | 0 |
| `mulLtOfLtOneRight` | `mul_lt_of_lt_one_right` | `src/Order.tot` | 18 | 0 |
| `invPos` | `inv_pos` | `src/Order.tot` | 66 | 4 |
| `divPos` | `div_pos` | `src/Order.tot` | 19 | 0 |
| `divLtOfLtMul` | `div_lt_iff₀` | `src/Order.tot` | 43 | 3 |
| `invLtInvOfLt` | `inv_lt_inv_of_lt` | `src/Order.tot` | 65 | 5 |
| `divLtDivOfPosLeft` | `div_lt_div_of_pos_left` | `src/Order.tot` | 29 | 0 |

`subPosOfLt` and `ltOfSubPos` are the two directions of `sub_pos`.
`ltAsymm`, `leOfLt`, `leRefl` and `ltOfLtOfLe` give the order interface
that the structural theorems read. `zeroLtOne` needs all three new
axioms: it takes the trichotomy of `fzero` and `fone`, it refutes the
equality with `zeroNeOne`, and it refutes `flt fone fzero` with
`mulPos` on `fneg fone` and `negMulNeg`.

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

The derivation library, in proof-term occurrences. Comment lines are
excluded from the counts.

| file | lines | `trans0` | `cong0` | `sym0` | `subst0` |
| --- | --- | --- | --- | --- | --- |
| `src/Axioms.tot` | 50 | 0 | 0 | 0 | 0 |
| `src/Ring.tot` | 221 | 16 | 7 | 10 | 0 |
| `src/Laws.tot` | 300 | 15 | 8 | 3 | 2 |
| `src/Compose.tot` | 19 | 0 | 0 | 0 | 0 |
| `src/Frac.tot` | 534 | 54 | 35 | 20 | 0 |
| `src/Order.tot` | 763 | 21 | 12 | 14 | 34 |
| total | 1887 | 106 | 62 | 47 | 36 |

The library costs 1887 lines once, for seventeen axioms, six helpers,
the eight laws, the composed theorem and the thirty-six lemmas of the
order and fraction library. The Lean side costs nothing here,
because Mathlib supplies the same lemmas. The composed theorem has
sixteen hypotheses in the signature and one application in the body.

`test/check.py` runs in about 0.8 seconds of wall time on the pinned
checker, for all thirty-eight cases.

## Scope and trust

The eight laws are theorems of `src/Laws.tot`, proved from the seventeen
axioms of `OrderedField`. Those axioms are hypotheses, not tot axioms.
The records `FieldLaws` and `OrderedField` are hypotheses of the same
kind: this repository supplies no inhabitant of either one. No file
declares an axiom, and `--no-axioms` rejects any axiom. Nothing in this
repository asserts that an ordered field exists. The signatures of
`swapOutputIdentity` and `swapOutputIdentityOf` therefore have no tot
inhabitant that this repository supplies: a caller must supply the
operations and one record. Both theorems are conditional on them.

The standalone foundation declares only `Empty` and indexed
propositional `Eq`, with `subst0`, `J0`, `sym0`, `trans0` and `cong0`.
Those seven items are copied verbatim from the tot prelude. There are no
postulates, admitted proofs or placeholder theorems. The default prelude
is excluded, including its unrelated IO-law axioms. Checking trusts
tot's current elaborator and kernel. This project does not establish
their metatheoretic soundness.

The port covers one theorem, in two forms. The other thirty theorems of
amm-lean are not ported. The order and fraction library holds thirty-six
lemmas that those theorems cite. It declares no axiom of its own: every
lemma is a def with a proof term, and the only new hypotheses are the
three fields that the record gained.

## Validation

On 2026-09-06, all thirty-eight checks passed with checker SHA-256
`30c4524d57f6723e39ba117097222f3ab8ef3e899a8a4af8b7e60c68337842bf` at
`/Users/oobi/Documents/kan-lang-tot-pin/_build/default/bin/tot.exe`,
built from tot commit `8cf0b8b` with a clean tree. Build that commit to
reproduce the reference checker.

The checker reports every rejection in this repository with the word
`mismatch`, except the axiom case, which reports `axiom`.

The thirty-eight checks:

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
- Seventeen checks, one for each axiom. Each check weakens that one axiom
  to a reflexive or trivial statement and leaves every proof unchanged.
  The first def that uses the axiom is rejected. Every axiom is load
  bearing. The three axioms of M3a fail at the defs that read them
  first: `mulPos` at `zeroLtOne`, `ltTrichotomy` at `ltOfLtOfLe` and
  `zeroNeOne` at `zeroLtOne`.
- One check replaces the body of `deriveMulComm` by `mulComm b a`. The
  def then contradicts its own return type.
- One check exchanges the `deriveAddMul` and `deriveMulComm` arguments
  of `fieldLawsOf`. The constructor then receives a law of the wrong
  type.
- A user axiom is rejected.
- Four checks, one for each of four lemmas of the library. Each check
  changes the result type of one def and keeps its proof, so the proof
  proves the original statement and the checker reports the mismatch at
  that def. `subPosOfLt` states `flt fzero (fsub b a)`, `divDiv` states
  `fdiv a (fmul c b)`, `invPos` states `flt (finv a) fzero`, and
  `divLtDivOfPosLeft` states `flt (fdiv a c) (fdiv a b)`. Each one is
  rejected at its own def.

For the seven checks that M3a adds, the runner also reads the position
of the diagnostic and confirms the name of the first failing def. A
mutation that moves the rejection to another def fails the case. Each
mutation helper asserts the exact number of occurrences of its anchor,
so a rename in a source file stops the runner instead of weakening a
case.

The negative controls show that specific proof terms are rejected. They
do not show that the false statements are unprovable.

No adjustment to the signature of the brief was necessary. The surface
accepts named binders in the constructor type of `fieldLaws`, so the
field names of the brief are kept. The checker did reject holes in the
erased argument slots of `trans0` and `cong0`, so the proof spells out
every carrier and every endpoint of the chain.

The derivation library also used the signatures of its brief verbatim.
The one design rule it needed is the quantity of the operations, stated
above.

## Probe results

Ten facts about tot, found with scratch files. The first five come from
the record milestone and the last five come from the M3a probes. The
scratch files are not part of this repository.

- A data record that bundles the eight field laws checks when the law
  fields carry quantity w. When the fields carry quantity 0 and a def
  projects one of them into a w position, the checker reports an erased
  variable used at runtime.
- The record binder of the theorem cannot carry quantity 0, because the
  body matches on it at a w position. The checker reports an erased
  variable used at runtime.
- A record at `Type 0` cannot hold a type-valued field, such as a
  relation `F -> F -> Type 0`, at quantity w. The checker reports that
  the constructor argument lives above the declared universe. A
  statement written through projections of such a record was therefore
  out of reach.
- A later constructor field may mention an earlier one. The record and
  its first projection check. A projection whose return type is stated
  through an earlier projection is rejected with a type mismatch,
  because the declared return type does not reduce against the raw field
  variables bound inside the match.
- The carrier type may live inside the record when the record is
  declared at `Type 1` and the carrier field keeps quantity w. The
  checker accepted this form on the first attempt.
- A plain def is opaque to conversion. `Eq F (sq a) (fmul a a)` is
  rejected for a plain `def sq` and accepted for a `reducible def sq`.
  Every def whose unfolding a later statement reads must be a reducible
  def. In this repository that concerns `exfalso` and `fle` only.
- A data type with two or three constructors, and a match with one arm
  for each constructor, check. A constructor payload at quantity w binds
  at quantity w in the arm, so an arm may return the payload.
- `Empty` is eliminated by an arm-less match with a return motive,
  `match e as x return A with end`. The binder may carry quantity 0.
- A reducible def may return `Type 0` and serve as the type of a binder.
  `fle` is such a def, and `fle F flt a b` is the type of a hypothesis
  and the result type of a def.
- A dependent proof field of a record projects through
  `match p as q return P q`, when the projection is a reducible def and
  the field carries quantity w. A plain def is rejected, because the
  declared return type does not reduce against the field variables that
  the match binds.

## Next milestones

1. M3b: `Pool` and `FeeRate` as data records with w proof fields and
   reducible projections, the fifteen definitions of `AmmLean/Basic.lean`
   as reducible defs, the eight theorems of that file, and the eleven
   positivity obligations of `swap`, `swapWithFee`, `addLiquidity` and
   `removeLiquidity`.
2. M3c: the four theorems of `AmmLean/Invariant.lean` and the six
   theorems of `AmmLean/NoDrain.lean`.
3. M3d: the five theorems of `AmmLean/PriceImpact.lean` and the seven
   theorems of `AmmLean/Liquidity.lean`. M3b, M3c and M3d together port
   the other thirty theorems of amm-lean. Measure whether the
   per-theorem overhead falls once the record, the derivation library
   and the order and fraction library exist.
4. Supply a concrete carrier: an inhabitant of `OrderedField` for one
   type, so that both theorems have a closed instance. tot has no
   rationals, so the carrier is a milestone of its own.

Sources: `src/Foundation.tot`, `src/Field.tot`, `src/Invariant.tot`,
`src/Axioms.tot`, `src/Ring.tot`, `src/Laws.tot`, `src/Compose.tot`,
`src/Frac.tot`, `src/Order.tot`.
