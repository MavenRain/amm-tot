# The AMM swap identity in tot

A standalone port of one theorem of amm-lean. The theorem is the core
algebraic identity of a constant-product automated market maker with no
fee. The port is verification only. It measures the cost of the same
proof in tot, a language with no fields, no division, no tactics and no
rewrite form. The theorem is proved twice: once against a record of the
eight field laws that the Lean proof cites, and once against a record of
seventeen ordered-field axioms, from which the eight laws are derived.
The port also states the AMM itself: the two data records of
`AmmLean/Basic.lean`, its nine definitions and its eight theorems. It
also proves the four remaining theorems of `AmmLean/Invariant.lean`, the
six theorems of `AmmLean/NoDrain.lean`, the five theorems of
`AmmLean/PriceImpact.lean` and the seven theorems of
`AmmLean/Liquidity.lean`. Every theorem of amm-lean is ported.

## Check

```sh
python3 test/check.py
```

Run from this directory. The runner uses the checker named by `TOT` when
that variable is set. Otherwise it uses the pinned checker at
`/Users/oobi/Documents/kan-lang-tot-pin/_build/default/bin/tot.exe` and
stops with a message when that file is absent. The runner concatenates
the seventeen source files of `src`, in the order in which the Sources line
at the end of
this file names them, in temporary files and checks with `--no-prelude --no-axioms`. It prints the checker
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

Every theorem of amm-lean is ported. The pilot proves
`swap_output_identity`, M3b proves the eight theorems of
`AmmLean/Basic.lean`, M3c proves the four remaining theorems of
`AmmLean/Invariant.lean` and the six theorems of `AmmLean/NoDrain.lean`,
and M3d proves the five theorems of `AmmLean/PriceImpact.lean` and the
seven theorems of `AmmLean/Liquidity.lean`. That is thirty-one theorems.

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
`src/Compose.tot` now says seventeen axioms, because M3b corrects that
one word.

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

## The pool and the fee rate

`src/Pool.tot` holds the two data records of `AmmLean/Basic.lean`.
`Pool` takes the parameters `F`, `fzero` and `flt`, and it has the six
fields `reserveX`, `reserveY`, `totalLP`, `hx : flt fzero reserveX`,
`hy : flt fzero reserveY` and `hlp : flt fzero totalLP`. `FeeRate` takes
the parameters `F`, `fzero`, `fone` and `flt`, and it has the three
fields `rate`, `hpos : flt fzero rate` and `hlt : flt rate fone`. No
operation of the field appears in either record type. The parameters
carry quantity 0, because a data type parameter must. The nine fields
carry quantity w, because a def projects each one into a w position.

The nine projections are `poolReserveX`, `poolReserveY`, `poolTotalLP`,
`poolHx`, `poolHy`, `poolHlp`, `feeRateRate`, `feeRateHpos` and
`feeRateHlt`. Each one is a reducible def. One rule governs them: a
dependent proof projection needs its value projection to be a reducible
def. `poolHx` states `flt fzero (poolReserveX F fzero flt p)` and it
projects through `match p as q return flt fzero (poolReserveX F fzero
flt q) with`. That return type reduces against the field variables of
the arm only when `poolReserveX` unfolds, so a plain `def poolReserveX`
is rejected. The same rule holds for `poolHy`, `poolHlp`,
`feeRateHpos` and `feeRateHlt`.

`src/Basic.tot` holds the nine pure definitions. Each one is a reducible
def over the ten operation parameters, and none of them takes the axiom
record, because no pure definition needs an axiom. Each body reads the
pool and the fee rate through the projections and never matches on the
variable, because a match on a variable pool is stuck and blocks every
later unfolding. The `let` bindings of `Basic.lean`, that is `dy`,
`ein`, `mintedLP`, `dxOut` and `dyOut`, are inlined.

| Lean name | tot name | `Basic.lean` line | `Basic.tot` line |
| --- | --- | --- | --- |
| `constantProduct` | `constantProduct` | 76 | 14 |
| `swapOutput` | `swapOutput` | 92 | 24 |
| `effectivePrice` | `effectivePrice` | 101 | 34 |
| `spotPrice` | `spotPrice` | 109 | 44 |
| `FeeRate.complement` | `feeComplement` | 146 | 54 |
| `effectiveInput` | `effectiveInput` | 161 | 64 |
| `swapOutputWithFee` | `swapOutputWithFee` | 169 | 74 |
| `redeemX` | `redeemX` | 226 | 84 |
| `redeemY` | `redeemY` | 232 | 94 |

The eight theorems of `Basic.lean` follow. Each one is a plain def over
the eleven parameters, and each one cites one axiom field or one lemma
of the library.

| Lean name | tot name | Mathlib lemma | library lemma |
| --- | --- | --- | --- |
| `constantProduct_pos`, line 79 | `constantProductPos` | `mul_pos` | axiom field `mulPos` |
| `FeeRate.complement_pos`, line 148 | `feeComplementPos` | `sub_pos.mpr` | `subPosOfLt` |
| `FeeRate.complement_lt_one`, line 151 | `feeComplementLtOne` | `sub_lt_self` | `subLtSelf` |
| `Pool.reserveX_ne_zero`, line 265 | `poolReserveXNeZero` | `ne_of_gt` | `deriveNeOfGt` |
| `Pool.reserveY_ne_zero`, line 269 | `poolReserveYNeZero` | `ne_of_gt` | `deriveNeOfGt` |
| `Pool.totalLP_ne_zero`, line 273 | `poolTotalLPNeZero` | `ne_of_gt` | `deriveNeOfGt` |
| `reserveX_add_pos`, line 277 | `reserveXAddPos` | `add_pos` | `deriveAddPos` |
| `reserveX_add_ne_zero`, line 282 | `reserveXAddNeZero` | `ne_of_gt` | `deriveNeOfGt` |

A nonzero statement is written inline as `(0 e : Eq F x fzero) -> Empty`,
and `deriveNeOfGt` takes the positivity proof, so each of the four
nonzero theorems is one partial application with two arguments.

Lean proves the positivity of each new field inline, inside the four
structure literals of `swap`, `swapWithFee`, `addLiquidity` and
`removeLiquidity`. tot proves each one as a named def, so that the four
constructors stay match-free. There are ten positivity obligations, not
eleven, because `swap` and `swapWithFee` carry the LP proof through
unchanged. The chain length counts the `trans0` steps and the `subst0`
steps of the proof term.

| Lean site | tot name | chain length |
| --- | --- | --- |
| `swap.hx`, line 117 | `swapHx` | 0 `trans0`, 0 `subst0` |
| `swap.hy`, line 117 | `swapHy` | 0 `trans0`, 1 `subst0` |
| `swapWithFee.hx`, line 182 | `swapWithFeeHx` | 0 `trans0`, 0 `subst0` |
| `swapWithFee.hy`, line 182 | `swapWithFeeHy` | 0 `trans0`, 1 `subst0` |
| `addLiquidity.hx`, line 208 | `addLiquidityHx` | 0 `trans0`, 0 `subst0` |
| `addLiquidity.hy`, line 208 | `addLiquidityHy` | 0 `trans0`, 0 `subst0` |
| `addLiquidity.hlp`, line 208 | `addLiquidityHlp` | 0 `trans0`, 0 `subst0` |
| `removeLiquidity.hx`, line 243 | `removeLiquidityHx` | 0 `trans0`, 1 `subst0` |
| `removeLiquidity.hy`, line 243 | `removeLiquidityHy` | 0 `trans0`, 1 `subst0` |
| `removeLiquidity.hlp`, line 243 | `removeLiquidityHlp` | 0 `trans0`, 0 `subst0` |

The three obligations with no transport cite `reserveXAddPos` and
nothing else. `addLiquidityHy` and `addLiquidityHlp` hold four library
calls each over the axiom field `mulPos`, that is `divPos`, `leOfLt`,
`leAddOfNonnegRight` and `ltOfLtOfLe`. `swapHy` and `swapWithFeeHy` each
transport one endpoint along `sym0` of `mulAdd`, and
`removeLiquidityHx` and `removeLiquidityHy` each transport one endpoint
along `mulComm`, which already points the right way.

The four constructors are reducible defs with match-free bodies. Each
body is one `pool` application with the three data parameters given
explicitly.

- `swap` computes `fadd rx dx` and `fsub ry (swapOutput OPS p dx)` and
  keeps `lpT`. It cites `swapHx`, `swapHy` and `poolHlp`.
- `swapWithFee` computes `fadd rx dx` and
  `fsub ry (swapOutputWithFee OPS p dx f)` and keeps `lpT`. It cites
  `swapWithFeeHx`, `swapWithFeeHy` and `poolHlp`. The full `dx` is
  deposited and the output is computed from the effective input.
- `addLiquidity` computes `fadd rx dx`, `fadd ry (fdiv (fmul dx ry) rx)`
  and `fadd lpT (fdiv (fmul dx lpT) rx)`. It cites `addLiquidityHx`,
  `addLiquidityHy` and `addLiquidityHlp`.
- `removeLiquidity` computes `fsub rx (redeemX OPS p lp)`,
  `fsub ry (redeemY OPS p lp)` and `fsub lpT lp`. It cites
  `removeLiquidityHx`, `removeLiquidityHy` and `removeLiquidityHlp`.

Here `rx`, `ry` and `lpT` are the three value projections of `p`, and
the files spell them out.

The three unfolding lemmas `swapReserveX`, `swapReserveY` and
`swapTotalLP` state the three components of `swap PARAMS p dx hdx`, and
`refl F TERM` proves each one. Probe P3 is green: the delta step of the
reducible constructor and the iota step of the projection match both
fire. M3c states its theorems on `swap PARAMS p dx hdx` and on
`swapWithFee PARAMS p dx hdx f` directly, and it cites none of the three
unfolding lemmas.

## The constant product and the no-drain property

Two files hold the ten theorems that M3c ports. `src/Product.tot` holds
the four remaining theorems of `AmmLean/Invariant.lean`, and
`src/NoDrain.tot` holds the six theorems of `AmmLean/NoDrain.lean`. The
split follows the Lean side, where `NoDrain.lean` imports
`AmmLean.Invariant`. There are two files and not one, because
`src/Invariant.tot` already holds the pilot theorem
`swap_output_identity`, which is the fifth theorem of `Invariant.lean`.
`src/Product.tot` comes before `src/NoDrain.tot` in the check order,
because `constantProductLowerBound` cites `swapPreservesProduct` and
`swapOutputWithFeeLtReserveY` cites `effectiveInputPos`.

| Lean name | tot name | Lean line | Mathlib lemmas | tot lemmas or axiom fields | transports |
| --- | --- | --- | --- | --- | --- |
| `swap_preserves_product` | `swapPreservesProduct` | 68 | `kan_exact` | `swapOutputIdentityOf` | 0 |
| `effectiveInput_lt` | `effectiveInputLt` | 77 | `mul_lt_of_lt_one_right` | `mulLtOfLtOneRight`, `feeComplementLtOne` | 0 |
| `effectiveInput_pos` | `effectiveInputPos` | 84 | `mul_pos` | axiom field `mulPos`, `feeComplementPos` | 0 |
| `swap_with_fee_increases_product` | `swapWithFeeIncreasesProduct` | 106 | `mul_pos`, `mul_lt_of_lt_one_right`, `add_lt_add_iff_left`, `sub_pos`, `div_lt_iff`, `mul_add`, `lt_add_of_pos_left`, `mul_lt_mul_of_pos_right` | axiom field `addLtAddLeft`, `mulLtMulOfPosRight`, `swapOutputIdentityOf`, `swapWithFeeHy` | 1 |
| `swap_output_lt_reserveY` | `swapOutputLtReserveY` | 56 | `div_lt_iff`, `mul_add`, `lt_add_of_pos_left`, `mul_pos` | `divLtOfLtMul`, `ltAddOfPosLeft`, `reserveXAddPos`, axiom fields `mulPos` and `mulAdd` | 1 |
| `swap_output_pos` | `swapOutputPos` | 67 | `div_pos`, `mul_pos`, `add_pos` | `divPos`, `reserveXAddPos`, axiom field `mulPos` | 0 |
| `swap_output_with_fee_lt_reserveY` | `swapOutputWithFeeLtReserveY` | 76 | `div_lt_iff`, `mul_add`, `lt_add_of_pos_left`, `mul_pos` | `divLtOfLtMul`, `ltAddOfPosLeft`, `deriveAddPos`, `effectiveInputPos`, axiom fields `mulPos` and `mulAdd` | 1 |
| `reserveY_pos_after_swap` | `reserveYPosAfterSwap` | 90 | `sub_pos.mpr` | `subPosOfLt` | 0 |
| `reserveY_pos_after_swap_with_fee` | `reserveYPosAfterSwapWithFee` | 95 | `sub_pos.mpr` | `subPosOfLt` | 0 |
| `constant_product_lower_bound` | `constantProductLowerBound` | 113 | `le_of_eq`, `Eq.symm` | `leOfEq`, `sym0` | 0 |

The Lean line is the line of the `theorem` keyword in the Lean file. The
transports column counts the `subst0` occurrences of the tot proof.

The theorems are stated on the constructors directly. A statement names
`swap PARAMS p dx hdx` or `swapWithFee PARAMS p dx hdx f`, and the
checker unfolds it, because the delta step of the reducible constructor
and the iota step of the projection match both fire in conversion. The
three unfolding lemmas of M3b, `swapReserveX`, `swapReserveY` and
`swapTotalLP`, are therefore not cited by any theorem of M3c.

`reserveYPosAfterSwap` has the type of `swapHy` of `src/Basic.tot`. It
keeps the structure of the Lean proof, which applies `sub_pos.mpr` to
`swap_output_lt_reserveY`, and it does not cite `swapHy`.
`swapOutputLtReserveY` is the inner chain of `swapHy` without its outer
`subPosOfLt`, and `swapOutputWithFeeLtReserveY` is the inner chain of
`swapWithFeeHy` without its outer `subPosOfLt`.

## Price impact and liquidity

Two files hold the twelve theorems that M3d ports. `src/PriceImpact.tot`
holds the five theorems of `AmmLean/PriceImpact.lean`, and
`src/Liquidity.tot` holds the seven theorems of `AmmLean/Liquidity.lean`
and one helper def. There are two files and not one, because they mirror
the two Lean files one for one. `src/PriceImpact.tot` comes before
`src/Liquidity.tot` in the check order, as `Liquidity.lean` comes after
`PriceImpact.lean` in the Lean import order, although no def of
`src/Liquidity.tot` cites a def of `src/PriceImpact.tot`.

| Lean name | tot name | Lean line | Mathlib lemmas | tot lemmas or axiom fields | transports |
| --- | --- | --- | --- | --- | --- |
| `effective_price_eq` | `effectivePriceEq` | 56 | `div_div`, `mul_div_mul_right` | `divDiv`, `mulDivMulRight`, `reserveXAddNeZero`, `deriveNeOfGt` | 0 |
| `effective_price_lt_spot` | `effectivePriceLtSpot` | 71 | `div_lt_div_of_pos_left`, `lt_add_of_pos_right` | `divLtDivOfPosLeft`, `ltAddOfPosRight`, `effectivePriceEq` | 1 |
| `effective_price_decreasing` | `effectivePriceDecreasing` | 89 | `div_lt_div_of_pos_left`, `add_pos`, `add_lt_add_iff_left` | `divLtDivOfPosLeft`, `reserveXAddPos`, axiom field `addLtAddLeft`, `effectivePriceEq` | 2 |
| `effective_price_le_spot` | `effectivePriceLeSpot` | 104 | `le_of_lt` | `leOfLt`, `effectivePriceLtSpot` | 0 |
| `effective_price_pos` | `effectivePricePos` | 111 | `div_pos`, `add_pos` | `divPos`, `reserveXAddPos`, `effectivePriceEq` | 1 |
| `add_liquidity_preserves_ratio` | `addLiquidityPreservesRatio` | 64 | `div_eq_div_iff`, `add_mul`, `div_mul_cancel`, `mul_add`, `mul_comm` | `divEqDivOfMulEq`, `deriveAddMul`, `divMulCancel`, `deriveMulComm`, axiom field `mulAdd`, `reserveXAddNeZero`, `poolReserveXNeZero` | 2 |
| `add_liquidity_preserves_price` | `addLiquidityPreservesPrice` | 78 | none, it is a direct corollary | `addLiquidityPreservesRatio` | 0 |
| none, the helper of `lp_share_proportional` | `lpShareCross` | 91 | `mul_add`, `div_mul_cancel`, `mul_comm`, `mul_add` | axiom field `mulAdd`, `divMulCancel`, `deriveMulComm`, `poolReserveXNeZero` | 2 |
| `lp_share_proportional` | `lpShareProportional` | 91 | `div_eq_div_iff .mpr` | `divEqDivOfMulEq`, `lpShareCross`, `deriveNeOfGt`, `addLiquidityHlp`, `reserveXAddNeZero` | 0 |
| `redeem_proportional_x` | `redeemProportionalX` | 113 | `div_div`, `mul_div_mul_right` | `divDiv`, `mulDivMulRight`, `poolTotalLPNeZero`, `poolReserveXNeZero` | 0 |
| `redeem_proportional_y` | `redeemProportionalY` | 118 | `div_div`, `mul_div_mul_right` | `divDiv`, `mulDivMulRight`, `poolTotalLPNeZero`, `poolReserveYNeZero` | 0 |
| `add_remove_roundtrip_x` | `addRemoveRoundtripX` | 134 | `div_eq_div_iff .mp`, `mul_div_cancel_right` | `lpShareCross`, `mulDivCancelRight`, `deriveNeOfGt`, `addLiquidityHlp` | 1 |
| `add_remove_roundtrip_y` | `addRemoveRoundtripY` | 147 | `mul_comm`, `mul_div_assoc`, `mul_div_assoc` prime, and the two earlier theorems | `deriveMulComm`, `deriveMulDivAssoc`, `lpShareProportional`, `addLiquidityPreservesRatio` | 4 `cong0` in 7 `trans0` |

The Lean line is the line of the `theorem` keyword in the Lean file.
`lpShareCross` has no Lean name of its own, and it comes from the
`kan_rw` list of `lp_share_proportional` at line 91. The transports
column counts the `subst0` occurrences of the tot proof, except in the
last row, which counts the `cong0` steps of the chain.

`effectivePrice` unfolds twice: the delta step of `effectivePrice` gives
`fdiv (swapOutput OPS p dx) dx`, and the delta step of `swapOutput` then
gives `fdiv (fdiv (fmul ry dx) (fadd rx dx)) dx`. `effectivePriceEq`
folds that unfolding into one identity, and the other four theorems of
`src/PriceImpact.tot` transport along it.

The statements of `src/Liquidity.tot` name the projections of
`addLiquidity PARAMS p dx hdx`, as Lean names
`(addLiquidity p dx hdx).reserveY`. `addLiquidity` is a reducible def
whose body is one pool constructor application, so the delta step of the
constructor and the iota step of the projection match unfold the
projections by conversion. No unfolding lemma is cited.

tot has no iff, so `lpShareCross` holds the cross-multiplied identity
that Lean reads off `lp_share_proportional` with `div_eq_div_iff`. It is
a def of its own, and `lpShareProportional` and `addRemoveRoundtripX`
both cite it.

`effectivePricePos` keeps the structure of the Lean proof, which rewrites
by `effective_price_eq` and then applies `div_pos`. The design notes name
a shorter alternative, the one call
`divPos PARAMS out dx (swapOutputPos PARAMS p dx hdx) hdx`, which the
port does not use.

## The natural numbers

`src/Nat.tot` is the first slice of milestone M4, the concrete carrier.
Every ordered field is infinite, because `fzero`, `fone`,
`fadd fone fone` and their successors are all different by `zeroNeOne`
and the order axioms. No finite type can therefore inhabit
`OrderedField`, and the smallest carrier that this repository can build
is the rationals. The rationals stand on the integers, and the integers
stand on the naturals, so the carrier milestone starts with the natural
numbers.

The file holds three data types, 34 defs and nineteen theorems. The
three data types are `Nat`, the witness record `NatLt` and `Dec`. The
computing defs are `add`, `mul` and `sub`, which are reducible defs with
recursion on the first argument, and `one`, `pred`, `natFamZero` and
`natLt`, which are reducible defs. Every other def is a proof. The
nineteen theorems are the two constructor lemmas `succInj` and
`zeroNotSucc`, the seven semiring laws `addZero`, `addComm`, `addAssoc`,
`mulComm`, `mulAssoc`, `mulOne` and `mulAdd` in the `OrderedField` field
shapes, the cancellation law `addCancelLeft`, the five order laws
`ltIrrefl`, `ltTrans`, `addLtAddLeft`, `mulPos` and `ltTrichotomy`, the
separation law `zeroNeOne`, the two subtraction laws `subAdd` and
`natLtOfAddLtAddLeft`, and the decision procedure `natDecEq`. The
remaining defs are the helpers that the theorems cite: `addSuccRight`,
`addLeftComm`, `mulZeroRight`, `mulSuccRight`, `addMulRight`,
`succLtSucc`, `subZeroRight` and `subAddCancelLeft`.

The order is the witness record `NatLt`. The proposition `m < n` holds
when one `k` has `add m (succ k) = n`, so a proof of `natLt m n` is a
pair of the difference `k` and that equation. `ltIrrefl`, `ltTrans`,
`addLtAddLeft`, `mulPos`, `subAdd` and `natLtOfAddLtAddLeft` are then
equational: each one reads the difference off its hypothesis and closes
with `trans0`, `cong0` and `sym0`, and none of them recurses. M4b also
reads the difference off the witness, which is what the integers need.

The inductive relation `ltZero` and `ltSucc` was probed and it checks
too, but it costs more. Its `ltIrrefl` fails the structural termination
guard when it transports the hypothesis into the recursive call, so it
needs a generalized statement and a second def. Its `ltTrans` cannot
recurse on the second hypothesis, so it needs two inversion helpers and
one `exfalso`. Every elimination of the indexed family also needs a
motive that binds one name per index. The witness record needs none of
that, because `NatLt` carries parameters and no index. The witness
record is therefore the prescribed form.

`natLt` is a reducible def over `NatLt`, and not the data type former
itself, because `Trichotomy` takes its relation at quantity w while a
data type former carries its parameters at quantity 0. Conversion joins
`natLt m n` and `NatLt m n` by the delta step, so `ltWitness m n k e`
inhabits `natLt m n` with no wrapper.

M4a adds no axiom. The seventeen axioms of `OrderedField` are unchanged,
and `src/Nat.tot` names none of them, because it is a closed development
on one carrier and takes no parameters. It cites six declarations of the
fifteen files that stand before it: `Empty`, `Eq`, `subst0`, `sym0`,
`trans0` and `cong0` of `src/Foundation.tot`, and the `Trichotomy`
declaration of `src/Axioms.tot`. It cites nothing else of them.

## The integers

`src/Int.tot` is the second slice of milestone M4. The rationals stand
on the integers, so the carrier milestone builds them next. `data Int`
is the Lean core shape, with the two constructors `pos` and `negsucc`:
`pos n` is the natural number `n`, and `negsucc n` is the negation of
`succ n`, so every integer has exactly one constructor form and no
integer has two. `intZero` is `pos zero` and `intOne` is `pos one`, both
reducible defs, so each name and its constructor form are interchangeable
by the delta step. The file holds three data types and 64 defs. The
three data types are `Int`, the representation record `IntRepr` and the
witness record `IntLt`. Ten defs compute: the reducible def rec `intMk`
and the nine reducible defs `intZero`, `intOne`, `negOfNat`, `intNeg`,
`intAdd`, `intMul`, `natAbs`, `intFamPos` and `intLt`. The other 54 defs
are proofs.

The arithmetic rides one canonical difference function. `intMk a b` is
`a` minus `b` in canonical form: it is `negOfNat b` when `a` is zero, it
is `pos (succ p)` when `a` is `succ p` and `b` is zero, and it is
`intMk p q` when both are successors. The shift
`intMk (succ a) (succ b)` is therefore `intMk a b` by conversion and not
by a lemma, so no def of the file states it, and every proof writes the
smaller term where the larger one is expected. `intMk` is the only
reducible def rec of the file, and every law of `intAdd` and `intMul` is
one equational chain over `intMk` forms, carried by `intAddMk`,
`intMulMk`, `intMkAddCancel`, `intMkCong2` and `intMkDiag`.

`data IntRepr` and `intReprOf` say that every integer is a canonical
difference: `intReprOf x` returns two naturals `a` and `b` and the
equation `intMk a b = x`. A law of three variables, and any law that
mixes `intAdd` and `intMul`, is a wrapper that opens one representation
per variable and transports its goal with one `subst0` per variable,
innermost variable first, down to a core lemma stated on `intMk` forms.
`intAddAssoc`, `intMulComm`, `intMulAssoc`, `intMulAdd`, `intMulNeg` and
`intLtTrichotomy` take that route, over the six cores
`intAddAssocCore`, `intMulCommCore`, `intMulAssocCore`,
`intMulAddCore`, `intMulNegCore` and `intLtTrichotomyCore`. A law of one
or two variables takes the direct constructor split instead, because the
four arms of the operation table already are the case analysis: in
`intAddComm` two arms close by conversion, since
`intAdd (pos m) (negsucc n)` and `intAdd (negsucc n) (pos m)` are the
same term `intMk m (succ n)`, and the other two are one `cong0` of
`addComm` each, which costs eleven lines against the twenty four of the
transport route. `intAddComm`, `intAddZero`, `intAddNegCancel`,
`intMulOne`, `intMulZero`, `natAbsMul`, `intMulEqZeroRight` and
`intDecEq` take the split.

The order is the witness record `IntLt`, in the `NatLt` shape of
`src/Nat.tot`. The proposition `x < y` holds when one `k` has
`intAdd x (pos (succ k)) = y`, so a proof of `intLt x y` is a pair of
the difference `k` and that equation. Both fields carry quantity 0, so
the four order laws accept erased hypotheses with the exact signatures
required by `OrderedField`. The witness is available in proofs and
erased from runtime computation. The record is not a comparison of
the two components of a canonical difference: an integer is a
constructor form and not a pair, `intMk a b` and
`intMk (succ a) (succ b)` are the same integer, and a comparison of
components would
therefore need a four way constructor split and its own shift lemma in
every proof. The witness carries one equation instead, so
`intLtIrrefl`, `intLtTrans`, `intAddLtAddLeft` and `intMulPos` read the
difference off the hypothesis and close with the addition laws, and none
of them recurses. `intLt` is a reducible def over `IntLt`, and not the
data type former itself, because `Trichotomy` takes its relation at
quantity w while a data type former carries its parameters at quantity
0. Conversion joins `intLt x y` and `IntLt x y` by the delta step, so
`intLtWitness x y k e` inhabits `intLt x y` with no wrapper.

The `OrderedField` record carries nine operation parameters, `fadd`,
`fmul`, `fsub`, `fdiv`, `fneg`, `finv`, `fzero`, `fone` and `flt`, and
states seventeen axioms over them. The fourteen axiom shapes that name
no subtraction, no division and no inverse are all present, with F
`Int`, fadd `intAdd`, fmul `intMul`, fneg `intNeg`, fzero `intZero`,
fone `intOne` and flt `intLt`:
the eight ring shapes `intAddComm`, `intAddAssoc`, `intAddZero`,
`intAddNegCancel`, `intMulComm`, `intMulAssoc`, `intMulOne` and
`intMulAdd`, and the six order shapes `intLtIrrefl`, `intLtTrans`,
`intAddLtAddLeft`, `intMulPos`, `intLtTrichotomy` and `intZeroNeOne`.

M4b adds no axiom. The seventeen axioms of `OrderedField` are unchanged,
and `src/Int.tot` names none of them, because it is a closed development
on the two carriers `Int` and `Nat` and takes no parameters. It cites
six declarations of `src/Foundation.tot`, `Empty`, `Eq`, `subst0`,
`sym0`, `trans0` and `cong0`, the `Trichotomy` declaration of
`src/Axioms.tot`, and the named laws of `src/Nat.tot`, which are
`succInj`, `zeroNotSucc`, `addZero`, `addSuccRight`, `addComm`,
`addAssoc`, `addLeftComm`, `mulZeroRight`, `mulSuccRight`, `mulComm`,
`addMulRight`, `mulAssoc`, `mulOne`, `mulAdd`, `ltTrichotomy`,
`zeroNeOne` and `natDecEq`, beside the carriers `Nat` and `Dec` and the
computing defs `add`, `mul` and `one`. It cites nothing else of the
sixteen frozen files.

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

`AmmLean/Basic.lean` against the two files that port it.

| Quantity | `AmmLean/Basic.lean` | `src/Pool.tot` and `src/Basic.tot` |
| --- | --- | --- |
| Lines | 286 | 86 and 634 |
| Structures, or data records | 2 | 2 |
| Definitions | 13 | 9 projections, 9 pure defs, 4 constructors |
| Theorems | 8 | 8 theorems, 10 obligations, 3 unfolding lemmas |

The Lean file counts thirteen definitions, because Lean states the four
pool-constructing definitions and the nine pure definitions in one file.
The tot side splits them: `src/Pool.tot` holds the nine projections that
Lean gets from its structure syntax for free, and `src/Basic.tot` holds
the nine pure defs, the eight theorems, the ten positivity obligations
that Lean proves inline, the four constructors and the three unfolding
lemmas. The two files hold 720 lines and 43 defs.

The two new files, in proof-term occurrences. Comment lines are excluded
from the counts.

| file | lines | `trans0` | `cong0` | `sym0` | `subst0` |
| --- | --- | --- | --- | --- | --- |
| `src/Pool.tot` | 86 | 0 | 0 | 0 | 0 |
| `src/Basic.tot` | 634 | 0 | 0 | 2 | 4 |

`src/Pool.tot` holds no rewrite, because every projection is one match.
The four `subst0` of `src/Basic.tot` are the transports of `swapHy`,
`swapWithFeeHy`, `removeLiquidityHx` and `removeLiquidityHy`, and the
two `sym0` are the symmetric forms of `mulAdd` in the first two of them.
No def of either file holds a `trans0` or a `cong0`, because no
obligation chains two equalities.

`AmmLean/Invariant.lean` and `AmmLean/NoDrain.lean` against the two files
that port their ten theorems.

| Quantity | `AmmLean/Invariant.lean` | `src/Product.tot` | `AmmLean/NoDrain.lean` | `src/NoDrain.tot` |
| --- | --- | --- | --- | --- |
| Lines | 126 | 105 | 117 | 173 |
| Theorems | 5 | 4 | 6 | 6 |

`AmmLean/Invariant.lean` holds five theorems, and the pilot ported one of
them, `swap_output_identity` at line 56. `src/Product.tot` holds the
other four, and `src/NoDrain.tot` holds all six theorems of
`AmmLean/NoDrain.lean`. Every def of both files is a plain def, because
no statement of M3c reads the unfolding of an M3c def.

The four theorems of `AmmLean/Invariant.lean` that `src/Product.tot`
ports hold 28 Lean lines, and the four tot defs hold 82 lines without
their four `check` lines, which is 2.9 times the Lean text. The six
theorems of `AmmLean/NoDrain.lean` hold 27 Lean lines, and the six tot
defs hold 144 lines without their six `check` lines, which is 5.3 times
the Lean text. Blank lines, comment lines and doc comments are excluded
from all four counts. The pilot theorem costs 55 tot lines in its record
form against 5 Lean lines, which is 11 times the Lean text, so the
per-theorem overhead falls once the libraries exist. That is the
question of the M3d item of Next milestones, and the M3d counts below
answer it again.

M3c adds no library lemma and no axiom. Every lemma that the ten
theorems cite is a lemma that M2, M3a or M3b already proved, and every
axiom field that they name is one of the seventeen axioms of
`OrderedField`.

The two files of M3c, in proof-term occurrences. Comment lines are
excluded from the counts.

| file | lines | `trans0` | `cong0` | `sym0` | `subst0` |
| --- | --- | --- | --- | --- | --- |
| `src/Product.tot` | 105 | 0 | 0 | 0 | 1 |
| `src/NoDrain.tot` | 173 | 0 | 0 | 3 | 2 |

The one `subst0` of `src/Product.tot` is the transport of
`swapWithFeeIncreasesProduct` along `swapOutputIdentityOf`. The two
`subst0` of `src/NoDrain.tot` are the transports of
`swapOutputLtReserveY` and of `swapOutputWithFeeLtReserveY` along the
symmetric form of the axiom field `mulAdd`, and the two `sym0` of those
two defs build that symmetric form. The third `sym0` is the symmetric
form of `swapPreservesProduct` inside `constantProductLowerBound`. No
def of either file holds a `trans0` or a `cong0`, because no theorem
chains two equalities.

`AmmLean/PriceImpact.lean` and `AmmLean/Liquidity.lean` against the two
files that port their twelve theorems.

| Quantity | `AmmLean/PriceImpact.lean` | `src/PriceImpact.tot` | `AmmLean/Liquidity.lean` | `src/Liquidity.tot` |
| --- | --- | --- | --- | --- |
| Lines | 116 | 151 | 171 | 293 |
| Theorems | 5 | 5 | 7 | 8 |

The eight defs of `src/Liquidity.tot` are the seven theorems and the
helper `lpShareCross`. Every def of both files is a plain def, because
no statement of M3d reads the unfolding of an M3d def.

The five theorems of `AmmLean/PriceImpact.lean` hold 23 Lean lines, and
the five tot defs hold 126 lines without their five `check` lines, which
is 5.5 times the Lean text. The seven theorems of
`AmmLean/Liquidity.lean` hold 67 Lean lines, and the eight tot defs hold
257 lines without their eight `check` lines, which is 3.8 times the Lean
text. Blank lines, comment lines and doc comments are excluded from all
four counts.

The whole port is thirty-one theorems: one in the pilot, eight in M3b,
ten in M3c and twelve in M3d, each count taken from the tables above.
The pilot theorem costs 11 times the Lean text in its record form. M3c
costs 2.9 times it in `src/Product.tot` and 5.3 times it in
`src/NoDrain.tot`, and M3d costs 5.5 times it in `src/PriceImpact.tot`
and 3.8 times it in `src/Liquidity.tot`. The per-theorem overhead
therefore fell once the libraries existed, from 11 times the Lean text
to a band of 2.9 to 5.5 times it, and it did not fall further in M3d.
That answers the question of the former Next milestone 1.

M3d adds no library lemma and no axiom. Every lemma that the twelve
theorems cite is a lemma that M2, M3a, M3b or M3c already proved, and
the one new def that is not a Lean theorem is `lpShareCross`.

The two files of M3d, in proof-term occurrences. Comment lines are
excluded from the counts.

| file | lines | `trans0` | `cong0` | `sym0` | `subst0` |
| --- | --- | --- | --- | --- | --- |
| `src/PriceImpact.tot` | 151 | 1 | 0 | 4 | 4 |
| `src/Liquidity.tot` | 293 | 11 | 4 | 5 | 5 |

The one `trans0` of `src/PriceImpact.tot` joins the two fraction lemmas
of `effectivePriceEq`. Its four `subst0`, each over one `sym0` of
`effectivePriceEq`, are the transports of the other four theorems: one
in `effectivePriceLtSpot`, two in `effectivePriceDecreasing` and one in
`effectivePricePos`. `effectivePriceLeSpot` holds no transport, because
it is one call of `leOfLt`. The eleven `trans0` of `src/Liquidity.tot`
are one in each of `addLiquidityPreservesRatio`, `lpShareCross`,
`redeemProportionalX` and `redeemProportionalY`, and seven in
`addRemoveRoundtripY`. The four `cong0` are the four steps of
`addRemoveRoundtripY` that rewrite under an `fdiv` context or an `fmul`
context. The five `subst0` are two in `addLiquidityPreservesRatio`, two
in `lpShareCross` and one in `addRemoveRoundtripX`.

The one file of M4a and the one file of M4b, in proof-term occurrences.
Comment lines are excluded from the counts, as in the tables above.

| file | Lean | lines | `trans0` | `cong0` | `sym0` | `subst0` |
| --- | --- | --- | --- | --- | --- | --- |
| `src/Nat.tot` | Lean core and Mathlib | 299 | 20 | 23 | 12 | 1 |
| src/Int.tot | Lean core | 1081 | 81 | 61 | 55 | 16 |

The file is 318 lines with its nineteen-line header comment, and 299
lines without it. The Lean column names the library that supplies the
same declarations: `Nat` and its lemmas come from Lean core and
Mathlib, so the Lean side of M4a costs no source file of its own. The
one `subst0` is the transport of `zeroNotSucc` over `natFamZero`. The
twenty `trans0`, the 23 `cong0` and the twelve `sym0` are the steps of
the semiring laws, the order laws and the two subtraction laws, which
chain equations by hand, because tot has no rewrite form.

`src/Int.tot` is 1106 lines with its twenty five line header comment,
and 1081 lines without it, which is the line count of its row. The four
other numbers of that row are 81 `trans0`, 61 `cong0`, 55 `sym0` and
sixteen `subst0`, and `J0` is 0 here, as in `src/Nat.tot`. The Lean
column names Lean core alone, because `Int`, its arithmetic and its
order all come from Lean core. The Nat rearrangement `natAddShuffle`
also has a Lean core source, `Nat.add_add_add_comm`, which
`src/Nat.tot` does not hold. The
sixteen `subst0` are the one transport of `posNeNegsucc` over
`intFamPos` and the fifteen transports of the six wrappers that open a
representation: three in `intAddAssoc`, two in `intMulComm`, three in
`intMulAssoc`, three in `intMulAdd`, two in `intMulNeg` and two in
`intLtTrichotomy`. The 81 `trans0`, the 61 `cong0` and the 55 `sym0` are
the steps of the ring laws, the order laws and the six cores, which
chain equations by hand for the same reason. The file is 3.6 times
`src/Nat.tot`, because every law of the integers is a law of the
naturals on two components at once.

The Lean source of each def of `src/Nat.tot`, in file order.

| def | Lean source |
| --- | --- |
| `pred` | no source |
| `natFamZero` | no source |
| `succInj` | Lean core `Nat.succ.inj` |
| `zeroNotSucc` | Lean core `Nat.noConfusion` |
| `addZero` | Mathlib `Nat.add_zero` |
| `addSuccRight` | Mathlib `Nat.add_succ` |
| `addComm` | Mathlib `Nat.add_comm` |
| `addAssoc` | Mathlib `Nat.add_assoc` |
| `addLeftComm` | Mathlib `Nat.add_left_comm` |
| `addCancelLeft` | Mathlib `Nat.add_left_cancel` |
| `mulZeroRight` | Mathlib `Nat.mul_zero` |
| `mulSuccRight` | Mathlib `Nat.mul_succ` |
| `mulComm` | Mathlib `Nat.mul_comm` |
| `addMulRight` | Mathlib `Nat.add_mul` |
| `mulAssoc` | Mathlib `Nat.mul_assoc` |
| `mulOne` | Mathlib `Nat.mul_one` |
| `mulAdd` | Mathlib `Nat.mul_add` |
| `natLt` | no source |
| `ltIrrefl` | Mathlib `lt_irrefl` |
| `ltTrans` | Mathlib `lt_trans` |
| `addLtAddLeft` | Mathlib `Nat.add_lt_add_left` |
| `mulPos` | Mathlib `Nat.mul_pos` |
| `succLtSucc` | Mathlib `Nat.succ_lt_succ` |
| `ltTrichotomy` | Mathlib `Nat.lt_trichotomy` |
| `zeroNeOne` | Mathlib `zero_ne_one` |
| `sub` | Mathlib `Nat.sub` |
| `subZeroRight` | Mathlib `Nat.sub_zero` |
| `subAddCancelLeft` | Mathlib `Nat.add_sub_cancel_left` |
| `subAdd` | Mathlib `Nat.add_sub_cancel'` |
| `natLtOfAddLtAddLeft` | Mathlib `Nat.lt_of_add_lt_add_left` |
| `natDecEq` | Lean core `Nat.decEq` |

`natFamZero`, `pred` and `natLt` have no Lean source. Lean core gets the
first two from `Nat.noConfusion`, and its order is `Nat.lt`, which is
`Nat.le` and not a witness record. The table lists no row for `add`,
`mul` and `one`, because those three are the Lean core declarations
`Nat.add`, `Nat.mul` and the numeral, and not theorems.

The Lean source of each def of `src/Int.tot`, in file order. The table
holds one row for each of the 64 defs, and no row for the three data
types.

| def | Lean source |
| --- | --- |
| `intZero` | no source |
| `intOne` | no source |
| `negOfNat` | Lean core `Int.negOfNat` |
| `intMk` | Lean core `Int.subNatNat` |
| `intNeg` | Lean core `Int.neg` |
| `intAdd` | Lean core `Int.add` |
| `intMul` | Lean core `Int.mul` |
| `natAbs` | Lean core `Int.natAbs` |
| `intFamPos` | no source |
| `posInj` | Lean core `Int.ofNat.inj` |
| `negsuccInj` | Lean core `Int.negSucc.inj` |
| `posNeNegsucc` | Lean core `Int.noConfusion` |
| `natAbsNegOfNat` | Lean core `Int.natAbs_negOfNat` |
| `intMkPos` | Lean core `Int.subNatNat_add_left`, with the subtracted natural zero |
| `intMkNegsucc` | Lean core `Int.subNatNat_add_right`, with the first natural zero |
| `intMkAddCancel` | Lean core `Int.subNatNat_add_add` |
| `intMkCong2` | no source |
| `intMkEqOfAdd` | no source |
| `intMkDiag` | Lean core `Int.subNatNat_self` |
| `intReprOf` | no source |
| `intAddZeroLeft` | Lean core `Int.zero_add` |
| `intAddPosMk` | Lean core `Int.subNatNat_add`, with the equality reversed |
| `intAddNegsuccMk` | Lean core `Int.subNatNat_add_negSucc`, using addition commutativity |
| `intAddMk` | no source |
| `intNegMk` | no source |
| `intMulZeroLeft` | Lean core `Int.zero_mul` |
| `intMulPosMk` | Lean core `Int.ofNat_mul_subNatNat` |
| `intMulNegsuccMk` | Lean core `Int.negSucc_mul_subNatNat` |
| `natAddShuffle` | Lean core `Nat.add_add_add_comm` |
| `intMulMk` | no source |
| `intAddComm` | Lean core `Int.add_comm` |
| `intAddAssocCore` | no source |
| `intAddAssoc` | Lean core `Int.add_assoc` |
| `intAddZero` | Lean core `Int.add_zero` |
| `intAddNegCancel` | Lean core `Int.add_right_neg` |
| `intNegAddCancel` | Lean core `Int.add_left_neg` |
| `intAddCancelLeft` | Lean core `Int.add_left_cancel` |
| `intMulCommCore` | no source |
| `intMulComm` | Lean core `Int.mul_comm` |
| `natMulAssocCross` | no source |
| `intMulAssocCore` | no source |
| `intMulAssoc` | Lean core `Int.mul_assoc` |
| `natMulAddShuffle` | no source |
| `intMulAddCore` | no source |
| `intMulAdd` | Lean core `Int.mul_add` |
| `intMulOne` | Lean core `Int.mul_one` |
| `intMulZero` | Lean core `Int.mul_zero` |
| `intMulNegCore` | no source |
| `intMulNeg` | Lean core `Int.mul_neg` |
| `intLt` | Lean core `Int.lt` |
| `intLtIrrefl` | Lean core `Int.lt_irrefl` |
| `intLtTrans` | Lean core `Int.lt_trans` |
| `intAddLtAddLeft` | Lean core `Int.add_lt_add_left` |
| `intMulPos` | Lean core `Int.mul_pos` |
| `natAddRightComm` | Lean core `Nat.add_right_comm` |
| `intLtTrichotomyCore` | no source |
| `intLtTrichotomy` | Lean core `Int.lt_trichotomy` |
| `intZeroNeOne` | Lean core `Int.zero_ne_one` |
| `natAbsMul` | Lean core `Int.natAbs_mul` |
| `natMulEqZeroRight` | Lean core `Nat.mul_eq_zero`, forward direction with a nonzero left factor |
| `intEqZeroOfNatAbs` | Lean core `Int.natAbs_eq_zero`, forward direction |
| `intMulEqZeroRight` | Lean core `Int.mul_eq_zero`, forward direction with a nonzero left factor |
| `intMulCancelLeft` | Lean core `Int.eq_of_mul_eq_mul_left` |
| `intDecEq` | Lean core `Int.decEq` |

`data IntLt` carries `Int.lt` as the relation and not as the definition:
Lean core defines `Int.lt a b` as `Int.le (a + 1) b`, while `IntLt`
holds the difference and its equation, and the row above names
`Int.lt` for the reducible def `intLt` that stands over the record. The
seventeen rows that read "no source" have no direct source listed:
`intZero`, `intOne`, `intFamPos`, `intMkCong2`, `intMkEqOfAdd`,
`intReprOf`, `intAddMk`, `intNegMk`, `intMulMk`, the six cores,
`natMulAssocCross` and `natMulAddShuffle`. The table names equivalent
laws in Lean core, with specializations, equality reversal and
commutativity noted where the interfaces differ. These references were
checked against the Lean v4.30.0-rc1 sources used by `amm-lean`.

`test/check.py` runs in about 16 seconds of wall time on the pinned
checker, for all 142 cases.

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

The port covers one theorem, in two forms, the eight theorems of
`AmmLean/Basic.lean`, the four remaining theorems of
`AmmLean/Invariant.lean`, the six theorems of `AmmLean/NoDrain.lean`, the
five theorems of `AmmLean/PriceImpact.lean` and the seven theorems of
`AmmLean/Liquidity.lean`. Every theorem of amm-lean is ported. The order and fraction library holds thirty-six
lemmas that those theorems cite. It declares no axiom of its own: every
lemma is a def with a proof term, and the only new hypotheses are the
three fields that the record gained.

## Validation

On 2026-09-06, all 142 checks passed with checker SHA-256
`30c4524d57f6723e39ba117097222f3ab8ef3e899a8a4af8b7e60c68337842bf` at
`/Users/oobi/Documents/kan-lang-tot-pin/_build/default/bin/tot.exe`,
built from tot commit `8cf0b8b` with a clean tree. Build that commit to
reproduce the reference checker.

The checker reports every rejection in this repository with the word
`mismatch`, except the axiom case, which reports `axiom`.

The 142 checks:

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
- Eight checks, one for each theorem of `src/Basic.tot`. Each check
  changes the result type of the theorem and keeps the proof, so each
  one is rejected at its own def:
  `wrong-constantproduct-pos` at `constantProductPos`,
  `wrong-feecomplement-pos` at `feeComplementPos`,
  `wrong-feecomplement-ltone` at `feeComplementLtOne`,
  `wrong-reservex-nezero` at `poolReserveXNeZero`,
  `wrong-reservey-nezero` at `poolReserveYNeZero`,
  `wrong-totallp-nezero` at `poolTotalLPNeZero`,
  `wrong-reservex-add-pos` at `reserveXAddPos` and
  `wrong-reservex-add-nezero` at `reserveXAddNeZero`.
- Ten checks, one for each positivity obligation, by the same recipe:
  `wrong-swap-hx` at `swapHx`, `wrong-swap-hy` at `swapHy`,
  `wrong-swapwithfee-hx` at `swapWithFeeHx`,
  `wrong-swapwithfee-hy` at `swapWithFeeHy`,
  `wrong-addliquidity-hx` at `addLiquidityHx`,
  `wrong-addliquidity-hy` at `addLiquidityHy`,
  `wrong-addliquidity-hlp` at `addLiquidityHlp`,
  `wrong-removeliquidity-hx` at `removeLiquidityHx`,
  `wrong-removeliquidity-hy` at `removeLiquidityHy` and
  `wrong-removeliquidity-hlp` at `removeLiquidityHlp`.
- Nine checks, one for each pure definition. Each check changes the body
  of the definition and keeps every statement, so the first def that
  unfolds the definition is rejected: `wrong-constantproduct` at
  `constantProductPos`, `wrong-swapoutput` at `swapHy`,
  `wrong-effectiveprice` at `effectivePrice`, `wrong-spotprice` at
  `spotPrice`, `wrong-feecomplement` at `feeComplementPos`,
  `wrong-effectiveinput` at `swapWithFeeHy`, `wrong-swapoutputwithfee`
  at `swapWithFeeHy`, `wrong-redeemx` at `removeLiquidityHx` and
  `wrong-redeemy` at `removeLiquidityHy`. `effectivePrice` and
  `spotPrice` are cited by no theorem of this milestone, so those two
  checks change the result type of the definition instead of its body.
- Two checks weaken a field of a record of `src/Pool.tot`. The
  constructor field, the result type of the projection and the return
  motive change together, so the projection still checks and the first
  consumer of the projection is rejected: `weak-pool-hx` states
  `hx : flt fzero totalLP` and is rejected at `constantProductPos`, and
  `weak-feerate-hlt` states `hlt : flt fone rate` and is rejected at
  `feeComplementPos`.
- Ten checks, one for each theorem of `src/Product.tot` and
  `src/NoDrain.tot`. Each check changes the result type of the theorem
  and keeps the proof, so each one is rejected at its own def:
  `wrong-swap-preserves-product` at `swapPreservesProduct`,
  `wrong-effectiveinput-lt` at `effectiveInputLt`,
  `wrong-effectiveinput-pos` at `effectiveInputPos`,
  `wrong-swapwithfee-increases-product` at
  `swapWithFeeIncreasesProduct`,
  `wrong-swapoutput-lt-reservey` at `swapOutputLtReserveY`,
  `wrong-swapoutput-pos` at `swapOutputPos`,
  `wrong-swapoutputwithfee-lt-reservey` at
  `swapOutputWithFeeLtReserveY`,
  `wrong-reservey-pos-after-swap` at `reserveYPosAfterSwap`,
  `wrong-reservey-pos-after-swapwithfee` at
  `reserveYPosAfterSwapWithFee` and
  `wrong-constantproduct-lowerbound` at `constantProductLowerBound`.
- Three checks keep the statement and break the proof, so each one is
  rejected at its own def: `wrong-swap-preserves-product-proof`
  exchanges the two reserves in the term of `swapPreservesProduct` and
  is rejected at `swapPreservesProduct`,
  `wrong-increases-product-notransport` removes the `subst0` wrapper of
  `swapWithFeeIncreasesProduct` and is rejected at
  `swapWithFeeIncreasesProduct`, and `wrong-lowerbound-nosym` removes
  the `sym0` of `constantProductLowerBound` and is rejected at
  `constantProductLowerBound`.
- Thirteen checks, one for each theorem of `src/PriceImpact.tot` and
  `src/Liquidity.tot` and one for the helper `lpShareCross`. Each check
  changes the result type and keeps the proof, so each one is rejected
  at its own def: `wrong-effectiveprice-eq` at `effectivePriceEq`,
  `wrong-effectiveprice-lt-spot` at `effectivePriceLtSpot`,
  `wrong-effectiveprice-decreasing` at `effectivePriceDecreasing`,
  `wrong-effectiveprice-le-spot` at `effectivePriceLeSpot`,
  `wrong-effectiveprice-pos` at `effectivePricePos`,
  `wrong-addliquidity-preserves-ratio` at
  `addLiquidityPreservesRatio`,
  `wrong-addliquidity-preserves-price` at
  `addLiquidityPreservesPrice`, `wrong-lpshare-cross` at
  `lpShareCross`, `wrong-lpshare-proportional` at
  `lpShareProportional`, `wrong-redeem-proportional-x` at
  `redeemProportionalX`, `wrong-redeem-proportional-y` at
  `redeemProportionalY`, `wrong-add-remove-roundtrip-x` at
  `addRemoveRoundtripX` and `wrong-add-remove-roundtrip-y` at
  `addRemoveRoundtripY`. The anchor of each one takes the `:=` of the
  def header, so the count of the mutation stays one and no step of the
  body changes.
- Four checks keep the statement and break the proof, so each one is
  rejected at its own def: `wrong-effectiveprice-eq-proof` exchanges the
  two arguments of `mulDivMulRight` in `effectivePriceEq` and is
  rejected at `effectivePriceEq`,
  `wrong-effectiveprice-lt-spot-notransport` removes the `subst0`
  wrapper of `effectivePriceLtSpot` and is rejected at
  `effectivePriceLtSpot`, `wrong-lpshare-proportional-proof` exchanges
  the two nonzero proofs of `lpShareProportional` and is rejected at
  `lpShareProportional`, and `wrong-roundtrip-x-nosym` removes the
  `sym0` of `addRemoveRoundtripX` and passes the cross identity to
  `subst0` directly, and is rejected at `addRemoveRoundtripX`.

- Nineteen checks, one for each theorem of `src/Nat.tot`. Each check
  changes the result type of the theorem and keeps the proof, so each
  one is rejected at its own def: `wrong-nat-succ-inj` at `succInj`,
  `wrong-nat-zero-not-succ` at `zeroNotSucc`, `wrong-nat-add-zero` at
  `addZero`, `wrong-nat-add-comm` at `addComm`, `wrong-nat-add-assoc`
  at `addAssoc`, `wrong-nat-mul-comm` at `mulComm`,
  `wrong-nat-mul-assoc` at `mulAssoc`, `wrong-nat-mul-one` at `mulOne`,
  `wrong-nat-mul-add` at `mulAdd`, `wrong-nat-add-cancel-left` at
  `addCancelLeft`, `wrong-nat-lt-irrefl` at `ltIrrefl`,
  `wrong-nat-lt-trans` at `ltTrans`, `wrong-nat-add-lt-add-left` at
  `addLtAddLeft`, `wrong-nat-mul-pos` at `mulPos`,
  `wrong-nat-lt-trichotomy` at `ltTrichotomy`, `wrong-nat-zero-ne-one`
  at `zeroNeOne`, `wrong-nat-sub-add` at `subAdd`,
  `wrong-nat-lt-of-add-lt-add-left` at `natLtOfAddLtAddLeft` and
  `wrong-nat-dec-eq` at `natDecEq`. The four helpers `addSuccRight`,
  `mulZeroRight`, `mulSuccRight` and `addMulRight` get no negative of
  their own, because a mutation of any of them is caught by the theorem
  that cites it.

- One positive check, `int-ordered-field-shapes`, assigns
  `intLtIrrefl`, `intLtTrans`, `intAddLtAddLeft` and `intMulPos` to the
  four order field signatures of `OrderedField`, specialized to `Int`.
  This checks that the hypothesis quantities match the interface as
  well as the propositions.
- Twenty five checks, one for each theorem of `src/Int.tot` that M4b
  adds. Each check changes the result type of the theorem and keeps the
  proof, so each one is rejected at its own def:
  `wrong-int-pos-inj` at `posInj`, `wrong-int-negsucc-inj` at
  `negsuccInj`, `wrong-int-pos-ne-negsucc` at `posNeNegsucc`,
  `wrong-int-add-comm` at `intAddComm`, `wrong-int-add-assoc` at
  `intAddAssoc`, `wrong-int-add-zero` at `intAddZero`,
  `wrong-int-add-neg-cancel` at `intAddNegCancel`,
  `wrong-int-add-cancel-left` at `intAddCancelLeft`,
  `wrong-int-mul-comm` at `intMulComm`, `wrong-int-mul-assoc` at
  `intMulAssoc`, `wrong-int-mul-one` at `intMulOne`,
  `wrong-int-mul-zero` at `intMulZero`, `wrong-int-mul-add` at
  `intMulAdd`, `wrong-int-mul-neg` at `intMulNeg`,
  `wrong-int-lt-irrefl` at `intLtIrrefl`, `wrong-int-lt-trans` at
  `intLtTrans`, `wrong-int-add-lt-add-left` at `intAddLtAddLeft`,
  `wrong-int-mul-pos` at `intMulPos`, `wrong-int-lt-trichotomy` at
  `intLtTrichotomy`, `wrong-int-zero-ne-one` at `intZeroNeOne`,
  `wrong-int-nat-abs-mul` at `natAbsMul`,
  `wrong-int-nat-mul-eq-zero-right` at `natMulEqZeroRight`,
  `wrong-int-mul-eq-zero-right` at `intMulEqZeroRight`,
  `wrong-int-mul-cancel-left` at `intMulCancelLeft` and
  `wrong-int-dec-eq` at `intDecEq`. Every anchor is the last line of the
  def header, the one that ends in the trailing `:=`, so the mutation
  changes the result type and no step of the body. The cores, the
  canonical difference lemmas and the Nat helpers get no negative of
  their own, because a mutation of any of them is caught by the theorem
  that cites it.

For the 110 checks that M3a, M3b, M3c, M3d, M4a and M4b add, the
runner also
reads
the position
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

Twenty-three facts about tot, found with scratch files. The first five
come from the record milestone, the next five come from the M3a probes,
the next four come from the M3b probes, the next two come from the M3c
probes, the next three come from the M3d probes and the last four come
from the M4a probes. The scratch files are not part of this
repository.

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
- Two data records with proof fields, and nine projections, check. The
  three dependent `Pool` projections and the two dependent `FeeRate`
  projections need the value projection to be a reducible def. The
  checker prints the projection type with the match already inlined,
  which is the evidence that the delta step happened.
- A reducible pure def unfolds inside the statement of a theorem that is
  proved through the axiom record. `constantProduct` unfolds inside the
  statement of `constantProductPos`, and the axiom field `mulPos`
  proves it with the two projections `poolHx` and `poolHy` in its two
  erased slots.
- A reducible constructor applied to the `pool` constructor unfolds by
  delta, and the projection match then reduces by iota, so `refl`
  proves the three unfolding lemmas of `swap`. The control changes the
  endpoint of `swapTotalLP` to `fadd rx dx` and the checker rejects it
  with a type mismatch.
- The full `swapHy` chain checks, with `subPosOfLt`, `divLtOfLtMul`, a
  `subst0` along `sym0` of `mulAdd`, and `ltAddOfPosLeft` over
  `mulPos`. It is the archetype of `swapWithFeeHy`, `removeLiquidityHx`
  and `removeLiquidityHy`.
- A theorem may be stated on a reducible constructor and unfolded by
  conversion alone. `swapPreservesProduct` states
  `Eq F (constantProduct OPS (swap PARAMS p dx hdx)) (constantProduct OPS p)`,
  and `swapOutputIdentityOf` alone proves it. No unfolding lemma is
  cited and no transport is written. The control exchanges the two
  endpoints of the `Eq` and the checker rejects it with a type
  mismatch.
- `leOfEq` accepts a `sym0` between two constant products in its w
  slot, and `fle` unfolds inside the statement.
  `constantProductLowerBound` states
  `fle F flt (constantProduct OPS p) (constantProduct OPS (swap PARAMS p dx hdx))`
  and cites `leOfEq` over `sym0` of `swapPreservesProduct`. The control
  removes the `sym0` and passes the proof of `swapPreservesProduct`
  straight into `leOfEq`, and the checker rejects it.
- A `trans0` chain proves a statement through a def that unfolds twice.
  `effectivePriceEq` states
  `Eq F (effectivePrice OPS p dx) (fdiv ry rxD)`, and the delta step of
  `effectivePrice` and then the delta step of `swapOutput` carry the
  statement to the type of one `trans0` over `divDiv` and
  `mulDivMulRight`. No unfolding lemma is cited and no `subst0` is
  written. The control swaps the two endpoints of the `Eq` and the
  checker rejects it with a type mismatch.
- A theorem may be stated on the projections of
  `addLiquidity PARAMS p dx hdx`, and another on `spotPrice OPS` of the
  same application. `addLiquidityPreservesRatio` names `poolReserveY`
  and `poolReserveX` of the constructor, and its term is stated on the
  unfolded reserves; the delta step of the reducible constructor with
  the iota step of the two projection matches closes the gap.
  `addLiquidityPreservesPrice` is that term with no wrapper, because the
  delta step of `spotPrice` on both sides gives the ratio statement. The
  control exchanges the two nonzero proofs and the checker rejects it.
- `cong0` rewrites under an `fdiv` context and under an `fmul` context
  over equations whose endpoints are stated in the projection form. In
  `addRemoveRoundtripY` the `cong0` endpoints stand in the unfolded
  forms `fdiv mint lpN`, `fdiv dx rxD`, `fdiv ryN rxD` and
  `fdiv ry rx`, while the cited `lpShareProportional` and
  `addLiquidityPreservesRatio` have types that name the projections of
  `addLiquidity`. The checker converts them. The control drops one
  `trans0` layer of the chain and the checker rejects it.

- (o) A data type former carries its parameters at quantity 0, while
  `Trichotomy` takes its relation at quantity w. `Trichotomy Nat NatLt`
  is therefore rejected, and data parameters cannot be marked w. A
  relation that `Trichotomy` accepts is a reducible def over the data
  type, `natLt m n`, whose delta step joins it to `NatLt m n`.
- (p) A match that is applied to an argument must be parenthesized. The
  form `match ... end h` is a parse error, and `(match ... end) h` is
  accepted. `addCancelLeft` needs that form, because the match on `k`
  cannot refine the type of the hypothesis, so it returns a function.
- (q) The inductive order relation checks too, and it costs two more
  defs, three more recursions, two inversion helpers, four index motives
  and one `exfalso`. The witness record is therefore the prescribed
  form.
- (r) The name `ltOfAddLtAddLeft` is already a global of
  `src/Order.tot`, and the sixteen files share one namespace, so the
  `Nat` lemma is `natLtOfAddLtAddLeft`. A sweep of the 42 names of M4a
  against the 141 globals of the fifteen earlier files finds that one
  collision and no other.

The five M3c probes Q1 to Q5 were all green on the first attempt, so
they forced no change to any statement and no change to any term of the
design notes. The six M3d probes R1 to R6 were all green on the first
attempt as well, so they forced no change either. Neither fallback of
the `addRemoveRoundtripY` design note was needed: the `cong0` endpoints
stand in the unfolded form, and no `subst0` replaces a `cong0` step.

## Next milestones

Milestone M4 supplies a concrete carrier: an inhabitant of
`OrderedField` for one type, so that every theorem has a closed
instance. Every ordered field is infinite, so the carrier is the
rationals, and M4 is cut into five slices.

1. M4a, the natural numbers, `src/Nat.tot`. Done.
2. M4b, the integers, `src/Int.tot`. Done, this commit.
3. M4c, divisibility and the greatest common divisor, `src/Gcd.tot`.
4. M4d, the reduced fractions and the field laws, `src/Rat.tot`.
5. M4e, the order, the `OrderedField` inhabitant and the closed
   instance, `src/RatOrder.tot` and `src/Instance.tot`.

Sources, nineteen files: `src/Foundation.tot`, `src/Field.tot`,
`src/Invariant.tot`, `src/Axioms.tot`, `src/Ring.tot`, `src/Laws.tot`,
`src/Compose.tot`, `src/Frac.tot`, `src/Order.tot`, `src/Pool.tot`,
`src/Basic.tot`, `src/Product.tot`, `src/NoDrain.tot`,
`src/PriceImpact.tot`, `src/Liquidity.tot`, `src/Nat.tot`,
`src/Int.tot`, `test/check.py`, `README.md`. The first seventeen are the
check order.
