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
the foundation and the proof source in temporary files and checks with
`--no-prelude --no-axioms`. It prints the checker SHA-256, so validation
identifies the binary actually used. No compiler rebuild is necessary
when a built checker exists.

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
hypothesis. The proof is the same six rewrites of the Lean tactic block,
in the same order, written as an equality chain.

| tot hypothesis | Mathlib source |
| --- | --- |
| `fadd`, `fmul`, `fsub`, `fdiv` | the `Field F` operations |
| `fzero`, `flt` | `0` and `<` from `LinearOrder F` |
| `addPos` | `add_pos` |
| `neOfGt` | `ne_of_gt` |
| `mulSub` | `mul_sub` |
| `mulDivAssoc` | `mul_div_assoc'` |
| `mulDivCancelLeft` | `mul_div_cancel_left₀` |
| `addMul` | `add_mul` |
| `mulComm` | `mul_comm` |
| `addSubCancelRight` | `add_sub_cancel_right` |

`neOfGt` states the disequality as a function to `Empty`, because tot has
no `Ne` and no `Prop`.

## Measurement

| Quantity | Lean | tot |
| --- | --- | --- |
| Statement lines | 2 | 14 |
| Proof lines | 3 | 46 |
| Context lambdas written by hand | 0 | 4 |
| Transitivity steps written by hand | 0 | 5 |
| Hypotheses in the signature | 5 | 20 |

The tot statement is `src/Invariant.tot` lines 4 to 17. The tot proof is
lines 17 to 62; line 17 carries both the end of the goal and the `:=`.
The context lambdas are the four `fun z => ...` terms. Each one names the
subterm that one rewrite replaces. Lean derives them from the goal.
The five transitivity steps are the `trans0` applications that join the
seven terms of the chain. Lean derives them from the list in `kan_rw`.
The Lean count of five hypotheses is `x`, `y`, `dx`, `hx` and `hdx`. The
tot count of twenty adds the carrier, six operations and eight laws.

`test/check.py` runs in about 0.13 seconds of wall time on the pinned
checker, for all fourteen cases.

## Scope and trust

The eight laws are hypotheses, not axioms. The file declares no axiom,
and `--no-axioms` rejects any axiom. Nothing in this repository asserts
that a field exists. The signature of `swapOutputIdentity` therefore has
no tot inhabitant that this repository supplies: a caller must supply
the operations and the proofs of the eight laws. The theorem is
conditional on them.

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

On 2026-09-06, all fourteen checks passed with checker SHA-256
`30c4524d57f6723e39ba117097222f3ab8ef3e899a8a4af8b7e60c68337842bf` at
`/Users/oobi/Documents/kan-lang-tot-pin/_build/default/bin/tot.exe`,
built from tot commit `8cf0b8b` with a clean tree. Build that commit to
reproduce the reference checker.

The checker reports every rejection in this repository with the word
`mismatch`, except the axiom case, which reports `axiom`.

The fourteen checks:

- The theorem checks without a prelude or axioms.
- The proof is rejected against a commuted right side, `fmul y x`.
- The proof is rejected against a wrong denominator, `x` in place of
  `fadd x dx`.
- The proof is rejected when the fifth step of the chain is removed.
- The proof is rejected when the positivity of `dx` is replaced by a
  second use of the positivity of `x`.
- Eight checks, one for each law. Each check weakens that one law to a
  trivial or wrong statement and leaves the proof unchanged. Each one is
  rejected. Every law is load bearing.
- A user axiom is rejected.

The negative controls show that specific proof terms are rejected. They
do not show that the false statements are unprovable.

No adjustment to the signature of the brief was necessary. The checker
did reject holes in the erased argument slots of `trans0` and `cong0`,
so the proof spells out every carrier and every endpoint of the chain.

## Next milestones

1. Bundle the carrier, the operations and the eight laws into one `data`
   record. Take that record as a single hypothesis. This shortens every
   later statement.
2. Derive the eight laws from a smaller set of field axioms in tot, and
   supply them once. The division laws need the disequality hypothesis
   that `mul_div_cancel_left₀` carries.
3. Port the other nineteen theorems of amm-lean against that record.
   Measure whether the per-theorem overhead falls after the bundle.
4. A tot data record bundling the eight field laws checks cleanly when
   the law fields carry quantity w, but fails with an erased-variable-
   used-at-runtime error when the same fields carry quantity 0 and a def
   projects one of them into a w position.

Sources: `src/Foundation.tot`, `src/Invariant.tot`.
