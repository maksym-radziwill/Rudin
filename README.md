# Rudin's problem: Lean formalization

A Lean 4 formalization of F. Gonçalves, J. P. Ferreira and M. Radziwiłł,
*Uniformly bounded orthonormal bases of homogeneous polynomials on the complex
sphere*, [arXiv:2610.14160](https://arxiv.org/abs/2610.14160).

## Layout

| File | Contents |
| --- | --- |
| `PaperFormalization/Core.lean` | the implementation |
| `PaperFormalization/Compatibility.lean` | wrappers |
| `PaperFormalization/Statements.lean` | each paper statement, beside its full Lean type |
| `Challenge.lean` | the trusted statement of Theorem 1, for `lake comparator` |
| `comparator.json` | the `lake comparator` configuration |
| `paper.tex` | a copy of the paper |
| `formalization.pdf` | a .pdf rendering of Statements.lean |
| `docgen/` | scripts for generating `formalization.pdf` from `Statements.lean` |

`Statements.lean` and `formalization.pdf` are meant for semantic checking. For
Theorem 1, the semantic check can be narrowed to `Challenge.lean`; see
[Checking Theorem 1 with comparator](#checking-theorem-1-with-comparator).

## Build

The project builds as an ordinary Lake project against Lean and Mathlib:

```bash
lake exe cache get
lake build
```

## Checking Theorem 1 with comparator

Theorem 1 is the paper's answer to Rudin's problem. `Challenge.lean` restates it,
with `sorry` as the proof, together with the definitions its statement uses:
`degIdx`, `PolySpaceH`, `polyEval` and `polyInner`. `lake comparator` judges the
formalization against that file:

```bash
lake exe cache get
lake comparator
```

## Checking all results with `lake check`

```bash
lake exe cache get
lake check
```

`lake check` builds the project's default targets in the same sandbox as
comparator, exports them, replays the export through Lean's kernel, and fails
if anything uses an axiom other than `propext`, `Quot.sound` and
`Classical.choice`. It covers every numbered result, not only Theorem 1.

## The numbered results

| Paper | Lean endpoints in `Statements.lean` |
| --- | --- |
| Theorem 1 (`thm:onb`) | `theorem1` |
| Theorem 2 (`thm:box`) | `theorem2` |
| Definition 3 (`def:equicomp`) | `definition3` (and `definition3Weak`, superseded — see below) |
| Proposition 4 (`prop:UNmap`) | `proposition4` |
| Theorem 5 (`thm:onbexplicit`) | `theorem5OrthonormalBasis`, `theorem5UniformBound`, `theorem5` |
| Lemma 6 (`lem:poisson1d`) | `lemma6` |
| Lemma 7 | `lemma7` |
| Definition 8 | `definition8` |
| Proposition 9 (`prop:shiftedONS`) | `proposition9Orthogonality`, `Proposition9.indexEquiv` — **partial**, see below |
| Proposition 10 (`prop:shiftedbound`) | `proposition10` |
| Lemma 11 (`lem:facenorm`) | `lemma11Isometry`, `lemma11SphereBound`, `lemma11Evaluation` — **partial**, see below |
| Lemma 12 | `lemma12` |
| Definition 13 | `definition13` |
| Theorem 14 (`thm:general`) | `theorem14` |
| Proposition 15 | `proposition15` |
| Lemma 16 (`lem:sgn`) | `lemma16`, `lemma16OddCoefficient`, `lemma16EvenCoefficient`, `lemma16CoefficientBound`, `lemma16CotWeightBound` |
| Lemma 17 (`lem:poisson`) | `lemma17Summation`, `lemma17Decay` |
| Lemma 18 | `lemma18` |
| Lemma 19 (`lem:weylgauss`) | `lemma19` |
| Definition 20 | `definition20` |
| Theorem 21 (`thm:decomp`) | `theorem21` |
| Definition 22 | `definition22` |
| Definition 23 | `definition23` |
| Lemma 24 | `lemma24TransitionComposition`, `lemma24`, `Piece.prod` (as `Lemma24.productPiece`), `lemma24TransitionProduct`, `lemma24DecompositionProduct` |
| Lemma 25 (`lem:split`) | `lemma25PlusIsPiece`, `lemma25MinusIsPiece`, `lemma25`, `lemma25PlusIndexDecreases`, `lemma25MinusSlabWidth` |
| Lemma 26 (`lem:short-coordinate`) | `lemma26` |
| Proposition 27 (`prop:pieces`) | `proposition27` |
| Proposition 28 | the conjuncts of `proposition28` |

Results split across several endpoints:

- **Theorem 5** has three. `theorem5OrthonormalBasis` is the orthonormality and
  spanning of the φ_l for degrees divisible by lcm_k; `theorem5UniformBound` is
  the uniform sup-norm bound for those degrees; `theorem5` is part 3, the
  all-degrees basis obtained from them by the absorption trick.
- **Lemma 16** has five. `lemma16` is the expansion `eq:saw`;
  `lemma16OddCoefficient` the cotangent formula; `lemma16EvenCoefficient` that
  the coefficient vanishes at even ℓ; `lemma16CoefficientBound` the bound on
  `sgnCoeff`; and `lemma16CotWeightBound` the lemma's last sentence,
  |ĉ_L(ℓ)| ≤ 2/(π|ℓ|), at **every** ℓ with 0 < |ℓ| < L/2. The fifth is needed
  because the paper defines ĉ_L(ℓ) = −(2i/L)cot(πℓ/L) for all ℓ, whereas
  `sgnCoeff` is 0 at even ℓ, so a bound on `sgnCoeff` says nothing there;
  `lemma16CotWeightBound` bounds the cotangent weight itself.
- **Lemma 17** has two: `lemma17Summation` is the Poisson-summation identity,
  `lemma17Decay` the decay estimate.
- **Lemma 24** has five: `lemma24TransitionComposition` and `lemma24` for
  composition of transitions and of decompositions, and `Piece.prod`,
  `lemma24TransitionProduct`, `lemma24DecompositionProduct` for products.
  (`Lemma24.compositionSizeBound` and `Lemma24.productSizeBound` carry the
  |Φ|_∞ bounds.)
- **Lemma 25** has five: `lemma25PlusIsPiece` and `lemma25MinusIsPiece` say the
  two split halves are pieces, `lemma25` is the disjoint identity-transition
  decomposition, `lemma25PlusIndexDecreases` the index decrease, and
  `lemma25MinusSlabWidth` the slab-width bound.
- **Proposition 28** is one theorem whose conjuncts are the separate assertions:
  the membership characterizations of the source and target pieces, the target
  base, and the explicit formulas for `foldMap` and `foldInv` with the identity
  that they invert each other.

## Deviations from the paper

Two, both as stated in the paper's own "Use of generative AI" section:

1. **The inner product.** It is defined by Rudin's monomial formula
   (`polyInner`, i.e. `def:innerprod`), not as an integral over the sphere
   S^{2K−1}. The two agree, but the agreement is not formalized. `Challenge.lean`
   uses the same formula.
2. **Proposition 4 has one proof, not two.** Section 5 gives two proofs of the
   simplex–box equidecomposition: an implicit one via unimodular
   triangulations and Ehrhart theory (§5.1), and an explicit constructive one
   (§5.2). Only §5.2 is formalized.

## What is missing

Two results are formalized in a weaker form than stated.

- **Proposition 9** is missing **spanning**: that the φ^b_l for l ∈ B_{N−b},
  which lie in the span of the z^n with n_K ≥ b, span that span. The paper gets
  it by a dimension count; `Compatibility.lean` exports only the index
  bijection for that count (`Proposition9.indexEquiv`), and the orthogonality
  (`proposition9Orthogonality`). There is deliberately no `Paper.proposition9`.
- **Lemma 11** is missing three things: the size c_{N,i} ≍_{K,i} N^{(i+1)/2};
  that the lift map is **onto** z_K^i H_{K−1,N−i} (part 1); and that the
  c_{N,i}·z_K^i·ψ_ν form an orthonormal **basis** of it (part 2). Its sup-norm
  bound is formalized with an explicit factor in place of N^{1/2}:
  `lemma11SphereBound` gives C·√(binom(N+k,k)/binom(N−i+k−1,k−1)). That ratio
  is asymptotic to N/k for fixed k and i and is ≪_{k,i} N for all N ≥ 1, so
  the bound implies the C·N^{1/2} of `eq:facesup`; this last estimate is
  elementary but not formalized. What is formalized is `lemma11Isometry`,
  `lemma11SphereBound` and `lemma11Evaluation`. There is deliberately no
  `Paper.lemma11`.

## Harmless differences

These are places where the Lean statement is not literally the paper's, in a
direction that loses nothing.

- **A nonempty-box hypothesis** is added in Theorem 14, Proposition 27 and
  Lemma 25 (`∀ s, lo s ≤ hi s`, resp. `∀ j, p.lo j ≤ p.hi j`). It excludes only
  empty boxes, where the sum is empty and `boxVol` is 0, so the bound would read
  0 ≤ 0; for Proposition 27, M = 0 satisfies the conclusion, and the paper's
  proof of Theorem 21 applies it to a nonempty box anyway.
- **`R : ℕ`** in Definitions 13 and 20, where the paper allows real R ≥ 1. The
  paper's Theorem 14 and Theorem 21 take an integer R, and the quantities
  bounded by R (|w|₁, #W, the c_j, |A|_∞) are integers, so nothing is lost.
- **Stronger forms.** Lemma 12's hypotheses follow from the paper's and its
  conclusion is the same, with `ip` required only to be sesquilinear.
  Lemma 18 states all three conjuncts for *every* integer `abar` inverse to a
  mod q, where the paper fixes a representative. Proposition 15 chooses its
  implied constant after the cutoff bound `Lam`, so it is uniform over all
  such cutoffs. Lemma 26 needs only `p.A ≤ R` where the paper has A = R, holds
  for every qc of maximal side where the paper chooses one, and adds the bound
  `transitionSize D ≤ C`; it also now asserts `Function.Injective U`, which is
  the paper's "a set U ⊂ ℤ^d, one piece per u ∈ U".
- **Definition 3** is stated for arbitrary `P`, `Q : Set (Fin k → ℤ)` and
  arbitrary `R : ℕ`, not only for ℤ-polytopes and R ≥ 1; for those it reads as
  the paper's definition (at R = 0 it says P = Q = ∅).
