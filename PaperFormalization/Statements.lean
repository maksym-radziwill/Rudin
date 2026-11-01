import PaperFormalization.Compatibility

set_option linter.all false

/-!
# A self-contained reading of the paper statements and their Lean encodings

This file sets each numbered statement of the paper, verbatim, beside its
full Lean type, in paper order. Paper definitions and notation precede the
statements that use them; unnumbered ones appear in "Paper context" sections
with the source excerpt and a note on their use, followed by the Lean
bodies. See also the accompanying certificate for Theorem 1.

Every definition that a displayed statement uses, directly or through other
definitions, is shown in full: 95, all from `Core.lean`. `Paper.definition3`
(the paper's Definition 3, below) and `Paper.definition3Weak` are shown too,
though no statement uses either.
Nothing else is shown: not the other 77 definitions of `Core.lean` (among them
`AllDegreesProof.goodEquiv`, which only an alias uses), nor the 19
paper-numbered aliases of `Compatibility.lean` (one-line `abbrev`s, listed after
the index). The paper-numbered statements and both Definition 3 predicates are
declared in `Compatibility.lean`, which this file imports; each wrapper below
has the same type as the corresponding theorem there and forwards to its proof
in `Core.lean`, or, where `Compatibility.lean` carries the proof itself
(`Paper.lemma16CotWeightBound`, the four hypothesis bridges of Theorem 5 and
Proposition 10, and the restated `theorem5UniformBound` and `proposition10`),
to that wrapper.

Definition 3: `Paper.definition3` is now the corrected predicate, with the
paper's two disjoint unions stated as a set equality plus pairwise
disjointness. The earlier, too weak encoding — whose unique-membership clauses
force neither the pieces into P nor their images into Q (`affine` context) —
is kept under the name `Paper.definition3Weak`, so that the counterexamples in
that context name a real declaration; it is not the paper's definition. Both
are declared in `Compatibility.lean`; this file adds no definition of its own.
No theorem uses either predicate.

## Coverage legend and proof status

Coverage tags (how endpoints are presented, not an axiom audit):

- `direct`: the main endpoint is shown; not every subsidiary clause need be.
- `direct-strengthened`: the paper's conclusion under weaker hypotheses or
  with extra output (Lemma 26).
- `all-degrees-conclusion` (Theorem 5): `theorem5` is part 3, the
  all-degrees basis; parts 1 and 2 are companion endpoints.
- `component`, `decomposition-component`: one named conclusion; companion
  endpoints are listed with it and may together cover the item.
- `component-only`: a partial presentation, not the full result.
- `direct-definition`, `direct-structure`: the source definition or
  structure, displayed for comparison, not certified equivalent to the paper.

Gaps: Proposition 9 and Lemma 11 are `component-only`.

## Reading the encodings

D-blocks are exact source excerpts, giving namespace, file, line and the
statements that use them; nothing is shadowed or changed. Conventions
G01–G14 (before Theorem 1) apply throughout; other library names are
explained, with the Mathlib declarations that fix them, in the Library
glossary near the end, and each block lists those it uses. The alphabetical
definition index is at the end. Displaying an encoding does not prove it
equivalent to the paper.
-/

namespace PaperReview

open scoped Matrix

/-!
## Lean and Mathlib conventions used throughout

These conventions (G01–G14) apply to all Lean code below and are not listed per
block. Text after `by` is a proof and never changes a value; `f (M := e)`
supplies the argument named M. Entries cite the declaration that fixes the
meaning (Mathlib v4.35.0, Lean v4.35.0, as pinned by
`lean-toolchain`; the environment available here for checking the file was Lean
4.34.0-rc2, one patch release behind -- see README.md).

### G01 — `Fin n`

Meaning: `Fin n` = {0, 1, …, n−1}: its elements are pairs ⟨v, h⟩ with v : ℕ and
h : v < n (`t.isLt` is that proof); `Fin 0` is empty. `x : Fin k → R` is a
k-tuple (x 0, …, x (k−1)) with coordinatewise +, −, scaling and `0`, so `w ≠ 0`
means some coordinate is nonzero. Equality, `≤` and `<` compare values.

Pinned by: structure `Fin` (fields `val : Nat`, `isLt : val < n`);
`Fin.eq_of_val_eq`: i.val = j.val → i = j; `Fin.le_def`: a ≤ b ↔ a.1 ≤ b.1;
`Finset.card_fin`: #(univ : Finset (Fin n)) = n.

Conventions: 0-based: paper coordinate j (1 ≤ j ≤ k) is Lean coordinate j−1.
Arithmetic in `Fin n` itself (+, −, *, numerals) is mod n (`Fin.val_ofNat`:
(Fin.ofNat n a).val = a % n); the displayed definitions do index arithmetic on
`.val` in ℕ instead (foldCoord, foldMap, foldInv). `Fin 0 → R` has one element
(the empty tuple); sums over `Fin 0` are 0, products 1.

### G02 — Pairs: `α × β`, `(a, b)`, `p.1`, `p.2`

Meaning: (a, b) : α × β is an ordered pair, `p.1 = p.fst`, `p.2 = p.snd`; (a, b,
c) = (a, (b, c)). The notation `.1`, `.2` is generic: on a subtype ↥s it means
n.val and n.property; on a Sigma type (m : Fin M) × Fin (N m), the index m and
the element of Fin (N m).

Pinned by: structure `Prod` (fields `fst`, `snd`); `Prod.le_def`: x ≤ y ↔ x.1 ≤
y.1 ∧ x.2 ≤ y.2 (componentwise order; `×ₗ` is the lexicographic one).

Conventions: For n in a subtype ↥s, `n.1` is the element and `n.2` a membership
proof, not a second coordinate; in Lemma 24, `.1`, `.2` of `(sigmaPieceIndexEquiv N).symm t` are
Sigma projections.

### G03 — `Finset α` and `Finset.univ`

Meaning: A `Finset α` is a finite subset of α (a duplicate-free multiset,
determined by its members). `Finset.univ` is the finset of all elements of a
finite type (for `Fin n`: {0, …, n−1}). A finset coerces to a `Set α` with the
same members.

Pinned by: `Finset.ext`: (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂; `Finset.mem_univ`: x
∈ (univ : Finset α); `Finset.mem_coe`: a ∈ (s : Set α) ↔ a ∈ s.

Conventions: No order and no multiplicity; #s counts distinct elements.
`classical` in definition bodies supplies the decidability that finset
operations need and does not change values.

### G04 — Big operators `∑ x ∈ s, f x`, `∑ i, f i`, `∏ x ∈ s, f x`, `∏ i, f i`

Meaning: `∑ x ∈ s, f x` is `Finset.sum s f`, the sum of f over the finset s; `∑
i, f i` (or `∑ i : ι, f i`) is the sum over `Finset.univ` of the finite type ι
(for `Fin k`: f 0 + ⋯ + f (k−1)); `∑ n : ↥s, f n` equals ∑ x ∈ s, f x. `∏` is
the same with products.

Pinned by: notation docstring in
Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean; `Finset.sum_empty`: ∑ x ∈
∅, f x = 0; `Finset.prod_empty`: ∏ x ∈ ∅, f x = 1; `Finset.sum_coe_sort`: ∑ i :
s, f i = ∑ i ∈ s, f i; library note «operator precedence of big operators»: the
body is parsed at precedence 67.

Conventions: Empty sum 0, empty product 1 (e.g. over Fin 0). Precedence 67 lies
between + (65) and * (70): the body extends over *, / and ^ but stops at +, −
and comparisons, so `∑ s, a s * x s + b` is (∑ s, a s * x s) + b and `∑ s, ‖z s‖
^ 2 = 1` is (∑ s, ‖z s‖ ^ 2) = 1. The sum is computed in the codomain of f (a
sum of ℕ-values is in ℕ).

### G05 — Casts `(n : ℝ)`, `((q : ℕ) : ℝ)`, `↑x`

Meaning: `(e : T)` elaborates e at type T, inserting the canonical coercion `↑e`
if needed: `Nat.cast` from ℕ, `Int.cast` from ℤ, `Complex.ofReal` from ℝ to ℂ.
Into ℤ, ℚ, ℝ, ℂ these are injective (semi)ring homomorphisms, order-preserving
into ℤ, ℚ, ℝ, and they compose consistently (ℕ → ℤ → ℝ is ℕ → ℝ), so equalities
and inequalities transfer exactly.

Pinned by: `Nat.cast_le`: (m : α) ≤ n ↔ m ≤ n; `Nat.cast_inj`: (m : R) = n ↔ m =
n; `Int.cast_le`, `Int.cast_inj` (same for ℤ); `Complex.ofReal_inj`: (z : ℂ) = w
↔ z = w; `Int.cast_natCast`: ((n : ℤ) : R) = n; `Nat.cast_sub` (m ≤ n): ((n - m
: ℕ) : R) = n - m; `Nat.cast_div` (n ∣ m, (n : K) ≠ 0): (↑(m / n) : K) = m / n.

Conventions: Casts commute with +, *, ^, max, |·|, but not with ℕ subtraction or
ℕ/ℤ division, so placement matters: `((N / k : ℕ) : ℤ)` floor-divides first,
`((k - s.val : ℕ) : ℝ)` subtracts in ℕ first, `((m : ℤ) - 1)` casts first. An
ascription of an arithmetic expression casts the leaves: `(a - b : ℝ)` with a b
: ℕ is (a : ℝ) − (b : ℝ) (no truncation), while a parenthesised `(N / (k -
s.val) : ℕ)` is one leaf computed in ℕ (src/Init/Notation.lean). A function
expecting ℝ inserts the cast silently, e.g. `Real.sqrt (Nat.multinomial …)`.

### G06 — `|x|` (`abs`) and `‖z‖` (`norm`)

Meaning: |a| = max a (−a) on ℤ and ℝ. ‖·‖ is the norm of the argument's type:
|x| on ℝ; the modulus √(re² + im²) on ℂ; on a finite product such as Fin K → ℂ
the sup norm max_s ‖z s‖, not the Euclidean norm.

Pinned by: `abs_eq_max_neg`: |a| = max a (-a); `Real.norm_eq_abs`: ‖r‖ = |r|;
`Complex.norm_eq_sqrt_sq_add_sq`: ‖z‖ = √(z.re ^ 2 + z.im ^ 2); `Pi.norm_def`:
‖f‖ = ↑(Finset.univ.sup fun b => ‖f b‖₊).

Conventions: For z : Fin K → ℂ, `‖z‖ < 1` would describe the polydisc, not the
ball; the Euclidean norm has to be written out as √(∑ s, ‖z s‖ ^ 2).

### G07 — `a - b` on `ℕ` (truncated subtraction)

Meaning: For a b : ℕ, `a - b` is max(a − b, 0); on ℤ, ℚ, ℝ, ℂ it is ordinary
subtraction. The type at which `-` is elaborated decides, not the values: `(N -
b + k).choose k` and `(k - s.val : ℕ)` truncate, `((m : ℤ) - 1)` does not.

Pinned by: `Nat.sub_eq_zero_iff_le`: n - m = 0 ↔ n ≤ m; `Nat.sub_add_cancel`: m
≤ n → n - m + m = n; `Nat.cast_sub`: m ≤ n → ((n - m : ℕ) : R) = n - m.

Conventions: Left-associative: `N-i+k-1` is ((N − i) + k) − 1, so truncation can
happen at an intermediate step (N − i = 0 if i > N). Cast placement: G05 (`(a -
b : ℝ)` with a b : ℕ does not truncate; `((a - b : ℕ) : ℝ)` does).

### G08 — `/`, `%`, `⁻¹`, `∣` (division, remainder, inverse, divides)

Meaning: On ℕ, a / b = ⌊a/b⌋ and a % b is the remainder. On ℤ, `/` and `%` are
Euclidean (`Int.ediv`, `Int.emod`): for b ≠ 0, a = b·(a / b) + a % b with 0 ≤ a
% b < |b|, so a / b = ⌊a/b⌋ for b > 0 and ⌈a/b⌉ for b < 0. On ℚ, ℝ, ℂ, x / y = x *
y⁻¹. `a ∣ b` means ∃ c, b = a * c.

Pinned by: `Int.ediv_emod_unique` (0 < b): a / b = q ∧ a % b = r ↔ r + b * q = a
∧ 0 ≤ r ∧ r < b; `Nat.div_add_mod`: n * (m / n) + m % n = m; `Nat.mod_lt`: 0 < y
→ x % y < y; `div_eq_mul_inv`: a / b = a * b⁻¹; `Int.dvd_def`: (a ∣ b) = ∃ c, b
= a * c.

Conventions: Junk values: n / 0 = 0 and n % 0 = n on ℕ, ℤ (`Nat.div_zero`,
`Nat.mod_zero`, `Int.ediv_zero`, `Int.emod_zero`); x / 0 = 0 and 0⁻¹ = 0 in ℚ,
ℝ, ℂ (`div_zero`, `inv_zero`). On ℤ, (−7) / 2 = −4 and (−7) % 2 = 1. `((N / k :
ℕ) : ℤ)` and `(N / (k - s.val) : ℕ)` divide in ℕ (`Int.natCast_ediv`: ((m / n :
ℕ) : ℤ) = (m : ℤ) / (n : ℤ)); `(a : ℝ) / (b : ℝ)` is real division. `0 ∣ n` only
for n = 0.

### G09 — `x ^ n` with `n : ℕ`

Meaning: For n : ℕ and x in a monoid (ℕ, ℤ, ℝ, ℂ, square matrices, …), x ^ 0 = 1
and x ^ (n+1) = x ^ n * x. A numeral exponent such as `2` is a natural number by
default. A real exponent (`lam ^ ((n : ℝ) / 2)`) is the different operation
`Real.rpow` (G56).

Pinned by: `pow_zero`: a ^ 0 = 1; `pow_succ`: a ^ (n + 1) = a ^ n * a; default
exponent type ℕ from `NPow.toPow` (`default_instance high`).

Conventions: 0 ^ 0 = 1, so a monomial factor z_s^0 is 1 even at z_s = 0.
Application binds tighter than ^, and ^ tighter than * and /: `Real.sqrt (q : ℝ)
^ k` is (√q)^k.

### G10 — `Matrix m n R`, `Matrix.of`, and matrix arithmetic

Meaning: `Matrix m n α` is `m → n → α`; `A i j` is the (i, j) entry, so `Matrix
(Fin k) (Fin k) ℤ` is a k×k integer matrix with 0-based indices. `Matrix.of f`
has entries f i j. `+`, `-`, `0`, `•` are entrywise, `A * B` is the product, `1`
the identity (`-1` its negative), `A⁻¹` the inverse.

Pinned by: definition `Matrix m n α := m → n → α`; `Matrix.of_apply`: of f i j =
f i j; `Matrix.mul_apply`: (M * N) i k = ∑ j, M i j * N j k; `Matrix.one_apply`:
(1 : Matrix n n α) i j = if i = j then 1 else 0.

Conventions: The inverse is total: `Matrix.inv_def`: A⁻¹ = A.det⁻¹ʳ • A.adjugate
(⁻¹ʳ is `Ring.inverse`), so A⁻¹ = 0 if A.det is not a unit
(`Matrix.nonsing_inv_apply_not_isUnit`); over ℚ, a unit means ≠ 0. `*ᵥ` and `ᵀ`
are scoped notations enabled by `open scoped Matrix`.

### G14 — `max` and `min`

Meaning: In a linear order (ℕ, ℤ, ℝ), max a b = if a ≤ b then b else a and min a
b = if a ≤ b then a else b.

Pinned by: `max_def`, `min_def` (these equations); `Nat.cast_max`: (↑(max m n :
ℕ) : α) = max (m : α) n; `Int.cast_max`: (↑(max a b) : R) = max (a : R) (b : R).

Terms used only inside definition bodies, one line each:

- G11 — `classical`: decidability instances by choice; values are unchanged.
- G12 — `abbrev`: a reducible definition; type classes see through the name.
- G13 — `noncomputable`: no executable code is generated; the meaning is
  unaffected (`Classical.choice`).
-/

/-!
## Theorem 1 (`thm:onb`)
-/

/-!
### Paper context: Notation and Lean reading conventions (`conventions`)

TeX macros in the excerpts: `\cp` = ℂ, `\RR` = ℝ, `\q`/`\Q` = ℚ,
`\z`/`\Z` = ℤ, `\zp` = nonnegative integers, `\rp` = nonnegative reals,
`\PolySpace` and `\H` = H, `\Sphere` = S, `\p` = φ; `\cP`, `\cS`, `\B`,
`\C`, `\D` are the P, S, B, C, D defined below; `\ov` = complex conjugation,
`\ft` = Fourier transform, `\dd` = differential, `\bo` = boldface,
`\mymod{r}` = modulo r; `\supp`, `\vol`, `\len`, `\sect`, `\lcmk` are
defined below; shortened Greek commands (al, la, ga, …) are α, λ, γ, ….

Notation: e(t) = exp(2πit), v·x = Σⱼ vⱼxⱼ, |v|₁ = Σⱼ |vⱼ|, and
|A|∞ = maxᵢⱼ |Aᵢⱼ| for a matrix (not the maximum absolute row sum). For
nonnegative X, Y, X ≪ₚ Y means X ≤ C(p)Y with C depending only on the
subscripted parameters, and X ≍ₚ Y means both inequalities; so the position
of `∃ C` relative to the other quantifiers matters. A disjoint union asserts
both exhaustion and pairwise disjointness.

In Lean, `Fin k` indexes coordinates from 0: paper coordinate j is Lean
coordinate j−1.

Lean definitions for this comparison: `expTwoPiI`.
Statements depending on these definitions: Theorem 5, Lemma 7, Proposition 9, Proposition 10, Theorem 14, Proposition 15, Lemma 16, Lemma 17, Lemma 18, Lemma 19.
-/

/-!
### D001 — `expTwoPiI`

`Core.lean:619` · Used by: Lemma 16, Lemma 17, Lemma 18; Theorem 5, Lemma 7,
Proposition 9, Proposition 10, Theorem 14, Proposition 15, Lemma 19
(indirectly).

```lean
noncomputable def expTwoPiI (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)
```

Library terms: G58 `Real.exp`.
-/

/-!
### Paper context: The ball, sphere, Hardy space, and homogeneous polynomials (`polynomials`)

Lean represents H_N (also written H_{K,N}) by monomial coefficients:
`PolySpaceH K N` holds coefficient vectors indexed by the multi-indices of
total degree N (`degIdx`), with pointwise operations, and `polyEval` maps c
to z ↦ Σⱼ cⱼz^j. Neither the Hardy space nor a subspace of L²(S^(2K−1)) is
constructed; `polyInner` (`pairing` context) is a coefficient formula.

Original paper definition/context (`article.txt:204-214`, verbatim TeX):
```tex
Let  $\mathbb B_K :=\{z\in\cp^K:
 |z_1|^2+\cdots+|z_K|^2<1\}$ be the complex unit ball and $\Sphere^{2K-1}=\partial {\mathbb B_K}$ be the complex unit sphere. Let $H^2(\mathbb B_K)$ {denote} the Hardy space of holomorphic functions} $f:\mathbb B_K\to \cp$ that have radial boundary values in $L^2$, that is, $f(r\,\cdot)$ converges in
$L^2(\Sphere^{2K-1})$ as $r\to1^-$. {In this way, the Hardy space $H^2(\mathbb B_K)$ inherits the Hilbert space structure of $L^2(\Sphere^{2K-1})$ (see \cite{R}). Write $z = (z_1, \ldots, z_K)$ and let
\[
\PolySpace_N :=\operatorname{span}_{\cp}
 \left\{z^j:j\in\z_{\geq 0}^K, \ j_1+\cdots+j_K=N\right\} \quad (z^{j} = z_1^{j_1} \cdots z_K^{j_K})
\]
denote the space of homogeneous polynomials of degree $N$ (note that the dimension $K$ is implied from the context). A routine calculation shows that $z^j$ and $z^l$ with $j\neq l$ are orthogonal in $H^2(\mathbb B_K)$. In particular, we have the following orthogonal decomposition
\[
 H^2(\mathbb B_K)=\widebar{\bigoplus_{N\geq0}\PolySpace_N}.
\]
```

Lean definitions for this comparison: `degIdx`, `PolySpaceH`, `polyEval`, `UniformBoundUnit.cSphere`.
Statements depending on these definitions: Theorem 1, Theorem 5, Proposition 9, Proposition 10, Lemma 11.
-/

/-!
### D002 — `degIdx`

`Core.lean:623` · Used by: Theorem 1, Theorem 5, Proposition 9, Proposition 10,
Lemma 11 (indirectly).

```lean
def degIdx (K N : ℕ) : Finset (Fin K → ℕ) := Finset.piAntidiag Finset.univ N
```

Library terms: G34 `Finset.piAntidiag`.
-/

/-!
### D003 — `PolySpaceH`

`Core.lean:625` · Used by: Theorem 1, Theorem 5, Lemma 11; Proposition 9,
Proposition 10 (indirectly).

```lean
abbrev PolySpaceH (K N : ℕ) : Type := ↥(degIdx K N) → ℂ
```

Library terms: G35 `↥s`.
-/

/-!
### D004 — `polyEval`

`Core.lean:627` · Used by: Theorem 1, Theorem 5, Proposition 10, Lemma 11.

```lean
noncomputable def polyEval (K N : ℕ) (c : PolySpaceH K N) (z : Fin K → ℂ) : ℂ :=
  ∑ n : ↥(degIdx K N), c n * ∏ s, z s ^ ((n : Fin K → ℕ) s)
```

Library terms: G15 `x.val`; G35 `↥s`.
-/

/-!
### D005 — `UniformBoundUnit.cSphere`

`Core.lean:3187` · Used by: Theorem 5, Lemma 11.

```lean
def cSphere (K : ℕ) : Set (Fin K → ℂ) := {z | ∑ s, ‖z s‖ ^ 2 = 1}
```
-/

/-!
### Paper context: Normalized surface measure and the polynomial inner product (`pairing`)

With σ normalized so that σ(S^(2K−1)) = 1, the paper's monomial norms
(excerpt below) give the pairing in coefficients,

    ⟨c,d⟩ = choose(N+K−1,K−1)⁻¹ Σⱼ multinomial(N;j)⁻¹ cⱼ overline(dⱼ),

which is the formula of `polyInner` (linear in c, conjugate-linear in d).
Its weights are the classical integrals: for K ≥ 1 and |j| = N,

    choose(N+K−1,K−1)⁻¹ · multinomial(N;j)⁻¹
      = [(K−1)! N!/(N+K−1)!] · [j₁!⋯j_K!/N!]
      = (K−1)! j₁!⋯j_K!/(N+K−1)! = ∫ |z^j|² dσ

(Rudin, Function Theory in the Unit Ball of ℂⁿ, Prop. 1.4.9; this is the
paper's reference [R]). With the orthogonality of distinct monomials, this
shows by hand that `polyInner K N c d` is the normalized L²(S^(2K−1))
pairing of `polyEval K N c` and `polyEval K N d`. This is a by-hand
identification, not a Lean theorem: Lean defines the pairing by the
coefficient formula, not by an integral, and the coefficient model is not a
checked identification with the Hardy space.

`Module.Basis` plus `polyInner ... = if i = j then 1 else 0` encode the
orthonormal basis of Theorem 1; its L∞ bound is on values on the open ball,
not on coefficients (sphere endpoints use `cSphere` or its equation).

Original paper definition/context (`article.txt:468-482`, verbatim TeX):
```tex
Recall that {the} $H^2(\mathbb B_K)$ space is equipped with the following
inner product 
\begin{align*}
 \langle f,g\rangle
 :=
 \int_{\Sphere^{2K-1}}f(z)\ov{g(z)}\,\dd\sigma(z),
\end{align*}
where $\si$ is the induced Lebesgue surface measure on $\Sphere^{2K-1}$ normalized so that $\si (\Sphere^{2K-1})=1$.
A routine computation (see \cite{R}) shows that for any $j,l \in \z_{\geq 0}^K$ {with $N=j_1+\cdots+j_K=l_1+\cdots+l_K$} we have
\begin{equation}\label{def:innerprod}
 \langle z^j,z^l\rangle
 =\binom{N+K-1}{K-1}^{-1}\binom Nj^{-1}{\bo \delta}_{j,l},
 \quad \text{where} \quad
 \binom Nj:=\frac{N!}{j_1!\cdots j_K!}.
\end{equation}
```

Original paper definition/context (`article.txt:526-529`, verbatim TeX):
```tex
For $z \in \Sphere^{2K - 1}$ we {put} $z_s = \sqrt{r_s} e(\theta_s)$, for $s=1,{\ldots},K$, where $e(z)=e^{2\pi i z}$,  $\theta_s\in \RR$ and $r_s \geq 0$ so that $\sum_{s=1}^K r_s = 1$. In order to estimate uniformly
\[
\|\p\|_{L^\infty(\mathbb B_K)} = \|\p\|_{L^\infty(\Sphere^{2K-1})} = \sup_{\substack{r_1+\cdots+r_{K}=1 \\ r_s\geq 0, \ \theta_s \in \RR}} |\p( \sqrt{r_1} e(\theta_1),\ldots,\sqrt{r_K} e(\theta_K))|
\]
```

Lean definitions for this comparison: `polyInner`.
Statements depending on these definitions: Theorem 1, Theorem 5, Proposition 9, Lemma 11.
-/

/-!
### D006 — `polyInner`

`Core.lean:630` · Used by: Theorem 1, Theorem 5, Proposition 9, Lemma 11.

```lean
noncomputable def polyInner (K N : ℕ) (c d : PolySpaceH K N) : ℂ :=
  ((Nat.choose (N + K - 1) (K - 1) : ℂ))⁻¹ *
    ∑ n : ↥(degIdx K N),
      ((Nat.multinomial Finset.univ (n : Fin K → ℕ) : ℂ))⁻¹ * c n * (starRingEnd ℂ) (d n)
```

Library terms: G15 `x.val`; G35 `↥s`; G52 `Nat.choose`; G53 `Nat.multinomial`;
G61 `starRingEnd ℂ`.
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{theorem}\label{thm:onb}
Let $K\geq 2$. Then for every $N\geq 0$
the space $\PolySpace_N$ admits an orthonormal basis
$\{\p_{1, N},\p_{2, N},\ldots,\p_{\dim\PolySpace_N, N}\}$ such that
\[
  \sup_{\substack{N \geq 0 \\ 1\leq i\leq \dim\PolySpace_N}}\|\p_{i, N}\|_{L^\infty(\mathbb B_K)}<\infty.
\]
\end{theorem}
```

Coverage: `direct`.
-/

/-!
Definitions used: `degIdx` (D002), `PolySpaceH` (D003), `polyEval` (D004),
`polyInner` (D006). Library terms: G67 `Module.Basis ι R M`; G68
`Module.finrank`.
-/
theorem theorem1 :
  ∀ (K : ℕ) (hK : 2 ≤ K),
∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ,
        ∃ φ : Module.Basis (Fin (Module.finrank ℂ (PolySpaceH K N))) ℂ (PolySpaceH K N),
          (∀ i j, polyInner K N (φ i) (φ j) = if i = j then 1 else 0) ∧
          ∀ i, ∀ z : Fin K → ℂ, ∑ s, ‖z s‖ ^ 2 < 1 →
            ‖polyEval K N (φ i) z‖ ≤ C :=
  @_root_.thm_onb

/-!
## Theorem 2 (`thm:box`)
-/

/-!
### Paper context: Integer polytopes, boxes, volume, and sections (`geometry`)

`polyPZ` is the paper's P(L) ⊆ ℤ^k (a ℤ-polytope need not be bounded);
`polyP` tests the same inequalities on ℕ-vectors. Further names: J ↦
`boxZ`, #Jⱼ ↦ `boxSide` (= max(hiⱼ−loⱼ+1,0)), vol ↦ `boxVol`, supp ↦
`vecSupport`, len ↦ `boxLen`, sect ↦ `boxSect`, P(L)∩J ↦ `polyBoxZ`; the
`UniformBoundUnit.*Z` variants are separate source definitions.
`quadExpSum k α c θ S` sums over an arbitrary finite S ⊆ ℤ^k; with
S = `polyBoxZ k L lo hi` it is the paper's sum over P(L)∩J.

Theorem 2's Lean type writes the box, constraint filter, exponential sum,
vol(I) and sect(w₀;I) inline; unfolded, these agree with `boxZ`,
`polyBoxZ`, `quadExpSum`, `boxVol` and `boxSect`, so root `ThmBox` unfolds
to Theorem 2's type (`basis` context). `UniformBoundUnit.ThmBox` uses the
`*Z` variants.

Original paper definition/context (`article.txt:358-375`, verbatim TeX):
```tex
Let $k \geq 1$.
For a finite set $L\subset\Z^k\times\Z$, whose elements we call
\emph{constraints}, put
\[
\cP(L):=\{n\in\Z^k : v\cdot n+b\ge0 \text{ for every }(v,b)\in L\}.
\]
A \emph{$\Z$-polytope} is a set of the form $\cP(L)$. 

A \emph{box} $J\subset \z^k$ is a product of finite intervals, i.e., 
$J=J_1\times\cdots\times J_k$ with $J_i = [a_i,b_i] \cap \mathbb{Z}$. 
For a box $J$ and $w = (w_1, \ldots, w_k) \in\z^k$, put
\[
  \len(w;J):=\max\Bigl(1,\max_{j : w_j \neq 0}\#J_j\Bigr).
\]
Thus $\len(w;J)$ is the longest side seen by $w$. Define
\[
\vol(J) := \prod_{i = 1}^{k} \# J_i \quad \text{and} \quad \sect(w;J):=\frac{\vol(J)}{\len(w;J)}.
\] 
```

Original paper definition/context (`article.txt:381-385`, verbatim TeX):
```tex
Finally, for any symbol $\Box$ whatsoever, whenever we write $\Box \in F^k$ with $F$ a set 
we will denote by $\Box_j$ the $j$th component of $\Box$ so that $\Box = (\Box_1, \ldots, \Box_k)$.   
Thus if $s \in \mathbb{Q}^k$ then we automatically infer that $s_2$ refers to the second component of $s$,
i.e., $s = (s_1, s_2, \ldots, s_k)$. For any vector $v \in F^k$ we will also denote by $\supp v$ the set of
indices $j$ for which $v_j \neq 0$. For a real vector $v$ we write $|v|_1=\sum_j|v_j|$ and
$|v|_\infty=\max_j|v_j|$, and for a real matrix $A$ we write $|A|_\infty$ for the largest absolute
value of an entry of $A$.
```

The three norms of the last sentence are `∑ j, |v j|`, `Finset.univ.sup fun j =>
(v j).natAbs` and `matInftyNorm` (D023) in the encodings below; `|v|_1 ≤ R` and
`|A|_∞ ≤ R` are the complexity bounds of Definition 3, Definition 20 and
Lemma 26, and `|v|_1 ≤ V` is the constraint bound of Theorem 2.

Lean definitions for this comparison: `polyPZ`, `polyP`, `vecSupport`, `boxZ`, `boxSide`, `boxVol`, `boxLen`, `boxSect`, `polyBoxZ`, `quadExpSum`, `UniformBoundUnit.latticePtsZ`, `UniformBoundUnit.boxVolZ`, `UniformBoundUnit.boxLenZ`, `UniformBoundUnit.boxSectZ`.
Statements depending on these definitions: Theorem 5, Proposition 10, Theorem 14, Theorem 21, Lemma 24, Lemma 25, Lemma 26, Proposition 27, Proposition 28.
-/

/-!
### D007 — `polyPZ`

`Core.lean:9571` · Used by: Theorem 21, Lemma 25, Lemma 26, Proposition 28;
Lemma 24, Proposition 27 (indirectly).

```lean
def polyPZ (d : ℕ) (W : Finset ((Fin d → ℤ) × ℤ)) : Set (Fin d → ℤ) :=
  {x | ∀ p ∈ W, 0 ≤ (∑ s, p.1 s * x s) + p.2}
```
-/

/-!
### D008 — `polyP`

`Core.lean:641` · Used by: Theorem 5, Proposition 10 (indirectly).

```lean
def polyP (k : ℕ) (L : Finset ((Fin k → ℤ) × ℤ)) : Set (Fin k → ℕ) :=
  {x | ∀ p ∈ L, 0 ≤ (∑ s, p.1 s * (x s : ℤ)) + p.2}
```
-/

/-!
### D009 — `vecSupport`

`Core.lean:9568` · Used by: Lemma 26; Lemma 25, Proposition 27 (indirectly).

```lean
def vecSupport {d : ℕ} (w : Fin d → ℤ) : Finset (Fin d) :=
  Finset.univ.filter fun j => w j ≠ 0
```

Library terms: G26 `Finset.filter`.
-/

/-!
### D010 — `boxZ`

`Core.lean:1978` · Used by: Theorem 21; Proposition 10, Theorem 14, Lemma 24,
Lemma 25, Lemma 26, Proposition 27 (indirectly).

```lean
def boxZ (k : ℕ) (lo hi : Fin k → ℤ) : Finset (Fin k → ℤ) :=
  Fintype.piFinset fun s => Finset.Icc (lo s) (hi s)
```

Library terms: G25 `Finset.Icc`; G33 `Fintype.piFinset`.
-/

/-!
### D011 — `boxSide`

`Core.lean:1981` · Used by: Proposition 10, Theorem 14, Theorem 21, Lemma 25,
Lemma 26, Proposition 27 (indirectly).

```lean
def boxSide (k : ℕ) (lo hi : Fin k → ℤ) (s : Fin k) : ℕ :=
  (Finset.Icc (lo s) (hi s)).card
```

Library terms: G25 `Finset.Icc`; G28 `Finset.card`.
-/

/-!
### D012 — `boxVol`

`Core.lean:1984` · Used by: Theorem 14, Theorem 21, Proposition 27; Proposition
10 (indirectly).

```lean
def boxVol (k : ℕ) (lo hi : Fin k → ℤ) : ℕ :=
  ∏ s, boxSide k lo hi s
```
-/

/-!
### D013 — `boxLen`

`Core.lean:1987` · Used by: Theorem 21; Proposition 10 (indirectly).

```lean
def boxLen (k : ℕ) (w : Fin k → ℤ) (lo hi : Fin k → ℤ) : ℕ :=
  max 1 ((Finset.univ.filter fun s : Fin k => w s ≠ 0).sup (boxSide k lo hi))
```

Library terms: G26 `Finset.filter`; G29 `Finset.sup`.
-/

/-!
### D014 — `boxSect`

`Core.lean:1990` · Used by: Proposition 10 (indirectly).

```lean
noncomputable def boxSect (k : ℕ) (w : Fin k → ℤ) (lo hi : Fin k → ℤ) : ℝ :=
  (boxVol k lo hi : ℝ) / (boxLen k w lo hi : ℝ)
```
-/

/-!
### D015 — `polyBoxZ`

`Core.lean:1993` · Used by: Theorem 14; Proposition 10 (indirectly).

```lean
def polyBoxZ (k : ℕ) (L : Finset ((Fin k → ℤ) × ℤ)) (lo hi : Fin k → ℤ) :
    Finset (Fin k → ℤ) :=
  (boxZ k lo hi).filter fun x => ∀ p ∈ L, 0 ≤ (∑ s, p.1 s * x s) + p.2
```

Library terms: G26 `Finset.filter`.
-/

/-!
### D016 — `quadExpSum`

`Core.lean:1997` · Used by: Theorem 14; Proposition 10 (indirectly).

```lean
noncomputable def quadExpSum (k : ℕ) (α : ℝ) (c : Fin k → ℕ) (θ : Fin k → ℝ)
    (S : Finset (Fin k → ℤ)) : ℂ :=
  ∑ n ∈ S, expTwoPiI (α * ∑ j, (c j : ℝ) * (n j : ℝ) ^ 2 + ∑ j, θ j * (n j : ℝ))
```
-/

/-!
### D017 — `UniformBoundUnit.latticePtsZ`

`Core.lean:3193` · Used by: Theorem 5 (indirectly).

```lean
def latticePtsZ (k : ℕ) (L : Finset ((Fin k → ℤ) × ℤ)) (lo hi : Fin k → ℤ) :
    Finset (Fin k → ℤ) :=
  (Fintype.piFinset fun j => Finset.Icc (lo j) (hi j)).filter
    fun n => ∀ p ∈ L, 0 ≤ (∑ s, p.1 s * n s) + p.2
```

Library terms: G25 `Finset.Icc`; G26 `Finset.filter`; G33 `Fintype.piFinset`.
-/

/-!
### D018 — `UniformBoundUnit.boxVolZ`

`Core.lean:3198` · Used by: Theorem 5 (indirectly).

```lean
def boxVolZ (k : ℕ) (lo hi : Fin k → ℤ) : ℕ :=
  ∏ j, (Finset.Icc (lo j) (hi j)).card
```

Library terms: G25 `Finset.Icc`; G28 `Finset.card`.
-/

/-!
### D019 — `UniformBoundUnit.boxLenZ`

`Core.lean:3201` · Used by: Theorem 5 (indirectly).

```lean
def boxLenZ (k : ℕ) (w : Fin k → ℤ) (lo hi : Fin k → ℤ) : ℕ :=
  max 1 ((Finset.univ.filter fun j => w j ≠ 0).sup fun j =>
    (Finset.Icc (lo j) (hi j)).card)
```

Library terms: G25 `Finset.Icc`; G26 `Finset.filter`; G28 `Finset.card`; G29
`Finset.sup`.
-/

/-!
### D020 — `UniformBoundUnit.boxSectZ`

`Core.lean:3205` · Used by: Theorem 5 (indirectly).

```lean
noncomputable def boxSectZ (k : ℕ) (w : Fin k → ℤ) (lo hi : Fin k → ℤ) : ℝ :=
  (boxVolZ k lo hi : ℝ) / (boxLenZ k w lo hi : ℝ)
```
-/

/-!
### Paper context: Continued fractions and bounded partial quotients (`fractions`)

The numbered statements bound only aᵢ for i ≥ 1, not a₀; the general
introductory wording is quoted unchanged below. Lean bounds every entry of
`(GenContFract.of α).partDens`, which omits a₀ (G76); convergents use
`.nums` and `.dens`. `UniformBoundUnit.BddPartQuot` packages irrationality
and this bound; other theorem types spell both conditions out.

Original paper definition/context (`article.txt:377-379`, verbatim TeX):
```tex
Given an irrational number $\al$ write $\alpha := [a_0; a_1, a_2, \ldots]$ for the continued fraction
expansion of $\al$. We say that $\al$ has bounded partial quotients when there exists a $C > 0$ such
that $a_i \leq C$ for all $a_i$.
```

Lean definitions for this comparison: `UniformBoundUnit.BddPartQuot`.
Statements depending on these definitions: Theorem 5.
-/

/-!
### D021 — `UniformBoundUnit.BddPartQuot`

`Core.lean:3189` · Used by: Theorem 5.

```lean
def BddPartQuot (a α : ℝ) : Prop :=
  Irrational α ∧
    ∀ (i : ℕ) (x : ℝ), (GenContFract.of α).partDens.get? i = some x → x ≤ a
```

Library terms: G55 `Irrational`; G76 `GenContFract.of`.
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{theorem}\label{thm:box}
Let {$k\geq1$,} $r\ge 0$ and $V,h,a\ge1$. Let $\alpha = [a_0; a_1, a_2, \ldots]$ be
an irrational number with $a_i \leq a$ for all $i \geq 1$.  
Let $c_1,{\ldots},c_k$ be positive integers with
$c_j\le h$. Let $I=I_1\times\cdots\times I_k$
be a box of nonempty intervals. Let
$L$ be a set of at most $r$ pairs $(v,b)\in\mathbb Z^k\times
\mathbb Z$ with $|v|_1\le V$. Then
\[
\sup_{\theta \in \RR^k} \, \Bigl|\sum_{n\in \cP(L) \cap I}e\Bigl(\alpha\sum_{j=1}^kc_jn_j^2
+\theta\cdot n\Bigr)\Bigr|
\ \ll_{k,r,V,h,a}\ \vol(I)^{1/2}.
\]
If both $(w_0,b_0)$ and $(-w_0,-b_0)$ belong to $L$, with
$w_0\ne0$, then also
\[
\sup_{\theta \in \RR^k} \, \Bigl|\sum_{n\in \cP(L) \cap I}e\Bigl(\alpha\sum_{j=1}^kc_jn_j^2
+\theta\cdot n\Bigr)\Bigr|
\ \ll_{k,r,V,h,a}\ \sect(w_0;I)^{1/2}.
\]
\end{theorem}
```

Coverage: `direct`.
-/

/-!
Library terms: G25 `Finset.Icc`; G26 `Finset.filter`; G28 `Finset.card`; G29
`Finset.sup`; G33 `Fintype.piFinset`; G55 `Irrational`; G57 `Real.sqrt`; G58
`Real.exp`; G76 `GenContFract.of`.
-/
theorem theorem2 :
  ∀ (k r V h : ℕ) (a : ℝ), 1 ≤ k → 1 ≤ V → 1 ≤ h → 1 ≤ a →
      ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, Irrational α →
        (∀ (i : ℕ) (x : ℝ), (GenContFract.of α).partDens.get? i = some x → x ≤ a) →
        ∀ c : Fin k → ℕ, (∀ j, 1 ≤ c j) → (∀ j, c j ≤ h) →
        ∀ lo hi : Fin k → ℤ, (∀ s, lo s ≤ hi s) →
        ∀ L : Finset ((Fin k → ℤ) × ℤ), L.card ≤ r →
          (∀ p ∈ L, ∑ s, |p.1 s| ≤ (V : ℤ)) →
        ∀ θ : Fin k → ℝ,
          ‖∑ n ∈ (Fintype.piFinset fun s => Finset.Icc (lo s) (hi s)).filter
                (fun x => ∀ p ∈ L, 0 ≤ (∑ s, p.1 s * x s) + p.2),
              Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                ((α * ∑ j, (c j : ℝ) * (n j : ℝ) ^ 2 + ∑ j, θ j * (n j : ℝ) : ℝ) : ℂ))‖
            ≤ C * Real.sqrt ((∏ s, (Finset.Icc (lo s) (hi s)).card : ℕ) : ℝ) ∧
          ∀ (w₀ : Fin k → ℤ) (b₀ : ℤ), w₀ ≠ 0 → (w₀, b₀) ∈ L → (-w₀, -b₀) ∈ L →
            ‖∑ n ∈ (Fintype.piFinset fun s => Finset.Icc (lo s) (hi s)).filter
                  (fun x => ∀ p ∈ L, 0 ≤ (∑ s, p.1 s * x s) + p.2),
                Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                  ((α * ∑ j, (c j : ℝ) * (n j : ℝ) ^ 2 + ∑ j, θ j * (n j : ℝ) : ℝ) : ℂ))‖
              ≤ C * Real.sqrt
                  (((∏ s, (Finset.Icc (lo s) (hi s)).card : ℕ) : ℝ) /
                    ((max 1 ((Finset.univ.filter fun s : Fin k => w₀ s ≠ 0).sup
                      fun s => (Finset.Icc (lo s) (hi s)).card) : ℕ) : ℝ)) :=
  @_root_.thm_box

/-!
## Definition 3 (`def:equicomp`)
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{definition}\label{def:equicomp}
Let $\aff_k(\Z) = \GL_k(\Z) \ltimes \Z^k $ be the group of affine transformations of the form $x\in \RR^k \mapsto Ax+b \in \RR^k$, where $A \in \GL_k(\Z)$ and $b\in \Z^k$. Let $P,Q\subset \mathbb Z^k$ be $\Z$-polytopes. We say that $P$ and $Q$ are \emph{$\aff_k(\Z)$-equidecomposable with complexity bounded by $R \geq 1$} if there is a disjoint collection of $\Z$-polytopes $\cP(L_1), \ldots, \cP(L_r)$ and aﬃne transformations $A_1 x + b_1,\ldots, A_r x + b_r \in \aff_k(\z)$ such that
\[
P = \bigsqcup_{i=1}^r {\cP(L_i)} \quad \text{and}  \quad Q = \bigsqcup_{i=1}^r (A_i \cP(L_i) + b_i),
\]
where
\[
r\leq R \ , \ \forall i: \# L_i \leq R \ , \ \forall i: |A_i|_\infty \leq R \ \ \text{and}\ \  \forall i \forall (v,b) \in L_i:   |v|_1 \leq R.
\]
\end{definition}
```

Coverage: `direct-definition`, referring to `Paper.definition3` (D025), which
states the paper's two disjoint unions as a set equality together with pairwise
disjointness. The superseded weak encoding is kept as `Paper.definition3Weak`
(D025w), displayed for comparison (see the `affine` context).
-/

/-!
Conformance: no displayed statement uses either predicate. Proposition 4 writes
the simplex–box equidecomposition out clause by clause; by its note, S_N, B_N ⊆
ℤ^k (lcm_k ∣ N) satisfy `Paper.definition3 k R`. `IsUNmap` (D029), the
ℕ-valued variant of Proposition 4's clauses that Theorem 5 and Proposition 10
use as a hypothesis (`simplex` context), is exported by `Compatibility.lean` as
`Paper.Definition3.simplexBoxAdmissibleMap`. It is not a specialization of
either Definition 3 predicate — its source-piece clause is the
unique-membership form of D025w, it decomposes the target not at all (only a
pointwise affine formula for U on each piece), and its complexity bounds are
entrywise — so the abbreviation, formerly named `simplexBoxSpecialization`, has
been renamed not to claim otherwise.
-/

/-!
### Paper context: Reading the affine-equidecomposition predicate (`affine`)

Known defect of `Paper.definition3Weak` (D025w), which is why it is not the
paper's definition: its clause `x ∈ P ↔ ∃! i, x ∈ piece i` lets a point
outside P lie in two pieces, and likewise for Q. Examples in ℤ¹ with R = 2:
pieces {0,…,3} and {1,…,3} with maps x↦x and x↦−x give P = {0} and
Q = {−3,…,3}; for n ≥ 1, two copies of {0,…,n−1} with x↦x and x↦x+n give
P = ∅ and Q = {0,…,2n−1}; pieces {0,…,n−1} and {n,…,2n−1} with x↦x and x↦x−n
give P = {0,…,2n−1} and Q = ∅. None is an equidecomposition.
`Paper.definition3` (D025) has the set equality and pairwise disjointness
instead, and admits none of them.

`transitionSize` = `matInftyNorm` is the largest |entry| (the paper's |A|∞)
and implies no invertibility; Definition 3 requires det = ±1, whereas
Definition 23 requires only det ≠ 0.

Lean definitions for this comparison: `Paper.definition3`, `Paper.definition3Weak`, `matInftyNorm`, `transitionSize`, `pieceAffineImage`.
Statements depending on these definitions: Theorem 21, Lemma 24, Lemma 25, Lemma 26, Proposition 27.
-/

/-!
### D022 — `pieceAffineImage`

`Core.lean:9680` · Used by: Theorem 21, Lemma 24, Lemma 25, Lemma 26,
Proposition 27 (indirectly).

```lean
def pieceAffineImage {d : ℕ} (u : Fin d → ℤ) (Φ : Matrix (Fin d) (Fin d) ℤ)
    (S : Set (Fin d → ℤ)) : Set (Fin d → ℤ) :=
  (fun y => u + Φ *ᵥ y) '' S
```

Library terms: G37 `f '' S`; G63 `Matrix.mulVec`.
-/

/-!
### D023 — `matInftyNorm`

`Core.lean:9666` · Used by: Theorem 21, Lemma 24, Lemma 26, Proposition 27
(indirectly).

```lean
def matInftyNorm {d : ℕ} (Φ : Matrix (Fin d) (Fin d) ℤ) : ℕ :=
  Finset.univ.sup fun ij : Fin d × Fin d => (Φ ij.1 ij.2).natAbs
```

Library terms: G29 `Finset.sup`; G46 `Int.natAbs`.
-/

/-!
### D024 — `transitionSize`

`Core.lean:9697` · Used by: Lemma 24, Lemma 26, Proposition 27.

```lean
def transitionSize {d : ℕ} (Φ : Matrix (Fin d) (Fin d) ℤ) : ℕ := matInftyNorm Φ
```
-/

/-!
### D025 — `Paper.definition3`

`Compatibility.lean:76` · Used by no displayed statement.

The paper's two displayed disjoint unions P = ⨆ᵢ 𝒫(Lᵢ) and
Q = ⨆ᵢ (Aᵢ 𝒫(Lᵢ) + bᵢ) are each stated as a set equality together with
pairwise disjointness of the summands. `det.natAbs = 1` is Aᵢ ∈ GL_k(ℤ);
`transitionSize` (D024) is the paper's |Aᵢ|_∞. The predicate does not require
P, Q to be ℤ-polytopes or R ≥ 1; for those it reads, by inspection, as the
paper's definition (for R = 0 it says P = Q = ∅), a harmless generalization.

```lean
def definition3 (k R : ℕ) (P Q : Set (Fin k → ℤ)) : Prop :=
  ∃ (r : ℕ) (L : Fin r → Finset ((Fin k → ℤ) × ℤ))
      (A : Fin r → Matrix (Fin k) (Fin k) ℤ) (b : Fin r → Fin k → ℤ),
    r ≤ R ∧
    (∀ i, (L i).card ≤ R) ∧
    (∀ i, (A i).det.natAbs = 1) ∧
    (∀ i, transitionSize (A i) ≤ R) ∧
    (∀ i, ∀ p ∈ L i, (∑ j, |p.1 j|) ≤ (R : ℤ)) ∧
    P = ⋃ i : Fin r, polyPZ k (L i) ∧
    (∀ i i' : Fin r, i ≠ i' → Disjoint (polyPZ k (L i)) (polyPZ k (L i'))) ∧
    Q = ⋃ i : Fin r, pieceAffineImage (b i) (A i) (polyPZ k (L i)) ∧
    ∀ i i' : Fin r, i ≠ i' →
      Disjoint (pieceAffineImage (b i) (A i) (polyPZ k (L i)))
        (pieceAffineImage (b i') (A i') (polyPZ k (L i')))
```

Library terms: G28 `Finset.card`; G38 `⋃ i, S i`; G39 `Disjoint`; G46
`Int.natAbs`; G62 `Matrix.det`.
-/

#check @_root_.Paper.definition3

/-!
### D025w — `Paper.definition3Weak`

`Compatibility.lean:100` · Used by no displayed statement.

**Not the paper's Definition 3.** This is the superseded encoding, kept only so
that the counterexamples in the `affine` context name a real declaration: it
has the first five clauses of D025 verbatim, but replaces the two disjoint
unions by unique-membership clauses, which force neither the pieces into P nor
their images into Q.

```lean
def definition3Weak (k R : ℕ) (P Q : Set (Fin k → ℤ)) : Prop :=
  ∃ (r : ℕ) (L : Fin r → Finset ((Fin k → ℤ) × ℤ))
      (A : Fin r → Matrix (Fin k) (Fin k) ℤ) (b : Fin r → Fin k → ℤ),
    r ≤ R ∧
    (∀ i, (L i).card ≤ R) ∧
    (∀ i, (A i).det.natAbs = 1) ∧
    (∀ i, transitionSize (A i) ≤ R) ∧
    (∀ i, ∀ p ∈ L i, (∑ j, |p.1 j|) ≤ (R : ℤ)) ∧
    (∀ x, x ∈ P ↔ ∃! i : Fin r, x ∈ polyPZ k (L i)) ∧
    ∀ y, y ∈ Q ↔
      ∃! i : Fin r, y ∈ pieceAffineImage (b i) (A i) (polyPZ k (L i))
```

Library terms: G28 `Finset.card`; G41 `∃!`; G46 `Int.natAbs`; G62 `Matrix.det`.
-/

#check @_root_.Paper.definition3Weak

/-!
## Proposition 4 (`prop:UNmap`)
-/

/-!
### Paper context: The simplex, rectangular index set, and admissible maps (`simplex`)

Here k = K−1. Lean's `boxB` indexes s from 0, so its N/(k − s) is the
paper's N/(k+1−s).

The paper defines B_N only when lcm_k ∣ N; `boxB` is total (ℕ-division), so
the divisibility is not built in. It is stated explicitly in Proposition 4,
`PropUNmap`, `UniformBoundUnit.PropUNmap` and the Theorem 5 endpoints that
use `boxB`; Proposition 10 uses N − N % lcmUpTo k, a multiple of lcm_k.
Proposition 9 has no divisibility hypothesis, but with M = N−b its
hypothesis `Set.BijOn U (simplexS k M) (boxB k M)` forces lcm_k ∣ M: a
bijection needs equal cardinalities, and #boxB k M = ∏_{s=1}^{k} (⌊M/s⌋+1)
≤ ∏_{s=1}^{k} (M/s+1) = choose(M+k,k) = #simplexS k M, with equality iff
every s ≤ k divides M.

`IsUNmap` has ℕ-valued vectors, so it uses `polyP`, not `polyPZ`. Its
source-piece clause has the unique-membership weakness of
`Paper.definition3Weak`, but its `Set.BijOn` is a true bijection. It occurs as a
hypothesis (`hU` of `theorem5OrthonormalBasis`, the U-hypotheses of
`theorem5UniformBound` and `proposition10`, and inside both `PropUNmap`s),
where its looseness can only strengthen them; the existence conjuncts of
`theorem5UniformBound` and `proposition10` only show that their bounds are
not vacuous. It is stricter in one respect: its affine clause must hold on
all of `polyP k (L i)`, even outside S_N. When lcm_k ∣ N, Proposition 4's
witness, converted to ℕ-values with `toNat`, satisfies it (`basis` context).

Original paper definition/context (`article.txt:424-426`, verbatim TeX):
```tex
$$
\lcmk := \text{lcm}(1,2,\ldots, k)
$$
```

Original paper definition/context (`article.txt:444-450`, verbatim TeX):
```tex
Define the following $\Z$-polytopes
\begin{align}\label{eq:originalSimplexAndBox}
\cS_N&:=\left\{j\in \Z_{\ge0}^k:
  j_1+\cdots+j_k\le N\right\} \quad \text{and} \quad
\B_N:=\prod_{s=1}^k \bigg\{0,1,\ldots, \frac{N}{k+1-s}\bigg\},
\end{align}
where $\B_N$ is only defined when $\lcmk \mid N$.
```

Lean definitions for this comparison: `lcmUpTo`, `simplexS`, `boxB`, `IsUNmap`.
Statements depending on these definitions: Theorem 5, Proposition 9, Proposition 10, Proposition 28.
-/

/-!
### D026 — `lcmUpTo`

`Core.lean:621` · Used by: Theorem 5, Proposition 10.

```lean
def lcmUpTo (k : ℕ) : ℕ := (Finset.Icc 1 k).lcm id
```

Library terms: G25 `Finset.Icc`; G31 `Finset.lcm`.
-/

/-!
### D027 — `simplexS`

`Core.lean:635` · Used by: Proposition 9, Proposition 28; Theorem 5, Proposition
10 (indirectly).

```lean
def simplexS (k N : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => Finset.range (N + 1)).filter fun j => ∑ s, j s ≤ N
```

Library terms: G24 `Finset.range`; G26 `Finset.filter`; G33 `Fintype.piFinset`.
-/

/-!
### D028 — `boxB`

`Core.lean:638` · Used by: Theorem 5, Proposition 9, Proposition 10.

```lean
def boxB (k N : ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset fun s : Fin k => Finset.range (N / (k - s.val) + 1)
```

Library terms: G15 `x.val`; G24 `Finset.range`; G33 `Fintype.piFinset`.
-/

/-!
### D029 — `IsUNmap`

`Core.lean:644` · Used by: Theorem 5, Proposition 10.

```lean
def IsUNmap (k R N : ℕ) (U : (Fin k → ℕ) → Fin k → ℕ) : Prop :=
  Set.BijOn U (simplexS k N : Set (Fin k → ℕ)) (boxB k N : Set (Fin k → ℕ)) ∧
    ∃ (r : ℕ) (L : Fin r → Finset ((Fin k → ℤ) × ℤ))
      (A : Fin r → Matrix (Fin k) (Fin k) ℤ) (c : Fin r → Fin k → ℤ),
      r ≤ R ∧
      (∀ i, (L i).card ≤ R) ∧
      (∀ i, ∀ p ∈ L i, ∑ s, |p.1 s| ≤ (R : ℤ)) ∧
      (∀ i, (A i).det = 1 ∨ (A i).det = -1) ∧
      (∀ i s t, |A i s t| ≤ (R : ℤ)) ∧
      (∀ x : Fin k → ℕ, x ∈ simplexS k N ↔ ∃! i : Fin r, x ∈ polyP k (L i)) ∧
      ∀ i, ∀ x ∈ polyP k (L i), ∀ s,
        (U x s : ℤ) = Matrix.mulVec (A i) (fun t => (x t : ℤ)) s + c i s
```

Library terms: G28 `Finset.card`; G40 `Set.BijOn`; G41 `∃!`; G62 `Matrix.det`;
G63 `Matrix.mulVec`.
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{proposition}\label{prop:UNmap}
Let {$N\geq0$ with} $\lcmk \mid N$. Then the $\Z$-polytopes $\cS_N$ and $\B_N$ are $\aff_k(\Z)$-equidecomposable with complexity $\ll_k 1$. Specifically, for each $N$, there exists a decomposition, 
$$
\cS_N := \bigsqcup_{i=1}^r {\cP(L_i)}
$$
with $r \ll_k 1$, $\#L_i \ll_k 1$ for each $i$, and 
$$
\sup_{\substack{1 \leq i \leq r \\ (v,b) \in L_i}} |v|_1 \ll_k 1,
$$
and a bijection $U_N : \cS_N \to \B_N$ such that ${U_N}_{|\cP(L_i)} = A_i x + b_i$
with $|A_i|_{\infty} \ll_k 1$ for each $i$.
\end{proposition}
```

Coverage: `direct`.

Reading note: the paper's image partition of B_N (the Q-side of
Definition 3) follows, since the pieces partition S_N and U N is a bijection
S_N→B_N equal to x ↦ A i x + c i on piece i. Hence for lcm_k ∣ N the sets
S_N, B_N ⊆ ℤ^k of the `Set.BijOn` clause satisfy `Paper.definition3 k R`
(same r, L, A; b = c; bounds by inspection), with R depending only on k, as
the proposition's first sentence asserts.
-/

/-!
Library terms: G15 `x.val`; G25 `Finset.Icc`; G28 `Finset.card`; G31
`Finset.lcm`; G40 `Set.BijOn`; G62 `Matrix.det`; G63 `Matrix.mulVec`.
-/
theorem proposition4 :
  ∀ k : ℕ, 1 ≤ k →
      ∃ (R : ℕ) (U : ℕ → (Fin k → ℤ) → Fin k → ℤ),
        ∀ N : ℕ, (Finset.Icc 1 k).lcm id ∣ N →
          Set.BijOn (U N)
            {x : Fin k → ℤ | (∀ s, 0 ≤ x s) ∧ ∑ s, x s ≤ (N : ℤ)}
            {l : Fin k → ℤ | ∀ s : Fin k, 0 ≤ l s ∧ l s ≤ ((N / (k - s.val) : ℕ) : ℤ)} ∧
          ∃ (r : ℕ) (L : Fin r → Finset ((Fin k → ℤ) × ℤ))
            (A : Fin r → Matrix (Fin k) (Fin k) ℤ) (c : Fin r → Fin k → ℤ),
            r ≤ R ∧
            (∀ i, (L i).card ≤ R) ∧
            (∀ i, ∀ p ∈ L i, ∑ s, |p.1 s| ≤ (R : ℤ)) ∧
            (∀ i, (A i).det = 1 ∨ (A i).det = -1) ∧
            (∀ i s t, |A i s t| ≤ (R : ℤ)) ∧
            (∀ i, ∀ x : Fin k → ℤ,
              (∀ p ∈ L i, 0 ≤ (∑ s, p.1 s * x s) + p.2) →
                (∀ s, 0 ≤ x s) ∧ ∑ s, x s ≤ (N : ℤ)) ∧
            (∀ i j, i ≠ j → ∀ x : Fin k → ℤ,
              ¬ ((∀ p ∈ L i, 0 ≤ (∑ s, p.1 s * x s) + p.2) ∧
                 (∀ p ∈ L j, 0 ≤ (∑ s, p.1 s * x s) + p.2))) ∧
            (∀ x : Fin k → ℤ, (∀ s, 0 ≤ x s) → ∑ s, x s ≤ (N : ℤ) →
              ∃ i, ∀ p ∈ L i, 0 ≤ (∑ s, p.1 s * x s) + p.2) ∧
            ∀ i, ∀ x : Fin k → ℤ,
              (∀ p ∈ L i, 0 ≤ (∑ s, p.1 s * x s) + p.2) →
                U N x = Matrix.mulVec (A i) x + c i :=
  @_root_.prop_UNmap_explicit

/-!
## Theorem 5 (`thm:onbexplicit`)
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{theorem}\label{thm:onbexplicit}
Let $K\ge2${, and} put $k=K-1$. Let $a\ge1$, and let $\alpha = [a_0; a_1, a_2, \ldots]$ be an
irrational number with $a_i \leq a$ for all $i \geq 1$. 
For each $N\ge1$, with $\lcmk\mid N$, let $U_N$ be the map given by Proposition \ref{prop:UNmap}.
Then:
\begin{enumerate}
\item Let $D_N = {\rm diag}(\frac{1}{N/k+1}, \frac{1}{N/(k-1)+1},\ldots, \frac{1}{N+1})$ and define for each $l \in \B_N$
  \begin{equation}
  \p_{l}(z):=
  \sum_{\substack{j\in\mathbb Z_{\ge0}^K\\j_1+\cdots+j_K=N}}
  \binom Nj^{1/2}z^j
  e\left(\alpha\sum_{s=1}^Kj_s^2
  +U_N(j_1,\ldots,j_k)\cdot D_N l\right),
  \label{eq:originalBasis}
  \end{equation}
 where
  $\binom Nj=N!/(j_1!\cdots j_K!)$.
  Then $\{\p_{l}:l\in\B_N\}$ is an orthonormal basis
  of $\PolySpace_N${.}
\item Assuming the estimate in Theorem~\ref{thm:box},
  \[
  \sup_{\substack{N\ge1\\ \lcmk\mid N}}
  \ \sup_{l\in\B_N}
  \|\p_{l}\|_{L^\infty(\Sphere^{2K-1})}\ll_{K,a}1{.}
  \]
\item The divisibility condition can be
  removed: assuming Theorem~\ref{thm:box}, then, for every $N\ge0$, the space $\PolySpace_N$ admits an orthonormal basis
  $(\psi_\nu)_{1\leq \nu\le\dim\PolySpace_N}$ satisfying
  \[
    \sup_{1\leq \nu\le\dim\PolySpace_N}
    \|\psi_\nu\|_{L^\infty(\Sphere^{2K-1})}\ll_{K,a}1.
  \]
\end{enumerate}
\end{theorem}
```

Coverage: `all-degrees-conclusion`.

Cross-references: `prop:UNmap` is Proposition 4; `thm:box` is Theorem 2.
-/

/-!
Reading note: `theorem5OrthonormalBasis`, `theorem5UniformBound` and
`theorem5` are parts 1, 2 and 3. Parts 1 and 2 quantify over every family U
with `IsUNmap k R M (U M)` for all M ≥ 1 with lcm_k ∣ M (part 1 also over
every R): at least as strong as a statement for one fixed U_N. In part 2 the
R and A, in part 3 the C, depend only on (k, a). Part 3 indexes its basis by
`Fin ((N + k).choose k)`, of size dim H_N = binom(N+K−1,K−1) (K = k+1).
-/

/-!
### Paper context: Polynomial coefficients and theorem-valued hypotheses (`basis`)

In `basisPhi` (the coefficient of z^j in φ_l) the entries of D_N use the
ℕ-division `N / (k - s.val)` (s.val = s−1), exact when lcm_k ∣ N.

`ThmBox` and `PropUNmap` (root and `UniformBoundUnit` versions) are
propositions packaging Theorem 2 and Proposition 4, not extra assumptions
of the paper. Core proves `UniformBoundUnit.ThmBox` and
`UniformBoundUnit.PropUNmap k` (k ≥ 1) as the private lemmas
`agent4_onb_box_bridge` (Core.lean:17627) and `agent4_onb_UN_bridge`
(Core.lean:17652); `thm_onb` (Core.lean:17681) applies
`UniformBoundUnit.thm_onbexplicit_allDegrees` to them with a = 2, α = √2
(`bddPartQuot_two_sqrtTwo`, Core.lean:4379). So Theorem 1 depends on no
unproved hypothesis, while Theorem 5 (`UniformBoundUnit` versions) and
Proposition 10 (root versions) are stated conditionally on them
(`theorem5OrthonormalBasis` assumes an `IsUNmap` family `hU` instead). Core
also proves the root `ThmBox` (private `a4boxOct14_new_finished_v2`,
Core.lean:14761), whence `thm_box`; the root `PropUNmap` occurs in Core only
in its definition and as the hypothesis `hUN` of `prop_shiftedbound`
(Core.lean:3121), and no declaration proves it.

All four follow from displayed theorems, and the derivations are now
exported from `Compatibility.lean` as `Paper.theorem2_to_thmBox`,
`Paper.theorem2_to_unitThmBox`, `Paper.proposition4_to_propUNmap` and
`Paper.proposition4_to_unitPropUNmap`:
- root `ThmBox` unfolds to the type of `theorem2`;
- `UniformBoundUnit.ThmBox` repackages it (`BddPartQuot`, binder order,
  `*Z` box definitions) and omits `∀ s, lo s ≤ hi s`, harmlessly: for an
  empty box both bounds read 0 ≤ 0;
- `PropUNmap` and `UniformBoundUnit.PropUNmap k` (k ≥ 1): keep the R, L, A,
  c of `proposition4` and take U′ N x = (U N x).toNat componentwise. The
  pieces lie in S_N, which U N maps onto the nonnegative B_N, so `toNat` is
  exact there, and the bijection, the `∃!` clause (from cover and
  disjointness) and the affine clause on `polyP` carry over.
`Paper.proposition4_to_unitPropUNmap` is derived from
`Paper.proposition4_to_propUNmap`, not from Core's private
`agent4_onb_UN_bridge`: `private` is not visible across the module boundary,
and going through `Paper.proposition4` puts the content in the displayed
statement anyway.

So `hbox`, `hUN` and `hU` are satisfiable and the Theorem 5 and
Proposition 10 endpoints are not vacuous; likewise the first conjunct of
`theorem5UniformBound` and of `proposition10` shows that the U-classes they
bound are nonempty. Their second conjunct gives the bound for **every**
complexity R, with A depending on k, a and R, rather than for one R chosen
together with A; that is what lets them be applied to whatever map
`proposition4` produces. Each implies its former `∃ R, ∃ A` form, by taking
A at the R the first conjunct supplies.

Lean definitions for this comparison: `basisPhi`, `ThmBox`, `PropUNmap`, `UniformBoundUnit.ThmBox`, `UniformBoundUnit.PropUNmap`.
Statements depending on these definitions: Theorem 5, Proposition 10.
-/

/-!
### D030 — `basisPhi`

`Core.lean:657` · Used by: Theorem 5.

```lean
noncomputable def basisPhi (k N : ℕ) (α : ℝ) (U : (Fin k → ℕ) → Fin k → ℕ)
    (l : Fin k → ℕ) : PolySpaceH (k + 1) N :=
  fun n =>
    (Real.sqrt (Nat.multinomial Finset.univ (n : Fin (k + 1) → ℕ)) : ℂ) *
      expTwoPiI
        (α * ∑ s, ((n : Fin (k + 1) → ℕ) s : ℝ) ^ 2 +
          ∑ s : Fin k,
            (U (fun t => (n : Fin (k + 1) → ℕ) t.castSucc) s : ℝ) * (l s : ℝ)
              / ((N / (k - s.val) : ℕ) + 1))
```

Library terms: G15 `x.val`; G17 `Fin.castSucc`; G53 `Nat.multinomial`; G57
`Real.sqrt`.
-/

/-!
### D031 — `ThmBox`

`Core.lean:2001` · Used by: Proposition 10.

```lean
def ThmBox : Prop :=
  ∀ (k r V h : ℕ) (a : ℝ), 1 ≤ k → 1 ≤ V → 1 ≤ h → 1 ≤ a →
    ∃ C > 0, ∀ α : ℝ, Irrational α →
      (∀ (i : ℕ) (x : ℝ), (GenContFract.of α).partDens.get? i = some x → x ≤ a) →
      ∀ c : Fin k → ℕ, (∀ j, 1 ≤ c j) → (∀ j, c j ≤ h) →
      ∀ lo hi : Fin k → ℤ, (∀ s, lo s ≤ hi s) →
      ∀ L : Finset ((Fin k → ℤ) × ℤ), L.card ≤ r →
        (∀ p ∈ L, ∑ s, |p.1 s| ≤ (V : ℤ)) →
      ∀ θ : Fin k → ℝ,
        ‖quadExpSum k α c θ (polyBoxZ k L lo hi)‖ ≤
            C * Real.sqrt (boxVol k lo hi) ∧
          ∀ (w₀ : Fin k → ℤ) (b₀ : ℤ), w₀ ≠ 0 → (w₀, b₀) ∈ L → (-w₀, -b₀) ∈ L →
            ‖quadExpSum k α c θ (polyBoxZ k L lo hi)‖ ≤
              C * Real.sqrt (boxSect k w₀ lo hi)
```

Library terms: G28 `Finset.card`; G55 `Irrational`; G57 `Real.sqrt`; G76
`GenContFract.of`.
-/

/-!
### D032 — `PropUNmap`

`Core.lean:2016` · Used by: Proposition 10.

```lean
def PropUNmap : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ (R : ℕ) (U : ℕ → (Fin k → ℕ) → Fin k → ℕ),
    ∀ M : ℕ, 1 ≤ M → lcmUpTo k ∣ M → IsUNmap k R M (U M)
```
-/

/-!
### D033 — `UniformBoundUnit.ThmBox`

`Core.lean:3208` · Used by: Theorem 5.

```lean
def ThmBox : Prop :=
  ∀ (k r V h : ℕ), 1 ≤ k → 1 ≤ V → 1 ≤ h → ∀ a : ℝ, 1 ≤ a →
    ∃ C : ℝ, 0 < C ∧
      ∀ α : ℝ, BddPartQuot a α →
        ∀ c : Fin k → ℕ, (∀ j, 1 ≤ c j ∧ c j ≤ h) →
        ∀ lo hi : Fin k → ℤ, ∀ L : Finset ((Fin k → ℤ) × ℤ), L.card ≤ r →
          (∀ p ∈ L, ∑ s, |p.1 s| ≤ (V : ℤ)) →
          ∀ θ : Fin k → ℝ,
            ‖∑ n ∈ latticePtsZ k L lo hi,
                expTwoPiI (α * ∑ j, (c j : ℝ) * (n j : ℝ) ^ 2 +
                  ∑ j, θ j * (n j : ℝ))‖
              ≤ C * Real.sqrt (boxVolZ k lo hi) ∧
            ∀ (w₀ : Fin k → ℤ) (b₀ : ℤ), w₀ ≠ 0 →
              (w₀, b₀) ∈ L → (-w₀, -b₀) ∈ L →
              ‖∑ n ∈ latticePtsZ k L lo hi,
                  expTwoPiI (α * ∑ j, (c j : ℝ) * (n j : ℝ) ^ 2 +
                    ∑ j, θ j * (n j : ℝ))‖
                ≤ C * Real.sqrt (boxSectZ k w₀ lo hi)
```

Library terms: G28 `Finset.card`; G57 `Real.sqrt`.
-/

/-!
### D034 — `UniformBoundUnit.PropUNmap`

`Core.lean:3227` · Used by: Theorem 5.

```lean
def PropUNmap (k : ℕ) : Prop :=
  ∃ R : ℕ, ∀ N : ℕ, 1 ≤ N → lcmUpTo k ∣ N →
    ∃ U : (Fin k → ℕ) → Fin k → ℕ, IsUNmap k R N U
```
-/

/-!
Definitions used: `degIdx` (D002), `PolySpaceH` (D003), `polyEval` (D004),
`polyInner` (D006), `UniformBoundUnit.cSphere` (D005),
`UniformBoundUnit.BddPartQuot` (D021), `expTwoPiI` (D001),
`UniformBoundUnit.latticePtsZ` (D017), `UniformBoundUnit.boxVolZ` (D018),
`UniformBoundUnit.boxLenZ` (D019), `UniformBoundUnit.boxSectZ` (D020),
`UniformBoundUnit.ThmBox` (D033), `lcmUpTo` (D026), `simplexS` (D027), `boxB`
(D028), `polyP` (D008), `IsUNmap` (D029), `UniformBoundUnit.PropUNmap` (D034).
Library terms: G52 `Nat.choose`; G67 `Module.Basis ι R M`.
-/
theorem theorem5 :
  ∀ (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : 1 ≤ a)
    (hbox : _root_.UniformBoundUnit.ThmBox) (hUN : ∀ j : ℕ, 1 ≤ j → j ≤ k → _root_.UniformBoundUnit.PropUNmap j),
∃ C : ℝ, 0 < C ∧
      ∀ α : ℝ, _root_.UniformBoundUnit.BddPartQuot a α →
        ∀ N : ℕ,
          ∃ ψ : Module.Basis (Fin ((N + k).choose k)) ℂ (PolySpaceH (k + 1) N),
            (∀ i j, polyInner (k + 1) N (ψ i) (ψ j) = if i = j then 1 else 0) ∧
            ∀ ν, ∀ z ∈ _root_.UniformBoundUnit.cSphere (k + 1), ‖polyEval (k + 1) N (ψ ν) z‖ ≤ C :=
  @_root_.UniformBoundUnit.thm_onbexplicit_allDegrees

/-!
Definitions used: `lcmUpTo` (D026), `degIdx` (D002), `PolySpaceH` (D003),
`polyInner` (D006), `boxB` (D028), `simplexS` (D027), `polyP` (D008), `IsUNmap`
(D029), `expTwoPiI` (D001), `basisPhi` (D030). Library terms: G37 `f '' S`; G55
`Irrational`; G69 `Submodule.span`; G76 `GenContFract.of`.
-/
theorem theorem5OrthonormalBasis :
  ∀ (k : ℕ) (hk : 1 ≤ k)
    (a α : ℝ) (ha : 1 ≤ a) (hα : Irrational α)
    (hbpq : ∀ (i : ℕ) (x : ℝ), (GenContFract.of α).partDens.get? i = some x → x ≤ a)
    (R : ℕ) (U : ℕ → (Fin k → ℕ) → Fin k → ℕ)
    (hU : ∀ M : ℕ, 1 ≤ M → lcmUpTo k ∣ M → IsUNmap k R M (U M))
    (N : ℕ) (hN : 1 ≤ N) (hlcm : lcmUpTo k ∣ N),
(∀ l ∈ boxB k N, ∀ l' ∈ boxB k N,
        polyInner (k + 1) N (basisPhi k N α (U N) l) (basisPhi k N α (U N) l') =
          if l = l' then 1 else 0) ∧
      Submodule.span ℂ (basisPhi k N α (U N) '' (boxB k N : Set (Fin k → ℕ))) = ⊤ :=
  @_root_.thm_onbexplicit_orthonormalBasis

/-!
Definitions used: `lcmUpTo` (D026), `degIdx` (D002), `PolySpaceH` (D003),
`polyEval` (D004), `boxB` (D028), `simplexS` (D027), `polyP` (D008), `IsUNmap`
(D029), `expTwoPiI` (D001), `basisPhi` (D030), `UniformBoundUnit.cSphere`
(D005), `UniformBoundUnit.BddPartQuot` (D021), `UniformBoundUnit.latticePtsZ`
(D017), `UniformBoundUnit.boxVolZ` (D018), `UniformBoundUnit.boxLenZ` (D019),
`UniformBoundUnit.boxSectZ` (D020), `UniformBoundUnit.ThmBox` (D033),
`UniformBoundUnit.PropUNmap` (D034).
-/
theorem theorem5UniformBound :
  ∀ (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : 1 ≤ a)
    (hbox : _root_.UniformBoundUnit.ThmBox) (hUN : _root_.UniformBoundUnit.PropUNmap k),
(∃ R : ℕ, ∀ N : ℕ, 1 ≤ N → lcmUpTo k ∣ N →
        ∃ U₀ : (Fin k → ℕ) → Fin k → ℕ, IsUNmap k R N U₀) ∧
      ∀ R : ℕ, ∃ A : ℝ, 0 < A ∧
        ∀ α : ℝ, _root_.UniformBoundUnit.BddPartQuot a α →
          ∀ U : ℕ → (Fin k → ℕ) → Fin k → ℕ,
            (∀ M : ℕ, 1 ≤ M → lcmUpTo k ∣ M → IsUNmap k R M (U M)) →
            ∀ N : ℕ, 1 ≤ N → lcmUpTo k ∣ N →
              ∀ l ∈ boxB k N, ∀ z ∈ _root_.UniformBoundUnit.cSphere (k + 1),
                ‖polyEval (k + 1) N (basisPhi k N α (U N) l) z‖ ≤ A :=
  @_root_.Paper.Theorem5.uniformBound

/-!
## Lemma 6 (`lem:poisson1d`)
-/

/-!
### Paper context: Poisson weights, scales, and forward differences (`poisson`)

`fwdDiff (1 : ℤ) (poissonQ lam) n` is Δq_λ(n) = q_λ(n+1)−q_λ(n). The
definitions are total; λ > 0 is a hypothesis of Lemmas 6 and 7. The
excerpt's a_{N,r}, c_N and c(n) do not occur in the Lemma 6 type.

Original paper definition/context (`article.txt:530-563`, verbatim TeX):
```tex
for $\p \in {\PolySpace_N}$, it will be useful to define the following auxiliary function.  For $\lambda>0$, define the square root of the Poisson
weight, extended by zero to the negative integers, by
\[
q_\lambda(n)=
\begin{cases}
\displaystyle e^{-\lambda/2}\frac{\lambda^{n/2}}{\sqrt{n!}},&n\geq0,\\[5pt]
0,&n<0.
\end{cases}
\]
Writing $r=(r_1,{\ldots},r_K)$, {for $N\ge1$} define for every $n\in\z^K$ the normalized multinomial weights
\[
a_{N,r}(n):=
\begin{cases}
\binom Nn^{1/2}\prod_{s=1}^Kr_s^{n_s/2},&n_1,{\ldots},n_K\ge0 \text{ and  } n_1+\cdots+n_K=N,\\[4pt]
0,&\text{otherwise}.
\end{cases}
\]
It is straightforward to see that when $a_{N,r}(n) \neq 0$ we have
\begin{align}
a_{N,r}(n)=c_N\prod_{s=1}^Kq_{Nr_s}(n_s)
\quad \text{with} \quad
c_N:=e^{N/2}\frac{\sqrt{N!}}{N^{N/2}}\asymp N^{1/4},
\label{eq:poissonFactorizationMultinomial}
\end{align}
where the estimate for $c_N$ follows from Stirling's \cite[Section~5.11]{DLMF}. Note that any $\p \in {\PolySpace_N}$, in the new coordinates $z_s = \sqrt{r_s} e(\theta_s)$, can be {expressed} as
\[
\p(z_1,\ldots,z_K) = \sum_{\substack{n \in \Z_{\geq 0}^K  \\  n_1+\cdots+n_K=N}} c(n) a_{N,r}(n) e(\theta \cdot n),
\]
for some coefficients $c(n)$, where $\theta = (\theta_1,\ldots,\theta_K)$. In particular, $\|\p\|^2 = \binom{N+K-1}{K-1}^{-1} \sum  |c(n)|^2$.  Put
\[
H_\lambda:=(1+\lambda)^{1/2}  \quad \text{and} \quad
\qquad \rho_\lambda(n):=\frac{|n-\lambda|}{H_\lambda}.
\]
{Also set} $\Delta b(j)=b(j+1)-b(j)$, for a sequence $b:\Z\to \cp$.  The next lemma produces the necessary bounds for the components of $a_{N,r}(n)$.
```

Lean definitions for this comparison: `poissonQ`, `poissonH`, `poissonRho`.
Statements depending on these definitions: Lemma 6, Lemma 7.
-/

/-!
### D035 — `poissonQ`

`Core.lean:932` · Used by: Lemma 6, Lemma 7.

```lean
noncomputable def poissonQ (lam : ℝ) (n : ℤ) : ℝ :=
  if 0 ≤ n then
    Real.exp (-lam / 2) * lam ^ ((n : ℝ) / 2) / Real.sqrt (Nat.factorial n.toNat)
  else 0
```

Library terms: G45 `Int.toNat`; G54 `Nat.factorial`; G56 `x ^ y`; G57
`Real.sqrt`; G58 `Real.exp`.
-/

/-!
### D036 — `poissonH`

`Core.lean:937` · Used by: Lemma 6, Lemma 7.

```lean
noncomputable def poissonH (lam : ℝ) : ℝ := Real.sqrt (1 + lam)
```

Library terms: G57 `Real.sqrt`.
-/

/-!
### D037 — `poissonRho`

`Core.lean:939` · Used by: Lemma 6.

```lean
noncomputable def poissonRho (lam : ℝ) (n : ℤ) : ℝ :=
  |(n : ℝ) - lam| / poissonH lam
```
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{lemma}\label{lem:poisson1d}
We have, for all $n \in \mathbb{Z}$,
\begin{align}
q_\lambda(n)\ll H_\lambda^{-1/2}e^{-\rho_\lambda(n)/4} \quad \text{and} \quad
|\Delta q_\lambda(n)|\ll H_\lambda^{-3/2}e^{-\rho_\lambda(n)/4}.
\label{eq:poissonPointwiseBound}
\end{align}
\end{lemma}
```

Coverage: `direct`.
-/

/-!
Definitions used: `poissonQ` (D035), `poissonH` (D036), `poissonRho` (D037).
Library terms: G56 `x ^ y`; G58 `Real.exp`; G75 `fwdDiff`.
-/
theorem lemma6 :
  ∃ C > 0, ∀ lam : ℝ, 0 < lam → ∀ n : ℤ,
      |poissonQ lam n| ≤
          C * poissonH lam ^ (-(1 : ℝ) / 2) * Real.exp (-poissonRho lam n / 4) ∧
        |fwdDiff (1 : ℤ) (poissonQ lam) n| ≤
          C * poissonH lam ^ (-(3 : ℝ) / 2) * Real.exp (-poissonRho lam n / 4) :=
  @_root_.lem_poisson1d

/-!
## Lemma 7 (`lem:fouriermass`)
-/

/-!
### Paper context: The hat function and Fourier transform convention (`fourier`)

`seqFourier` takes real-valued sequences (the paper allows complex ones;
real suffices here). Its `∑'` (0 for a non-summable family) cannot make
Lemma 7 trivial: by the support conjunct each `poissonQLoc lam m` is
finitely supported, so the `∑'` is the paper's finite sum (a continuous
trigonometric polynomial in u), and the m-series is asserted `Summable`
before its `∑'` is bounded.

Original paper definition/context (`article.txt:609-618`, verbatim TeX):
```tex
Fix the hat function $\eta(x)=(1-|x|)_+$.
It is supported in $[-1,1]$, bounded by one, $1$-Lipschitz and {satisfies}
\begin{align}
\sum_{n\in\z}\eta(x-n)=1,
\label{eq:shiftFreePartitionUnity}
\end{align}
for every $x\in\RR$. For a finitely supported $b:\z\to\cp$, write
\[
\ft b(u)=\sum_{j\in\z}b(j)e(-uj) \quad \text{for} \quad u\in \RR.
\]
```

Lean definitions for this comparison: `hatEta`, `poissonQLoc`, `seqFourier`.
Statements depending on these definitions: Lemma 7.
-/

/-!
### D038 — `hatEta`

`Core.lean:1221` · Used by: Lemma 7 (indirectly).

```lean
noncomputable def hatEta (x : ℝ) : ℝ := max (1 - |x|) 0
```
-/

/-!
### D039 — `poissonQLoc`

`Core.lean:1223` · Used by: Lemma 7.

```lean
noncomputable def poissonQLoc (lam : ℝ) (m : ℤ) (n : ℤ) : ℝ :=
  poissonQ lam n * hatEta ((n : ℝ) / poissonH lam - (m : ℝ))
```
-/

/-!
### D040 — `seqFourier`

`Core.lean:1226` · Used by: Lemma 7.

```lean
noncomputable def seqFourier (b : ℤ → ℝ) (u : ℝ) : ℂ :=
  ∑' j : ℤ, (b j : ℂ) * expTwoPiI (-(u * (j : ℝ)))
```

Library terms: G71 `Summable`.
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{lemma}\label{lem:fouriermass}
For $m\in\z$ put
\begin{align}
q_{\lambda,m}(n):=q_\lambda(n)\eta(n/H_{\la}-m).
\label{eq:localizedMultinomialSequence}
\end{align}
Then $q_\lambda=\sum_mq_{\lambda,m}$, each $q_{\lambda,m}$ is
supported on $\{n:\ |n/H_\lambda-m|<1\}$ and
\begin{align}
\sum_{m\in\z}\int_0^1|\ft{q_{\lambda,m}}(u)|\,\dd u\ \ll\ H_\lambda^{-1/2},
\label{eq:multinomialTotalFourierMass}
\end{align}
where the implied constant {is} independent of $\la >0$.
\end{lemma}
```

Coverage: `direct`.
-/

/-!
Definitions used: `poissonQ` (D035), `poissonH` (D036), `hatEta` (D038),
`poissonQLoc` (D039), `expTwoPiI` (D001), `seqFourier` (D040). Library terms:
G56 `x ^ y`; G71 `Summable`; G72 `∫ x, f x`.
-/
theorem lemma7 :
  ∃ C > 0, ∀ lam : ℝ, 0 < lam →
      (∀ n : ℤ, HasSum (fun m : ℤ => poissonQLoc lam m n) (poissonQ lam n)) ∧
      (∀ m n : ℤ, 1 ≤ |(n : ℝ) / poissonH lam - (m : ℝ)| → poissonQLoc lam m n = 0) ∧
      (Summable fun m : ℤ => ∫ u in (0:ℝ)..1, ‖seqFourier (poissonQLoc lam m) u‖) ∧
      (∑' m : ℤ, ∫ u in (0:ℝ)..1, ‖seqFourier (poissonQLoc lam m) u‖) ≤
        C * poissonH lam ^ (-(1 : ℝ) / 2) :=
  @_root_.lem_fouriermass

/-!
## Definition 8 (`def:shiftedbasis`)
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{definition}[Shifted basis]\label{def:shiftedbasis}
Let $N\geq 0$ and set
\begin{align}
b:=N-\lcmk\Bigl\lfloor\frac N{\lcmk}\Bigr\rfloor \quad \text{and} \quad N'=N-b.
\end{align}
Also write
\begin{align}
D:=\binom{N+k}{k}=\dim\PolySpace_N\quad \text{and}\quad
D':=\binom{N'+k}{k}=\dim\PolySpace_{N'}.
\label{eq:dimensions}
\end{align}
For $l\in\B_{N'}$ put
\begin{align}
\p^b_{l}(z)
=\Bigl(\frac{D}{D'}\Bigr)^{1/2}
\sum_{\substack{n\in\z_{\ge0}^K,\\ n_1+\cdots+n_K=N\\ n_K\ge b}}
\binom Nn^{1/2}z^n\,
e\Bigl(\al\sum_{s=1}^Kn_s^2
+U_{N'}(n_1,\ldots,n_k)\cdot D_{N'}l\Bigr).
\label{eq:shiftedBasis}
\end{align}
\end{definition}
```

Coverage: `direct-definition`.
-/

/-!
Conformance with the statements: Definition 8 is encoded by
`shiftedBasisPhi` (D041), the coefficients of φ^b_l in `PolySpaceH (k+1) N`
(K = k+1), 0 when n_K < b. b, α, U, l are free arguments:
`proposition9Orthogonality` allows any b ≤ N, real α and bijection U (which
forces b ≡ N mod lcm_k, see Proposition 9); `proposition10` takes
b = `N % lcmUpTo k`, the paper's residue, U_{N′} = `U N′` for any `IsUNmap`
family U, l ∈ B_{N′} and α as in the paper. There the body is
`eq:shiftedBasis`; the ℕ-division `(N - b) / (k - s.val)` (s.val = s−1) in
D_{N′} is exact as lcm_k ∣ N′. For b = 0 the values are those of `basisPhi`
(D030), as the paper remarks.
-/

/-!
### Paper context: Shifted coefficients, residue, and dimensions (`shifted`)

Encoding and the hypotheses on b: see the Definition 8 conformance note.

Lean definitions for this comparison: `shiftedBasisPhi`.
Statements depending on these definitions: Proposition 9, Proposition 10.
-/

/-!
### D041 — `shiftedBasisPhi`

`Core.lean:2020` · Used by: Proposition 9, Proposition 10.

```lean
noncomputable def shiftedBasisPhi (k N b : ℕ) (α : ℝ)
    (U : (Fin k → ℕ) → Fin k → ℕ) (l : Fin k → ℕ) : PolySpaceH (k + 1) N :=
  fun n =>
    if b ≤ (n : Fin (k + 1) → ℕ) (Fin.last k) then
      (Real.sqrt (((N + k).choose k : ℝ) / ((N - b + k).choose k : ℝ)) : ℂ) *
        (Real.sqrt (Nat.multinomial Finset.univ (n : Fin (k + 1) → ℕ)) : ℂ) *
        expTwoPiI
          (α * ∑ s, ((n : Fin (k + 1) → ℕ) s : ℝ) ^ 2 +
            ∑ s : Fin k,
              (U (fun t => (n : Fin (k + 1) → ℕ) t.castSucc) s : ℝ) * (l s : ℝ)
                / (((N - b) / (k - s.val) : ℕ) + 1))
    else 0
```

Library terms: G15 `x.val`; G16 `Fin.last`; G17 `Fin.castSucc`; G52
`Nat.choose`; G53 `Nat.multinomial`; G57 `Real.sqrt`.
-/

#check @_root_.shiftedBasisPhi

/-!
## Proposition 9 (`prop:shiftedONS`)
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{proposition}\label{prop:shiftedONS}
The functions $\{\p^b_{l}:l\in\B_{N'}\}$ form an orthonormal basis of the 
subspace spanned by the monomials $z^n \in {\PolySpace_N}$ with
$n_K\ge b$.
\end{proposition}
```

Coverage: `component-only`.

Reading note: there is no divisibility hypothesis, but `hU` forces lcm_k ∣ N−b
(cardinality count in the `simplex` context), i.e. b ≡ N (mod lcm_k); the
paper's residue is the case b < lcm_k. Not displayed, hence `component-only`:
that the φ^b_l, l ∈ B_{N−b} (which lie in the span of the z^n with n_K ≥ b),
span it; the paper gets this by counting dimensions (`Compatibility.lean`
exports only the index bijection for that count,
`Paper.Proposition9.indexEquiv`). `Compatibility.lean` deliberately exports no
`Paper.proposition9`. `assemble_faces_clean` (Core.lean:4078) combines
`shifted_orth` with the face lifts of Lemma 11 into binom(N+k,k) = dim H_{K,N}
orthonormal polynomials of degree N.
-/

/-!
Definitions used: `degIdx` (D002), `PolySpaceH` (D003), `polyInner` (D006),
`simplexS` (D027), `boxB` (D028), `expTwoPiI` (D001), `shiftedBasisPhi` (D041).
Library terms: G40 `Set.BijOn`.
-/
theorem proposition9Orthogonality :
  ∀ (k N b : ℕ) (hb : b ≤ N) (α : ℝ)
    (U : (Fin k → ℕ) → Fin k → ℕ)
    (hU : Set.BijOn U (simplexS k (N-b) : Set _) (boxB k (N-b) : Set _))
    (l l' : Fin k → ℕ) (hl : l ∈ boxB k (N-b)) (hl' : l' ∈ boxB k (N-b)),
polyInner (k+1) N (shiftedBasisPhi k N b α U l)
      (shiftedBasisPhi k N b α U l') = if l=l' then 1 else 0 :=
  @_root_.AllDegreesProof.shifted_orth

/-!
## Proposition 10 (`prop:shiftedbound`)
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{proposition}\label{prop:shiftedbound}
Let $a\ge1$ and let $\alpha=[a_0;a_1,a_2,\ldots]$ be an irrational number
with $a_i\le a$ for all $i\ge1$.  Let $N\ge0$, with $b \in [0, \lcmk)$ the residue of $N$ modulo $\lcmk$ and $N'=N-b$, and let $\p^b_{l}(z)$ be defined as in \eqref{eq:shiftedBasis}. Then there is a constant $A=A(K,a)$ such that
\[
  \sup_{l\in\B_{N'}}\ \sup_{z\in\Sphere^{2K-1}}
  \bigl|\p^b_{l}(z)\bigr|\ \le\ A.
\]
\end{proposition}
```

Coverage: `direct`.

Cross-references: `eq:shiftedBasis` is the display in Definition 8.

Reading note: A and R depend only on k and a, so A = A(K,a). The bound holds
for every family U with `IsUNmap k R M (U M)` for all M ≥ 1 with lcm_k ∣ M
(the paper uses one U_{N′}). If N < lcm_k, then N′ = 0 and `U 0` is
unconstrained, but `boxB k 0` = {0} forces l = 0, and the polynomial is
√binom(N+k,k)·e(αN²)·z_K^N, bounded on the sphere in terms of k. `hbox`,
`hUN` stand for the paper's standing assumption here (“Throughout this
section we will assume Theorem 2 and Proposition 4”, `article.txt:678`).
-/

/-!
Definitions used: `lcmUpTo` (D026), `degIdx` (D002), `PolySpaceH` (D003),
`polyEval` (D004), `boxB` (D028), `simplexS` (D027), `polyP` (D008), `IsUNmap`
(D029), `boxSide` (D011), `boxVol` (D012), `boxLen` (D013), `boxSect` (D014),
`boxZ` (D010), `polyBoxZ` (D015), `expTwoPiI` (D001), `quadExpSum` (D016),
`ThmBox` (D031), `PropUNmap` (D032), `shiftedBasisPhi` (D041). Library terms:
G55 `Irrational`; G76 `GenContFract.of`.
-/
theorem proposition10 :
  ∀ (hbox : _root_.ThmBox) (hUN : _root_.PropUNmap) (k : ℕ) (hk : 1 ≤ k)
    (a : ℝ) (ha : 1 ≤ a),
(∃ (R : ℕ) (U : ℕ → (Fin k → ℕ) → Fin k → ℕ),
        ∀ M : ℕ, 1 ≤ M → lcmUpTo k ∣ M → IsUNmap k R M (U M)) ∧
      ∀ R : ℕ, ∃ A > 0,
        ∀ U : ℕ → (Fin k → ℕ) → Fin k → ℕ,
          (∀ M : ℕ, 1 ≤ M → lcmUpTo k ∣ M → IsUNmap k R M (U M)) →
          ∀ α : ℝ, Irrational α →
            (∀ (i : ℕ) (x : ℝ), (GenContFract.of α).partDens.get? i = some x → x ≤ a) →
          ∀ N : ℕ, ∀ l ∈ boxB k (N - N % lcmUpTo k),
          ∀ z : Fin (k + 1) → ℂ, ∑ s, ‖z s‖ ^ 2 = 1 →
            ‖polyEval (k + 1) N
                (shiftedBasisPhi k N (N % lcmUpTo k) α
                  (U (N - N % lcmUpTo k)) l) z‖ ≤ A :=
  @_root_.Paper.proposition10

/-!
## Lemma 11 (`lem:facenorm`)
-/

/-!
### Paper context: The face subspaces and multiplication by the last coordinate (`faces`)

`faceLift k N i c` maps into z_K^i H_{K−1,N−i} (last exponent exactly i),
which for i < N is smaller than the “at least i” space H_{K,N}^{(i)};
`faceScale`: see Lemma 11.

Original paper definition/context (`article.txt:836-843`, verbatim TeX):
```tex
Let $N\geq 0$ and put
$$
\H_{K,N}^{(i)} = \text{span}\{z^n : n\in \Z_{\geq 0}^K, \, n_1+\cdots+n_K=N, \,  n_K\geq i\}
$$
and set $\H_{K,N}:=\H_{K,N}^{(0)}{=\PolySpace_N}$. Let $b \in [0, \lcmk)$ {be} the residue of $N$ modulo $\lcmk$ and $N'=N-b$. We start by noticing that
\begin{align}\label{eq:Hfacesdecomp}
\H_{K,N} =  \H_{K,N}^{(b)} \bigoplus \bigg(\bigoplus_{0\leq i<b} z_K^i \H_{K-1,N-i} \bigg),
\end{align}
```

Lean definitions for this comparison: `AllDegreesProof.faceLift`, `AllDegreesProof.faceScale`.
Statements depending on these definitions: Lemma 11.
-/

/-!
### D042 — `AllDegreesProof.faceLift`

`Core.lean:3646` · Used by: Lemma 11.

```lean
noncomputable def faceLift (k N i : ℕ) (c : ℂ) (v : PolySpaceH k (N-i)) :
    PolySpaceH (k+1) N := fun n =>
  if h : n.val (Fin.last k) = i then
    c * v ⟨Fin.init n.val, by
      apply (onb_mem_deg _ _ _).2
      have hn := (onb_mem_deg _ _ _).1 n.property
      rw [Fin.sum_univ_castSucc, h] at hn
      change (∑ j : Fin k, n.val j.castSucc) = N-i
      omega⟩
  else 0
```

Library terms: G15 `x.val`; G16 `Fin.last`; G17 `Fin.castSucc`; G18 `Fin.init`.
-/

/-!
### D043 — `AllDegreesProof.faceScale`

`Core.lean:3719` · Used by: Lemma 11.

```lean
noncomputable def faceScale (k N i : ℕ) : ℝ :=
  Real.sqrt (((N+k).choose k : ℝ) * (N.choose i : ℝ) /
    ((N-i+k-1).choose (k-1) : ℝ))
```

Library terms: G52 `Nat.choose`; G57 `Real.sqrt`.
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{lemma}[The faces]\label{lem:facenorm}
{Let $K\ge2$, $N\ge1$ and $0\le i\le N$ be integers.} Put 
\begin{align}
c_{N,i}^2
:=\frac{\binom{N+K-1}{K-1}\binom Ni}
{\binom{N-i+K-2}{K-2}}.
\label{eq:facenorm}
\end{align}
Then  $c_{N,i}\asymp_{K,i} N^{(i+1)/2}$.
Moreover:
\begin{enumerate}
\item The map $\psi\mapsto c_{N,i}\,z_K^{\,i}\psi$ is a linear isometry
from ${\H_{K-1,N-i}} \subset  L^2(\Sphere^{2K-3})$ onto
$z_K^i \H_{K-1,N-i} \subset L^2(\Sphere^{2K-1})${.}
\item If ${\H_{K-1,N-i}}$ has an orthonormal basis
$\{\psi_1,{\ldots},\psi_{{\dim\H_{K-1,N-i}}}\}$ with
$\|\psi_\nu\|_{L^\infty(\Sphere^{2K-3})}\le C$, then the functions
$c_{N,i}z_K^{\,i}\psi_\nu$ form an orthonormal basis of $z_K^i \H_{K-1,N-i}$ satisfying
\begin{align}
\bigl\|c_{N,i}z_K^{\,i}\psi_\nu\bigr\|_{L^\infty(\Sphere^{2K-1})}
 \ll_{K,i}\ C\,N^{1/2}.
\label{eq:facesup}
\end{align}
\end{enumerate}
\end{lemma}
```

Coverage: `component-only`.

Reading note: for k ≥ 1 and i ≤ N the ℕ-subtractions in `faceScale` are
exact and `faceScale k N i`² is the paper's c_{N,i}² (K = k+1).
`lemma11Isometry` assumes only i ≤ N (no k ≥ 1, N ≥ 1): at k = 0 the `k-1`
of `faceScale` and the `K - 1` of `polyInner k (N-i)` truncate to 0.
`lemma11SphereBound` needs no basis: it bounds the lift of any v with
|v| ≤ C on the smaller sphere by C·√(binom(N+k,k)/binom(N−i+k−1,k−1)), a
ratio asymptotic to N/k for fixed k, i; for N ≥ 1 this is `eq:facesup`.
`lemma11Evaluation` identifies `faceLift k N i c` (i ≤ N) with the paper's
map ψ ↦ c·z_K^i·ψ. Not displayed: c_{N,i} ≍_{K,i} N^{(i+1)/2}; that the map
is onto z_K^i H_{K−1,N−i} (part 1); that the c_{N,i}·z_K^i·ψ_ν form an
orthonormal basis of it (part 2). The last two follow from the isometry by
linear algebra, given the evaluation formula and the `pairing` context.
`Compatibility.lean` deliberately exports no `Paper.lemma11` (the
asymptotics of the normalizing factor are not bundled as a theorem).
-/

/-!
Definitions used: `degIdx` (D002), `PolySpaceH` (D003), `polyInner` (D006),
`AllDegreesProof.faceLift` (D042), `AllDegreesProof.faceScale` (D043).
-/
theorem lemma11Isometry :
  ∀ (k N i : ℕ) (hi : i ≤ N)
    (v w : PolySpaceH k (N-i)),
polyInner (k+1) N (_root_.AllDegreesProof.faceLift k N i (_root_.AllDegreesProof.faceScale k N i) v)
      (_root_.AllDegreesProof.faceLift k N i (_root_.AllDegreesProof.faceScale k N i) w) = polyInner k (N-i) v w :=
  @_root_.AllDegreesProof.face_norm_inner

/-!
Definitions used: `degIdx` (D002), `PolySpaceH` (D003), `polyEval` (D004),
`UniformBoundUnit.cSphere` (D005), `AllDegreesProof.faceLift` (D042),
`AllDegreesProof.faceScale` (D043). Library terms: G52 `Nat.choose`; G57
`Real.sqrt`.
-/
theorem lemma11SphereBound :
  ∀ (k N i : ℕ) (hk : 1 ≤ k) (hi : i ≤ N)
    (v : PolySpaceH k (N-i)) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ z ∈ UniformBoundUnit.cSphere k, ‖polyEval k (N-i) v z‖ ≤ C)
    (z : Fin (k+1) → ℂ) (hz : z ∈ UniformBoundUnit.cSphere (k+1)),
‖polyEval (k+1) N (_root_.AllDegreesProof.faceLift k N i (_root_.AllDegreesProof.faceScale k N i) v) z‖ ≤
      C * Real.sqrt (((N+k).choose k : ℝ) / ((N-i+k-1).choose (k-1) : ℝ)) :=
  @_root_.AllDegreesProof.face_eval_bound

/-!
Definitions used: `degIdx` (D002), `PolySpaceH` (D003), `polyEval` (D004),
`AllDegreesProof.faceLift` (D042). Library terms: G16 `Fin.last`; G18
`Fin.init`.
-/
theorem lemma11Evaluation :
  ∀ (k N i : ℕ) (hi : i ≤ N) (c : ℂ)
    (v : PolySpaceH k (N-i)) (z : Fin (k+1) → ℂ),
polyEval (k+1) N (_root_.AllDegreesProof.faceLift k N i c v) z =
      c * z (Fin.last k)^i * polyEval k (N-i) v (Fin.init z) :=
  @_root_.AllDegreesProof.faceLift_eval

/-!
## Lemma 12 (`lem:absorption`)
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{lemma}[Absorption Lemma]\label{lem:absorption}
Let $D \geq 2$. Let $X$ be a set. Let $V$ be a $D$-dimensional complex vector space
of functions $f: X\to\mathbb C$.
Let $\p_1,{\ldots},\p_D$ be an orthonormal
basis of $V$ with respect to an inner product $\langle \cdot, \cdot \rangle : V \times V \rightarrow \mathbb{C}$. Let $A,B\ge0$ and let $D_2$ be an integer with
$1\le D_2\le D/2$. Suppose
\[
\sup_{x \in X} |\p_j(x)| \leq B \quad(1\le j\le D_2)
{\quad \text{and} \quad}
\sup_{x \in X} |\p_j(x)| \le A \quad(D_2<j\le D).
\]
Then $V$ has an orthonormal basis $\psi_1,{\ldots},\psi_D$ with respect to 
the inner product $\langle \cdot, \cdot \rangle$ such that
\[
\max_{1\le s\le D} \sup_{x \in X} |\psi_s(x)|
\le 10A+10B\sqrt{D_2/D}.
\]
\end{lemma}
```

Coverage: `direct`.

Reading note: `ip` is only sesquilinear (no positivity or conjugate
symmetry); the paper's construction (ψ = Qφ, Q real orthogonal, QQᵀ = I)
needs no more. Indices are 0-based: `(j : ℕ) < D₂` is 1 ≤ j ≤ D₂,
`D₂ ≤ (j : ℕ)` is D₂ < j ≤ D, and `2 * D₂ ≤ D` is D₂ ≤ D/2. So the Lean
hypotheses follow from the paper's; the conclusion is the same.
-/

/-!
Library terms: G15 `x.val`; G57 `Real.sqrt`; G67 `Module.Basis ι R M`; G69
`Submodule.span`; G70 `V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ`.
-/
theorem lemma12 :
  ∀ {X : Type*} {D : ℕ} (hD : 2 ≤ D)
    (V : Submodule ℂ (X → ℂ))
    (ip : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (φ : Module.Basis (Fin D) ℂ V)
    (hφ : ∀ i j, ip (φ i) (φ j) = if i = j then 1 else 0)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (D₂ : ℕ) (hD₂ : 1 ≤ D₂) (hD₂' : 2 * D₂ ≤ D)
    (hbigB : ∀ j : Fin D, (j : ℕ) < D₂ → ∀ x : X, ‖(φ j : X → ℂ) x‖ ≤ B)
    (hbigA : ∀ j : Fin D, D₂ ≤ (j : ℕ) → ∀ x : X, ‖(φ j : X → ℂ) x‖ ≤ A),
∃ ψ : Module.Basis (Fin D) ℂ V,
      (∀ i j, ip (ψ i) (ψ j) = if i = j then 1 else 0) ∧
      ∀ s : Fin D, ∀ x : X,
        ‖(ψ s : X → ℂ) x‖ ≤ 10 * A + 10 * B * Real.sqrt ((D₂ : ℝ) / (D : ℝ)) :=
  @_root_.absorption_lemma

/-!
## Definition 13 (`def:balanced`)
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{definition}\label{def:balanced}
Let $k\geq1$ and $R\ge1$. Let $I=\prod_{j=1}^kI_j$ be a box and
$L\subset\Z^k\times\Z$ a finite set of constraints. We say that the pair
$(L,I)$ is \emph{$R$-balanced} if
\[
 {\#L\le R \quad \text{and} \quad 0<|v|_1\le R \quad \text{for all }(v,b)\in L},
\]
and
\[
 \#I_i\le R\,\#I_j\ \ \text{ for all } i,j{.}
\]
The locations of the intervals and the constants $b$ are unrestricted. 
\end{definition}
```

Coverage: `direct-definition`.
-/

/-!
Conformance with the statements: Definition 13 is encoded by
`IsBalancedPair` (D044). Only `theorem14` uses it, as a hypothesis on (L, I),
I = `boxZ k lo hi`; the body is the paper's three conditions with
#I_j = `boxSide k lo hi j` (0 for an empty interval). k ≥ 1 and R ≥ 1 are
not part of the predicate (unlike `IsBalancedWrt`, Definition 20) but are
`hk`, `hR` of `theorem14`. R : ℕ and `lo ≤ hi`: see the `balanced` context.
-/

/-!
### Paper context: Global balance is not componentwise balance (`balanced`)

This is global balance (all pairs of sides), unlike Definition 20 (only
coordinates connected in the constraint graph). R : ℕ, while Definition 13
allows real R ≥ 1, loses nothing: the paper's Theorem 14 takes an integer R.
`theorem14` adds `∀ s, lo s ≤ hi s`, excluding only empty boxes, where the
sum is empty and `boxVol` = 0, so the bound would read 0 ≤ 0.

Lean definitions for this comparison: `IsBalancedPair`.
Statements depending on these definitions: Theorem 14.
-/

/-!
### D044 — `IsBalancedPair`

`Core.lean:4394` · Used by: Theorem 14.

```lean
def IsBalancedPair (k R : ℕ) (L : Finset ((Fin k → ℤ) × ℤ)) (lo hi : Fin k → ℤ) : Prop :=
  L.card ≤ R ∧
    (∀ p ∈ L, 0 < ∑ s, |p.1 s| ∧ ∑ s, |p.1 s| ≤ (R : ℤ)) ∧
    ∀ i j : Fin k, boxSide k lo hi i ≤ R * boxSide k lo hi j
```

Library terms: G28 `Finset.card`.
-/

#check @_root_.IsBalancedPair

/-!
## Theorem 14 (`thm:general`)
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{theorem}\label{thm:general}
Let $k,R\geq1$ be integers. Let $(L,I)$ be an $R$-balanced pair.  Let $\alpha = [a_0; a_1, a_2, \ldots]$
be an irrational number with $a_i \leq R$ for all $i \geq 1$
and $c_1,{\ldots},c_k$ be positive integers with
$c_j\le R$.  Then
\[
\sup_{\theta\in\mathbb R^k} \Bigl|\sum_{n\in \cP(L) \cap I}e\Bigl(\alpha\sum_{j=1}^kc_jn_j^2
 +\theta\cdot n\Bigr)\Bigr|\ll_{k,R}\vol(I)^{1/2}.
\]
\end{theorem}
```

Coverage: `direct`.
-/

/-!
Definitions used: `boxSide` (D011), `boxVol` (D012), `boxZ` (D010), `polyBoxZ`
(D015), `expTwoPiI` (D001), `quadExpSum` (D016), `IsBalancedPair` (D044).
Library terms: G55 `Irrational`; G57 `Real.sqrt`; G76 `GenContFract.of`.
-/
theorem theorem14 :
  ∀ (k R : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R),
∃ C > 0, ∀ α : ℝ, Irrational α →
      (∀ (i : ℕ) (x : ℝ),
        (GenContFract.of α).partDens.get? i = some x → x ≤ (R : ℝ)) →
      ∀ c : Fin k → ℕ, (∀ j, 1 ≤ c j) → (∀ j, c j ≤ R) →
      ∀ lo hi : Fin k → ℤ, (∀ s, lo s ≤ hi s) →
      ∀ L : Finset ((Fin k → ℤ) × ℤ), IsBalancedPair k R L lo hi →
      ∀ θ : Fin k → ℝ,
        ‖quadExpSum k α c θ (polyBoxZ k L lo hi)‖ ≤
          C * Real.sqrt (boxVol k lo hi) :=
  @_root_.thm_general

/-!
## Proposition 15 (`prop:multiwall`)
-/

/-!
### Paper context: Smooth cutoffs, signs, and the multiwall summand (`cutoff`)

`IsSmoothCutoff` asks only C∞ and support in [−2,2] (no nonnegativity or
|U| ≤ 1); ‖U^(m)‖₁ = ∫ℝ |U^(m)|, U^(0) = U. Each sign factor of
`multiwallTerm` is ±1, as 2t+1 ≠ 0 for integer t.

Original paper definition/context (`article.txt:1088-1098`, verbatim TeX):
```tex
Let $U$ be smooth and supported in $[-2,2]$, and let
$\beta\in\RR^k$. Then
\[
\Bigl|\sum_{h\in\mathbb Z^k}\ \prod_{i=1}^r
\operatorname{sgn}\bigl(2(w_i\cdot h-B_i)+1\bigr)
\prod_{j=1}^kU\Bigl(\frac{h_j}P\Bigr)\,
e\Bigl(\alpha\sum_{j=1}^kc_jh_j^2+\beta\cdot h\Bigr)\Bigr|
\ \ll\ q^{k/2},
\]
where the implied constant depends only on $A$, $k$, $r$, $V$, $C$ and
$\|U^{(m)}\|_{L^1}$ for $0\le m\le2$.
```

Lean definitions for this comparison: `IsSmoothCutoff`, `multiwallTerm`, `multiwallT`.
Statements depending on these definitions: Proposition 15, Lemma 17.
-/

/-!
### D045 — `IsSmoothCutoff`

`Core.lean:5122` · Used by: Proposition 15, Lemma 17.

```lean
def IsSmoothCutoff (U : ℝ → ℂ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U ∧
    Function.support U ⊆ Set.Icc (-2 : ℝ) 2
```

Library terms: G36 `Set.Icc`; G43 `Function.support`; G74 `ContDiff ℝ ((⊤ : ℕ∞)
: WithTop ℕ∞)`.
-/

/-!
### D046 — `multiwallTerm`

`Core.lean:7144` · Used by: Proposition 15.

```lean
noncomputable def multiwallTerm (k r : ℕ) (α : ℝ) (c : Fin k → ℕ) (β : Fin k → ℝ)
    (U : ℝ → ℂ) (P : ℕ) (w : Fin r → Fin k → ℤ) (B : Fin r → ℤ)
    (h : Fin k → ℤ) : ℂ :=
  (∏ i, ((Int.sign (2 * ((∑ s, w i s * h s) - B i) + 1) : ℤ) : ℂ)) *
    (∏ j, U ((h j : ℝ) / (P : ℝ))) *
    expTwoPiI (α * ∑ j, (c j : ℝ) * (h j : ℝ) ^ 2 + ∑ j, β j * (h j : ℝ))
```

Library terms: G47 `Int.sign`.
-/

/-!
### D047 — `multiwallT`

`Core.lean:7151` · Used by: Proposition 15.

```lean
noncomputable def multiwallT (k r : ℕ) (α : ℝ) (c : Fin k → ℕ) (β : Fin k → ℝ)
    (U : ℝ → ℂ) (P : ℕ) (w : Fin r → Fin k → ℤ) (B : Fin r → ℤ) : ℂ :=
  ∑' h : Fin k → ℤ, multiwallTerm k r α c β U P w B h
```

Library terms: G71 `Summable`.
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{proposition}\label{prop:multiwall}
Let $A, C, V, k \geq 1$ and $r \geq 0$.
Let $\alpha = [a_0; a_1, a_2, \ldots]$ be an irrational number with
$a_i \leq A$ for all $i \geq 1$, and let $a/q$ be a convergent of
$\alpha$. Let $c_1,{\ldots},c_k$ be integers with $1\le c_j\le C$, let
$1 \leq P \leq q$ be an integer, let $w_1,{\ldots},w_r\in\Z^k\setminus\{0\}$ with
$|w_i|_1\le V$, and let $B_1,{\ldots},B_r$ be integers such that
\[
|w_i\cdot h-B_i|\le\frac q4
\qquad\text{whenever } |h_j|\le2P \text{ for all } j.
\]
Let $U$ be smooth and supported in $[-2,2]$, and let
$\beta\in\RR^k$. Then
\[
\Bigl|\sum_{h\in\mathbb Z^k}\ \prod_{i=1}^r
\operatorname{sgn}\bigl(2(w_i\cdot h-B_i)+1\bigr)
\prod_{j=1}^kU\Bigl(\frac{h_j}P\Bigr)\,
e\Bigl(\alpha\sum_{j=1}^kc_jh_j^2+\beta\cdot h\Bigr)\Bigr|
\ \ll\ q^{k/2},
\]
where the implied constant depends only on $A$, $k$, $r$, $V$, $C$ and
$\|U^{(m)}\|_{L^1}$ for $0\le m\le2$.

\end{proposition}
```

Coverage: `direct`.

Reading note: Lean's `h` is the paper's C (bound on the c_j), Lean's `C` the
implied constant; `V`, `h` : ℕ lose nothing (|w_i|₁ and the c_j are
integers). `Lam` bounds ∫‖U‖, ∫‖U′‖, ∫‖U″‖ and `C` is chosen after it, so
`C` is uniform in such U: at least as strong as the paper. The `nums s` and
`dens s` equations make a/q the s-th convergent (nums 0 = ⌊α⌋, dens 0 = 1),
so the extra `0 < q` and `Int.gcd a q = 1` hold automatically. The added
`Summable` holds as the summand vanishes unless every |h_j| ≤ 2P.
-/

/-!
Definitions used: `IsSmoothCutoff` (D045), `expTwoPiI` (D001), `multiwallTerm`
(D046), `multiwallT` (D047). Library terms: G48 `Int.gcd`; G55 `Irrational`; G57
`Real.sqrt`; G71 `Summable`; G72 `∫ x, f x`; G73 `deriv`; G76 `GenContFract.of`.
-/
theorem proposition15 :
  ∀ (A : ℝ) (k r V h : ℕ) (Lam : ℝ) (hA : 1 ≤ A) (hk : 1 ≤ k)
    (hV : 1 ≤ V) (hh : 1 ≤ h) (hLam : 1 ≤ Lam),
∃ C > 0, ∀ α : ℝ, Irrational α →
      (∀ (i : ℕ) (x : ℝ), (GenContFract.of α).partDens.get? i = some x → x ≤ A) →
      ∀ (s : ℕ) (a : ℤ) (q : ℕ), 0 < q →
        (a : ℝ) = (GenContFract.of α).nums s →
        ((q : ℕ) : ℝ) = (GenContFract.of α).dens s →
        Int.gcd a q = 1 →
        ∀ c : Fin k → ℕ, (∀ j, 1 ≤ c j) → (∀ j, c j ≤ h) →
        ∀ P : ℕ, 1 ≤ P → P ≤ q →
        ∀ w : Fin r → Fin k → ℤ, (∀ i, w i ≠ 0) →
          (∀ i, ∑ j, |w i j| ≤ (V : ℤ)) →
        ∀ B : Fin r → ℤ,
          (∀ x : Fin k → ℤ, (∀ j, |x j| ≤ 2 * (P : ℤ)) →
            ∀ i, 4 * |(∑ t, w i t * x t) - B i| ≤ (q : ℤ)) →
        ∀ U : ℝ → ℂ, IsSmoothCutoff U →
          (∫ t : ℝ, ‖U t‖) ≤ Lam →
          (∫ t : ℝ, ‖deriv U t‖) ≤ Lam →
          (∫ t : ℝ, ‖deriv (deriv U) t‖) ≤ Lam →
        ∀ β : Fin k → ℝ,
          Summable (multiwallTerm k r α c β U P w B) ∧
            ‖multiwallT k r α c β U P w B‖ ≤ C * Real.sqrt (q : ℝ) ^ k :=
  @_root_.prop_multiwall

/-!
## Lemma 16 (`lem:sgn`)
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{lemma}\label{lem:sgn}
Let $L\ge4$ be an even integer. Then for every integer $h$ with $|h|<L/2$,
\begin{equation}\label{eq:saw}
\operatorname{sgn}(h)
=\sum_{\substack{0<|\ell|<L/2\\ \ell\ \mathrm{odd}}}
\widehat c_L(\ell)\,e\Bigl(\frac{\ell h}L\Bigr)
\quad \text{with} \quad
\widehat c_L(\ell)=-\frac{2i}L\cot\Bigl(\frac{\pi\ell}L\Bigr).
\end{equation}
In particular, $|\widehat c_L(\ell)|\ \le\ \frac2{\pi|\ell|}$ for $0<|\ell|<L/2$.
\end{lemma}
```

Coverage: `direct`.

`lemma16` is `eq:saw` (2|h| < L is |h| < L/2; for even L, `sgnIndex L` is
the paper's index set); `lemma16OddCoefficient` is the cotangent formula
for odd ℓ and every L; `lemma16CoefficientBound` (`norm_sgnCoeff_le`,
Core.lean:4800) has the paper's L ≥ 4 and 0 < |ℓ| < L/2 but not L even, a
harmless generalization. `sgnCoeff` is 0 at even ℓ
(`lemma16EvenCoefficient`); for even ℓ with 0 < |ℓ| < L/2 the paper's
ĉ_L(ℓ) ≠ 0, so there the displayed bound is about 0. This is harmless: only
odd ℓ occur in the expansion, and the proof of Proposition 15 uses
ĉ_{2q}(v) = 0 for even v, as Lean does.

The last sentence of the lemma -- the bound at every ℓ with 0 < |ℓ| < L/2,
even ℓ included -- is therefore exported on its own, as
`Paper.lemma16CotWeightBound` (displayed below, after the other
endpoints): it bounds
|`sgnCotWeight L ℓ`| = |ĉ_L(ℓ)|, so it covers the even case, and it wraps
Core's `abs_sgnCotWeight_le` (Core.lean:4766). On odd ℓ the two bounds agree,
by `Lemma16.oddCoefficientFormula` together with ‖-i·z‖ = ‖z‖.
-/

/-!
### Paper context: The finite sign expansion (`sign`)

The definitions are total, with no condition on L; for the index set and
even ℓ see Lemma 16's note.

Lean definitions for this comparison: `sgnCotWeight`, `sgnCoeff`, `sgnIndex`.
Statements depending on these definitions: Lemma 16.
-/

/-!
### D048 — `sgnCotWeight`

`Core.lean:4454` · Used by: Lemma 16 (indirectly).

```lean
noncomputable def sgnCotWeight (L : ℕ) (x : ℝ) : ℝ :=
  2 / (L : ℝ) * Real.cot (Real.pi * x / (L : ℝ))
```

Library terms: G58 `Real.exp`; G60 `Real.cot`.
-/

/-!
### D049 — `sgnCoeff`

`Core.lean:4457` · Used by: Lemma 16.

```lean
noncomputable def sgnCoeff (L : ℕ) (l : ℤ) : ℂ :=
  if Odd l then -Complex.I * (sgnCotWeight L (l : ℝ) : ℂ) else 0
```

Library terms: G51 `Odd`; G58 `Real.exp`.
-/

/-!
### D050 — `sgnIndex`

`Core.lean:4460` · Used by: Lemma 16.

```lean
def sgnIndex (L : ℕ) : Finset ℤ :=
  (Finset.Ioo (-((L : ℤ) / 2)) ((L : ℤ) / 2)).filter fun l => Odd l
```

Library terms: G25 `Finset.Icc`; G26 `Finset.filter`; G51 `Odd`.
-/

/-!
Definitions used: `expTwoPiI` (D001), `sgnCotWeight` (D048), `sgnCoeff` (D049),
`sgnIndex` (D050). Library terms: G47 `Int.sign`; G51 `Odd`.
-/
theorem lemma16 :
  ∀ (L : ℕ) (hL : 4 ≤ L) (hLe : Even L) (h : ℤ) (hh : 2 * |h| < (L : ℤ)),
(Int.sign h : ℂ) =
      ∑ l ∈ sgnIndex L, sgnCoeff L l * expTwoPiI (((l * h : ℤ) : ℝ) / (L : ℝ)) :=
  @_root_.lem_sgn

/-!
Definitions used: `sgnCotWeight` (D048), `sgnCoeff` (D049). Library terms: G51
`Odd`; G58 `Real.exp`; G60 `Real.cot`.
-/
theorem lemma16OddCoefficient :
  ∀ (L : ℕ) (l : ℤ) (hl : Odd l),
sgnCoeff L l =
      -(2 * Complex.I / (L : ℂ)) * (Real.cot (Real.pi * (l : ℝ) / (L : ℝ)) : ℂ) :=
  @_root_.sgnCoeff_of_odd

/-!
Definitions used: `sgnCotWeight` (D048), `sgnCoeff` (D049). Library terms: G51
`Odd`.
-/
theorem lemma16EvenCoefficient :
  ∀ (L : ℕ) (l : ℤ) (hl : Even l),
sgnCoeff L l = 0 :=
  @_root_.sgnCoeff_of_even

/-!
Definitions used: `sgnCotWeight` (D048), `sgnCoeff` (D049). Library terms: G58
`Real.exp`.
-/
theorem lemma16CoefficientBound :
  ∀ (L : ℕ) (hL : 4 ≤ L) (l : ℤ) (hl : l ≠ 0)
    (hlL : 2 * |l| < (L : ℤ)),
‖sgnCoeff L l‖ ≤ 2 / (Real.pi * |(l : ℝ)|) :=
  @_root_.norm_sgnCoeff_le

/-!
Definitions used: `sgnCotWeight` (D048).
-/
theorem lemma16CotWeightBound :
  ∀ (L : ℕ) (hL : 4 ≤ L) (hLe : Even L) (l : ℤ) (hl : 0 < |l|)
    (hlL : |l| < (L : ℤ) / 2),
|sgnCotWeight L (l : ℝ)| ≤ 2 / (Real.pi * |(l : ℝ)|) :=
  @_root_.Paper.lemma16CotWeightBound

/-!
## Lemma 17 (`lem:poisson`)
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{lemma}\label{lem:poisson}
Let $U:\mathbb R\to\mathbb C$ be a smooth function supported in $[-2,2]$. 
Given $\lambda,\xi\in\RR$ set
\[
W_U(\lambda;\xi):=\int_{\mathbb R}U(t)\,e\bigl(\lambda t^2+\xi t\bigr)\,{dt}
\]
and, for an integer $q \geq 1$ and $a,b \in \mathbb{Z}$, set
\[
G(a,b;q):=\sum_{x\bmod q}e\Bigl(\frac{ax^2+bx}q\Bigr).
\]
Then for any $N, q \geq 1$, $\delta, \theta \in \RR$ and $a, b \in \mathbb{Z}$,  
\begin{equation}\label{eq:poisson}
\sum_{n\in\mathbb Z}e\Bigl(\Bigl(\frac aq+\delta\Bigr)n^2
+\Bigl(\frac bq+\theta\Bigr)n\Bigr)\,U\Bigl(\frac nN\Bigr)
=\frac Nq\sum_{\ell\in\mathbb Z}G(a,b+\ell;q)\,
W_U\Bigl(\delta N^2;\,N\Bigl(\theta-\frac{\ell}q\Bigr)\Bigr).
\end{equation}
Moreover, for $\Lambda\ge1$, $|\lambda|\le\Lambda$ and $\xi\in\RR$,
\[
|W_U(\lambda;\xi)|\ll_{\Lambda} (1 + \|U'\|_{1} + \|U''\|_{1}) \cdot \frac{1}{1+|\xi|^2}.
\]
\end{lemma}
```

Coverage: `component`.

`lemma17Summation` (the identity) and `lemma17Decay` (the bound on W_U, in
the paper's form) cover the whole lemma. N is real, N ≥ 1; the ℓ-series is
asserted `Summable`, and the n-sum is a `∑'` with finite support.
-/

/-!
### Paper context: Oscillatory integrals and complete Gauss sums (`integrals`)

`quadGaussSum` sums over the representatives 0,…,q−1 and takes a proof of
q > 0; `quadPhase` is one summand.

Lean definitions for this comparison: `quadPhase`, `quadGaussSum`, `oscIntegralW`.
Statements depending on these definitions: Lemma 17, Lemma 18.
-/

/-!
### D051 — `quadPhase`

`Core.lean:5042` · Used by: Lemma 17, Lemma 18 (indirectly).

```lean
noncomputable def quadPhase (a b : ℤ) (q : ℕ) (_hq : 0 < q) (x : ℤ) : ℂ :=
  expTwoPiI (((a * x ^ 2 + b * x : ℤ) : ℝ) / (q : ℝ))
```
-/

/-!
### D052 — `quadGaussSum`

`Core.lean:5045` · Used by: Lemma 17, Lemma 18.

```lean
noncomputable def quadGaussSum (a b : ℤ) (q : ℕ) (hq : 0 < q) : ℂ :=
  ∑ x ∈ Finset.range q, quadPhase a b q hq (x : ℤ)
```

Library terms: G24 `Finset.range`.
-/

/-!
### D053 — `oscIntegralW`

`Core.lean:5128` · Used by: Lemma 17.

```lean
noncomputable def oscIntegralW (U : ℝ → ℂ) (lam xi : ℝ) : ℂ :=
  ∫ t : ℝ, U t * expTwoPiI (lam * t ^ 2 + xi * t)
```

Library terms: G72 `∫ x, f x`.
-/

/-!
Definitions used: `expTwoPiI` (D001), `quadPhase` (D051), `quadGaussSum` (D052),
`IsSmoothCutoff` (D045), `oscIntegralW` (D053). Library terms: G71 `Summable`.
-/
theorem lemma17Summation :
  ∀ (U : ℝ → ℂ) (hU : IsSmoothCutoff U)
    (N : ℝ) (hN : 1 ≤ N) (q : ℕ) (hq : 0 < q)
    (δ θ : ℝ) (a b : ℤ),
Summable (fun l : ℤ =>
        quadGaussSum a (b + l) q hq *
          oscIntegralW U (δ * N ^ 2) (N * (θ - (l : ℝ) / (q : ℝ)))) ∧
      ∑' n : ℤ,
          expTwoPiI (((a : ℝ) / (q : ℝ) + δ) * (n : ℝ) ^ 2 +
            ((b : ℝ) / (q : ℝ) + θ) * (n : ℝ)) * U ((n : ℝ) / N) =
        ((N : ℂ) / (q : ℂ)) *
          ∑' l : ℤ,
            quadGaussSum a (b + l) q hq *
              oscIntegralW U (δ * N ^ 2) (N * (θ - (l : ℝ) / (q : ℝ))) :=
  @_root_.lem_poisson_summation

/-!
Definitions used: `IsSmoothCutoff` (D045), `expTwoPiI` (D001), `oscIntegralW`
(D053). Library terms: G72 `∫ x, f x`; G73 `deriv`.
-/
theorem lemma17Decay :
  ∀ (Λ : ℝ) (hΛ : 1 ≤ Λ),
∃ C > 0, ∀ U : ℝ → ℂ, IsSmoothCutoff U →
      ∀ lam : ℝ, |lam| ≤ Λ → ∀ xi : ℝ,
        ‖oscIntegralW U lam xi‖ ≤
          C * (1 + (∫ t : ℝ, ‖deriv U t‖) + (∫ t : ℝ, ‖deriv (deriv U) t‖)) /
            (1 + |xi| ^ 2) :=
  @_root_.lem_poisson_decay

/-!
## Lemma 18 (`lem:gaussphase`)
-/

/-!
### Paper context: The periodic Gauss-phase factor (`gaussphase`)

φ_{a,q} is defined in the paper's proof (excerpt below); `gaussPhasePhi`
takes ā as an explicit argument. (Not the basis φ_l of Theorem 5.)

Original paper definition/context (`article.txt:1226-1229`, verbatim TeX):
```tex
Let
\[
\phi_{a,q}(x;c) := \frac{1}{\sqrt{q}} \cdot G(ca, x; q) e \Big ( \frac{\overline{a} x^2}{4 c q} \Big ).
\]
```

Lean definitions for this comparison: `gaussPhasePhi`.
Statements depending on these definitions: Lemma 18.
-/

/-!
### D054 — `gaussPhasePhi`

`Core.lean:5752` · Used by: Lemma 18.

```lean
noncomputable def gaussPhasePhi (a abar : ℤ) (c q : ℕ) (hq : 0 < q) (x : ℤ) : ℂ :=
  (Real.sqrt (q : ℝ) : ℂ)⁻¹ * quadGaussSum ((c : ℤ) * a) x q hq *
    expTwoPiI ((abar : ℝ) * (x : ℝ) ^ 2 / (4 * (c : ℝ) * (q : ℝ)))
```

Library terms: G57 `Real.sqrt`.
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{lemma}\label{lem:gaussphase}
Let $c, q \geq 1$ and $(a,q) = 1$. Denote by $\overline{a}$ the inverse
of $a$ modulo $q$. Then, for all $b \in \mathbb{Z}$, 
\[
G(ca,b;q)=\sqrt q \cdot \phi_{a,q}(b;c) \cdot e\Big(-\frac{\overline a\,b^2}{4cq}\Big),
\]
where $x \mapsto \phi_{a,q}(x; c)$ is periodic modulo $2c$ and
$|\phi_{a,q}(x; c)|\leq \sqrt{2c}$ for all $x \in \mathbb{Z}$.
\end{lemma}
```

Coverage: `direct`.

Reading note: `gaussPhasePhi` is the paper's φ_{a,q}, so the first conjunct
is essentially its definition; the content is the 2c-periodicity and the
bound √(2c). φ depends on ā through e(āx²/(4cq)); Lean states all three
conjuncts for every integer `abar` with a·abar ≡ 1 mod q (the lemma fixes
no representative), so Lean is at least as strong.
-/

/-!
Definitions used: `expTwoPiI` (D001), `quadPhase` (D051), `quadGaussSum` (D052),
`gaussPhasePhi` (D054). Library terms: G48 `Int.gcd`; G49 `a ≡ b [ZMOD n]`; G57
`Real.sqrt`.
-/
theorem lemma18 :
  ∀ (a abar : ℤ) (c q : ℕ) (hc : 1 ≤ c) (hq : 0 < q)
    (ha : Int.gcd a q = 1) (habar : a * abar ≡ 1 [ZMOD (q : ℤ)]),
(∀ b : ℤ,
        quadGaussSum ((c : ℤ) * a) b q hq =
          (Real.sqrt (q : ℝ) : ℂ) * gaussPhasePhi a abar c q hq b *
            expTwoPiI (-((abar : ℝ) * (b : ℝ) ^ 2) / (4 * (c : ℝ) * (q : ℝ)))) ∧
      (∀ x : ℤ,
        gaussPhasePhi a abar c q hq (x + 2 * (c : ℤ)) = gaussPhasePhi a abar c q hq x) ∧
      (∀ x : ℤ, ‖gaussPhasePhi a abar c q hq x‖ ≤ Real.sqrt (2 * (c : ℝ))) :=
  @_root_.lem_gaussphase

/-!
## Lemma 19 (`lem:weylgauss`)
-/

/-!
### Paper context: Nearest-integer distance and progression sums (`weyl`)

The paper's ‖x‖ (distance to the nearest integer) occurs in no displayed
statement (Core's `intDist`, Core.lean:5930, only in auxiliary lemmas and
proofs). `weylProgIco N R v r` is {h ∈ ℤ : N ≤ h < N+R, h ≡ v mod r}.

Original paper definition/context (`article.txt:1263-1266`, verbatim TeX):
```tex
Throughout this section $\alpha = [a_0; a_1, a_2, \ldots]$ is an irrational
number with $a_i \leq A$ for all $i \geq 1$, and
$a/q$ is a convergent of $\alpha$, and for $x\in\RR$ we write $\|x\|$ for
the distance from $x$ to the nearest integer.
```

Lean definitions for this comparison: `weylProgIco`, `weylProgSum`.
Statements depending on these definitions: Lemma 19.
-/

/-!
### D055 — `weylProgIco`

`Core.lean:7076` · Used by: Lemma 19 (indirectly).

```lean
noncomputable def weylProgIco (N : ℤ) (R : ℝ) (v r : ℤ) : Finset ℤ :=
  (Finset.Ico N (N + ⌈R⌉)).filter fun h => (h : ℝ) < (N : ℝ) + R ∧ h ≡ v [ZMOD r]
```

Library terms: G25 `Finset.Icc`; G26 `Finset.filter`; G49 `a ≡ b [ZMOD n]`; G50
`⌈x⌉`.
-/

/-!
### D056 — `weylProgSum`

`Core.lean:7081` · Used by: Lemma 19.

```lean
noncomputable def weylProgSum (alpha' beta : ℝ) (N : ℤ) (R : ℝ) (v r : ℤ) : ℂ :=
  ∑ h ∈ weylProgIco N R v r, expTwoPiI (alpha' * (h : ℝ) ^ 2 + beta * (h : ℝ))
```
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{lemma}\label{lem:weylgauss}
Let $A , M \geq 1$.
Let $\alpha = [a_0; a_1, a_2, \ldots]$ be an irrational number with $a_i \leq A$ for all $i \geq 1$.
Let $a / q$ be a convergent of $\alpha$ and denote by $\overline{a} \in [0,q)$
the modular inverse of $a$ modulo $q$. Then, for all $1 \leq R \leq 2q$,
$$
\sup_{\beta \in \mathbb{R}} \sup_{\substack{1 \leq |m|,|n| \leq M \\ m, n, N \in \mathbb{Z} \\ v, r \geq 1}} \Big | \sum_{\substack{N \leq h < N + R \\ h \equiv v \mymod{r}}} e \Big ( \frac{m}{n} \cdot \frac{\overline{a}}{4 q} \cdot h^2 + \beta h \Big ) \Big | \ll_{M,A} \sqrt{R\log(2R)}.
$$
\end{lemma}
```

Coverage: `direct`.
-/

/-!
Definitions used: `expTwoPiI` (D001), `weylProgIco` (D055), `weylProgSum`
(D056). Library terms: G49 `a ≡ b [ZMOD n]`; G55 `Irrational`; G57 `Real.sqrt`;
G59 `Real.log`; G76 `GenContFract.of`.
-/
theorem lemma19 :
  ∀ (A M : ℝ) (hA : 1 ≤ A) (hM : 1 ≤ M),
∃ C > 0, ∀ α : ℝ, Irrational α →
      (∀ (i : ℕ) (x : ℝ), (GenContFract.of α).partDens.get? i = some x → x ≤ A) →
      ∀ s : ℕ, ∀ a q : ℤ,
        (a : ℝ) = (GenContFract.of α).nums s →
        (q : ℝ) = (GenContFract.of α).dens s →
        ∀ abar : ℤ, a * abar ≡ 1 [ZMOD q] → 0 ≤ abar → abar < q →
        ∀ R : ℝ, 1 ≤ R → R ≤ 2 * (q : ℝ) →
        ∀ (beta : ℝ) (m n : ℤ), 1 ≤ |m| → (|m| : ℝ) ≤ M → 1 ≤ |n| → (|n| : ℝ) ≤ M →
        ∀ N v r : ℤ, 1 ≤ v → 1 ≤ r →
          ‖weylProgSum ((m : ℝ) / (n : ℝ) * ((abar : ℝ) / (4 * (q : ℝ)))) beta N R v r‖ ≤
            C * Real.sqrt (R * Real.log (2 * R)) :=
  @_root_.lem_weylgauss

/-!
## Definition 20 (`def:balanced-W`)
-/

/-!
### Paper context: Constraint weight and the coordinate-interaction graph (`graph`)

ρ is a constraint-complexity measure, not the Poisson deviation ρ_λ.

Original paper definition/context (`article.txt:1553-1558`, verbatim TeX):
```tex
For a finite $W\subset\z^k\times\z$ we write
\[
 \rho(W)=\max\Bigl\{\#W,\ \max_{(w,b)\in W}|w|_1\Bigr\},
\]
and associate to $W$ the undirected graph $\Gamma_k(W)$ with vertices $\{1, \ldots, k\}$, in which $i\neq j$ are joined
by an edge whenever they occur together in some inequality of $W$, i.e.\ $w_iw_j\neq0$ for some $(w,b)\in W$.
```

Lean definitions for this comparison: `constraintRho`, `constraintGraph`.
Statements depending on these definitions: Theorem 21, Lemma 24, Lemma 25, Lemma 26, Proposition 27.
-/

/-!
### D057 — `constraintRho`

`Core.lean:9510` · Used by: Theorem 21, Lemma 24, Lemma 25, Lemma 26,
Proposition 27 (indirectly).

```lean
def constraintRho (k : ℕ) (W : Finset ((Fin k → ℤ) × ℤ)) : ℕ :=
  max W.card (W.sup fun p => (∑ s, |p.1 s|).toNat)
```

Library terms: G28 `Finset.card`; G29 `Finset.sup`; G45 `Int.toNat`.
-/

/-!
### D058 — `constraintGraph`

`Core.lean:9513` · Used by: Theorem 21, Proposition 27 (indirectly).

```lean
def constraintGraph (k : ℕ) (W : Finset ((Fin k → ℤ) × ℤ)) : SimpleGraph (Fin k) :=
  SimpleGraph.fromRel fun i j => ∃ p ∈ W, p.1 i * p.1 j ≠ 0
```

Library terms: G77 `SimpleGraph`.
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{definition}[Componentwise balanced boxes]\label{def:balanced-W}
Let $k, R\ge1$ and let $W\subset(\z^k\setminus\{0\})\times\z$ be finite. A box $J=\prod_{j=1}^kJ_j$
is \emph{$R$-balanced with respect to $W$} if
\[
 \#J_i\le R\#J_j
 \quad\text{whenever }i,j\text{ belong to the same component of }
 \Gamma_k(W).
\]
\end{definition}
```

Coverage: `direct-definition`.
-/

/-!
Conformance with the statements: Definition 20 is `IsBalancedWrt` (D059):
Γ_k(W) is `constraintGraph` (D058), “same component” is equality of
`connectedComponentMk`, #J_i ≤ R#J_j is compared in ℕ via `boxSide` (k, R
natural), and the standing hypotheses 1 ≤ k, 1 ≤ R and nonzero normals are
conjuncts, so each conclusion `IsBalancedWrt …` asserts them. No displayed
statement assumes it; it is concluded in Proposition 27 (last conjunct; for
the normals see its reading note) and in Theorem 21 through
`BalancedDecompData` (D060), with J_m = `boxZ k (lo' m) (hi' m)` (there the
normals repeat its clause `∀ m, ∀ p ∈ W' m, p.1 ≠ 0`). `constraintRho`
(D057) is not part of Definition 20 (it enters via `BalancedDecompData` and
the field `rho_le_A` of `Piece`).
-/

/-!
### Paper context: Balance along connected components (`components`)

`IsBalancedWrt` bounds neither #W nor |w|₁ (separate conjuncts of the
conclusions) and does not require nonempty intervals.

Lean definitions for this comparison: `IsBalancedWrt`.
Statements depending on these definitions: Theorem 21, Proposition 27.
-/

/-!
### D059 — `IsBalancedWrt`

`Core.lean:9554` · Used by: Proposition 27; Theorem 21 (indirectly).

```lean
def IsBalancedWrt (k R : ℕ) (W : Finset ((Fin k → ℤ) × ℤ)) (lo hi : Fin k → ℤ) : Prop :=
  1 ≤ k ∧ 1 ≤ R ∧ (∀ p ∈ W, p.1 ≠ 0) ∧
    ∀ i j : Fin k,
      (constraintGraph k W).connectedComponentMk i =
          (constraintGraph k W).connectedComponentMk j →
        boxSide k lo hi i ≤ R * boxSide k lo hi j
```

Library terms: G78 `SimpleGraph.connectedComponentMk`.
-/

#check @_root_.IsBalancedWrt

/-!
## Theorem 21 (`thm:decomp`)
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{theorem}[Decomposition with balanced enclosing boxes]\label{thm:decomp}
Let $k,V,h\ge1$ and $r\ge0$ be integers, and let $c_1,\ldots,c_k$ be positive integers with
$c_j\le h$. Let $W\subset\z^k\times\z$ with $\#W\le r$ be such that $0<|w|_1\le V$ for all $(w,b)\in W$.
Suppose that $P=\cP(W)$ is finite and nonempty, and let $I$ be the smallest box containing $P$.
Then, there exists an integer $R=R(k,r,V,h)$ and a disjoint decomposition
\begin{equation}\label{eq:decomposition}
 P=\bigsqcup_{m=1}^M\bigl(u_m+\Phi_m\cP(W_m)\bigr)
\end{equation}
with the property that $M\le R$, $u_m\in\z^k$, $\Phi_m\in\z^{k\times k}$ is non-singular, each $W_m \subset \z^k \setminus\{0\} \times \z$ is finite, the boxes $J_m$ are $R$-balanced with respect to
$W_m$ and
\begin{equation}\label{eq:boxed-conclusion}
 \cP(W_m)\subseteq J_m \quad \text{and} \quad  \vol(J_m)\le R\vol(I).
\end{equation}
Furthermore each
$\Phi_m^{\mathsf T}\operatorname{diag}(c_j)\Phi_m$ is diagonal, and
\[
\max\Bigl(|\Phi_m|_\infty ,\, |\Phi_m^{\mathsf T}\operatorname{diag}(c_j)\Phi_m|_\infty ,\, \rho(W_m)\Bigr) \leq R
\qquad(1\le m\le M).
\]
If moreover both $(w_0,b_0)$ and $(-w_0,-b_0)$ belong to $W$, then the decomposition
\eqref{eq:decomposition} can be chosen so that, in addition,
\begin{equation}\label{eq:decomposition-section}
 \vol(J_m)\le R\,\frac{\vol(I)}{\len(w_0;I)}\qquad(1\le m\le M).
\end{equation}
\end{theorem}
```

Coverage: `direct`.
-/

/-!
### Paper context: The packaged decomposition conclusion (`decomposition`)

In `theorem21`, I is `boxZ k lo hi`: it contains P(W) and each `lo j`,
`hi j` is attained on P(W), so they are the coordinatewise extrema. The
image clause `⊆ polyPZ k W` is implied by the union equality; as
y ↦ u_m+Φ_m y is injective (det Φ_m ≠ 0), union plus disjointness is the
paper's disjoint union. The sectional bound reads vol(J_m)·len(w₀;I) ≤
R·vol(I), equivalent to the quotient as `boxLen` ≥ 1 (w₀ ≠ 0 since
0 < |w|₁ on W).

Lean definitions for this comparison: `BalancedDecompData`.
Statements depending on these definitions: Theorem 21.
-/

/-!
### D060 — `BalancedDecompData`

`Core.lean:13951` · Used by: Theorem 21.

```lean
def BalancedDecompData (k R : ℕ) (c : Fin k → ℕ) (W : Finset ((Fin k → ℤ) × ℤ))
    (lo hi : Fin k → ℤ) (M : ℕ) (u : Fin M → Fin k → ℤ)
    (Φ : Fin M → Matrix (Fin k) (Fin k) ℤ) (W' : Fin M → Finset ((Fin k → ℤ) × ℤ))
    (lo' hi' : Fin M → Fin k → ℤ) : Prop :=
  M ≤ R ∧
    (∀ m, (Φ m).det ≠ 0) ∧
    (∀ m, pieceAffineImage (u m) (Φ m) (polyPZ k (W' m)) ⊆ polyPZ k W) ∧
    (∀ m m' : Fin M, m ≠ m' →
      Disjoint (pieceAffineImage (u m) (Φ m) (polyPZ k (W' m)))
        (pieceAffineImage (u m') (Φ m') (polyPZ k (W' m')))) ∧
    polyPZ k W = ⋃ m : Fin M, pieceAffineImage (u m) (Φ m) (polyPZ k (W' m)) ∧
    (∀ m, ∀ p ∈ W' m, p.1 ≠ 0) ∧
    (∀ m, IsBalancedWrt k R (W' m) (lo' m) (hi' m)) ∧
    (∀ m, polyPZ k (W' m) ⊆ (boxZ k (lo' m) (hi' m) : Set (Fin k → ℤ))) ∧
    (∀ m, boxVol k (lo' m) (hi' m) ≤ R * boxVol k lo hi) ∧
    (∀ m, ((Φ m).transpose * Matrix.diagonal (fun j => (c j : ℤ)) * Φ m).IsDiag) ∧
    (∀ m, matInftyNorm (Φ m) ≤ R) ∧
    (∀ m, matInftyNorm ((Φ m).transpose * Matrix.diagonal (fun j => (c j : ℤ)) * Φ m) ≤ R) ∧
    (∀ m, constraintRho k (W' m) ≤ R)
```

Library terms: G38 `⋃ i, S i`; G39 `Disjoint`; G62 `Matrix.det`; G64
`Matrix.transpose`; G65 `Matrix.diagonal`.
-/

/-!
Definitions used: `boxZ` (D010), `boxSide` (D011), `boxVol` (D012), `boxLen`
(D013), `polyPZ` (D007), `constraintRho` (D057), `constraintGraph` (D058),
`IsBalancedWrt` (D059), `matInftyNorm` (D023), `pieceAffineImage` (D022),
`BalancedDecompData` (D060). Library terms: G28 `Finset.card`; G42 `Set.Finite`.
-/
theorem theorem21 :
  ∀ (k V h r : ℕ) (hk : 1 ≤ k) (hV : 1 ≤ V) (hh : 1 ≤ h),
∃ R : ℕ, 1 ≤ R ∧
      ∀ c : Fin k → ℕ, (∀ j, 1 ≤ c j) → (∀ j, c j ≤ h) →
      ∀ W : Finset ((Fin k → ℤ) × ℤ), W.card ≤ r →
        (∀ p ∈ W, 0 < ∑ s, |p.1 s| ∧ ∑ s, |p.1 s| ≤ (V : ℤ)) →
        (polyPZ k W).Finite → (polyPZ k W).Nonempty →
      ∀ lo hi : Fin k → ℤ,
        polyPZ k W ⊆ (boxZ k lo hi : Set (Fin k → ℤ)) →
        (∀ j, ∃ x ∈ polyPZ k W, x j = lo j) →
        (∀ j, ∃ x ∈ polyPZ k W, x j = hi j) →
        (∃ (M : ℕ) (u : Fin M → Fin k → ℤ) (Φ : Fin M → Matrix (Fin k) (Fin k) ℤ)
            (W' : Fin M → Finset ((Fin k → ℤ) × ℤ)) (lo' hi' : Fin M → Fin k → ℤ),
            BalancedDecompData k R c W lo hi M u Φ W' lo' hi') ∧
        ∀ (w₀ : Fin k → ℤ) (b₀ : ℤ), (w₀, b₀) ∈ W → (-w₀, -b₀) ∈ W →
          ∃ (M : ℕ) (u : Fin M → Fin k → ℤ) (Φ : Fin M → Matrix (Fin k) (Fin k) ℤ)
            (W' : Fin M → Finset ((Fin k → ℤ) × ℤ)) (lo' hi' : Fin M → Fin k → ℤ),
            BalancedDecompData k R c W lo hi M u Φ W' lo' hi' ∧
            ∀ m, boxVol k (lo' m) (hi' m) * boxLen k w₀ lo hi ≤ R * boxVol k lo hi :=
  @_root_.thm_decomp

/-!
## Definition 22 (`def:piece`)
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{definition}[Pieces]\label{def:piece}
A \emph{piece} of dimension $d\ge1$ is a quadruple $(W,J,Q,A)$, where $W\subset\Z^d\times\Z$ is finite,
$J=\prod_{j=1}^dJ_j$ is a box, $Q(x)=\sum_{j=1}^d\gamma_jx_j^2$ with integers $\gamma_j\ge1$, and
$A\ge1$ is an integer, such that
\[
 \cP(W)\subseteq J\qquad\text{and}\qquad\max\{d,\rho(W),|(\gamma_j)|_\infty\}\le A.
\]
Let $H=\min_{1\le j\le d}\#J_j$. A coordinate $j$ is said to be \emph{short} if $\#J_j\le AH$ and \emph{long}
otherwise. We define $B:=\{j : \#J_j \leq AH\}$ and $B^c=\{1,\ldots,d\}\setminus B$ as the sets of short and long coordinates. An
inequality $(w,b)\in W$ is said to be \emph{mixed} if $\supp w$ has nonempty intersection with both $B$ and $B^c$.
The \emph{index} of the piece is $(d,n_{\mathrm{long}},n_{\mathrm{mix}})$, where $n_{\mathrm{long}}=\#B^c$ and $n_{\mathrm{mix}}$ is the number of mixed inequalities in $W$. Indices are ordered lexicographically.
\end{definition}
```

Coverage: `direct-structure`.
-/

/-!
Conformance with the statements: Definition 22 is the structure `Piece`
(D061): data fields W, lo, hi, gamma, A give (W, J, Q, A) with
J = `boxZ d lo hi`, Q = `Piece.quad` (D062); the proof fields are the
paper's conditions (max{d, ρ(W), |(γ_j)|∞} ≤ A as three fields), with d,
γ_j, A natural; the derived notions are D063–D071 (index ordered via
`toLex`). Uses: Lemma 24 only through transitions, decompositions and
`Piece.prod`; Lemma 25 assumes `p.IsMixed (w, b)`, concludes
`pPlus.index < p.index` and the bound A²H, and states “… are pieces” as
existence of a `Piece` (see `split`); Lemma 26 constrains `p.A`,
`p.minSide`, `p.side` and the outputs' `A`, `gamma`, sides and intervals;
Proposition 27 assumes `p.A = A`, `p.nLong = nlong`, `p.nMix = nmix` (index
(d, n_long, n_mix), d the type parameter) and bounds the outputs' `A` and
box volume. Theorem 21 does not use `Piece`. The structure does not require
`lo j ≤ hi j`; Lemmas 25, 26 and Proposition 27 assume it, Lemma 24 does
not.
-/

/-!
### Paper context: All fields of a piece and its lexicographic index (`pieces`)

Core.lean's `Piece.IsShort`, `Piece.IsLong` (Core.lean:9597, 9600) occur in
no statement and are not shown.

Lean definitions for this comparison: `Piece`, `Piece.quad`, `Piece.side`, `Piece.minSide`, `Piece.shortCoords`, `Piece.longCoords`, `Piece.IsMixed`, `Piece.mixedIneqs`, `Piece.nLong`, `Piece.nMix`, `Piece.index`.
Statements depending on these definitions: Lemma 24, Lemma 25, Lemma 26, Proposition 27.
-/

/-!
### D061 — `Piece`

`Core.lean:9574` · Used by: Lemma 24, Lemma 25, Lemma 26, Proposition 27.

```lean
structure Piece (d : ℕ) where
  W : Finset ((Fin d → ℤ) × ℤ)
  lo : Fin d → ℤ
  hi : Fin d → ℤ
  gamma : Fin d → ℕ
  A : ℕ
  one_le_dim : 1 ≤ d
  one_le_gamma : ∀ j, 1 ≤ gamma j
  one_le_A : 1 ≤ A
  poly_subset_box : polyPZ d W ⊆ (boxZ d lo hi : Set (Fin d → ℤ))
  dim_le_A : d ≤ A
  rho_le_A : constraintRho d W ≤ A
  gamma_le_A : ∀ j, gamma j ≤ A
```
-/

/-!
### D062 — `Piece.quad`

`Core.lean:9588` · Used by: Lemma 24, Lemma 25, Lemma 26, Proposition 27
(indirectly).

```lean
def Piece.quad {d : ℕ} (p : Piece d) (x : Fin d → ℤ) : ℤ :=
  ∑ j, (p.gamma j : ℤ) * x j ^ 2
```
-/

/-!
### D063 — `Piece.side`

`Core.lean:9591` · Used by: Lemma 26; Lemma 25, Proposition 27 (indirectly).

```lean
def Piece.side {d : ℕ} (p : Piece d) (j : Fin d) : ℕ := boxSide d p.lo p.hi j
```
-/

/-!
### D064 — `Piece.minSide`

`Core.lean:9593` · Used by: Lemma 25, Lemma 26; Proposition 27 (indirectly).

```lean
def Piece.minSide {d : ℕ} (p : Piece d) : ℕ :=
  Finset.univ.inf'
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp p.one_le_dim)) p.side
```

Library terms: G30 `Finset.inf'`.
-/

/-!
### D065 — `Piece.shortCoords`

`Core.lean:9602` · Used by: Lemma 25, Proposition 27 (indirectly).

```lean
def Piece.shortCoords {d : ℕ} (p : Piece d) : Finset (Fin d) :=
  Finset.univ.filter fun j => p.side j ≤ p.A * p.minSide
```

Library terms: G26 `Finset.filter`.
-/

/-!
### D066 — `Piece.longCoords`

`Core.lean:9605` · Used by: Lemma 25, Proposition 27 (indirectly).

```lean
def Piece.longCoords {d : ℕ} (p : Piece d) : Finset (Fin d) :=
  Finset.univ.filter fun j => ¬ p.side j ≤ p.A * p.minSide
```

Library terms: G26 `Finset.filter`.
-/

/-!
### D067 — `Piece.IsMixed`

`Core.lean:9608` · Used by: Lemma 25; Proposition 27 (indirectly).

```lean
def Piece.IsMixed {d : ℕ} (p : Piece d) (q : (Fin d → ℤ) × ℤ) : Prop :=
  (vecSupport q.1 ∩ p.shortCoords).Nonempty ∧
    (vecSupport q.1 ∩ p.longCoords).Nonempty
```

Library terms: G32 `insert`; G42 `Set.Finite`.
-/

/-!
### D068 — `Piece.mixedIneqs`

`Core.lean:9612` · Used by: Lemma 25, Proposition 27 (indirectly).

```lean
noncomputable def Piece.mixedIneqs {d : ℕ} (p : Piece d) :
    Finset ((Fin d → ℤ) × ℤ) := by
  classical
  exact p.W.filter fun q => p.IsMixed q
```

Library terms: G26 `Finset.filter`.
-/

/-!
### D069 — `Piece.nLong`

`Core.lean:9617` · Used by: Proposition 27; Lemma 25 (indirectly).

```lean
def Piece.nLong {d : ℕ} (p : Piece d) : ℕ := p.longCoords.card
```

Library terms: G28 `Finset.card`.
-/

/-!
### D070 — `Piece.nMix`

`Core.lean:9619` · Used by: Proposition 27; Lemma 25 (indirectly).

```lean
noncomputable def Piece.nMix {d : ℕ} (p : Piece d) : ℕ := p.mixedIneqs.card
```

Library terms: G28 `Finset.card`.
-/

/-!
### D071 — `Piece.index`

`Core.lean:9621` · Used by: Lemma 25.

```lean
noncomputable def Piece.index {d : ℕ} (p : Piece d) : ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (d, toLex (p.nLong, p.nMix))
```

Library terms: G22 `toLex`.
-/

#check @_root_.Piece

#check @_root_.Piece.quad

#check @_root_.Piece.side

#check @_root_.Piece.minSide

/-!
## Definition 23 (`def:transition`)
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{definition}[Transitions, size and decompositions]\label{def:transition}
Let $(W,J,Q,A)$ and $(W',J',Q',A')$ be pieces of dimension $d$. A \emph{transition} from
$(W,J,Q,A)$ to $(W',J',Q',A')$ is a substitution $x=u+\Phi y$, with $u\in\Z^d$ and
$\Phi\in\Z^{d\times d}$ non-singular, such that
\[
 u+\Phi\,\cP(W')\subseteq\cP(W)\qquad\text{and}\qquad Q'(y)=Q(\Phi y).
\]
We define the size of a transition by $|\Phi|_\infty$. A \emph{decomposition} of $(W,J,Q,A)$ is a finite family of
transitions $x=u_m+\Phi_my$ from $(W,J,Q,A)$ to pieces $(W_m,J_m,Q_m,A_m)$ such that
\[
\cP(W)=\bigsqcup_m\bigl(u_m+\Phi_m\cP(W_m)\bigr).
\]
\end{definition}
```

Coverage: `direct-structure`.
-/

/-!
Conformance with the statements: Definition 23 is `IsTransition` (D072),
whose fields are the paper's conditions (`quad_eq`, for all y ∈ ℤ^d, is
equivalent to the polynomial identity, since a polynomial vanishing on ℤ^d
is zero), with size `transitionSize` (D024) = `matInftyNorm` (D023) = |Φ|∞
and decompositions `IsDecomposition` (D073), indexed by `Fin M`. Uses:
Lemma 24 composes transitions and decompositions and forms products (its
two size bounds concern integer matrices only); Lemma 25 concludes
`IsTransition p pPlus 0 1`, `IsTransition p pMinus 0 1` and
`IsDecomposition (M := 2) …` (u = 0, Φ = 1: the identity map); Lemma 26
and Proposition 27 conclude `IsDecomposition p q …` and
`transitionSize … ≤ C`. Theorem 21 uses none of these: `BalancedDecompData`
repeats det Φ_m ≠ 0, image, disjointness and union for explicit u, Φ, W′,
but has no pieces and no Q′(y) = Q(Φy) (instead Φ_mᵀ diag(c) Φ_m is
diagonal), and bounds |Φ_m|∞ by `matInftyNorm` directly.
-/

/-!
### Paper context: Transitions versus unimodular equidecompositions (`transitions`)

Non-singular means det Φ ≠ 0; unlike Definition 3, det Φ = ±1 is not
required.

Lean definitions for this comparison: `IsTransition`, `IsDecomposition`.
Statements depending on these definitions: Lemma 24, Lemma 25, Lemma 26, Proposition 27.
-/

/-!
### D072 — `IsTransition`

`Core.lean:9690` · Used by: Lemma 24, Lemma 25; Lemma 26, Proposition 27
(indirectly).

```lean
structure IsTransition {d : ℕ} (p p' : Piece d) (u : Fin d → ℤ)
    (Φ : Matrix (Fin d) (Fin d) ℤ) : Prop where
  det_ne_zero : Φ.det ≠ 0
  image_subset : pieceAffineImage u Φ (polyPZ d p'.W) ⊆ polyPZ d p.W
  quad_eq : ∀ y : Fin d → ℤ, p'.quad y = p.quad (Φ *ᵥ y)
```

Library terms: G62 `Matrix.det`; G63 `Matrix.mulVec`.
-/

/-!
### D073 — `IsDecomposition`

`Core.lean:9700` · Used by: Lemma 24, Lemma 25, Lemma 26, Proposition 27.

```lean
structure IsDecomposition {d M : ℕ} (p : Piece d) (q : Fin M → Piece d)
    (u : Fin M → Fin d → ℤ) (Φ : Fin M → Matrix (Fin d) (Fin d) ℤ) : Prop where
  transitions : ∀ m, IsTransition p (q m) (u m) (Φ m)
  pieces_disjoint : ∀ m m' : Fin M, m ≠ m' →
    Disjoint (pieceAffineImage (u m) (Φ m) (polyPZ d (q m).W))
      (pieceAffineImage (u m') (Φ m') (polyPZ d (q m').W))
  iUnion_eq : polyPZ d p.W =
    ⋃ m : Fin M, pieceAffineImage (u m) (Φ m) (polyPZ d (q m).W)
```

Library terms: G38 `⋃ i, S i`; G39 `Disjoint`.
-/

#check @_root_.IsTransition

#check @_root_.transitionSize

#check @_root_.IsDecomposition

/-!
## Lemma 24 (`lem:compose`)
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{lemma}[Composing and multiplying transitions]\label{lem:compose}
The following holds true:
\begin{enumerate}
\item If $x=u+\Phi y$ is a transition from $(W,J,Q,A)$ to $(W',J',Q',A')$ and $y=v+\Psi z$ is one
from $(W',J',Q',A')$ to $(W'',J'',Q'',A'')$, then $x=(u+\Phi v)+\Phi\Psi z$ is a transition from
$(W,J,Q,A)$ to $(W'',J'',Q'',A'')$ of size at most $d\,|\Phi|_\infty|\Psi|_\infty$. Consequently, a
decomposition of a piece, followed by decompositions of each of the resulting pieces, gives a
valid decomposition of the original piece.
\item If $(W_i,J_i,Q_i,A_i)$ is a piece of dimension $d_i$ for $i=1,2$, then
$(W_1\oplus W_2,\,J_1\times J_2,\,Q_1\oplus Q_2,\,A_1+A_2)$ is a piece of dimension $d_1+d_2$, where
$W_1\oplus W_2$ is the union of $W_1$ and $W_2$ with the vectors $w$ padded with zeros and
$(Q_1\oplus Q_2)(y_1,y_2)=Q_1(y_1)+Q_2(y_2)$. Transitions from $P_i := (W_i,J_i,Q_i,A_i)$ to
$P'_i := (W'_i,J'_i,Q'_i,A'_i)$, $i=1,2$, combine coordinatewise into a transition from the product of 
$P_1$ and $P_2$ to the product of $P_1'$ and $P_2'$. Consequently, decompositions of two lower-dimensional 
pieces combine into a decomposition of their product.
\end{enumerate}
\end{lemma}
```

Coverage: `decomposition-component`.
-/

/-!
### Paper context: Products, zero padding, and composition indices (`products`)

`Piece.prod` (written `p₁.prod p₂`) witnesses that (W₁⊕W₂, J₁×J₂, Q₁⊕Q₂,
A₁+A₂) is a piece (Lemma 24(2)). Core.lean's block projections `leftPart`,
`rightPart` (Core.lean:9909, 9912) occur only in auxiliary lemmas and
proofs and are not shown. `sigmaPieceIndexEquiv` is only an indexing
device. `lemma24` omits the size bound d|Φ|∞|Ψ|∞ for Φ_mΨ_{m,n}, which
follows from `lemma24CompositionSizeBound`; `lemma24ProductSizeBound` is
not in the paper.

Lean definitions for this comparison: `padLeftVec`, `padRightVec`, `oplusConstraints`, `blockDiagMat`, `Piece.prod`, `sigmaPieceIndexEquiv`.
Statements depending on these definitions: Lemma 24.
-/

/-!
### D074 — `padLeftVec`

`Core.lean:9896` · Used by: Lemma 24 (indirectly).

```lean
def padLeftVec (d₁ d₂ : ℕ) (w : Fin d₁ → ℤ) : Fin (d₁ + d₂) → ℤ :=
  Fin.append w 0
```

Library terms: G19 `Fin.append`.
-/

/-!
### D075 — `padRightVec`

`Core.lean:9899` · Used by: Lemma 24 (indirectly).

```lean
def padRightVec (d₁ d₂ : ℕ) (w : Fin d₂ → ℤ) : Fin (d₁ + d₂) → ℤ :=
  Fin.append 0 w
```

Library terms: G19 `Fin.append`.
-/

/-!
### D076 — `oplusConstraints`

`Core.lean:9902` · Used by: Lemma 24 (indirectly).

```lean
noncomputable def oplusConstraints (d₁ d₂ : ℕ)
    (W₁ : Finset ((Fin d₁ → ℤ) × ℤ)) (W₂ : Finset ((Fin d₂ → ℤ) × ℤ)) :
    Finset ((Fin (d₁ + d₂) → ℤ) × ℤ) := by
  classical
  exact W₁.image (fun p => (padLeftVec d₁ d₂ p.1, p.2)) ∪
    W₂.image (fun p => (padRightVec d₁ d₂ p.1, p.2))
```

Library terms: G27 `Finset.image`; G32 `insert`.
-/

/-!
### D077 — `blockDiagMat`

`Core.lean:9915` · Used by: Lemma 24.

```lean
def blockDiagMat {d₁ d₂ : ℕ} (Φ₁ : Matrix (Fin d₁) (Fin d₁) ℤ)
    (Φ₂ : Matrix (Fin d₂) (Fin d₂) ℤ) :
    Matrix (Fin (d₁ + d₂)) (Fin (d₁ + d₂)) ℤ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks Φ₁ 0 0 Φ₂)
```

Library terms: G20 `finSumFinEquiv`; G66 `Matrix.fromBlocks`.
-/

/-!
### D078 — `Piece.prod`

`Core.lean:9973` · Used by: Lemma 24.

```lean
noncomputable def Piece.prod {d₁ d₂ : ℕ} (p : Piece d₁) (p' : Piece d₂) :
    Piece (d₁ + d₂) where
  W := oplusConstraints d₁ d₂ p.W p'.W
  lo := Fin.append p.lo p'.lo
  hi := Fin.append p.hi p'.hi
  gamma := Fin.append p.gamma p'.gamma
  A := p.A + p'.A
  one_le_dim := by have := p.one_le_dim; omega
  one_le_gamma := by
    rw [Fin.forall_fin_add]
    simpa using And.intro p.one_le_gamma p'.one_le_gamma
  one_le_A := by have := p.one_le_A; omega
  poly_subset_box := by
    intro x hx
    rw [polyPZ_oplusConstraints] at hx
    exact (mem_boxZ_append _ _ _ _ _ _ _).2
      ⟨p.poly_subset_box hx.1, p'.poly_subset_box hx.2⟩
  dim_le_A := add_le_add p.dim_le_A p'.dim_le_A
  rho_le_A := (constraintRho_oplusConstraints_le _ _ _ _).trans
    (add_le_add p.rho_le_A p'.rho_le_A)
  gamma_le_A := by
    rw [Fin.forall_fin_add]
    constructor
    · intro j
      simpa using (p.gamma_le_A j).trans (Nat.le_add_right _ _)
    · intro j
      simpa using (p'.gamma_le_A j).trans (Nat.le_add_left _ _)
```

Library terms: G19 `Fin.append`.
-/

/-!
### D079 — `sigmaPieceIndexEquiv`

`Core.lean:9795` · Used by: Lemma 24.

```lean
def sigmaPieceIndexEquiv {M : ℕ} (N : Fin M → ℕ) :
    ((m : Fin M) × Fin (N m)) ≃ Fin (∑ m, N m) :=
  finSigmaFinEquiv
```

Library terms: G20 `finSumFinEquiv`; G21 `Equiv`.
-/

/-!
Definitions used: `boxZ` (D010), `constraintRho` (D057), `polyPZ` (D007),
`Piece` (D061), `pieceAffineImage` (D022), `Piece.quad` (D062), `IsTransition`
(D072), `IsDecomposition` (D073), `sigmaPieceIndexEquiv` (D079). Library terms:
G21 `Equiv`; G63 `Matrix.mulVec`.
-/
theorem lemma24 :
  ∀ {d M : ℕ} {p : Piece d} {q : Fin M → Piece d}
    {u : Fin M → Fin d → ℤ} {Φ : Fin M → Matrix (Fin d) (Fin d) ℤ}
    (h : IsDecomposition p q u Φ)
    (N : Fin M → ℕ) (q' : (m : Fin M) → Fin (N m) → Piece d)
    (v : (m : Fin M) → Fin (N m) → Fin d → ℤ)
    (Ψ : (m : Fin M) → Fin (N m) → Matrix (Fin d) (Fin d) ℤ)
    (h' : ∀ m, IsDecomposition (q m) (q' m) (v m) (Ψ m)),
IsDecomposition (M := ∑ m, N m) p
      (fun t =>
        q' ((sigmaPieceIndexEquiv N).symm t).1 ((sigmaPieceIndexEquiv N).symm t).2)
      (fun t =>
        u ((sigmaPieceIndexEquiv N).symm t).1 +
          Φ ((sigmaPieceIndexEquiv N).symm t).1 *ᵥ
            v ((sigmaPieceIndexEquiv N).symm t).1 ((sigmaPieceIndexEquiv N).symm t).2)
      (fun t =>
        Φ ((sigmaPieceIndexEquiv N).symm t).1 *
          Ψ ((sigmaPieceIndexEquiv N).symm t).1 ((sigmaPieceIndexEquiv N).symm t).2) :=
  @_root_.IsDecomposition.comp

/-!
Definitions used: `boxZ` (D010), `constraintRho` (D057), `polyPZ` (D007),
`Piece` (D061), `Piece.quad` (D062), `pieceAffineImage` (D022), `IsTransition`
(D072), `matInftyNorm` (D023), `transitionSize` (D024). Library terms: G63
`Matrix.mulVec`.
-/
theorem lemma24TransitionComposition :
  ∀ {d : ℕ} {p p' p'' : Piece d} {u v : Fin d → ℤ}
    {Φ Ψ : Matrix (Fin d) (Fin d) ℤ}
    (h : IsTransition p p' u Φ) (h' : IsTransition p' p'' v Ψ),
IsTransition p p'' (u + Φ *ᵥ v) (Φ * Ψ) ∧
      transitionSize (Φ * Ψ) ≤ d * transitionSize Φ * transitionSize Ψ :=
  @_root_.IsTransition.comp

/-!
Definitions used: `matInftyNorm` (D023), `transitionSize` (D024).
-/
theorem lemma24CompositionSizeBound :
  ∀ {d : ℕ} (Φ Ψ : Matrix (Fin d) (Fin d) ℤ),
transitionSize (Φ * Ψ) ≤ d * transitionSize Φ * transitionSize Ψ :=
  @_root_.transitionSize_mul_le

/-!
Definitions used: `boxZ` (D010), `constraintRho` (D057), `polyPZ` (D007),
`Piece` (D061), `Piece.quad` (D062), `pieceAffineImage` (D022), `IsTransition`
(D072), `blockDiagMat` (D077), `padLeftVec` (D074), `padRightVec` (D075),
`oplusConstraints` (D076), `Piece.prod` (D078). Library terms: G19 `Fin.append`.
-/
theorem lemma24TransitionProduct :
  ∀ {d₁ d₂ : ℕ}
    {p₁ p₁' : Piece d₁} {p₂ p₂' : Piece d₂}
    {u₁ : Fin d₁ → ℤ} {u₂ : Fin d₂ → ℤ}
    {Φ₁ : Matrix (Fin d₁) (Fin d₁) ℤ} {Φ₂ : Matrix (Fin d₂) (Fin d₂) ℤ}
    (h₁ : IsTransition p₁ p₁' u₁ Φ₁) (h₂ : IsTransition p₂ p₂' u₂ Φ₂),
IsTransition (p₁.prod p₂) (p₁'.prod p₂') (Fin.append u₁ u₂)
      (blockDiagMat Φ₁ Φ₂) :=
  @_root_.IsTransition.prod

/-!
Definitions used: `boxZ` (D010), `constraintRho` (D057), `polyPZ` (D007),
`Piece` (D061), `pieceAffineImage` (D022), `Piece.quad` (D062), `IsTransition`
(D072), `IsDecomposition` (D073), `blockDiagMat` (D077), `padLeftVec` (D074),
`padRightVec` (D075), `oplusConstraints` (D076), `Piece.prod` (D078). Library
terms: G19 `Fin.append`; G20 `finSumFinEquiv`; G21 `Equiv`.
-/
theorem lemma24DecompositionProduct :
  ∀ {d₁ d₂ M₁ M₂ : ℕ} {p₁ : Piece d₁} {p₂ : Piece d₂}
    {q₁ : Fin M₁ → Piece d₁} {q₂ : Fin M₂ → Piece d₂}
    {u₁ : Fin M₁ → Fin d₁ → ℤ} {u₂ : Fin M₂ → Fin d₂ → ℤ}
    {Φ₁ : Fin M₁ → Matrix (Fin d₁) (Fin d₁) ℤ}
    {Φ₂ : Fin M₂ → Matrix (Fin d₂) (Fin d₂) ℤ}
    (h₁ : IsDecomposition p₁ q₁ u₁ Φ₁) (h₂ : IsDecomposition p₂ q₂ u₂ Φ₂),
IsDecomposition (M := M₁ * M₂) (p₁.prod p₂)
      (fun t =>
        (q₁ (finProdFinEquiv.symm t).1).prod (q₂ (finProdFinEquiv.symm t).2))
      (fun t =>
        Fin.append (u₁ (finProdFinEquiv.symm t).1) (u₂ (finProdFinEquiv.symm t).2))
      (fun t =>
        blockDiagMat (Φ₁ (finProdFinEquiv.symm t).1)
          (Φ₂ (finProdFinEquiv.symm t).2)) :=
  @_root_.IsDecomposition.prod

/-!
Definitions used: `matInftyNorm` (D023), `transitionSize` (D024), `blockDiagMat`
(D077).
-/
theorem lemma24ProductSizeBound :
  ∀ {d₁ d₂ : ℕ}
    (Φ₁ : Matrix (Fin d₁) (Fin d₁) ℤ)
    (Φ₂ : Matrix (Fin d₂) (Fin d₂) ℤ),
transitionSize (blockDiagMat Φ₁ Φ₂) ≤
      max (transitionSize Φ₁) (transitionSize Φ₂) :=
  @_root_.transitionSize_blockDiagMat_le

/-!
## Lemma 25 (`lem:split`)
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{lemma}[Splitting along a mixed inequality]\label{lem:split}
Let $(W,J,Q,A)$ be a piece of index $(d,n_{\mathrm{long}},n_{\mathrm{mix}})$ with $B$ the set of 
short coordinates, and let $(w,b)\in W$ be mixed. Write $w=w_B+w_{B^c}$, 
where $w_B$ is obtained from $w$ by setting its entries outside $B$ to $0$,
and $w_{B^c}=w-w_B$, and let $\lambda_{w,b}=\min_{x\in J}(w_B\cdot x+b)$. Let $W^+$ be
obtained from $W$ by replacing $(w,b)$ with $(w_{B^c},\lambda_{w,b})$ and adjoining the $2d$ inequalities
$x_j\ge\min J_j$ and $x_j\le\max J_j$, and let $W^-=W\cup\{(-w_{B^c},-\lambda_{w,b}-1)\}$. Then
$(W^+,J,Q,A+2d)$ and $(W^-,J,Q,A+1)$ are pieces {with the following properties:}
\begin{enumerate}
\item The identity map gives transitions from $(W,J,Q,A)$ to $(W^+,J,Q,A+2d)$ and from $(W,J,Q,A)$ to $(W^-,J,Q,A+1)$, forming a
decomposition of $(W,J,Q,A)$;
\item The piece $(W^+,J,Q,A+2d)$ has index strictly smaller than $(d,n_{\mathrm{long}},n_{\mathrm{mix}})$;
\item We have $|w_{B^c}\cdot(x-x')|<A^2H$ for $x,x'\in\cP(W^-)$.
\end{enumerate}
\end{lemma}
```

Coverage: `decomposition-component`.
-/

/-!
### Paper context: The two split pieces and the minimum defining lambda (`split`)

`splitLambda` (via `boxMinAffine`) is total; under the nonempty-interval
hypothesis `hJ` of all Lemma 25 statements it is the paper's minimum.
“(W⁺,J,Q,A+2d) and (W⁻,J,Q,A+1) are pieces” is `lemma25PlusIsPiece`,
`lemma25MinusIsPiece` (a `Piece` with these data fields exists); `lemma25`
and `lemma25PlusIndexDecreases` take such pieces with the field equations
as hypotheses; `lemma25MinusSlabWidth` uses P(`p.splitMinusW w b`).

Lean definitions for this comparison: `restrictVec`, `coordVec`, `boxConstraints`, `Piece.shortPart`, `Piece.longPart`, `Piece.splitLambda`, `Piece.splitPlusW`, `Piece.splitMinusW`.
Statements depending on these definitions: Lemma 25.
-/

/-!
### D080 — `restrictVec`

`Core.lean:10206` · Used by: Lemma 25 (indirectly).

```lean
def restrictVec (d : ℕ) (S : Finset (Fin d)) (w : Fin d → ℤ) : Fin d → ℤ :=
  fun j => if j ∈ S then w j else 0
```
-/

/-!
### D081 — `coordVec`

`Core.lean:10241` · Used by: Lemma 25 (indirectly).

```lean
def coordVec (d : ℕ) (j : Fin d) : Fin d → ℤ := fun s => if s = j then 1 else 0
```
-/

/-!
### D082 — `boxConstraints`

`Core.lean:10243` · Used by: Lemma 25 (indirectly).

```lean
noncomputable def boxConstraints (d : ℕ) (lo hi : Fin d → ℤ) :
    Finset ((Fin d → ℤ) × ℤ) := by
  classical
  exact (Finset.univ.image fun j : Fin d => (coordVec d j, -lo j)) ∪
    (Finset.univ.image fun j : Fin d => (-coordVec d j, hi j))
```

Library terms: G27 `Finset.image`; G32 `insert`.
-/

/-!
### D083 — `Piece.shortPart`

`Core.lean:10337` · Used by: Lemma 25 (indirectly).

```lean
noncomputable def Piece.shortPart {d : ℕ} (p : Piece d) (w : Fin d → ℤ) : Fin d → ℤ :=
  restrictVec d p.shortCoords w
```
-/

/-!
### D084 — `Piece.longPart`

`Core.lean:10340` · Used by: Lemma 25.

```lean
noncomputable def Piece.longPart {d : ℕ} (p : Piece d) (w : Fin d → ℤ) : Fin d → ℤ :=
  w - p.shortPart w
```
-/

/-!
### D085 — `boxMinAffine`

`Core.lean:10300` · Used by: Lemma 25 (indirectly).

Implementation helper, no paper definition.

```lean
noncomputable def boxMinAffine (d : ℕ) (lo hi : Fin d → ℤ) (w : Fin d → ℤ) (b : ℤ) : ℤ :=
  b + ∑ j, min (w j * lo j) (w j * hi j)
```
-/

/-!
### D086 — `Piece.splitLambda`

`Core.lean:10347` · Used by: Lemma 25 (indirectly).

```lean
noncomputable def Piece.splitLambda {d : ℕ} (p : Piece d) (w : Fin d → ℤ) (b : ℤ) : ℤ :=
  boxMinAffine d p.lo p.hi (p.shortPart w) b
```
-/

/-!
### D087 — `Piece.splitPlusW`

`Core.lean:10358` · Used by: Lemma 25.

```lean
noncomputable def Piece.splitPlusW {d : ℕ} (p : Piece d) (w : Fin d → ℤ) (b : ℤ) :
    Finset ((Fin d → ℤ) × ℤ) := by
  classical
  exact insert (p.longPart w, p.splitLambda w b) (p.W.erase (w, b)) ∪
    boxConstraints d p.lo p.hi
```

Library terms: G32 `insert`.
-/

/-!
### D088 — `Piece.splitMinusW`

`Core.lean:10364` · Used by: Lemma 25.

```lean
noncomputable def Piece.splitMinusW {d : ℕ} (p : Piece d) (w : Fin d → ℤ) (b : ℤ) :
    Finset ((Fin d → ℤ) × ℤ) := by
  classical
  exact insert (-p.longPart w, -p.splitLambda w b - 1) p.W
```

Library terms: G32 `insert`.
-/

/-!
Definitions used: `polyPZ` (D007), `boxZ` (D010), `constraintRho` (D057),
`Piece` (D061), `vecSupport` (D009), `boxSide` (D011), `Piece.side` (D063),
`Piece.minSide` (D064), `Piece.shortCoords` (D065), `Piece.longCoords` (D066),
`Piece.IsMixed` (D067), `Piece.quad` (D062), `pieceAffineImage` (D022),
`IsTransition` (D072), `IsDecomposition` (D073), `coordVec` (D081),
`boxConstraints` (D082), `restrictVec` (D080), `Piece.shortPart` (D083),
`Piece.longPart` (D084), `boxMinAffine` (D085), `Piece.splitLambda` (D086),
`Piece.splitPlusW` (D087), `Piece.splitMinusW` (D088). Library terms: G23 `![a,
b, …]`; G32 `insert`; G39 `Disjoint`.
-/
theorem lemma25 :
  ∀ {d : ℕ} (p pPlus pMinus : Piece d)
    (hJ : ∀ j, p.lo j ≤ p.hi j) (w : Fin d → ℤ) (b : ℤ)
    (hmem : (w, b) ∈ p.W) (hmix : p.IsMixed (w, b))
    (hPlusW : pPlus.W = p.splitPlusW w b) (hPluslo : pPlus.lo = p.lo)
    (hPlushi : pPlus.hi = p.hi) (hPlusgamma : pPlus.gamma = p.gamma)
    (hPlusA : pPlus.A = p.A + 2 * d)
    (hMinusW : pMinus.W = p.splitMinusW w b) (hMinuslo : pMinus.lo = p.lo)
    (hMinushi : pMinus.hi = p.hi) (hMinusgamma : pMinus.gamma = p.gamma)
    (hMinusA : pMinus.A = p.A + 1),
IsTransition p pPlus 0 1 ∧ IsTransition p pMinus 0 1 ∧
      Disjoint (polyPZ d pPlus.W) (polyPZ d pMinus.W) ∧
      polyPZ d p.W = polyPZ d pPlus.W ∪ polyPZ d pMinus.W ∧
      IsDecomposition (M := 2) p ![pPlus, pMinus] (fun _ => 0) (fun _ => 1) :=
  @_root_.Piece.split_identity_decomposition

/-!
Definitions used: `boxZ` (D010), `constraintRho` (D057), `polyPZ` (D007),
`Piece` (D061), `vecSupport` (D009), `boxSide` (D011), `Piece.side` (D063),
`Piece.minSide` (D064), `Piece.shortCoords` (D065), `Piece.longCoords` (D066),
`Piece.IsMixed` (D067), `coordVec` (D081), `boxConstraints` (D082),
`restrictVec` (D080), `Piece.shortPart` (D083), `Piece.longPart` (D084),
`boxMinAffine` (D085), `Piece.splitLambda` (D086), `Piece.splitPlusW` (D087).
-/
theorem lemma25PlusIsPiece :
  ∀ {d : ℕ} (p : Piece d) (hJ : ∀ j, p.lo j ≤ p.hi j)
    (w : Fin d → ℤ) (b : ℤ) (hmem : (w, b) ∈ p.W) (hmix : p.IsMixed (w, b)),
∃ p' : Piece d, p'.W = p.splitPlusW w b ∧ p'.lo = p.lo ∧ p'.hi = p.hi ∧
      p'.gamma = p.gamma ∧ p'.A = p.A + 2 * d :=
  @_root_.Piece.splitPlus_isPiece

/-!
Definitions used: `boxZ` (D010), `constraintRho` (D057), `polyPZ` (D007),
`Piece` (D061), `vecSupport` (D009), `boxSide` (D011), `Piece.side` (D063),
`Piece.minSide` (D064), `Piece.shortCoords` (D065), `Piece.longCoords` (D066),
`Piece.IsMixed` (D067), `restrictVec` (D080), `Piece.shortPart` (D083),
`Piece.longPart` (D084), `boxMinAffine` (D085), `Piece.splitLambda` (D086),
`Piece.splitMinusW` (D088).
-/
theorem lemma25MinusIsPiece :
  ∀ {d : ℕ} (p : Piece d) (hJ : ∀ j, p.lo j ≤ p.hi j)
    (w : Fin d → ℤ) (b : ℤ) (hmem : (w, b) ∈ p.W) (hmix : p.IsMixed (w, b)),
∃ p' : Piece d, p'.W = p.splitMinusW w b ∧ p'.lo = p.lo ∧ p'.hi = p.hi ∧
      p'.gamma = p.gamma ∧ p'.A = p.A + 1 :=
  @_root_.Piece.splitMinus_isPiece

/-!
Definitions used: `boxZ` (D010), `constraintRho` (D057), `polyPZ` (D007),
`Piece` (D061), `vecSupport` (D009), `boxSide` (D011), `Piece.side` (D063),
`Piece.minSide` (D064), `Piece.shortCoords` (D065), `Piece.longCoords` (D066),
`Piece.IsMixed` (D067), `Piece.mixedIneqs` (D068), `Piece.nLong` (D069),
`Piece.nMix` (D070), `Piece.index` (D071), `coordVec` (D081), `boxConstraints`
(D082), `restrictVec` (D080), `Piece.shortPart` (D083), `Piece.longPart` (D084),
`boxMinAffine` (D085), `Piece.splitLambda` (D086), `Piece.splitPlusW` (D087).
-/
theorem lemma25PlusIndexDecreases :
  ∀ {d : ℕ} (p pPlus : Piece d)
    (hJ : ∀ j, p.lo j ≤ p.hi j) (w : Fin d → ℤ) (b : ℤ)
    (hmem : (w, b) ∈ p.W) (hmix : p.IsMixed (w, b))
    (hPlusW : pPlus.W = p.splitPlusW w b) (hlo : pPlus.lo = p.lo) (hhi : pPlus.hi = p.hi)
    (hgamma : pPlus.gamma = p.gamma) (hA : pPlus.A = p.A + 2 * d),
pPlus.index < p.index :=
  @_root_.Piece.splitPlus_index_lt

/-!
Definitions used: `polyPZ` (D007), `boxZ` (D010), `constraintRho` (D057),
`Piece` (D061), `boxSide` (D011), `Piece.side` (D063), `Piece.minSide` (D064),
`vecSupport` (D009), `Piece.shortCoords` (D065), `Piece.longCoords` (D066),
`Piece.IsMixed` (D067), `restrictVec` (D080), `Piece.shortPart` (D083),
`Piece.longPart` (D084), `boxMinAffine` (D085), `Piece.splitLambda` (D086),
`Piece.splitMinusW` (D088).
-/
theorem lemma25MinusSlabWidth :
  ∀ {d : ℕ} (p : Piece d)
    (hJ : ∀ j, p.lo j ≤ p.hi j) (w : Fin d → ℤ) (b : ℤ)
    (hmem : (w, b) ∈ p.W) (hmix : p.IsMixed (w, b))
    (x x' : Fin d → ℤ) (hx : x ∈ polyPZ d (p.splitMinusW w b))
    (hx' : x' ∈ polyPZ d (p.splitMinusW w b)),
|∑ j, p.longPart w j * (x j - x' j)| < (p.A : ℤ) ^ 2 * (p.minSide : ℤ) :=
  @_root_.Piece.splitMinus_longPart_variation_lt

/-!
## Lemma 26 (`lem:short-coordinate`)
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{lemma}[A short linear combination as a coordinate]\label{lem:short-coordinate}
Let $(W,J,Q,R)$ be a piece of dimension $d$, let $H$ be an integer with $1\le H\le\min_j\#J_j$, and let
$a\in\Z^d\setminus\{0\}$ satisfy $|a|_1\le R$ and $|a\cdot(x-x')|\le RH$ for $x,x'\in\cP(W)$.
Choose $q\in\supp a$ with largest $\#J_q$. Then there exist a set $U\subset\Z^d$ with $\# U\ll_R 1$ and a matrix
$D\in\Z^{d\times d}$ such that the transitions $x=u+Dy$, $u\in U$, give a
decomposition of $(W,J,Q,R)$ into pieces $(W'_u,J'_u,Q',R')$ with $R'\ll_R1$ and
\[
 \#J'_{u,q}=H,\qquad \#J_j\le\#J'_{u,j}\le3\#J_j\ (j\ne q) \quad \text{and} \quad J'_{u,j}=J_j\ (j\notin\supp a).
\]
\end{lemma}
```

Coverage: `direct-strengthened`.
-/

/-!
### Paper context: The common new complexity parameter (`common_bound`)

The outputs' common Q′ and R′ are encoded by equal `(q m).gamma` and
`(q m).A = R'`. C is chosen before d, p, H, a, qc, so depends only on R.
Stronger than the paper: the input needs only `p.A ≤ R` (paper: A = R);
the conclusion holds for every qc ∈ supp a of maximal side (paper: “choose
q”); `transitionSize D ≤ C` is added (the paper's proof gives |D|∞ ≪_R 1).
The paper's translations form a *set* U ⊂ ℤ^d, one piece per u ∈ U; that the
`Fin M`-indexed family `U : Fin M → Fin d → ℤ` enumerates such a set without
repetition is the conjunct `Function.Injective U`, so no translation is used
twice and M is the size of the paper's U. Form only: `∀ j, p.lo j ≤ p.hi j`
follows from 1 ≤ H ≤ `p.minSide`; if P(W) = ∅, M = 0 satisfies the conclusion,
as for the paper's decompositions.
-/

/-!
Definitions used: `vecSupport` (D009), `polyPZ` (D007), `boxZ` (D010),
`constraintRho` (D057), `Piece` (D061), `boxSide` (D011), `Piece.side` (D063),
`Piece.minSide` (D064), `matInftyNorm` (D023), `transitionSize` (D024),
`pieceAffineImage` (D022), `Piece.quad` (D062), `IsTransition` (D072),
`IsDecomposition` (D073).
-/
theorem lemma26 :
  ∀ (R : ℕ) (hR : 1 ≤ R),
∃ C : ℕ, 1 ≤ C ∧
      ∀ (d : ℕ) (p : Piece d), p.A ≤ R → (∀ j, p.lo j ≤ p.hi j) →
        ∀ H : ℕ, 1 ≤ H → H ≤ p.minSide →
          ∀ a : Fin d → ℤ, a ≠ 0 → (∑ j, |a j|) ≤ (R : ℤ) →
            (∀ x ∈ polyPZ d p.W, ∀ x' ∈ polyPZ d p.W,
              |∑ j, a j * (x j - x' j)| ≤ (R : ℤ) * (H : ℤ)) →
            ∀ qc : Fin d, qc ∈ vecSupport a →
              (∀ j ∈ vecSupport a, p.side j ≤ p.side qc) →
              ∃ (M : ℕ) (U : Fin M → Fin d → ℤ) (D : Matrix (Fin d) (Fin d) ℤ)
                (q : Fin M → Piece d) (R' : ℕ),
                M ≤ C ∧
                R' ≤ C ∧
                IsDecomposition p q U (fun _ => D) ∧
                Function.Injective U ∧
                transitionSize D ≤ C ∧
                (∀ m, (q m).A = R') ∧
                (∀ m m', (q m).gamma = (q m').gamma) ∧
                (∀ m, (q m).side qc = H) ∧
                (∀ (m : Fin M) (j : Fin d), j ≠ qc →
                  p.side j ≤ (q m).side j ∧ (q m).side j ≤ 3 * p.side j) ∧
                ∀ (m : Fin M) (j : Fin d), j ∉ vecSupport a →
                  (q m).lo j = p.lo j ∧ (q m).hi j = p.hi j :=
  @_root_.lem_short_coordinate

/-!
## Proposition 27 (`prop:pieces`)
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{proposition}\label{prop:pieces}
For all $d,n_{\mathrm{long}},n_{\mathrm{mix}},A$ there is $C=C(d,n_{\mathrm{long}},n_{\mathrm{mix}},A)$ such that every piece $(W,J,Q,A)$ of
index $(d,n_{\mathrm{long}},n_{\mathrm{mix}})$ has a decomposition by at most $C$ transitions
$x=u_m+\Phi_my$ of size at most $C$ to pieces $(W_m,J_m,Q_m,A_m)$ with $A_m\le C$,
$\vol(J_m)\le C\vol(J)$ and $J_m$ $C$-balanced with respect to $W_m$.
\end{proposition}
```

Coverage: `direct`.

Reading note: Lean adds `∀ j, p.lo j ≤ p.hi j` (the paper is silent);
harmless, since otherwise J and P(W) are empty and M = 0 works, and the
paper's proof of Theorem 21 applies Proposition 27 to the nonempty box I.
The conclusion `IsBalancedWrt d C (q m).W …` also requires nonzero normals
in each W_m (presupposed by Definition 20); this can be arranged, as a
constraint (0,b) is vacuous if b ≥ 0 and empties P(W_m) if b < 0, so it can
be deleted or the piece dropped.
-/

/-!
Definitions used: `boxSide` (D011), `boxVol` (D012), `constraintGraph` (D058),
`IsBalancedWrt` (D059), `boxZ` (D010), `constraintRho` (D057), `polyPZ` (D007),
`Piece` (D061), `vecSupport` (D009), `Piece.side` (D063), `Piece.minSide`
(D064), `Piece.shortCoords` (D065), `Piece.longCoords` (D066), `Piece.IsMixed`
(D067), `Piece.mixedIneqs` (D068), `Piece.nLong` (D069), `Piece.nMix` (D070),
`matInftyNorm` (D023), `transitionSize` (D024), `pieceAffineImage` (D022),
`Piece.quad` (D062), `IsTransition` (D072), `IsDecomposition` (D073).
-/
theorem proposition27 :
  ∀ (d nlong nmix A : ℕ),
∃ C : ℕ, 1 ≤ C ∧
      ∀ p : Piece d, p.A = A → p.nLong = nlong → p.nMix = nmix →
        (∀ j, p.lo j ≤ p.hi j) →
        ∃ (M : ℕ) (q : Fin M → Piece d) (u : Fin M → Fin d → ℤ)
          (Φ : Fin M → Matrix (Fin d) (Fin d) ℤ),
          M ≤ C ∧
          IsDecomposition p q u Φ ∧
          (∀ m, transitionSize (Φ m) ≤ C) ∧
          (∀ m, (q m).A ≤ C) ∧
          (∀ m, boxVol d (q m).lo (q m).hi ≤ C * boxVol d p.lo p.hi) ∧
          ∀ m, IsBalancedWrt d C (q m).W (q m).lo (q m).hi :=
  @_root_.prop_pieces

/-!
## Proposition 28 (`prop:fold`)
-/

/-!
### Paper context: The fold's source pieces, target pieces, map, and inverse (`fold`)

The paper omits out-of-bounds coordinate expressions and empty blocks;
`foldCoord` is a one-based lookup into `Fin k`, zero outside the range.
`foldMapGlobal` picks a piece when one exists and is 0 otherwise; the
theorem's hypotheses, not this default, identify it with the paper's map.

Original paper definition/context (`article.txt:2125-2180`, verbatim TeX):
```tex
We now construct  an explicit $\aff_k(\Z)$-equidecomposition of $\cS_{k,N}$ and $\{0,1,\ldots,N/k\} \times \cS_{k-1,N}$.
Set $\Phi_{1,N} = \text{Id}$.  For $k\geq2${, $N\geq0$ with $k\mid N$,} and ${1\leq m\leq k}$, define
\begin{align}
\C_{k,N,m}=\left\{x\in{\cS_{k,N}}:
 \sum_{\nu=1}^{i}x_\nu>\frac{iN}{k}\ (1\leq i<m),
 \quad
 \sum_{\nu=1}^{m}x_\nu\leq\frac{mN}{k}\right\}.
\label{eq:sourcePieces}
\end{align}
These are disjoint $\Z$-polytopes {that produce a partition of}
${\cS_{k,N}}$. {In what follows, coordinate expressions or constraints containing {out-of-bounds} variables should be omitted in their entirety. Coordinate blocks with empty index ranges should also be omitted.} For $x\in\C_{k,N,m}$, define the exact map directly by
\begin{align}
\Phi_{k,N}(x)
&=
\begin{cases}
\big(x_1,x_1+x_2,x_3,\ldots,x_k\big),
& \text{if }m=1,\\[1mm]
\begin{aligned}[t]
&\left(\displaystyle\sum_{\nu=1}^{m}x_\nu
-\frac{(m-1)N}{k},
x_m,x_{m-1},\ldots,x_3,\right.\\[-1mm]
&\quad \quad \left.x_1-\frac Nk-1,
x_2+x_{m+1}+\frac Nk+1,x_{m+2},\ldots,x_k\right),
\end{aligned}
& \text{if }2\leq m \leq k.
\end{cases}
\label{eq:fold}
\end{align}
It is now clear that $\Phi_{k,N}(\cS_{k,N}) \subset \{0,1,\ldots,N/k\} \times \cS_{k-1,N}$ and that $\Phi_{k,N}$ is piecewise affine, with integer matrices and translations. We now describe its inverse. Let
{
\begin{align}
\D_{k,N,m}=\bigg\{y\in\{0,1,\ldots,N/k\}\times\cS_{k-1,N}:{}&
 \sum_{\nu=2}^{i+1}y_\nu<y_1+\frac{(i-1)N}{k}\ (1\leq i<m),
 \nonumber\\[-1mm]
&\sum_{\nu=2}^{m+1}y_\nu\geq y_1+\frac{(m-1)N}{k}  (m<k) \bigg\},
\label{eq:targetPieces}
\end{align}
for $m=1,\ldots,k$. We claim that $\Phi_{k,N}({\C_{k,N,m}}) = \D_{k,N,m}$ for each $m$ and that
\begin{align}
\Phi_{k,N}^{-1}(y)
&=
\begin{cases}
\big(y_1,y_2-y_1,y_3,\ldots,y_k\big),
& \text{if }m=1,\\[1mm]
\begin{aligned}[t]
&\Big(
y_m+\frac Nk+1,
y_1+\frac{(m-2)N}{k}-1-\sum_{\nu=2}^{m}y_\nu,
y_{m-1},\ldots,y_2,\\
& \quad \quad \sum_{\nu=2}^{m+1}y_\nu-y_1-\frac{(m-1)N}{k},
y_{m+2},\ldots,y_k\Big),
\end{aligned}
& \text{if }2\leq m \leq k.
\end{cases}
\label{eq:foldInverse}
\end{align}
```

Lean definitions for this comparison: `foldPrefixSum`, `foldSourcePiece`, `foldCoord`, `foldMap`, `foldMapGlobal`, `foldTargetBase`, `foldTargetPiece`, `foldInv`.
Statements depending on these definitions: Proposition 28.
-/

/-!
### D089 — `foldPrefixSum`

`Core.lean:14881` · Used by: Proposition 28 (indirectly).

```lean
def foldPrefixSum (k : ℕ) (x : Fin k → ℕ) (i : ℕ) : ℕ :=
  ∑ ν ∈ Finset.univ.filter (fun ν : Fin k => ν.val < i), x ν
```

Library terms: G15 `x.val`; G26 `Finset.filter`.
-/

/-!
### D090 — `foldSourcePiece`

`Core.lean:14887` · Used by: Proposition 28.

```lean
noncomputable def foldSourcePiece (k N m : ℕ) : Finset (Fin k → ℕ) := by
  classical
  exact (simplexS k N).filter fun x =>
    (∀ i ∈ Finset.Ico 1 m, i * N < k * foldPrefixSum k x i) ∧
      k * foldPrefixSum k x m ≤ m * N
```

Library terms: G25 `Finset.Icc`; G26 `Finset.filter`.
-/

/-!
### D091 — `foldCoord`

`Core.lean:14981` · Used by: Proposition 28 (indirectly).

```lean
def foldCoord {k : ℕ} (x : Fin k → ℤ) (i : ℕ) : ℤ :=
  if h : 1 ≤ i ∧ i ≤ k then x ⟨i - 1, by omega⟩ else 0
```
-/

/-!
### D092 — `foldMap`

`Core.lean:14984` · Used by: Proposition 28.

```lean
def foldMap (k N m : ℕ) (x : Fin k → ℤ) : Fin k → ℤ := fun t =>
  let j := t.val + 1
  let q : ℤ := ((N / k : ℕ) : ℤ)
  if m = 1 then
    (if j = 2 then foldCoord x 1 + foldCoord x 2 else foldCoord x j)
  else if j = 1 then (∑ ν ∈ Finset.Icc 1 m, foldCoord x ν) - ((m : ℤ) - 1) * q
  else if j < m then foldCoord x (m + 2 - j)
  else if j = m then foldCoord x 1 - q - 1
  else if j = m + 1 then foldCoord x 2 + foldCoord x (m + 1) + q + 1
  else foldCoord x j
```

Library terms: G15 `x.val`; G25 `Finset.Icc`.
-/

/-!
### D093 — `foldMapGlobal`

`Core.lean:14995` · Used by: Proposition 28.

```lean
noncomputable def foldMapGlobal (k N : ℕ) (x : Fin k → ℕ) : Fin k → ℤ := by
  classical
  exact
    if h : ∃ m, 1 ≤ m ∧ m ≤ k ∧ x ∈ foldSourcePiece k N m then
      foldMap k N (Nat.find h) (fun t => (x t : ℤ))
    else 0
```

Library terms: G44 `Nat.find`.
-/

/-!
### D094 — `foldTargetBase`

`Core.lean:15002` · Used by: Proposition 28.

```lean
def foldTargetBase (k N : ℕ) : Set (Fin k → ℤ) :=
  {y | (∀ t, 0 ≤ y t) ∧ foldCoord y 1 ≤ ((N / k : ℕ) : ℤ) ∧
    ∑ j ∈ Finset.Icc 2 k, foldCoord y j ≤ (N : ℤ)}
```

Library terms: G25 `Finset.Icc`.
-/

/-!
### D095 — `foldTargetPiece`

`Core.lean:15006` · Used by: Proposition 28.

```lean
def foldTargetPiece (k N m : ℕ) : Set (Fin k → ℤ) :=
  {y | y ∈ foldTargetBase k N ∧
    (∀ i ∈ Finset.Ico 1 m,
      ∑ ν ∈ Finset.Icc 2 (i + 1), foldCoord y ν <
        foldCoord y 1 + ((i : ℤ) - 1) * ((N / k : ℕ) : ℤ)) ∧
    (m < k →
      foldCoord y 1 + ((m : ℤ) - 1) * ((N / k : ℕ) : ℤ) ≤
        ∑ ν ∈ Finset.Icc 2 (m + 1), foldCoord y ν)}
```

Library terms: G25 `Finset.Icc`.
-/

/-!
### D096 — `foldInv`

`Core.lean:15015` · Used by: Proposition 28.

```lean
def foldInv (k N m : ℕ) (y : Fin k → ℤ) : Fin k → ℤ := fun t =>
  let j := t.val + 1
  let q : ℤ := ((N / k : ℕ) : ℤ)
  if m = 1 then
    (if j = 2 then foldCoord y 2 - foldCoord y 1 else foldCoord y j)
  else if j = 1 then foldCoord y m + q + 1
  else if j = 2 then
    foldCoord y 1 + ((m : ℤ) - 2) * q - 1 - ∑ ν ∈ Finset.Icc 2 m, foldCoord y ν
  else if j ≤ m then foldCoord y (m + 2 - j)
  else if j = m + 1 then
    (∑ ν ∈ Finset.Icc 2 (m + 1), foldCoord y ν) - foldCoord y 1 - ((m : ℤ) - 1) * q
  else foldCoord y j
```

Library terms: G15 `x.val`; G25 `Finset.Icc`.
-/

/-!
Paper statement (verbatim TeX):
```tex
\begin{proposition}[The fold]\label{prop:fold}
{Let $k\geq2$ and let $N\geq1$ be divisible by $k$.}
The map
\begin{align*}
 \Phi_{k,N}:\cS_{k,N}
 \longrightarrow
 \{0,1,\ldots,N/k\}\times
{\cS_{k-1,N}}
\end{align*}
induces an $\aff_k(\Z)$-equidecomposition of $\cS_{k,N}$ and $ \{0,1,\ldots,N/k\}\times \cS_{k-1,N}$ given by \eqref{eq:sourcePieces} and \eqref{eq:targetPieces} (respectively) 
of complexity bounded by ${2k+1}$.
{Its inverse is given by \eqref{eq:foldInverse}.}
\end{proposition}
```

Coverage: `direct`.

`eq:sourcePieces`, `eq:targetPieces`, `eq:foldInverse`: see the `fold` context.

Reading note: the partition of S_{k,N} into C_{k,N,1}, …, C_{k,N,k} is not
a conjunct but follows from the first one: with s_i = x_1+⋯+x_i, x ∈ C_m
needs s_m ≤ mN/k and x ∈ C_{m′} (m′ > m) needs s_m > mN/k, so the pieces
are disjoint, and s_k ≤ N = kN/k puts x in C_m for the least m with
s_m ≤ mN/k. The complexity bound is stated piece by piece (last conjunct),
not via the Definition 3 predicate: k pieces, each source and target piece
P(L) with #L ≤ 2k+1 and normals of ℓ¹-norm ≤ k, each `foldMap k N m`
affine with a 0/1 matrix of determinant ±1.
-/

/-!
### Paper context: The recursive simplex-to-box map (`fold_recursion`)

Core.lean implements U_{k,N} as `foldUN` (Core.lean:16470, totalized) with
the auxiliary `foldStage` (Core.lean:16478); neither occurs in a
`Compatibility.lean` statement, so neither is shown. The proof of
Proposition 4 (`prop_UNmap_explicit`, Core.lean:17372) takes as U N the
map x ↦ `foldUN k N` of the coordinatewise `toNat` of x, cast to ℤ
(`a4FreshUnit_a4UNU`, Core.lean:17066); `proposition4` only asserts that some U exists, and the
Theorem 5 and Proposition 10 endpoints do not name `foldUN` (see their
notes). The recursion is not part of Proposition 28.

Original paper definition/context (`article.txt:2031-2033`, verbatim TeX):
```tex
\begin{align}\label{def:UN}
U_{k,N}(x) = (l_1,  U_{k-1,N}(l_2,\ldots,l_k) ) \quad \text{if} \quad \Phi_{k,N}(x) = (l_1,l_2,\ldots,l_k).
\end{align}
```

Lean definitions for this comparison: none displayed (see above).
Statements depending on these definitions: none of the displayed theorem statements.
-/

/-!
Definitions used: `simplexS` (D027), `polyPZ` (D007), `foldPrefixSum` (D089),
`foldSourcePiece` (D090), `foldCoord` (D091), `foldMap` (D092), `foldMapGlobal`
(D093), `foldTargetBase` (D094), `foldTargetPiece` (D095), `foldInv` (D096).
Library terms: G15 `x.val`; G24 `Finset.range`; G25 `Finset.Icc`; G26
`Finset.filter`; G28 `Finset.card`; G37 `f '' S`; G40 `Set.BijOn`; G41 `∃!`; G62
`Matrix.det`; G63 `Matrix.mulVec`.
-/
theorem proposition28 :
  ∀ (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N) (hkN : k ∣ N),
(∀ m, 1 ≤ m → m ≤ k → ∀ x : Fin k → ℕ,
      x ∈ foldSourcePiece k N m ↔
        (∑ s, x s ≤ N) ∧
        (∀ i ∈ Finset.Ico 1 m,
          i * (N / k) < ∑ ν ∈ Finset.univ.filter (fun ν : Fin k => ν.val < i), x ν) ∧
        ∑ ν ∈ Finset.univ.filter (fun ν : Fin k => ν.val < m), x ν ≤ m * (N / k)) ∧
    (∀ y : Fin k → ℤ, y ∈ foldTargetBase k N ↔
      (∀ t, 0 ≤ y t) ∧ y ⟨0, by omega⟩ ≤ ((N / k : ℕ) : ℤ) ∧
        ∑ t ∈ Finset.univ.filter (fun t : Fin k => 0 < t.val), y t ≤ (N : ℤ)) ∧
    (∀ m, 1 ≤ m → m ≤ k → ∀ y : Fin k → ℤ,
      let g : ℕ → ℤ := fun i => if h : i < k then y ⟨i, h⟩ else 0
      let q : ℤ := ((N / k : ℕ) : ℤ)
      (y ∈ foldTargetPiece k N m ↔
        y ∈ foldTargetBase k N ∧
        (∀ i ∈ Finset.Ico 1 m,
          ∑ j ∈ Finset.Ico 1 (i + 1), g j < g 0 + ((i : ℤ) - 1) * q) ∧
        (m < k → g 0 + ((m : ℤ) - 1) * q ≤ ∑ j ∈ Finset.Ico 1 (m + 1), g j)) ∧
      ∀ t : Fin k,
        foldMap k N m y t =
          (if m = 1 then (if t.val = 1 then g 0 + g 1 else y t)
          else if t.val = 0 then (∑ i ∈ Finset.range m, g i) - ((m : ℤ) - 1) * q
          else if t.val < m - 1 then g (m - t.val)
          else if t.val = m - 1 then g 0 - q - 1
          else if t.val = m then g 1 + g m + q + 1
          else y t) ∧
        foldInv k N m y t =
          (if m = 1 then (if t.val = 1 then g 1 - g 0 else y t)
          else if t.val = 0 then g (m - 1) + q + 1
          else if t.val = 1 then
            g 0 + ((m : ℤ) - 2) * q - 1 - ∑ i ∈ Finset.Ico 1 m, g i
          else if t.val < m then g (m - t.val)
          else if t.val = m then
            (∑ i ∈ Finset.Ico 1 (m + 1), g i) - g 0 - ((m : ℤ) - 1) * q
          else y t)) ∧
    (∀ m, 1 ≤ m → m ≤ k →
      foldMap k N m '' ((fun x : Fin k → ℕ => fun t => (x t : ℤ)) ''
          (foldSourcePiece k N m : Set (Fin k → ℕ))) = foldTargetPiece k N m) ∧
    (∀ m, 1 ≤ m → m ≤ k → foldTargetPiece k N m ⊆ foldTargetBase k N) ∧
    (∀ y ∈ foldTargetBase k N, ∃! m, 1 ≤ m ∧ m ≤ k ∧ y ∈ foldTargetPiece k N m) ∧
    (∀ m, 1 ≤ m → m ≤ k → ∀ y ∈ foldTargetPiece k N m,
      foldInv k N m y ∈ (fun x : Fin k → ℕ => fun t => (x t : ℤ)) ''
          (foldSourcePiece k N m : Set (Fin k → ℕ)) ∧
        foldMap k N m (foldInv k N m y) = y) ∧
    (∀ m, 1 ≤ m → m ≤ k → ∀ x ∈ foldSourcePiece k N m,
      foldInv k N m (foldMap k N m (fun t => (x t : ℤ))) = fun t => (x t : ℤ)) ∧
    Set.BijOn (foldMapGlobal k N) (simplexS k N : Set (Fin k → ℕ)) (foldTargetBase k N) ∧
    (∀ m, 1 ≤ m → m ≤ k →
      (∃ L : Finset ((Fin k → ℤ) × ℤ),
        (fun x : Fin k → ℕ => fun t => (x t : ℤ)) ''
            (foldSourcePiece k N m : Set (Fin k → ℕ)) = polyPZ k L ∧
        L.card ≤ 2 * k + 1 ∧ ∀ p ∈ L, ∑ s, |p.1 s| ≤ (k : ℤ)) ∧
      (∃ L : Finset ((Fin k → ℤ) × ℤ),
        foldTargetPiece k N m = polyPZ k L ∧
        L.card ≤ 2 * k + 1 ∧ ∀ p ∈ L, ∑ s, |p.1 s| ≤ (k : ℤ)) ∧
      ∃ (A : Matrix (Fin k) (Fin k) ℤ) (c : Fin k → ℤ),
        (A.det = 1 ∨ A.det = -1) ∧ (∀ i j, A i j = 0 ∨ A i j = 1) ∧
        ∀ x : Fin k → ℤ, foldMap k N m x = A.mulVec x + c) :=
  @_root_.prop_fold

/-!
## Library glossary (Mathlib and Lean core)

Entries G15–G78: full entries for terms in theorem statements, one line for the
others. Each definition and statement above lists the entries it uses.

### G15 — `x.val` (`Fin.val`, `Subtype.val`) and the coercions `(t : ℕ)`, `(n : Fin K → ℕ)`

Meaning: For t : Fin n, `t.val` (also `t.1`, `↑t`, `(t : ℕ)`) is the number t ∈
{0, …, n−1}. For n : ↥s = {x // x ∈ s}, `n.val` (also `n.1`, `↑n`, or an
ascription such as `(n : Fin K → ℕ)`) is the underlying element and `n.property`
(`n.2`) the proof that it lies in s. Both coercions are these projections, and
both are injective.

Pinned by: structure fields `Fin.val`, `Subtype.val`; coercions `Fin.coeToNat`
and `subtypeCoe`, both v ↦ v.val; `Subtype.ext`: val a1 = val a2 → a1 = a2.

Conventions: `t.val` is 0-based (paper index t.val + 1). Arithmetic on it is in
ℕ, so `k - s.val` is truncated subtraction, though never truncated for s : Fin k
(s.val ≤ k−1).

### G16 — `Fin.last`

Meaning: `Fin.last n : Fin (n+1)` is ⟨n, _⟩, the last of the indices 0, …, n
(the argument is one less than the size). For x : Fin (k+1) → R, `x (Fin.last
k)` is the last coordinate (paper coordinate k+1).

Pinned by: `def last (n : Nat) : Fin (n + 1) := ⟨n, n.lt_succ_self⟩`;
`Fin.val_last`: (last n).1 = n.

### G18 — `Fin.init` and `Fin.snoc`

Meaning: For an (n+1)-tuple q, `Fin.init q` = (q 0, …, q (n−1)) drops the last
entry; `Fin.snoc p x` = (p 0, …, p (n−1), x) appends x at `Fin.last n`. They are
mutually inverse.

Pinned by: `Fin.init_def`: init q = fun k : Fin n ↦ q k.castSucc;
`Fin.snoc_castSucc`: snoc p x i.castSucc = p i; `Fin.snoc_last`: snoc p x (last
n) = x; `Fin.init_snoc`: init (snoc p x) = p; `Fin.snoc_init_self`: snoc (init
q) (q (last n)) = q.

Conventions: init and snoc act at the END (index n); `Fin.tail` and `Fin.cons`
at the FRONT (index 0).

### G19 — `Fin.append`, `Fin.castAdd`, `Fin.natAdd`

Meaning: `Fin.castAdd m i` has value i (first block); `Fin.natAdd n i` has value
n + i (second block). `Fin.append a b` = (a 0, …, a (m−1), b 0, …, b (n−1)): the
LEFT argument occupies the first coordinates.

Pinned by: `Fin.val_castAdd`: (castAdd m i : Nat) = i; `Fin.val_natAdd`: (natAdd
n i : Nat) = n + i; `Fin.append_left`: append u v (castAdd n i) = u i;
`Fin.append_right`: append u v (natAdd m i) = v i.

Conventions: In `Fin.castAdd d₂ j`, d₂ is the size of the block AFTER j's block;
in `Fin.natAdd d₁ j`, d₁ is the size of the block BEFORE it (the shift).

### G20 — `finSumFinEquiv`, `finProdFinEquiv`, `finSigmaFinEquiv` (and `finCongr`)

Meaning: `finSumFinEquiv`: inl i ↦ i, inr j ↦ m + j. `finProdFinEquiv`: (i, j) ↦
j + n·i (row-major, second component fastest), so its inverse is t ↦ (t / n, t %
n). `finSigmaFinEquiv`: ⟨i, j⟩ ↦ n 0 + ⋯ + n (i−1) + j (blocks Fin (n 0), Fin (n
1), … laid out consecutively). `finCongr h` keeps the value and changes only the
bound.

Pinned by: `finSumFinEquiv_apply_left`: finSumFinEquiv (Sum.inl i) = Fin.castAdd
n i; `finSumFinEquiv_apply_right`: finSumFinEquiv (Sum.inr i) = Fin.natAdd m i;
definition of `finProdFinEquiv`: toFun x := ⟨x.2 + n * x.1, _⟩, invFun x :=
(x.divNat, x.modNat); `finSigmaFinEquiv_apply`: (finSigmaFinEquiv k : ℕ) = ∑ i :
Fin k.1, n (Fin.castLE k.1.2.le i) + k.2; `finCongr_apply_coe`: (finCongr h k :
ℕ) = k.

Conventions: `Fin.divNat`, `Fin.modNat` are in Batteries (not checked), but the
inverse (t / n, t % n) is forced, since symm inverts toFun and j < n. `.1`, `.2`
of `finProdFinEquiv.symm t` are the two factors; of `(sigmaPieceIndexEquiv
N).symm t` they are the block index m and the position inside block m.

### G21 — `Equiv` (`α ≃ β`), `e.symm`, `e.trans`, `Equiv.Perm`

Meaning: e : α ≃ β is a bijection: a function α → β (applied as `e x`) with a
two-sided inverse `e.symm : β ≃ α`. `e.trans f : α ≃ γ` is x ↦ f (e x);
`Equiv.Perm α` is α ≃ α. A `def … : α ≃ β where toFun … invFun … left_inv …
right_inv …` gives both maps and proves them mutually inverse.

Pinned by: structure `Equiv` with `left_inv : LeftInverse invFun toFun`,
`right_inv : RightInverse invFun toFun`; `Equiv.trans_apply`: (f.trans g) a = g
(f a); `abbrev Equiv.Perm (α : Sort*) := Equiv α α`.

Conventions: `e.trans f` applies e FIRST (opposite to ∘). An Equiv into or out
of a subtype ↥s also carries membership proofs; the map is read off `toFun`.

### G23 — `![a, b, …]` (vector notation)

Meaning: `![a₀, a₁, …]` is the function on Fin n with 0 ↦ a₀, 1 ↦ a₁, …
(0-based): notation for nested `Matrix.vecCons a₀ (… Matrix.vecEmpty)`, with
`Matrix.vecCons h t = Fin.cons h t`. Despite the namespace it is a vector, not a
matrix.

Pinned by: `Matrix.cons_val_zero`: vecCons x u 0 = x; `Matrix.cons_val_one`:
vecCons x u 1 = u 0 (both `rfl`).

### G24 — `Finset.range`

Meaning: `Finset.range n` = {m : ℕ | m < n} = {0, …, n−1}, with n elements; `∑ i
∈ Finset.range m, g i` = g 0 + ⋯ + g (m−1).

Pinned by: `Finset.mem_range`: m ∈ range n ↔ m < n; `Finset.card_range`: #(range
n) = n.

Conventions: Starts at 0 and excludes n; `Finset.range_zero`: range 0 = ∅.

### G25 — `Finset.Icc`, `Finset.Ico`, `Finset.Ioo`, `Finset.Iic`

Meaning: Icc a b = {x | a ≤ x ≤ b}, Ico a b = {x | a ≤ x < b}, Ioo a b = {x | a
< x < b}, Iic b = {x | x ≤ b}, with x in the type of the bounds (so on ℤ, Icc a
b = [a, b] ∩ ℤ). Crossed bounds give the empty set.

Pinned by: `Finset.mem_Icc`: x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b (likewise
`Finset.mem_Ico`, `Finset.mem_Ioo`, `Finset.mem_Iic`);
`Finset.Icc_eq_empty_iff`: Icc a b = ∅ ↔ ¬a ≤ b; `Finset.Ico_eq_empty_iff`: Ico
a b = ∅ ↔ ¬a < b.

Conventions: Finset.Icc 1 k ⊆ ℕ, Finset.Icc (lo s) (hi s) ⊆ ℤ, Finset.Iic j ⊆
Fin d (= {0, …, j}; Fin compares values). Cardinalities: G28; `Fin.card_Iic`: #(Iic
b) = b + 1.

### G26 — `Finset.filter` (`s.filter p`)

Meaning: `s.filter p` (also `Finset.filter p s`) is {x ∈ s | p x}.

Pinned by: `Finset.mem_filter`: a ∈ s.filter p ↔ a ∈ s ∧ p a.

Conventions: The predicate is everything after `fun x =>` up to the enclosing
parenthesis, so `B.filter fun x => P x ∧ Q x` filters by P ∧ Q. The decidability
instance (from `classical`) does not affect the result.

### G28 — `Finset.card` (`s.card`, `#s`)

Meaning: `s.card` (`#s`) is the number of distinct elements of s.

Pinned by: definition `card s = Multiset.card s.1`; `Int.card_Icc`: #(Icc a b) =
(b + 1 - a).toNat; `Nat.card_Icc`: #(Icc a b) = b + 1 - a;
`Fintype.card_piFinset`: #(piFinset s) = ∏ i, #(s i).

Conventions: On ℤ, #(Icc a b) is b − a + 1 if a ≤ b + 1 and 0 otherwise
(`Int.toNat` sends negatives to 0); on ℕ the subtraction is truncated.

### G29 — `Finset.sup` (`s.sup f`)

Meaning: `s.sup f` = f b₁ ⊔ ⋯ ⊔ f bₙ over the elements of s, folded from ⊥. On ℕ
(⊔ = max, ⊥ = 0) it is max_{b ∈ s} f b (attained) for nonempty s, and 0 for s =
∅.

Pinned by: definition `s.sup f = s.fold (· ⊔ ·) ⊥ f`; `Finset.sup_empty`: (∅ :
Finset β).sup f = ⊥; `Finset.sup_le_iff`: s.sup f ≤ a ↔ ∀ b ∈ s, f b ≤ a;
`Finset.exists_mem_eq_sup` (linear orders): s.Nonempty → ∃ i, i ∈ s ∧ s.sup f =
f i; `Nat.bot_eq_zero`: ⊥ = 0.

Conventions: Requires a bottom element, so it is used here only with ℕ values
(integers are first converted with natAbs or toNat).

### G31 — `Finset.lcm` (`s.lcm f`)

Meaning: `s.lcm f` folds `GCDMonoid.lcm` (on ℕ: `Nat.lcm`) over the f b, b ∈ s,
starting from 1: the least common multiple.

Pinned by: definition `s.lcm f = s.fold GCDMonoid.lcm 1 f`;
`Finset.lcm_dvd_iff`: s.lcm f ∣ a ↔ ∀ b ∈ s, f b ∣ a; `lcm_eq_nat_lcm`: lcm m n
= Nat.lcm m n.

Conventions: The empty lcm is 1 (`Finset.lcm_empty`). The lcm is 0 iff some f b
= 0 (`Finset.lcm_eq_zero_iff`), which does not happen for (Finset.Icc 1 k).lcm
id.

### G32 — `insert`, `Finset.erase`, `∪`, `∩` (and `{a, b}`)

Meaning: `insert a s` is s with a added (unchanged if a ∈ s); `s.erase a` is s
with a removed (unchanged if a ∉ s); `∪`, `∩` are union and intersection, of
finsets or of sets (as in Lemma 25's `polyPZ d p.W = polyPZ d pPlus.W ∪ polyPZ d
pMinus.W`); `{a, b}` is insert a {b}.

Pinned by: `Finset.mem_insert`: a ∈ insert b s ↔ a = b ∨ a ∈ s;
`Finset.mem_erase`: a ∈ erase s b ↔ a ≠ b ∧ a ∈ s; `Finset.mem_union`: a ∈ s ∪ t
↔ a ∈ s ∨ a ∈ t (`Set.mem_union` for sets); `Finset.mem_inter`: a ∈ s₁ ∩ s₂ ↔ a
∈ s₁ ∧ a ∈ s₂; `{x, xs,*}` expands to `insert x {xs,*}`
(Init/NotationExtra.lean).

Conventions: Application binds tighter than ∪: `insert a (s.erase c) ∪ t` =
(insert a (s.erase c)) ∪ t. For constraint sets, a union imposes both families
of inequalities.

### G33 — `Fintype.piFinset`

Meaning: `Fintype.piFinset t` is the finset of all f with f i ∈ t i for every i:
for ι = Fin k the box t 0 × ⋯ × t (k−1), with ∏ i, #(t i) elements.

Pinned by: `Fintype.mem_piFinset`: f ∈ piFinset t ↔ ∀ a, f a ∈ t a;
`Fintype.card_piFinset`: #(piFinset s) = ∏ i, #(s i).

Conventions: Empty if some t i is empty. For k = 0 it is {the empty tuple}
(`Fintype.piFinset_of_isEmpty`: piFinset s = univ).

### G37 — `f '' S` (`Set.image`)

Meaning: For `S : Set α`, `f '' S : Set β` is {f x | x ∈ S}; coinciding values
merge, no injectivity is implied. A finset s is first coerced to `(s : Set α)`.

Pinned by: `Set.mem_image`: y ∈ f '' s ↔ ∃ x ∈ s, f x = y (by definition
`Set.image f s := {f a | a ∈ s}`).

Conventions: `infixr:80`; application binds tighter, so `g a b '' S` is `(g a b)
'' S`.

### G39 — `Disjoint`

Meaning: In a partial order with ⊥, `Disjoint a b` says every x with x ≤ a and x
≤ b satisfies x ≤ ⊥; for sets: no common element. Pairwise disjointness is
written `∀ i i', i ≠ i' → Disjoint (S i) (S i')`.

Pinned by: definition `Disjoint a b := ∀ ⦃x⦄, x ≤ a → x ≤ b → x ≤ ⊥`;
`Set.disjoint_iff_inter_eq_empty`: Disjoint s t ↔ s ∩ t = ∅.

Conventions: ∅ is disjoint from every set, including itself.

### G40 — `Set.BijOn`

Meaning: `Set.BijOn f s t`: f maps s into t, is injective on s, and hits every y
∈ t from s; i.e. f restricted to s is a bijection s → t. Values of f outside s
are unconstrained.

Pinned by: definition `Set.BijOn f s t := MapsTo f s t ∧ InjOn f s ∧ SurjOn f s
t` with `MapsTo f s t := ∀ ⦃x⦄, x ∈ s → f x ∈ t`, `InjOn f s := ∀ ⦃x₁⦄, x₁ ∈ s →
∀ ⦃x₂⦄, x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂`, `SurjOn f s t := t ⊆ f '' s`.

Conventions: Finsets are coerced to sets, e.g. `(simplexS k N : Set (Fin k →
ℕ))`.

### G41 — `∃!` (`ExistsUnique`)

Meaning: `∃! x, p x` holds iff some x satisfies p and every y satisfying p
equals it. It binds one variable: `∃! m, A m ∧ B m` means exactly one m
satisfies the conjunction.

Pinned by: definition `ExistsUnique p := ∃ x, p x ∧ ∀ y, p y → y = x`.

Conventions: `x ∈ P ↔ ∃! i, x ∈ S i` makes P the set of points in exactly one S
i; it forces neither S i ⊆ P nor disjointness (points in two pieces are excluded
from P). Over `Fin 0`, `∃! i, …` is false.

### G42 — `Set.Finite`, `Set.Nonempty` (and `Finset.Nonempty`)

Meaning: For `s : Set α`, `s.Finite` means ↥s is in bijection with some `Fin n`;
`s.Nonempty` (for a Set or a Finset) means ∃ x, x ∈ s. A Finset is finite by
construction.

Pinned by: `Set.Finite s := Finite s` (the subtype ↥s), with `class inductive
Finite (α) | intro {n : ℕ} : α ≃ Fin n → Finite α`; `Set.Nonempty s := ∃ x, x ∈
s`; `Finset.Nonempty s := ∃ x : α, x ∈ s`.

Conventions: ∅ is finite and not nonempty.

### G47 — `Int.sign`

Meaning: sign z = 1, 0, −1 for z > 0, z = 0, z < 0; sign z · |z| = z.

Pinned by: definition `Int.sign`: ofNat (n+1) ↦ 1, ofNat 0 ↦ 0, negSucc _ ↦ −1;
`Int.sign_mul_abs`: sign a * |a| = a.

Conventions: sign 0 = 0 (not 1). In this file the value is cast to ℂ.

### G48 — `Int.gcd`

Meaning: `Int.gcd m n` is the natural number Nat.gcd |m| |n|; Int.gcd m 0 = |m|,
Int.gcd 0 0 = 0.

Pinned by: `Int.gcd_eq_natAbs_gcd_natAbs`: gcd m n = Nat.gcd m.natAbs n.natAbs
(by rfl); `Int.isCoprime_iff_gcd_eq_one`: IsCoprime m n ↔ Int.gcd m n = 1.

Conventions: `Int.gcd a q = 1` is an equation in ℕ; signs of the arguments are
ignored.

### G49 — `a ≡ b [ZMOD n]` (`Int.ModEq`)

Meaning: Congruence modulo n: equal Euclidean remainders a % n = b % n;
equivalently n ∣ b − a.

Pinned by: definition `Int.ModEq n a b := a % n = b % n`; `Int.modEq_iff_dvd`: a
≡ b [ZMOD n] ↔ n ∣ b - a; `Int.modEq_zero_iff`: a ≡ b [ZMOD 0] ↔ a = b.

Conventions: Modulus 0 means equality; the sign of n is irrelevant
(`Int.modEq_neg`). Precedence 50: `a * abar ≡ 1 [ZMOD q]` is Int.ModEq q (a *
abar) 1. A ℕ modulus is cast: `[ZMOD (q : ℤ)]`.

### G51 — `Odd` and `Even`

Meaning: Odd n: n = 2m + 1 for some m of the same type; Even n: n = r + r for
some r. On ℤ, Odd l ↔ l % 2 = 1 (so −1 is odd); on ℕ, Even L ↔ L % 2 = 0.

Pinned by: definitions `Odd a := ∃ k, a = 2 * k + 1`, `Even a := ∃ r, a = r +
r`; `Int.odd_iff`: Odd n ↔ n % 2 = 1; `Nat.even_iff`: Even n ↔ n % 2 = 0;
`Int.not_even_iff_odd`: ¬Even n ↔ Odd n.

Conventions: 0 is even and not odd.

### G52 — `Nat.choose` (also `n.choose k`)

Meaning: n.choose k = C(n, k) = n! / (k!·(n−k)!) for k ≤ n, and 0 for k > n (no
error); defined by Pascal's rule.

Pinned by: definition: choose _ 0 = 1, choose 0 (k+1) = 0, choose (n+1) (k+1) =
choose n k + choose n (k+1); `Nat.choose_eq_factorial_div_factorial` (k ≤ n):
choose n k = n ! / (k ! * (n - k)!); `Nat.choose_eq_zero_of_lt`: n < k → choose
n k = 0.

Conventions: Arguments are in ℕ, so truncated subtraction inside an argument is
evaluated first.

### G55 — `Irrational`

Meaning: `Irrational x` (x : ℝ) means x ∉ ℚ; a hypothesis, not a computation.

Pinned by: definition `Irrational x := x ∉ Set.range ((↑) : ℚ → ℝ)`.

Conventions: For irrational α, `GenContFract.of α` never terminates
(`GenContFract.terminates_iff_rat`), so every `(GenContFract.of α).partDens.get?
i` is `some _` (G76).

### G56 — `x ^ y` with real exponent (`Real.rpow`)

Meaning: For real x and y, `x ^ y` is `Real.rpow x y`, the real part of (x : ℂ)
^ (y : ℂ); for x > 0 it is exp(y·log x) > 0. With a ℕ exponent (`t ^ 2`, `2 ^
n`, `Real.sqrt q ^ k` with k : ℕ), `^` is repeated multiplication (G09); the two
agree on x ^ (n : ℝ).

Pinned by: `Real.rpow_def_of_pos`: 0 < x → x ^ y = exp (log x * y);
`Real.rpow_natCast`: x ^ (n : ℝ) = x ^ n; `Real.rpow_neg`: 0 ≤ x → x ^ (-y) = (x
^ y)⁻¹.

Conventions: `Real.zero_rpow`: y ≠ 0 → 0 ^ y = 0; `Real.rpow_zero`: x ^ (0 : ℝ)
= 1 for every x. For x < 0, x ^ y = exp (log x * y) * cos (y * π)
(`Real.rpow_def_of_neg`; log x = log |x|), a convention, not a real root. `-(1 :
ℝ) / 2` parses as (−1)/2.

### G57 — `Real.sqrt` (notation `√x`)

Meaning: For x ≥ 0, `Real.sqrt x` is the unique y ≥ 0 with y·y = x. It is
`NNReal.sqrt (Real.toNNReal x)`, so a negative input is first replaced by 0.

Pinned by: `Real.sqrt_nonneg`: 0 ≤ √x; `Real.mul_self_sqrt`: 0 ≤ x → √x * √x =
x; `Real.sqrt_eq_zero'`: √x = 0 ↔ x ≤ 0.

Conventions: √x = 0 for every x ≤ 0 (no error, no complex value); with a / 0 = 0
this gives √(a / 0) = 0. `Real.sqrt_eq_rpow`: √x = x ^ (1 / (2 : ℝ)) for all
real x.

### G58 — `Real.exp`, `Complex.exp`, `Complex.I`, `Real.pi`

Meaning: `Complex.exp z` = Σ_{m≥0} z^m/m!; `Real.exp x` is its real part at x,
the usual eˣ > 0; `Complex.I` = ⟨0, 1⟩ = i; `Real.pi` = π, twice the zero of cos
in [1, 2]. No junk values.

Pinned by: definitions `Complex.exp z := CauSeq.lim (exp' z)` (exp' z the
partial sums Σ_{m<n} z^m / m!), `Real.exp x := (Complex.exp x).re`, `Complex.I
:= ⟨0, 1⟩`, `Real.pi := 2 * Classical.choose exists_cos_eq_zero`;
`Complex.exp_mul_I`: exp (x * I) = cos x + sin x * I;
`Complex.exp_two_pi_mul_I`: exp (2 * π * I) = 1.

Conventions: In `Complex.exp (2 * Real.pi * Complex.I * x)` with x : ℝ,
`Real.pi` and x are cast to ℂ, so the argument is 2πix.

### G59 — `Real.log`

Meaning: For x > 0, `Real.log x` is the natural logarithm (inverse of
`Real.exp`).

Pinned by: definition `log x := if x = 0 then 0 else expOrderIso.symm ⟨|x|, _⟩`;
`Real.exp_log`: 0 < x → exp (log x) = x; `Real.log_zero`: log 0 = 0;
`Real.log_abs`: log |x| = log x.

Conventions: Junk extensions: log 0 = 0 and log x = log |x| for x < 0.

### G60 — `Real.cot`

Meaning: `Real.cot x` = cos x / sin x for every real x (defined as the real part
of the complex cotangent).

Pinned by: definitions `Real.cot x := (Complex.cot x).re`, `Complex.cot z := cos
z / sin z`; `Real.cot_eq_cos_div_sin`: cot x = cos x / sin x (all x : ℝ).

Conventions: At x ∈ πℤ (sin x = 0) the value is cos x / 0 = 0 (`div_zero`); e.g.
cot 0 = 0. No Mathlib lemma states this case separately.

### G62 — `Matrix.det` (`A.det`)

Meaning: For square `M : Matrix n n R` over a commutative ring, `M.det = ∑_σ
sign(σ) ∏_i M (σ i) i` over all permutations σ of n; an integer for an integer
matrix (`.natAbs` is its absolute value in ℕ).

Pinned by: `Matrix.det_apply`: M.det = ∑ σ : Perm n, Equiv.Perm.sign σ • ∏ i, M
(σ i) i; `Matrix.det_mul`: det (M * N) = det M * det N.

Conventions: The empty 0×0 matrix has determinant 1 (`Matrix.det_isEmpty`).

### G63 — `Matrix.mulVec` (`A *ᵥ v`)

Meaning: For `A : Matrix m n α` and `v : n → α`, `A *ᵥ v` (= `A.mulVec v`) is
the vector with i-th entry ∑_j A i j · v j.

Pinned by: `Matrix.mulVec_apply_eq_sum`: (M *ᵥ v) i = ∑ j : n, M i j * v j;
`Matrix.mulVec_mulVec`: M *ᵥ N *ᵥ v = (M * N) *ᵥ v.

Conventions: `infixr:73` (scoped in `Matrix`): tighter than `+` (65), looser
than application, so `u + Φ *ᵥ y` is u + Φy, `A i *ᵥ x + c i` is (A i)x + c i,
and `M *ᵥ N *ᵥ v` is M(Nv).

### G67 — `Module.Basis ι R M`

Meaning: A basis b of the R-module M indexed by ι is a linear isomorphism
`b.repr : M ≃ₗ[R] (ι →₀ R)`, with `b i := b.repr.symm (Finsupp.single i 1)`; the
b i are linearly independent and span M, and `Module.Basis.mk` makes any such
family a basis. No inner product or normalization is involved.

Pinned by: `Module.Basis.linearIndependent`: LinearIndependent R b;
`Module.Basis.span_eq`: span R (range b) = ⊤; `Module.finrank_eq_card_basis`: (h
: Basis ι R M) → finrank R M = Fintype.card ι.

Conventions: With ι = `Fin D` the vectors are indexed 0, …, D−1 and dim M = D.
Over a nonzero ring they are pairwise distinct (`Module.Basis.injective`).

### G68 — `Module.finrank`

Meaning: `Module.finrank R M := Cardinal.toNat (Module.rank R M)`: dim_R M if
finite, else 0.

Pinned by: `Module.finrank_of_not_finite`: ¬Module.Finite R M → finrank R M = 0;
`Module.finrank_pi`: finrank R (ι → R) = Fintype.card ι.

Conventions: The junk value 0 is not relevant here (the spaces are
finite-dimensional).

### G69 — `Submodule.span`, `⊤`, `Submodule`

Meaning: `Submodule.span R s` is the smallest submodule containing s: the finite
linear combinations ∑ c_i v_i with v_i ∈ s. `⊤` is the whole module, so
`Submodule.span R s = ⊤` means s spans. A `Submodule ℂ (X → ℂ)` is a complex
linear subspace of the functions X → ℂ; ↥V is the type of its elements.

Pinned by: definition `Submodule.span R s := sInf {p | s ⊆ p}`;
`Submodule.mem_span_set'`: m ∈ span R s ↔ ∃ (n : ℕ) (f : Fin n → R) (g : Fin n →
s), ∑ i, f i • (g i : M) = m; `Submodule.eq_top_iff'`: p = ⊤ ↔ ∀ x, x ∈ p.

Conventions: `Submodule.span_empty`: span R ∅ = ⊥.

### G70 — `V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ` (sesquilinear forms)

Meaning: `M →ₗ[R] N` is the type of R-linear maps, `M →ₗ⋆[R] N` of
conjugate-linear maps (f (c • y) = conj(c) • f y). Arrows associate to the
right: `ip : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ` is additive in each argument, ip (c • x) y = c
· ip x y and ip x (c • y) = conj(c) · ip x y. Hermitian symmetry and positivity
are not implied.

Pinned by: notations `M →ₗ[R] M₂ := LinearMap (RingHom.id R) M M₂`, `M →ₗ⋆[R] M₂
:= LinearMap (starRingEnd R) M M₂`; `LinearMap.map_smul₂`: f (r • x) y = r • f x
y; `LinearMap.map_smulₛₗ`: f (c • x) = σ c • f x, here σ = `starRingEnd ℂ`,
complex conjugation (`starRingEnd_apply`).

Conventions: Same convention as the paper's ⟨f, g⟩: linear in f,
conjugate-linear in g.

### G71 — `Summable`, `HasSum`, `∑' i, f i` (`tsum`)

Meaning: `HasSum f a` (default summation filter, used throughout) means the
finite partial sums Σ_{b ∈ s} f b tend to a as the finite set s ⊆ β grows (no
ordering of β is used). `Summable f` is ∃ a, HasSum f a, and `∑' i, f i` is that
a if f is summable, else 0. For ℝ- or ℂ-valued f, Summable f ↔ Σ |f i| < ∞; so
∑' over ℤ is not the symmetric limit lim_N Σ_{|n| ≤ N}.

Pinned by: `HasSum f a L := Tendsto (fun s : Finset β ↦ ∑ b ∈ s, f b) L.filter
(𝓝 a)` with `(unconditional β).filter = atTop`; `HasSum.tsum_eq`: HasSum f a →
∑' b, f b = a; `tsum_eq_zero_of_not_summable`: ¬Summable f → ∑' b, f b = 0;
`summable_norm_iff` (finite-dimensional, e.g. ℂ): (Summable fun x => ‖f x‖) ↔
Summable f.

Conventions: Junk value: ∑' of a non-summable family is 0, so a bound on a ∑' is
informative only when summability is known or asserted. A family with finite
support is summable with ∑' the finite sum (`tsum_eq_sum`). No `∑'[L]`
(non-default filter) occurs.

### G72 — `∫ x, f x` and `∫ x in a..b, f x`

Meaning: `∫ t : ℝ, f t` is the Bochner integral with respect to `volume`
(Lebesgue measure on ℝ): the Lebesgue integral over ℝ for integrable f. `∫ x in
a..b, f x` is ∫_{(a,b]} f − ∫_{(b,a]} f: ∫_{(a,b]} f if a ≤ b, with a sign
change when a and b are swapped.

Pinned by: `MeasureTheory.integral_undef`: ¬Integrable f μ → ∫ a, f a ∂μ = 0;
definition `intervalIntegral f a b μ := (∫ x in Ioc a b, f x ∂μ) - ∫ x in Ioc b
a, f x ∂μ`; `intervalIntegral.integral_undef`: ¬IntervalIntegrable f μ a b → ∫ x
in a..b, f x ∂μ = 0; `Real.volume_Icc`: volume (Icc a b) = ofReal (b - a).

Conventions: Junk value 0 for a non-integrable integrand (e.g. ∫ t : ℝ, (1 : ℝ)
= 0), so a hypothesis `∫ … ≤ Lam` would hold trivially for it. Integrability
criteria: `Continuous.integrable_of_hasCompactSupport`: Continuous f →
HasCompactSupport f → Integrable f μ; `Continuous.intervalIntegrable`:
Continuous u → IntervalIntegrable u μ a b.

Source:
Mathlib/MeasureTheory/Integral/{Bochner/Basic,IntervalIntegral/Basic}.lean,
Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean,
Mathlib/MeasureTheory/Function/LocallyIntegrable.lean.

### G73 — `deriv`

Meaning: `deriv f x := fderiv 𝕜 f x 1` is f′(x) = lim_{h→0, h ≠ 0} (f(x+h) −
f(x))/h when f is differentiable at x (here 𝕜 = ℝ, f : ℝ → ℂ, so h is real);
`deriv (deriv U)` is U″ when U is twice differentiable.

Pinned by: `HasDerivAt.deriv`: HasDerivAt f f' x → deriv f x = f';
`deriv_zero_of_not_differentiableAt`: ¬DifferentiableAt 𝕜 f x → deriv f x = 0;
`hasDerivAt_iff_tendsto_slope`: HasDerivAt f f' x ↔ Tendsto (slope f x) (𝓝[≠] x)
(𝓝 f').

Conventions: Junk value 0 where f is not differentiable.

### G75 — `fwdDiff`

Meaning: For f : M → G (M an additive commutative monoid, G an additive
commutative group) and a step h : M, `fwdDiff h f` (also Δ_[h] f) is y ↦ f (y +
h) − f y.

Pinned by: definition `fwdDiff h f := fun n ↦ f (n + h) - f n` (no separate
apply lemma).

### G76 — `GenContFract.of` and `.h`, `.partDens`, `.nums`, `.dens` (with `get?`, `getD`)

Meaning: `GenContFract.of α` is the regular continued fraction α = [a₀; a₁, a₂,
…] of the floor algorithm: a head `h = ⌊α⌋ = a₀` (a real) and a possibly finite
sequence of pairs (partial numerator 1, partial denominator a_{i+1}), i = 0, 1,
…. `nums s`, `dens s` (s ≥ 0) are the convergents' numerators and denominators
p_s, q_s, p_s/q_s = [a₀; a₁, …, a_s]: p₀ = a₀, q₀ = 1, p₁ = a₁a₀ + 1, q₁ = a₁,
p_{s+2} = a_{s+2}p_{s+1} + p_s, q_{s+2} = a_{s+2}q_{s+1} + q_s.

Pinned by: `GenContFract.of_h_eq_floor`: (of v).h = ⌊v⌋;
`GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream`:
IntFractPair.stream v (n + 1) = some ifp → (of v).s.get? n = some ⟨1, ifp.b⟩;
`GenContFract.exists_int_eq_of_partDen`: (of v).partDens.get? n = some b → ∃ z :
ℤ, b = z; `GenContFract.of_one_le_get?_partDen` (same hypothesis): 1 ≤ b;
`GenContFract.zeroth_num_eq_h`, `zeroth_den_eq_one`, `first_num_eq`,
`first_den_eq`, `nums_recurrence`, `dens_recurrence` (the formulas above, with
partial numerators 1 by `GenContFract.of_partNum_eq_one`);
`GenContFract.terminatedAt_iff_partDen_none`: g.TerminatedAt n ↔ g.partDens.get?
n = none; `GenContFract.terminates_iff_rat`: (of v).Terminates ↔ ∃ q : ℚ, v = q;
`GenContFract.of_convergence`: Tendsto (of v).convs atTop (𝓝 v).

Conventions: Index shift: `partDens.get? i` is `some a_{i+1}` (i ≥ 0), and a₀ =
⌊α⌋ is `h`, so a bound on all `partDens` entries bounds a₁, a₂, … but not a₀.
`get?` returns `none` after a rational α's expansion ends, never for irrational
α. `Option.getD o d` is x if o = some x and d if o = none. After termination
`nums`/`dens` stay constant (`GenContFract.nums_stable_of_terminated`). The
values are integral reals with dens s ≥ 1 (`zeroth_den_eq_one`,
`GenContFract.of_den_mono`). Coprimality of p_s, q_s follows from
`GenContFract.determinant`: g.nums n * g.dens (n + 1) - g.dens n * g.nums (n +
1) = ∏ i ∈ Finset.range (n + 1), -(g.partNums.get? i).getD 0, which is
(−1)^{n+1} here.

Terms used only inside definition bodies, one line each:

- G17 — `Fin.castSucc`: Fin n → Fin (n+1), i ↦ i (same value)
  (`Fin.val_castSucc`).
- G22 — `toLex`: α ×ₗ β is α × β ordered lexicographically; toLex (a, b) is (a,
  b) in that order (`Prod.Lex.toLex_lt_toLex`).
- G27 — `Finset.image`: s.image f = {f x | x ∈ s}; equal values merge, so #(s.image
  f) ≤ #s (`Finset.mem_image`).
- G30 — `Finset.inf'`: s.inf' H f is the minimum of f over s, H proving s
  nonempty (`Finset.inf'`).
- G34 — `Finset.piAntidiag s n`: all f : ι → μ supported in s with ∑_{i ∈ s} f i
  = n (`Finset.mem_piAntidiag`).
- G35 — ↥s = {x // x ∈ s}: elements of s paired with membership proofs
  (`SetLike.coe_mem`).
- G36 — `Set.Icc a b` = [a, b], `Set.Ico a b` = [a, b): Sets, not Finsets
  (`Set.mem_Icc`).
- G38 — `⋃ i, S i` = {x | ∃ i, x ∈ S i} (`Set.mem_iUnion`).
- G43 — `Function.support f` = {x | f x ≠ 0}, not its closure
  (`Function.support_subset_iff'`).
- G44 — `Nat.find h`: the least n : ℕ with p n, for h : ∃ n, p n
  (`Nat.find_spec`).
- G45 — `Int.toNat z`: z if z ≥ 0, and 0 if z < 0.
- G46 — `Int.natAbs z`: |z| as a natural number (`Int.natCast_natAbs`).
- G50 — ⌈x⌉: the least integer ≥ x; `round x`: the nearest integer, ties rounded
  up (`Int.ceil_le`).
- G53 — `Nat.multinomial s f` = (∑_{i∈s} f i)! / ∏_{i∈s} (f i)!, an exact
  quotient ≥ 1 (`Nat.multinomial_spec`).
- G54 — `Nat.factorial n` = n! = 1·2⋯n, with 0! = 1.
- G61 — `starRingEnd ℂ`: complex conjugation as a ring homomorphism ℂ → ℂ
  (`starRingEnd_apply`).
- G64 — `Aᵀ` (`Matrix.transpose`): Aᵀ i j = A j i (`Matrix.transpose_apply`).
- G65 — `Matrix.diagonal d`: diagonal matrix with entries d i; `A.IsDiag`:
  off-diagonal entries 0 (`Matrix.diagonal_apply`).
- G66 — `Matrix.fromBlocks`: block matrix [[A, B], [C, D]] on sum indices;
  `reindex` relabels rows and columns (`Matrix.fromBlocks_apply₁₁`).
- G74 — `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U`: U is C^∞; analyticity (`ω`) is
  not required.
- G77 — `SimpleGraph.fromRel r`: edge a–b iff a ≠ b and (r a b or r b a)
  (`SimpleGraph.fromRel_adj`).
- G78 — `SimpleGraph.connectedComponentMk`: G.connectedComponentMk v is the
  connected component of G containing v (`SimpleGraph.ConnectedComponent.eq`).
-/

/-!
## Alphabetical definition index

Search for the heading `### D…` to jump to a body (scope: see the file
header). `Paper.definition3Weak` is D025w.
Library names are not indexed (glossary G15–G78 above; G01–G14 before
Theorem 1).

- `AllDegreesProof.faceLift` (D042): Paper context / faces
- `AllDegreesProof.faceScale` (D043): Paper context / faces
- `BalancedDecompData` (D060): Paper context / decomposition
- `IsBalancedPair` (D044): Paper context / balanced
- `IsBalancedWrt` (D059): Paper context / components
- `IsDecomposition` (D073): Paper context / transitions
- `IsSmoothCutoff` (D045): Paper context / cutoff
- `IsTransition` (D072): Paper context / transitions
- `IsUNmap` (D029): Paper context / simplex
- `Paper.definition3` (D025): Definition 3 / Paper context / affine
- `Paper.definition3Weak` (D025w): Paper context / affine
- `Piece` (D061): Paper context / pieces
- `Piece.IsMixed` (D067): Paper context / pieces
- `Piece.index` (D071): Paper context / pieces
- `Piece.longCoords` (D066): Paper context / pieces
- `Piece.longPart` (D084): Paper context / split
- `Piece.minSide` (D064): Paper context / pieces
- `Piece.mixedIneqs` (D068): Paper context / pieces
- `Piece.nLong` (D069): Paper context / pieces
- `Piece.nMix` (D070): Paper context / pieces
- `Piece.prod` (D078): Paper context / products
- `Piece.quad` (D062): Paper context / pieces
- `Piece.shortCoords` (D065): Paper context / pieces
- `Piece.shortPart` (D083): Paper context / split
- `Piece.side` (D063): Paper context / pieces
- `Piece.splitLambda` (D086): Paper context / split
- `Piece.splitMinusW` (D088): Paper context / split
- `Piece.splitPlusW` (D087): Paper context / split
- `PolySpaceH` (D003): Paper context / polynomials
- `PropUNmap` (D032): Paper context / basis
- `ThmBox` (D031): Paper context / basis
- `UniformBoundUnit.BddPartQuot` (D021): Paper context / fractions
- `UniformBoundUnit.PropUNmap` (D034): Paper context / basis
- `UniformBoundUnit.ThmBox` (D033): Paper context / basis
- `UniformBoundUnit.boxLenZ` (D019): Paper context / geometry
- `UniformBoundUnit.boxSectZ` (D020): Paper context / geometry
- `UniformBoundUnit.boxVolZ` (D018): Paper context / geometry
- `UniformBoundUnit.cSphere` (D005): Paper context / polynomials
- `UniformBoundUnit.latticePtsZ` (D017): Paper context / geometry
- `basisPhi` (D030): Paper context / basis
- `blockDiagMat` (D077): Paper context / products
- `boxB` (D028): Paper context / simplex
- `boxConstraints` (D082): Paper context / split
- `boxLen` (D013): Paper context / geometry
- `boxMinAffine` (D085): Paper context / split
- `boxSect` (D014): Paper context / geometry
- `boxSide` (D011): Paper context / geometry
- `boxVol` (D012): Paper context / geometry
- `boxZ` (D010): Paper context / geometry
- `constraintGraph` (D058): Paper context / graph
- `constraintRho` (D057): Paper context / graph
- `coordVec` (D081): Paper context / split
- `degIdx` (D002): Paper context / polynomials
- `expTwoPiI` (D001): Paper context / conventions
- `foldCoord` (D091): Paper context / fold
- `foldInv` (D096): Paper context / fold
- `foldMap` (D092): Paper context / fold
- `foldMapGlobal` (D093): Paper context / fold
- `foldPrefixSum` (D089): Paper context / fold
- `foldSourcePiece` (D090): Paper context / fold
- `foldTargetBase` (D094): Paper context / fold
- `foldTargetPiece` (D095): Paper context / fold
- `gaussPhasePhi` (D054): Paper context / gaussphase
- `hatEta` (D038): Paper context / fourier
- `lcmUpTo` (D026): Paper context / simplex
- `matInftyNorm` (D023): Paper context / affine
- `multiwallT` (D047): Paper context / cutoff
- `multiwallTerm` (D046): Paper context / cutoff
- `oplusConstraints` (D076): Paper context / products
- `oscIntegralW` (D053): Paper context / integrals
- `padLeftVec` (D074): Paper context / products
- `padRightVec` (D075): Paper context / products
- `pieceAffineImage` (D022): Paper context / affine
- `poissonH` (D036): Paper context / poisson
- `poissonQ` (D035): Paper context / poisson
- `poissonQLoc` (D039): Paper context / fourier
- `poissonRho` (D037): Paper context / poisson
- `polyBoxZ` (D015): Paper context / geometry
- `polyEval` (D004): Paper context / polynomials
- `polyInner` (D006): Paper context / pairing
- `polyP` (D008): Paper context / geometry
- `polyPZ` (D007): Paper context / geometry
- `quadExpSum` (D016): Paper context / geometry
- `quadGaussSum` (D052): Paper context / integrals
- `quadPhase` (D051): Paper context / integrals
- `restrictVec` (D080): Paper context / split
- `seqFourier` (D040): Paper context / fourier
- `sgnCoeff` (D049): Paper context / sign
- `sgnCotWeight` (D048): Paper context / sign
- `sgnIndex` (D050): Paper context / sign
- `shiftedBasisPhi` (D041): Paper context / shifted
- `sigmaPieceIndexEquiv` (D079): Paper context / products
- `simplexS` (D027): Paper context / simplex
- `transitionSize` (D024): Paper context / affine
- `vecSupport` (D009): Paper context / geometry
- `weylProgIco` (D055): Paper context / weyl
- `weylProgSum` (D056): Paper context / weyl

Paper-numbered aliases in `Compatibility.lean` (not shown; each is
`abbrev name := @_root_.target`, so it adds nothing to its target):

- `Paper.definition13` = `IsBalancedPair` (D044)
- `Paper.definition20` = `IsBalancedWrt` (D059)
- `Paper.definition22` = `Piece` (D061)
- `Paper.Definition22.minimumSide` = `Piece.minSide` (D064)
- `Paper.Definition22.polyhedron` = `polyPZ` (D007)
- `Paper.Definition22.quadraticForm` = `Piece.quad` (D062)
- `Paper.Definition22.side` = `Piece.side` (D063)
- `Paper.definition23` = `IsTransition` (D072)
- `Paper.Definition23.affineImage` = `pieceAffineImage` (D022)
- `Paper.Definition23.decomposition` = `IsDecomposition` (D073)
- `Paper.Definition23.size` = `transitionSize` (D024)
- `Paper.Definition3.simplexBoxAdmissibleMap` = `IsUNmap` (D029)
- `Paper.definition8` = `shiftedBasisPhi` (D041)
- `Paper.Lemma11.lift` = `AllDegreesProof.faceLift` (D042)
- `Paper.Lemma11.scale` = `AllDegreesProof.faceScale` (D043)
- `Paper.Lemma16.coefficient` = `sgnCoeff` (D049)
- `Paper.Lemma16.indexSet` = `sgnIndex` (D050)
- `Paper.Lemma24.productPiece` = `Piece.prod` (D078)
- `Paper.Proposition9.indexEquiv` = `AllDegreesProof.goodEquiv` (`Core.lean:3381`;
  not shown, used only by this alias)
-/

end PaperReview
