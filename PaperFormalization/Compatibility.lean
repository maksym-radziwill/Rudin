import PaperFormalization.Core

set_option linter.all false

/-!
# Paper-numbered compatibility API

Names in namespace `Paper` for the paper's numbered statements, following its
single counter: Theorem 1, Theorem 2, Definition 3, ..., Proposition 28. Most
are one-line forwards to `Core.lean` with the type written out in full. Six
carry short proofs of their own, built from `Core.lean` results: the bridges
`theorem2_to_unitThmBox`, `proposition4_to_propUNmap` and
`proposition4_to_unitPropUNmap`, the restated `Theorem5.uniformBound` and
`proposition10`, and `lemma16CotWeightBound`. `definition3` states Definition 3
directly; `definition3Weak` is the superseded encoding, kept for reference.

Capitalized namespaces collect items formalized in several pieces. Proposition 9
and Lemma 11 are partial, so there is deliberately no lower-case alias for them.
-/

namespace Paper

open scoped Matrix

/-! ## Main analytic and basis results -/

/-- Paper Theorem 1 (`thm:onb`). -/
theorem theorem1 :
  ∀ (K : ℕ) (hK : 2 ≤ K),
∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ,
        ∃ φ : Module.Basis (Fin (Module.finrank ℂ (PolySpaceH K N))) ℂ (PolySpaceH K N),
          (∀ i j, polyInner K N (φ i) (φ j) = if i = j then 1 else 0) ∧
          ∀ i, ∀ z : Fin K → ℂ, ∑ s, ‖z s‖ ^ 2 < 1 →
            ‖polyEval K N (φ i) z‖ ≤ C :=
  @_root_.thm_onb

/-- Paper Theorem 2 (`thm:box`). -/
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

/--
Paper Definition 3 (`def:equicomp`): `P` and `Q` are `Aff_k(ℤ)`-equidecomposable
with complexity at most `R`.  The two displayed disjoint unions
`P = ⨆ᵢ 𝒫(Lᵢ)` and `Q = ⨆ᵢ (Aᵢ 𝒫(Lᵢ) + bᵢ)` are stated as an equality of sets
together with pairwise disjointness.  `det.natAbs = 1` says that the linear part
belongs to `GL k ℤ`; `transitionSize = matInftyNorm` is the paper's `|Aᵢ|_∞`, and
the remaining clauses are the other three complexity bounds.

Neither this predicate nor `Paper.definition3Weak` requires `P`, `Q` to be
ℤ-polytopes or `R ≥ 1`; for those, this one reads, by inspection, as the paper's
definition (for `R = 0` it says `P = Q = ∅`), a harmless generalization.
-/
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

/--
**Not the paper's Definition 3.**  This is the earlier, too weak encoding, kept
only so that the counterexample discussion in `Statements.lean` names a real
declaration.  Its clause `x ∈ P ↔ ∃! i, x ∈ 𝒫(Lᵢ)` forces neither the pieces
into `P` nor their images into `Q`: with `k = 1`, `R = 2`, pieces `[0,3]` and
`[1,3]` and maps `x ↦ x`, `x ↦ -x`, it holds with `P = {0}` and
`Q = {-3,…,3}`, which is not an equidecomposition.  No theorem uses it; use
`Paper.definition3`.
-/
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

namespace Definition3

/--
The ℕ-valued simplex-to-box admissible-map predicate that Theorem 5 and
Proposition 10 take as a hypothesis.  It is **not** a specialization of
`Paper.definition3`: its source-piece clause is the unique-membership form of
`Paper.definition3Weak`, it carries no decomposition of the target at all (only
a pointwise affine formula for `U` on each piece), and its complexity bounds are
stated entrywise.  Its `Set.BijOn` clause is, on the other hand, a genuine
bijection, which Definition 3 does not state.
-/
abbrev simplexBoxAdmissibleMap := @_root_.IsUNmap

end Definition3

/-- Paper Proposition 4 (`prop:UNmap`). -/
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

/-! ### Discharging the hypotheses of Theorem 5 and Proposition 10

Theorem 5 and Proposition 10 are conditional, as in the paper: they take the
square-root-cancellation bound of Theorem 2 and the simplex-to-box
equidecomposition of Proposition 4 as hypotheses, in the packaged forms
`ThmBox`, `UniformBoundUnit.ThmBox`, `PropUNmap` and
`UniformBoundUnit.PropUNmap k`.  Those packages are not the same statements as
`Paper.theorem2` and `Paper.proposition4` — they are repackagings, and in
Proposition 4's case a conversion from ℤ-valued to ℕ-valued maps — and the
steps that get from one to the other were internal to `Core.lean`.  The four
theorems below export them, so that each hypothesis of Theorem 5 and
Proposition 10 can be discharged from the paper-numbered results.
-/

/-- Paper Theorem 2 packaged as the root `ThmBox`.  The two statements are the
same up to unfolding `quadExpSum`, `polyBoxZ`, `boxVol` and `boxSect`. -/
theorem theorem2_to_thmBox : _root_.ThmBox := theorem2

/-- Paper Theorem 2 packaged as `UniformBoundUnit.ThmBox`, which bundles
`Irrational α` with the partial-quotient bound into `BddPartQuot a α`, states
the exponential sum with `latticePtsZ`/`boxVolZ`/`boxSectZ`, and drops the
hypothesis `∀ s, lo s ≤ hi s` (for an empty box both sides vanish). -/
theorem theorem2_to_unitThmBox : _root_.UniformBoundUnit.ThmBox := by
  classical
  intro k r V h hk hV hh a ha
  obtain ⟨C, hC, hb⟩ := theorem2 k r V h a hk hV hh ha
  refine ⟨C, hC, ?_⟩
  intro α hα c hc lo hi L hL hLV θ
  by_cases hlo : ∀ j, lo j ≤ hi j
  · simpa only [_root_.UniformBoundUnit.latticePtsZ,
      _root_.UniformBoundUnit.boxVolZ, _root_.UniformBoundUnit.boxSectZ,
      _root_.UniformBoundUnit.boxLenZ, expTwoPiI] using
      hb α hα.1 hα.2 c (fun j => (hc j).1) (fun j => (hc j).2)
        lo hi hlo L hL hLV θ
  · have hempty : _root_.UniformBoundUnit.latticePtsZ k L lo hi = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hlo
      intro j
      have hj := Finset.mem_Icc.mp
        (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx).1 j)
      exact hj.1.trans hj.2
    rw [hempty]
    simp only [Finset.sum_empty, norm_zero]
    refine ⟨by positivity, ?_⟩
    intro w b hw hwL hneg
    positivity

/--
Paper Proposition 4 packaged as the root `PropUNmap`.

`proposition4` produces a ℤ-valued bijection of the ℤ-polytopes
`S_N = {x | 0 ≤ x, ∑ x ≤ N}` and `B_N`, whereas `IsUNmap` — the form Theorem 5
and Proposition 10 use — wants an ℕ-valued map on the `Finset`s `simplexS k N`
and `boxB k N`.  The witness is `U` postcomposed with `Int.toNat`; this is
faithful because every piece of the decomposition lies in `S_N` (the `hsub`
clause), so `U` is nonnegative wherever it is applied, and `Int.toNat` inverts
the cast there.
-/
theorem proposition4_to_propUNmap : _root_.PropUNmap := by
  classical
  intro k hk
  obtain ⟨R, U, hU⟩ := proposition4 k hk
  refine ⟨R, fun M x s => (U M (fun t => (x t : ℤ)) s).toNat, ?_⟩
  intro M _hM hdvd
  obtain ⟨hbij, r, L, A, c, hr, hcard, hnorm, hdet, hmat, hsub, hdis, hcover,
    haffine⟩ := hU M hdvd
  have hmemS : ∀ x : Fin k → ℕ,
      ((fun t => (x t : ℤ)) ∈
          {y : Fin k → ℤ | (∀ s, 0 ≤ y s) ∧ ∑ s, y s ≤ (M : ℤ)}) ↔
        x ∈ simplexS k M := by
    intro x
    simp only [Set.mem_setOf_eq, simplexS, Finset.mem_filter,
      Fintype.mem_piFinset, Finset.mem_range]
    constructor
    · rintro ⟨-, hsum⟩
      have hsum' : (∑ s, x s) ≤ M := by
        have hz : ((∑ s, x s : ℕ) : ℤ) ≤ (M : ℤ) := by push_cast; exact hsum
        exact_mod_cast hz
      refine ⟨fun s => ?_, hsum'⟩
      have hle := Finset.single_le_sum
        (f := fun s : Fin k => x s) (fun i _ => Nat.zero_le _) (Finset.mem_univ s)
      omega
    · rintro ⟨-, hsum⟩
      refine ⟨fun s => Int.natCast_nonneg _, ?_⟩
      have hz : ((∑ s, x s : ℕ) : ℤ) ≤ (M : ℤ) := by exact_mod_cast hsum
      push_cast at hz
      exact hz
  have hmemB : ∀ l : Fin k → ℕ,
      ((fun t => (l t : ℤ)) ∈
          {y : Fin k → ℤ | ∀ s : Fin k,
            0 ≤ y s ∧ y s ≤ ((M / (k - s.val) : ℕ) : ℤ)}) ↔
        l ∈ boxB k M := by
    intro l
    simp only [Set.mem_setOf_eq, boxB, Fintype.mem_piFinset, Finset.mem_range]
    constructor
    · intro hl s
      exact Nat.lt_succ_iff.mpr (by exact_mod_cast (hl s).2)
    · intro hl s
      exact ⟨Int.natCast_nonneg _, by exact_mod_cast Nat.lt_succ_iff.mp (hl s)⟩
  have hStoN : ∀ y : Fin k → ℤ, (∀ s, 0 ≤ y s) →
      (fun t => ((y t).toNat : ℤ)) = y := by
    intro y hy
    funext t
    exact Int.toNat_of_nonneg (hy t)
  have hmapsB : ∀ x : Fin k → ℕ, x ∈ simplexS k M →
      ∀ s, 0 ≤ U M (fun t => (x t : ℤ)) s := by
    intro x hx s
    exact (hbij.mapsTo ((hmemS x).2 hx) s).1
  have hcast : ∀ x : Fin k → ℕ, x ∈ simplexS k M →
      (fun s => ((U M (fun t => (x t : ℤ)) s).toNat : ℤ)) =
        U M (fun t => (x t : ℤ)) :=
    fun x hx => hStoN _ (hmapsB x hx)
  refine ⟨⟨?_, ?_, ?_⟩, r, L, A, c, hr, hcard, hnorm, hdet, hmat, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_coe] at hx ⊢
    refine (hmemB _).1 ?_
    rw [hcast x hx]
    exact hbij.mapsTo ((hmemS x).2 hx)
  · intro x hx x' hx' heq
    simp only [Finset.mem_coe] at hx hx'
    have hUeq : U M (fun t => (x t : ℤ)) = U M (fun t => (x' t : ℤ)) := by
      rw [← hcast x hx, ← hcast x' hx']
      funext s
      exact_mod_cast congrFun heq s
    have hxx := hbij.injOn ((hmemS x).2 hx) ((hmemS x').2 hx') hUeq
    funext t
    exact_mod_cast congrFun hxx t
  · intro l hl
    simp only [Finset.mem_coe] at hl
    obtain ⟨y, hyS, hy⟩ := hbij.surjOn ((hmemB l).2 hl)
    have hyn : (fun t => ((y t).toNat : ℤ)) = y := hStoN y hyS.1
    refine ⟨fun t => (y t).toNat, ?_, ?_⟩
    · simp only [Finset.mem_coe]
      refine (hmemS _).1 ?_
      rw [hyn]
      exact hyS
    · funext s
      show (U M (fun t => ((y t).toNat : ℤ)) s).toNat = l s
      rw [hyn, hy]
      exact Int.toNat_natCast _
  · intro x
    constructor
    · intro hx
      have hxS := (hmemS x).2 hx
      obtain ⟨i, hi⟩ := hcover (fun t => (x t : ℤ)) hxS.1 hxS.2
      refine ⟨i, hi, ?_⟩
      intro j hj
      by_contra hji
      exact hdis j i hji (fun t => (x t : ℤ)) ⟨hj, hi⟩
    · rintro ⟨i, hi, -⟩
      exact (hmemS x).1 (hsub i (fun t => (x t : ℤ)) hi)
  · intro i x hx s
    have hxsimp : x ∈ simplexS k M :=
      (hmemS x).1 (hsub i (fun t => (x t : ℤ)) hx)
    rw [Int.toNat_of_nonneg (hmapsB x hxsimp s)]
    exact congrFun (haffine i (fun t => (x t : ℤ)) hx) s

/--
Paper Proposition 4 packaged as `UniformBoundUnit.PropUNmap k`, which asks for
one map per admissible `N` rather than a single `ℕ`-indexed family.

`Core.lean` has a private proof of this that goes through the internals of the
§5.2 construction directly; this one goes through `Paper.proposition4` and
`Paper.proposition4_to_propUNmap`, so the `Paper.*` statement is what carries
the content.
-/
theorem proposition4_to_unitPropUNmap (k : ℕ) (hk : 1 ≤ k) :
    _root_.UniformBoundUnit.PropUNmap k := by
  obtain ⟨R, U, hU⟩ := proposition4_to_propUNmap k hk
  exact ⟨R, fun N hN hd => ⟨U N, hU N hN hd⟩⟩

/--
Paper Theorem 5 (`thm:onbexplicit`), in its all-degrees form.  The divisible-
degree orthonormal-basis and uniform-bound components are also exported in
`Theorem5` below.
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

namespace Theorem5

/-- The divisible-degree orthonormal-basis component of Paper Theorem 5. -/
theorem orthonormalBasis :
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

/--
The divisible-degree uniform-bound component of Paper Theorem 5.

The bound is stated for **every** complexity `R`, not only for one chosen
together with `A`: `A` depends on `k`, `a` and `R`, so the statement covers
whatever map `Paper.proposition4` happens to produce rather than a single
`R` extracted from `hUN`.  The first conjunct is the former existence clause,
retained; together the two imply the earlier `∃ R A, 0 < A ∧ … ∧ …` form, by
taking `A` at the `R` the first conjunct supplies.
-/
theorem uniformBound :
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
                ‖polyEval (k + 1) N (basisPhi k N α (U N) l) z‖ ≤ A := by
  classical
  intro k hk a ha hbox hUN
  refine ⟨hUN, ?_⟩
  intro R
  have hbox' : _root_.ThmBox := by
    intro K r V h a' hK hV hh ha'
    obtain ⟨C, hC, hc⟩ := hbox K r V h hK hV hh a' ha'
    refine ⟨C, hC, ?_⟩
    intro α hα hαa c hc1 hc2 lo hi hlo L hL hL1 θ
    exact hc α ⟨hα, hαa⟩ c (fun j => ⟨hc1 j, hc2 j⟩) lo hi L hL hL1 θ
  obtain ⟨C, hC, hc⟩ := _root_.shifted_piece_bound_ok hbox' k R a ha
  refine ⟨(R : ℝ) * C + 1, by positivity, ?_⟩
  intro α hα U hU N hN hdiv l hl
  have he : shiftedBasisPhi k N 0 α (U N) l = basisPhi k N α (U N) l := by
    have hn : ((N + k).choose k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (show k ≤ N + k by omega)))
    funext n
    simp [shiftedBasisPhi, basisPhi, hn]
  rw [← he]
  apply _root_.shifted_sphere_boundary_ok (k + 1) N (by omega)
  intro z hz hs
  have hb := _root_.shifted_assembly_bound_ok k R N 0 (by omega) α (U N)
    (by simpa using hU N hN hdiv) l z C hC.le
    (fun L hL hL1 θ => hc α hα.1 hα.2 N hN 0 L hL hL1 θ z hz hs)
  have hn : ((N + k).choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (show k ≤ N + k by omega)))
  simp only [Nat.sub_zero, div_self hn, Real.sqrt_one, one_mul] at hb
  exact hb.trans (by linarith)

/-- The all-degrees conclusion, identical to `Paper.theorem5`. -/
theorem allDegrees :
  ∀ (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : 1 ≤ a)
    (hbox : _root_.UniformBoundUnit.ThmBox) (hUN : ∀ j : ℕ, 1 ≤ j → j ≤ k → _root_.UniformBoundUnit.PropUNmap j),
∃ C : ℝ, 0 < C ∧
      ∀ α : ℝ, _root_.UniformBoundUnit.BddPartQuot a α →
        ∀ N : ℕ,
          ∃ ψ : Module.Basis (Fin ((N + k).choose k)) ℂ (PolySpaceH (k + 1) N),
            (∀ i j, polyInner (k + 1) N (ψ i) (ψ j) = if i = j then 1 else 0) ∧
            ∀ ν, ∀ z ∈ _root_.UniformBoundUnit.cSphere (k + 1), ‖polyEval (k + 1) N (ψ ν) z‖ ≤ C :=
  @_root_.UniformBoundUnit.thm_onbexplicit_allDegrees

end Theorem5

/-- Paper Lemma 6 (`lem:poisson1d`). -/
theorem lemma6 :
  ∃ C > 0, ∀ lam : ℝ, 0 < lam → ∀ n : ℤ,
      |poissonQ lam n| ≤
          C * poissonH lam ^ (-(1 : ℝ) / 2) * Real.exp (-poissonRho lam n / 4) ∧
        |fwdDiff (1 : ℤ) (poissonQ lam) n| ≤
          C * poissonH lam ^ (-(3 : ℝ) / 2) * Real.exp (-poissonRho lam n / 4) :=
  @_root_.lem_poisson1d

/-- Paper Lemma 7 (`lem:fouriermass`). -/
theorem lemma7 :
  ∃ C > 0, ∀ lam : ℝ, 0 < lam →
      (∀ n : ℤ, HasSum (fun m : ℤ => poissonQLoc lam m n) (poissonQ lam n)) ∧
      (∀ m n : ℤ, 1 ≤ |(n : ℝ) / poissonH lam - (m : ℝ)| → poissonQLoc lam m n = 0) ∧
      (Summable fun m : ℤ => ∫ u in (0:ℝ)..1, ‖seqFourier (poissonQLoc lam m) u‖) ∧
      (∑' m : ℤ, ∫ u in (0:ℝ)..1, ‖seqFourier (poissonQLoc lam m) u‖) ≤
        C * poissonH lam ^ (-(1 : ℝ) / 2) :=
  @_root_.lem_fouriermass

/-- Paper Definition 8 (`def:shiftedbasis`). -/
noncomputable abbrev definition8 := @_root_.shiftedBasisPhi

namespace Proposition9

/-- Index equivalence used for the spanning/dimension part of Proposition 9. -/
noncomputable abbrev indexEquiv := @_root_.AllDegreesProof.goodEquiv

/-- The orthogonality identity used in paper Proposition 9. -/
theorem orthogonality :
  ∀ (k N b : ℕ) (hb : b ≤ N) (α : ℝ)
    (U : (Fin k → ℕ) → Fin k → ℕ)
    (hU : Set.BijOn U (simplexS k (N-b) : Set _) (boxB k (N-b) : Set _))
    (l l' : Fin k → ℕ) (hl : l ∈ boxB k (N-b)) (hl' : l' ∈ boxB k (N-b)),
polyInner (k+1) N (shiftedBasisPhi k N b α U l)
      (shiftedBasisPhi k N b α U l') = if l=l' then 1 else 0 :=
  @_root_.AllDegreesProof.shifted_orth

/-!
The accepted development uses `indexEquiv` and `orthogonality` together in the
downstream basis construction.  It does not expose a single theorem whose type
is the full ON-basis statement of paper Proposition 9, so this compatibility
layer deliberately does not publish a misleading `Paper.proposition9` alias.
-/

end Proposition9

/--
Paper Proposition 10 (`prop:shiftedbound`).

As with `Theorem5.uniformBound`, the bound is stated for **every** complexity
`R`, with `A` depending on `k`, `a` and `R`, so that it applies to whatever map
`Paper.proposition4` produces instead of to one `R` extracted from `hUN`.  The
first conjunct is the former existence clause, retained; the two together imply
the earlier `∃ A > 0, ∃ R, … ∧ …` form.
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
                  (U (N - N % lcmUpTo k)) l) z‖ ≤ A := by
  classical
  intro hbox hUN k hk a ha
  refine ⟨hUN k hk, ?_⟩
  intro R
  obtain ⟨C, hC, hc⟩ := _root_.shifted_piece_bound_ok hbox k R a ha
  set T : ℝ := ∑ N ∈ Finset.range (lcmUpTo k),
    ∑ n : ↥(degIdx (k + 1) N), Real.sqrt (Nat.multinomial Finset.univ n.val : ℝ)
    with hTdef
  have hT : 0 ≤ T := Finset.sum_nonneg (fun N _ =>
    Finset.sum_nonneg (fun n _ => Real.sqrt_nonneg _))
  set Q : ℝ := Real.sqrt (((lcmUpTo k : ℝ) + 1) ^ k) with hQdef
  have hQ : 0 < Q := by rw [hQdef]; positivity
  refine ⟨Q * ((R : ℝ) * C + T + 1), by positivity, ?_⟩
  intro U hU α hα hαa N l hl
  apply _root_.shifted_sphere_boundary_ok (k + 1) N (by omega)
  intro z hz hs
  have hscale : Real.sqrt (((N + k).choose k : ℝ) /
      ((N - N % lcmUpTo k + k).choose k : ℝ)) ≤ Q :=
    Real.sqrt_le_sqrt (_root_.shifted_ratio_bound_checked k N)
  by_cases hM : 1 ≤ N - N % lcmUpTo k
  · have hu := hU (N - N % lcmUpTo k) hM (Nat.dvd_sub_mod N)
    have hbound := _root_.shifted_assembly_bound_ok k R N (N % lcmUpTo k)
      (Nat.mod_le N _) α (U (N - N % lcmUpTo k)) hu l z C hC.le
      (fun L hL hL1 θ => hc α hα hαa N (by omega) (N % lcmUpTo k)
        L hL hL1 θ z hz hs)
    apply hbound.trans
    exact mul_le_mul hscale (by linarith) (mul_nonneg (Nat.cast_nonneg R) hC.le) hQ.le
  · have hlcm : 0 < lcmUpTo k := by
      apply Nat.pos_of_ne_zero
      intro hzero
      obtain ⟨x, hx, hx0⟩ := Finset.lcm_eq_zero_iff.mp hzero
      have hx1 := (Finset.mem_Icc.mp hx).1
      change x = 0 at hx0
      omega
    have hNsmall : N < lcmUpTo k := by
      have h1 := Nat.mod_lt N hlcm
      have h2 := Nat.mod_le N (lcmUpTo k)
      omega
    have hsum : (∑ n : ↥(degIdx (k + 1) N),
        Real.sqrt (Nat.multinomial Finset.univ n.val : ℝ)) ≤ T :=
      Finset.single_le_sum (f := fun M => ∑ n : ↥(degIdx (k + 1) M),
        Real.sqrt (Nat.multinomial Finset.univ n.val : ℝ))
        (fun M _ => Finset.sum_nonneg (fun n _ => Real.sqrt_nonneg _))
        (Finset.mem_range.mpr hNsmall)
    apply (_root_.shifted_crude_bound_ok k N (N % lcmUpTo k) α
      (U (N - N % lcmUpTo k)) l z hs).trans
    apply mul_le_mul hscale
    · have hRC : 0 ≤ (R : ℝ) * C := mul_nonneg (Nat.cast_nonneg _) hC.le
      linarith
    · exact Finset.sum_nonneg (fun n _ => Real.sqrt_nonneg _)
    · exact hQ.le

namespace Lemma11

noncomputable abbrev scale := @_root_.AllDegreesProof.faceScale
noncomputable abbrev lift := @_root_.AllDegreesProof.faceLift
theorem evaluation :
  ∀ (k N i : ℕ) (hi : i ≤ N) (c : ℂ)
    (v : PolySpaceH k (N-i)) (z : Fin (k+1) → ℂ),
polyEval (k+1) N (_root_.AllDegreesProof.faceLift k N i c v) z =
      c * z (Fin.last k)^i * polyEval k (N-i) v (Fin.init z) :=
  @_root_.AllDegreesProof.faceLift_eval

theorem isometry :
  ∀ (k N i : ℕ) (hi : i ≤ N)
    (v w : PolySpaceH k (N-i)),
polyInner (k+1) N (_root_.AllDegreesProof.faceLift k N i (_root_.AllDegreesProof.faceScale k N i) v)
      (_root_.AllDegreesProof.faceLift k N i (_root_.AllDegreesProof.faceScale k N i) w) = polyInner k (N-i) v w :=
  @_root_.AllDegreesProof.face_norm_inner

theorem sphereBound :
  ∀ (k N i : ℕ) (hk : 1 ≤ k) (hi : i ≤ N)
    (v : PolySpaceH k (N-i)) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ z ∈ UniformBoundUnit.cSphere k, ‖polyEval k (N-i) v z‖ ≤ C)
    (z : Fin (k+1) → ℂ) (hz : z ∈ UniformBoundUnit.cSphere (k+1)),
‖polyEval (k+1) N (_root_.AllDegreesProof.faceLift k N i (_root_.AllDegreesProof.faceScale k N i) v) z‖ ≤
      C * Real.sqrt (((N+k).choose k : ℝ) / ((N-i+k-1).choose (k-1) : ℝ)) :=
  @_root_.AllDegreesProof.face_eval_bound

/-!
These declarations cover the exact isometry and the quantitative evaluation
bound used downstream.  The paper's separate asymptotic notation for the
normalizing factor is not bundled as a theorem, so there is intentionally no
overstated `Paper.lemma11` alias.
-/

end Lemma11

/-- Paper Lemma 12 (`lem:absorption`). -/
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

/-! ## Exponential-sum results -/

/-- Paper Definition 13 (`def:balanced`). -/
abbrev definition13 := @_root_.IsBalancedPair

/-- Paper Theorem 14 (`thm:general`). -/
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

/-- Paper Proposition 15 (`prop:multiwall`). -/
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

/-- Paper Lemma 16 (`lem:sgn`), the exact finite Fourier expansion. -/
theorem lemma16 :
  ∀ (L : ℕ) (hL : 4 ≤ L) (hLe : Even L) (h : ℤ) (hh : 2 * |h| < (L : ℤ)),
(Int.sign h : ℂ) =
      ∑ l ∈ sgnIndex L, sgnCoeff L l * expTwoPiI (((l * h : ℤ) : ℝ) / (L : ℝ)) :=
  @_root_.lem_sgn

/--
Paper Lemma 16 (`lem:sgn`), the coefficient bound at **every** nonzero
frequency, including the even ones.

The paper sets `ĉ_L(ℓ) = -(2i/L) cot(πℓ/L)` for all `ℓ` and claims
`|ĉ_L(ℓ)| ≤ 2/(π|ℓ|)` for every `0 < |ℓ| < L/2`.  `Paper.Lemma16.coefficientBound`
bounds `sgnCoeff`, which is `0` at even `ℓ` (`Lemma16.evenCoefficientVanishes`),
so it does not export the even case; this states the bound for the cotangent
weight `sgnCotWeight L ℓ` itself, which is `‖ĉ_L(ℓ)‖` at every `ℓ`.
-/
theorem lemma16CotWeightBound :
  ∀ (L : ℕ) (hL : 4 ≤ L) (hLe : Even L) (l : ℤ) (hl : 0 < |l|)
    (hlL : |l| < (L : ℤ) / 2),
|sgnCotWeight L (l : ℝ)| ≤ 2 / (Real.pi * |(l : ℝ)|) := by
  intro L hL hLe l hl hlL
  refine _root_.abs_sgnCotWeight_le L hL l (by rwa [abs_pos] at hl) ?_
  obtain ⟨c, hc⟩ := hLe
  have hLc : (L : ℤ) = (c : ℤ) + (c : ℤ) := by exact_mod_cast hc
  omega

namespace Lemma16

noncomputable abbrev coefficient := @_root_.sgnCoeff
abbrev indexSet := @_root_.sgnIndex
theorem oddCoefficientFormula :
  ∀ (L : ℕ) (l : ℤ) (hl : Odd l),
sgnCoeff L l =
      -(2 * Complex.I / (L : ℂ)) * (Real.cot (Real.pi * (l : ℝ) / (L : ℝ)) : ℂ) :=
  @_root_.sgnCoeff_of_odd

theorem evenCoefficientVanishes :
  ∀ (L : ℕ) (l : ℤ) (hl : Even l),
sgnCoeff L l = 0 :=
  @_root_.sgnCoeff_of_even

theorem coefficientBound :
  ∀ (L : ℕ) (hL : 4 ≤ L) (l : ℤ) (hl : l ≠ 0)
    (hlL : 2 * |l| < (L : ℤ)),
‖sgnCoeff L l‖ ≤ 2 / (Real.pi * |(l : ℝ)|) :=
  @_root_.norm_sgnCoeff_le

theorem expansion :
  ∀ (L : ℕ) (hL : 4 ≤ L) (hLe : Even L) (h : ℤ) (hh : 2 * |h| < (L : ℤ)),
(Int.sign h : ℂ) =
      ∑ l ∈ sgnIndex L, sgnCoeff L l * expTwoPiI (((l * h : ℤ) : ℝ) / (L : ℝ)) :=
  @_root_.lem_sgn

end Lemma16

/--
Paper Lemma 17 (`lem:poisson`), its exact Poisson-summation identity.  The
decay half of the lemma is `Lemma17.decay`.
-/
theorem lemma17 :
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

namespace Lemma17

theorem summation :
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

theorem decay :
  ∀ (Λ : ℝ) (hΛ : 1 ≤ Λ),
∃ C > 0, ∀ U : ℝ → ℂ, IsSmoothCutoff U →
      ∀ lam : ℝ, |lam| ≤ Λ → ∀ xi : ℝ,
        ‖oscIntegralW U lam xi‖ ≤
          C * (1 + (∫ t : ℝ, ‖deriv U t‖) + (∫ t : ℝ, ‖deriv (deriv U) t‖)) /
            (1 + |xi| ^ 2) :=
  @_root_.lem_poisson_decay

end Lemma17

/-- Paper Lemma 18 (`lem:gaussphase`). -/
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

/-- Paper Lemma 19 (`lem:weylgauss`). -/
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

/-! ## Polyhedral decomposition results -/

/-- Paper Definition 20 (`def:balanced-W`). -/
abbrev definition20 := @_root_.IsBalancedWrt

/-- Paper Theorem 21 (`thm:decomp`). -/
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

/-- Paper Definition 22 (`def:piece`). -/
abbrev definition22 := @_root_.Piece

namespace Definition22

abbrev polyhedron := @_root_.polyPZ
abbrev quadraticForm := @_root_.Piece.quad
abbrev side := @_root_.Piece.side
noncomputable abbrev minimumSide := @_root_.Piece.minSide

end Definition22

/-- Paper Definition 23 (`def:transition`), the transition predicate. -/
abbrev definition23 := @_root_.IsTransition

namespace Definition23

abbrev size := @_root_.transitionSize
abbrev decomposition := @_root_.IsDecomposition
abbrev affineImage := @_root_.pieceAffineImage

end Definition23

/--
Paper Lemma 24 (`lem:compose`), the decomposition-composition assertion.
Transition composition, size control, and products are exported in `Lemma24`.
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

namespace Lemma24

theorem transitionComposition :
  ∀ {d : ℕ} {p p' p'' : Piece d} {u v : Fin d → ℤ}
    {Φ Ψ : Matrix (Fin d) (Fin d) ℤ}
    (h : IsTransition p p' u Φ) (h' : IsTransition p' p'' v Ψ),
IsTransition p p'' (u + Φ *ᵥ v) (Φ * Ψ) ∧
      transitionSize (Φ * Ψ) ≤ d * transitionSize Φ * transitionSize Ψ :=
  @_root_.IsTransition.comp

theorem decompositionComposition :
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

theorem compositionSizeBound :
  ∀ {d : ℕ} (Φ Ψ : Matrix (Fin d) (Fin d) ℤ),
transitionSize (Φ * Ψ) ≤ d * transitionSize Φ * transitionSize Ψ :=
  @_root_.transitionSize_mul_le

noncomputable abbrev productPiece := @_root_.Piece.prod
theorem transitionProduct :
  ∀ {d₁ d₂ : ℕ}
    {p₁ p₁' : Piece d₁} {p₂ p₂' : Piece d₂}
    {u₁ : Fin d₁ → ℤ} {u₂ : Fin d₂ → ℤ}
    {Φ₁ : Matrix (Fin d₁) (Fin d₁) ℤ} {Φ₂ : Matrix (Fin d₂) (Fin d₂) ℤ}
    (h₁ : IsTransition p₁ p₁' u₁ Φ₁) (h₂ : IsTransition p₂ p₂' u₂ Φ₂),
IsTransition (p₁.prod p₂) (p₁'.prod p₂') (Fin.append u₁ u₂)
      (blockDiagMat Φ₁ Φ₂) :=
  @_root_.IsTransition.prod

theorem decompositionProduct :
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

theorem productSizeBound :
  ∀ {d₁ d₂ : ℕ}
    (Φ₁ : Matrix (Fin d₁) (Fin d₁) ℤ)
    (Φ₂ : Matrix (Fin d₂) (Fin d₂) ℤ),
transitionSize (blockDiagMat Φ₁ Φ₂) ≤
      max (transitionSize Φ₁) (transitionSize Φ₂) :=
  @_root_.transitionSize_blockDiagMat_le

end Lemma24

/--
Paper Lemma 25 (`lem:split`), the disjoint identity-transition decomposition.
The piece, index-decrease, and slab-width assertions are in `Lemma25`.
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

namespace Lemma25

theorem plusIsPiece :
  ∀ {d : ℕ} (p : Piece d) (hJ : ∀ j, p.lo j ≤ p.hi j)
    (w : Fin d → ℤ) (b : ℤ) (hmem : (w, b) ∈ p.W) (hmix : p.IsMixed (w, b)),
∃ p' : Piece d, p'.W = p.splitPlusW w b ∧ p'.lo = p.lo ∧ p'.hi = p.hi ∧
      p'.gamma = p.gamma ∧ p'.A = p.A + 2 * d :=
  @_root_.Piece.splitPlus_isPiece

theorem minusIsPiece :
  ∀ {d : ℕ} (p : Piece d) (hJ : ∀ j, p.lo j ≤ p.hi j)
    (w : Fin d → ℤ) (b : ℤ) (hmem : (w, b) ∈ p.W) (hmix : p.IsMixed (w, b)),
∃ p' : Piece d, p'.W = p.splitMinusW w b ∧ p'.lo = p.lo ∧ p'.hi = p.hi ∧
      p'.gamma = p.gamma ∧ p'.A = p.A + 1 :=
  @_root_.Piece.splitMinus_isPiece

theorem decomposition :
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

theorem plusIndexDecreases :
  ∀ {d : ℕ} (p pPlus : Piece d)
    (hJ : ∀ j, p.lo j ≤ p.hi j) (w : Fin d → ℤ) (b : ℤ)
    (hmem : (w, b) ∈ p.W) (hmix : p.IsMixed (w, b))
    (hPlusW : pPlus.W = p.splitPlusW w b) (hlo : pPlus.lo = p.lo) (hhi : pPlus.hi = p.hi)
    (hgamma : pPlus.gamma = p.gamma) (hA : pPlus.A = p.A + 2 * d),
pPlus.index < p.index :=
  @_root_.Piece.splitPlus_index_lt

theorem minusSlabWidth :
  ∀ {d : ℕ} (p : Piece d)
    (hJ : ∀ j, p.lo j ≤ p.hi j) (w : Fin d → ℤ) (b : ℤ)
    (hmem : (w, b) ∈ p.W) (hmix : p.IsMixed (w, b))
    (x x' : Fin d → ℤ) (hx : x ∈ polyPZ d (p.splitMinusW w b))
    (hx' : x' ∈ polyPZ d (p.splitMinusW w b)),
|∑ j, p.longPart w j * (x j - x' j)| < (p.A : ℤ) ^ 2 * (p.minSide : ℤ) :=
  @_root_.Piece.splitMinus_longPart_variation_lt

end Lemma25

/-- Paper Lemma 26 (`lem:short-coordinate`).  The paper's translations form a
*set* `U ⊂ ℤ^d`, one piece per `u ∈ U`; `Function.Injective U` is that, for the
`Fin M`-indexed family. -/
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

/-- Paper Proposition 27 (`prop:pieces`). -/
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

/-- Paper Proposition 28 (`prop:fold`). -/
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

end Paper
