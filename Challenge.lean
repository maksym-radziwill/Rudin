import Mathlib

/-!
# Comparator challenge: Theorem 1 (`thm:onb`), Rudin's problem

The trusted statement for `lake comparator` (configured by `comparator.json`).

The four definitions below are copied verbatim from `PaperFormalization/Core.lean`
(lines 621–632), in the same context: `import Mathlib` and `open scoped Matrix`, at the
root namespace. The theorem is copied verbatim from `PaperFormalization/Statements.lean`
(lines 474–481), inside `namespace PaperReview` as there, with its proof replaced by
`sorry`.

Comparator checks that the solution module (`PaperFormalization.Statements`) proves
`PaperReview.theorem1` with exactly this statement, that the definitions it uses are
identical to these, that only the permitted axioms are used, and that the kernel accepts
the proof.

What remains for a human to check is that this file says what the paper's Theorem 1
says. In particular, `polyInner` is Rudin's coefficient formula for the inner product
of the Hardy space, not an integral over the sphere (README, "Deviations", item 1).

This module is deliberately not a default build target: it contains `sorry`, so
`lake build` and `lake check` must not build it.
-/

open scoped Matrix

def degIdx (K N : ℕ) : Finset (Fin K → ℕ) := Finset.piAntidiag Finset.univ N

abbrev PolySpaceH (K N : ℕ) : Type := ↥(degIdx K N) → ℂ

noncomputable def polyEval (K N : ℕ) (c : PolySpaceH K N) (z : Fin K → ℂ) : ℂ :=
  ∑ n : ↥(degIdx K N), c n * ∏ s, z s ^ ((n : Fin K → ℕ) s)

noncomputable def polyInner (K N : ℕ) (c d : PolySpaceH K N) : ℂ :=
  ((Nat.choose (N + K - 1) (K - 1) : ℂ))⁻¹ *
    ∑ n : ↥(degIdx K N),
      ((Nat.multinomial Finset.univ (n : Fin K → ℕ) : ℂ))⁻¹ * c n * (starRingEnd ℂ) (d n)

namespace PaperReview

open scoped Matrix

theorem theorem1 :
  ∀ (K : ℕ) (hK : 2 ≤ K),
∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ,
        ∃ φ : Module.Basis (Fin (Module.finrank ℂ (PolySpaceH K N))) ℂ (PolySpaceH K N),
          (∀ i j, polyInner K N (φ i) (φ j) = if i = j then 1 else 0) ∧
          ∀ i, ∀ z : Fin K → ℂ, ∑ s, ‖z s‖ ^ 2 < 1 →
            ‖polyEval K N (φ i) z‖ ≤ C := by
  sorry

end PaperReview
