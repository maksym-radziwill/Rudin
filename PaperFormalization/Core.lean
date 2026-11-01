import Mathlib

set_option linter.all false

open scoped Matrix

/-- The equivalence used to glue the two halves of the recursive construction. -/
def haarEquiv (n : ℕ) : Fin (2 ^ n) ⊕ Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
  finSumFinEquiv.trans (finCongr (by ring))

/-- The matrices of the Absorption Lemma. -/
noncomputable def haarR : (n : ℕ) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ
  | 0 => 1
  | n + 1 =>
      (Real.sqrt 2)⁻¹ •
        Matrix.reindex (haarEquiv n) (haarEquiv n)
          (Matrix.fromBlocks (haarR n) 1 (haarR n) (-1))

theorem haarR_mul_transpose (n : ℕ) : haarR n * (haarR n)ᵀ = 1 := by
  induction n with
  | zero => simp [haarR]
  | succ n ih =>
    have hb :
        Matrix.fromBlocks (haarR n) 1 (haarR n) (-1) *
          (Matrix.fromBlocks (haarR n) 1 (haarR n) (-1))ᵀ =
        (2 : ℝ) • (1 : Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n)) _ ℝ) := by
      simp only [Matrix.fromBlocks_transpose, Matrix.transpose_one,
        Matrix.transpose_neg, Matrix.fromBlocks_multiply,
        Matrix.mul_one, Matrix.mul_neg, neg_neg, ih]
      rw [show (2 : ℝ) • (1 : Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n)) _ ℝ) =
        1 + 1 by module]
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
      simp
    have hs : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * (2 : ℝ) = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
      norm_num
    rw [haarR, Matrix.transpose_smul, Matrix.transpose_reindex,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, hb]
    simp only [Matrix.submatrix_smul, Pi.smul_apply, smul_smul, hs, one_smul]
    exact Matrix.submatrix_one _ (haarEquiv n).symm.injective


namespace HaarRowProof

def haarBlock (n l : ℕ) : Finset (Fin (2 ^ n)) :=
  Finset.univ.filter fun j => 2 ^ l ≤ (j : ℕ) ∧ (j : ℕ) < 2 ^ (l + 1)

lemma haarEquiv_inl_val (n : ℕ) (i : Fin (2 ^ n)) :
    (haarEquiv n (Sum.inl i)).val = i.val := by
  simp [haarEquiv, finSumFinEquiv_apply_left]

lemma haarEquiv_inr_val (n : ℕ) (i : Fin (2 ^ n)) :
    (haarEquiv n (Sum.inr i)).val = 2 ^ n + i.val := by
  simp [haarEquiv, finSumFinEquiv_apply_right, Nat.add_comm]

lemma haarR_step (n : ℕ) (s j : Fin (2 ^ n) ⊕ Fin (2 ^ n)) :
    haarR (n + 1) (haarEquiv n s) (haarEquiv n j) =
      (Real.sqrt 2)⁻¹ *
        Matrix.fromBlocks (haarR n) 1 (haarR n) (-1) s j := by
  simp [haarR, Matrix.reindex_apply, Matrix.submatrix_apply]

lemma haarScale (n : ℕ) :
    (Real.sqrt 2)⁻¹ * (2 : ℝ) ^ (-(n : ℝ) / 2) =
      (2 : ℝ) ^ (-((n + 1 : ℕ) : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow,
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  push_cast
  ring

theorem haarR_apply_zero (n : ℕ) (s : Fin (2 ^ n)) :
    haarR n s 0 = (2 : ℝ) ^ (-(n : ℝ) / 2) := by
  induction n with
  | zero =>
      have hs : s = 0 := by
        apply Fin.ext
        have := s.isLt
        norm_num at this ⊢
      subst s
      norm_num [haarR]
  | succ n ih =>
      have hz : haarEquiv n (Sum.inl (0 : Fin (2 ^ n))) = 0 := by
        apply Fin.ext
        simp [haarEquiv, finSumFinEquiv_apply_left]
      have hz' : (haarEquiv n).symm 0 = Sum.inl (0 : Fin (2 ^ n)) := by
        rw [← hz, Equiv.symm_apply_apply]
      simp only [haarR, Matrix.smul_apply, Matrix.reindex_apply,
        Matrix.submatrix_apply, hz', smul_eq_mul]
      rcases (haarEquiv n).symm s with t | t <;>
        simpa only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, ih]
          using haarScale n

lemma haarScale_block (n l : ℕ) :
    (Real.sqrt 2)⁻¹ * (2 : ℝ) ^ (((l : ℝ) - n) / 2) =
      (2 : ℝ) ^ (((l : ℝ) - (n + 1 : ℕ)) / 2) := by
  rw [Real.sqrt_eq_rpow,
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  push_cast
  ring

lemma haarScale_last (n : ℕ) :
    (Real.sqrt 2)⁻¹ =
      (2 : ℝ) ^ (((n : ℝ) - (n + 1 : ℕ)) / 2) := by
  rw [Real.sqrt_eq_rpow,
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  push_cast
  ring

lemma haarBlock_inl_iff (n l : ℕ) (j : Fin (2 ^ n)) :
    haarEquiv n (Sum.inl j) ∈ haarBlock (n + 1) l ↔
      j ∈ haarBlock n l := by
  simp [haarBlock, haarEquiv_inl_val]

lemma haarBlock_inr_not (n l : ℕ) (hl : l < n) (j : Fin (2 ^ n)) :
    haarEquiv n (Sum.inr j) ∉ haarBlock (n + 1) l := by
  intro h
  have h' := (Finset.mem_filter.mp h).2.2
  rw [haarEquiv_inr_val] at h'
  have hp : 2 ^ (l + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hl
  omega

lemma haarBlock_top_inl_not (n : ℕ) (j : Fin (2 ^ n)) :
    haarEquiv n (Sum.inl j) ∉ haarBlock (n + 1) n := by
  intro h
  have h' := (Finset.mem_filter.mp h).2.1
  rw [haarEquiv_inl_val] at h'
  exact (not_le_of_gt j.isLt) h'

lemma haarBlock_top_inr (n : ℕ) (j : Fin (2 ^ n)) :
    haarEquiv n (Sum.inr j) ∈ haarBlock (n + 1) n := by
  simp only [haarBlock, Finset.mem_filter, Finset.mem_univ, true_and,
    haarEquiv_inr_val, pow_succ]
  have := j.isLt
  omega

lemma haarR_left_ne (n : ℕ) (r : Fin (2 ^ n) ⊕ Fin (2 ^ n))
    (j : Fin (2 ^ n)) :
    haarR (n + 1) (haarEquiv n r) (haarEquiv n (Sum.inl j)) ≠ 0 ↔
      haarR n (r.elim id id) j ≠ 0 := by
  have hc : (Real.sqrt (2 : ℝ))⁻¹ ≠ 0 := by positivity
  cases r <;> simp [haarR_step, Matrix.fromBlocks, hc]

lemma haarR_right_ne (n : ℕ) (r : Fin (2 ^ n) ⊕ Fin (2 ^ n))
    (j : Fin (2 ^ n)) :
    haarR (n + 1) (haarEquiv n r) (haarEquiv n (Sum.inr j)) ≠ 0 ↔
      j = r.elim id id := by
  have hc : (Real.sqrt (2 : ℝ))⁻¹ ≠ 0 := by positivity
  cases r with
  | inl i =>
      by_cases h : i = j
      · subst j
        simp [haarR_step, Matrix.fromBlocks, hc]
      · simp [haarR_step, Matrix.fromBlocks, Matrix.one_apply, h, hc, Ne.symm h]
  | inr i =>
      by_cases h : i = j
      · subst j
        simp [haarR_step, Matrix.fromBlocks, hc]
      · simp [haarR_step, Matrix.fromBlocks, Matrix.one_apply, h, hc, Ne.symm h]

lemma haarR_sum_abs_step (n : ℕ) (s : Fin (2 ^ n) ⊕ Fin (2 ^ n)) :
    (∑ j, |haarR (n + 1) (haarEquiv n s) j|) =
      (Real.sqrt 2)⁻¹ * ((∑ j, |haarR n (s.elim id id) j|) + 1) := by
  classical
  rw [← (haarEquiv n).sum_comp, Fintype.sum_sum_type]
  cases s <;>
    simp [haarR_step, Matrix.one_apply, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg 2)),
      apply_ite abs, ← Finset.mul_sum, mul_add]

theorem haarR_existsUnique_ne_zero_of_mem_haarBlock
    (n l : ℕ) (hl : l < n) (s : Fin (2 ^ n)) :
    ∃! j : Fin (2 ^ n), j ∈ haarBlock n l ∧ haarR n s j ≠ 0 := by
  induction n generalizing l with
  | zero => omega
  | succ n ih =>
      obtain ⟨r, rfl⟩ := (haarEquiv n).surjective s
      by_cases hlt : l < n
      · obtain ⟨j, hj, hu⟩ := ih l hlt (r.elim id id)
        refine ⟨haarEquiv n (Sum.inl j),
          ⟨(haarBlock_inl_iff n l j).2 hj.1, (haarR_left_ne n r j).2 hj.2⟩, ?_⟩
        intro k hk
        obtain ⟨t, rfl⟩ := (haarEquiv n).surjective k
        cases t with
        | inl k =>
            have he : k = j :=
              hu k ⟨(haarBlock_inl_iff n l k).1 hk.1,
                (haarR_left_ne n r k).1 hk.2⟩
            subst k
            rfl
        | inr k => exact False.elim (haarBlock_inr_not n l hlt k hk.1)
      · have he : l = n := by omega
        subst l
        refine ⟨haarEquiv n (Sum.inr (r.elim id id)),
          ⟨haarBlock_top_inr n _, (haarR_right_ne n r _).2 rfl⟩, ?_⟩
        intro k hk
        obtain ⟨t, rfl⟩ := (haarEquiv n).surjective k
        cases t with
        | inl k => exact False.elim (haarBlock_top_inl_not n k hk.1)
        | inr k => rw [(haarR_right_ne n r k).1 hk.2]

lemma haarR_left_abs (n : ℕ) (r : Fin (2 ^ n) ⊕ Fin (2 ^ n))
    (j : Fin (2 ^ n)) :
    |haarR (n + 1) (haarEquiv n r) (haarEquiv n (Sum.inl j))| =
      (Real.sqrt 2)⁻¹ * |haarR n (r.elim id id) j| := by
  have hc : 0 ≤ (Real.sqrt (2 : ℝ))⁻¹ := by positivity
  cases r <;> simp [haarR_step, Matrix.fromBlocks, abs_mul, abs_of_nonneg hc]

lemma haarR_right_abs (n : ℕ) (r : Fin (2 ^ n) ⊕ Fin (2 ^ n))
    (j : Fin (2 ^ n))
    (h : haarR (n + 1) (haarEquiv n r) (haarEquiv n (Sum.inr j)) ≠ 0) :
    |haarR (n + 1) (haarEquiv n r) (haarEquiv n (Sum.inr j))| =
      (Real.sqrt 2)⁻¹ := by
  have he := (haarR_right_ne n r j).1 h
  subst j
  have hc : 0 ≤ (Real.sqrt (2 : ℝ))⁻¹ := by positivity
  cases r <;>
    simp [haarR_step, Matrix.fromBlocks, Matrix.one_apply, abs_mul,
      abs_of_nonneg hc]

theorem haarR_abs_of_mem_haarBlock (n l : ℕ) (hl : l < n)
    (s j : Fin (2 ^ n)) (hj : j ∈ haarBlock n l) (hne : haarR n s j ≠ 0) :
    |haarR n s j| = (2 : ℝ) ^ (((l : ℝ) - (n : ℝ)) / 2) := by
  induction n generalizing l with
  | zero => omega
  | succ n ih =>
      obtain ⟨r, rfl⟩ := (haarEquiv n).surjective s
      obtain ⟨t, rfl⟩ := (haarEquiv n).surjective j
      by_cases hlt : l < n
      · cases t with
        | inl j =>
            rw [haarR_left_abs]
            rw [ih l hlt (r.elim id id) j
              ((haarBlock_inl_iff n l j).1 hj)
              ((haarR_left_ne n r j).1 hne)]
            exact haarScale_block n l
        | inr j => exact False.elim (haarBlock_inr_not n l hlt j hj)
      · have he : l = n := by omega
        subst l
        cases t with
        | inl j => exact False.elim (haarBlock_top_inl_not n j hj)
        | inr j =>
            rw [haarR_right_abs n r j hne]
            exact haarScale_last n

lemma haarR_prefix_step (n d : ℕ) (hd : d ≤ 2 ^ n)
    (s : Fin (2 ^ n) ⊕ Fin (2 ^ n)) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (2 ^ (n + 1)) => j.val < d),
      |haarR (n + 1) (haarEquiv n s) j|) =
    (Real.sqrt 2)⁻¹ *
      (∑ j ∈ Finset.univ.filter (fun j : Fin (2 ^ n) => j.val < d),
        |haarR n (s.elim id id) j|) := by
  classical
  simp only [Finset.sum_filter]
  rw [← (haarEquiv n).sum_comp, Fintype.sum_sum_type]
  have hr (j : Fin (2 ^ n)) : ¬ 2 ^ n + j.val < d := by omega
  cases s <;>
    simp [haarEquiv_inl_val, haarEquiv_inr_val, hr, haarR_step,
      abs_mul, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg 2)),
      Finset.mul_sum, mul_ite]

lemma haarR_sum_abs_total_le (n : ℕ) (s : Fin (2 ^ n)) :
    (∑ j, |haarR n s j|) ≤ 3 := by
  classical
  induction n with
  | zero =>
      simp [haarR, Matrix.one_apply, apply_ite abs]
      split_ifs <;> norm_num
  | succ n ih =>
      obtain ⟨s, rfl⟩ := (haarEquiv n).surjective s
      rw [haarR_sum_abs_step]
      have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      have h4 : (4 : ℝ) ≤ Real.sqrt 2 * 3 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      calc
        _ ≤ (Real.sqrt 2)⁻¹ * 4 :=
          mul_le_mul_of_nonneg_left
            (by linarith [ih (s.elim id id)]) (inv_nonneg.mpr hs.le)
        _ ≤ 3 := (inv_mul_le_iff₀ hs).2 h4

lemma haar_numeric (n d : ℕ) (h : 2 ^ n < d) :
    3 ≤ 5 * Real.sqrt d * (2 : ℝ) ^ (-((n + 1 : ℕ) : ℝ) / 2) := by
  have hp : 0 < (2 : ℝ) ^ ((n : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hb : (2 : ℝ) ^ ((n : ℝ) / 2) ≤ Real.sqrt (d : ℝ) := by
    calc
      _ = Real.sqrt ((2 : ℝ) ^ n) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      _ ≤ Real.sqrt (d : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast (Nat.le_of_lt h))
  have hs : 3 * Real.sqrt 2 ≤ 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg (2 : ℝ)]
  have he : -((n + 1 : ℕ) : ℝ) / 2 = -((n : ℝ) / 2 + 1 / 2) := by
    push_cast
    ring
  rw [he, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.sqrt_eq_rpow]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc
    3 * ((2 : ℝ) ^ ((n : ℝ) / 2) * Real.sqrt 2) =
        (2 : ℝ) ^ ((n : ℝ) / 2) * (3 * Real.sqrt 2) := by ring
    _ ≤ (2 : ℝ) ^ ((n : ℝ) / 2) * 5 :=
      mul_le_mul_of_nonneg_left hs hp.le
    _ ≤ 5 * Real.sqrt (d : ℝ) := by nlinarith

theorem haarR_sum_abs_le (n : ℕ) (s : Fin (2 ^ n)) (d : ℕ)
    (hd : 1 ≤ d) (hdn : d ≤ 2 ^ n) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (2 ^ n) => (j : ℕ) < d),
      |haarR n s j| ≤
      5 * Real.sqrt d * (2 : ℝ) ^ (-(n : ℝ) / 2) := by
  classical
  induction n generalizing d with
  | zero =>
      have hd1 : d = 1 := by
        norm_num at hdn
        omega
      subst d
      simp [haarR, Matrix.one_apply, apply_ite abs]
      split_ifs <;> norm_num
  | succ n ih =>
      obtain ⟨r, rfl⟩ := (haarEquiv n).surjective s
      by_cases h : d ≤ 2 ^ n
      · rw [haarR_prefix_step n d h]
        calc
          _ ≤ (Real.sqrt 2)⁻¹ *
              (5 * Real.sqrt d * (2 : ℝ) ^ (-(n : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left (ih (r.elim id id) d hd h) (by positivity)
          _ = 5 * Real.sqrt d * (2 : ℝ) ^ (-((n + 1 : ℕ) : ℝ) / 2) := by
            rw [← haarScale n]
            ring
      · calc
          _ ≤ ∑ j, |haarR (n + 1) (haarEquiv n r) j| :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (by intro j _ _; exact abs_nonneg _)
          _ ≤ 3 := haarR_sum_abs_total_le _ _
          _ ≤ _ := haar_numeric n d (by omega)

end HaarRowProof

lemma haarRow_nat_scale (n : ℕ) :
    (2 : ℝ) ^ (-(n : ℝ) / 2) = (Real.sqrt 2 ^ n)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

lemma haarRow_int_scale (l n : ℕ) :
    (2 : ℝ) ^ (((l : ℝ) - (n : ℝ)) / 2) =
      Real.sqrt 2 ^ ((l : ℤ) - (n : ℤ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  push_cast
  ring

/-- The first entry of any row of `haarR n` equals `2 ^ (-n/2)`. -/
theorem haarR_apply_zero (n : ℕ) (s : Fin (2 ^ n)) :
    haarR n s ⟨0, Nat.two_pow_pos n⟩ = (Real.sqrt 2 ^ n)⁻¹ := by
  have hz : (⟨0, Nat.two_pow_pos n⟩ : Fin (2 ^ n)) = 0 := by
    apply Fin.ext
    simp
  rw [hz]
  exact (HaarRowProof.haarR_apply_zero n s).trans (haarRow_nat_scale n)

/-- In each dyadic block of columns `2 ^ ℓ ≤ j < 2 ^ (ℓ + 1)` with `ℓ < n`, a row of
`haarR n` has exactly one nonzero entry, and its modulus is `2 ^ ((ℓ - n)/2)`. -/
theorem haarR_dyadic_block (n : ℕ) (s : Fin (2 ^ n)) (l : ℕ) (hl : l < n) :
    ∃ j : Fin (2 ^ n), 2 ^ l ≤ (j : ℕ) ∧ (j : ℕ) < 2 ^ (l + 1) ∧
      |haarR n s j| = Real.sqrt 2 ^ ((l : ℤ) - (n : ℤ)) ∧
      ∀ j' : Fin (2 ^ n), 2 ^ l ≤ (j' : ℕ) → (j' : ℕ) < 2 ^ (l + 1) → j' ≠ j →
        haarR n s j' = 0 := by
  classical
  obtain ⟨j, hj, hu⟩ :=
    HaarRowProof.haarR_existsUnique_ne_zero_of_mem_haarBlock n l hl s
  have hb := (Finset.mem_filter.mp hj.1).2
  refine ⟨j, hb.1, hb.2, ?_, ?_⟩
  · rw [← haarRow_int_scale]
    exact HaarRowProof.haarR_abs_of_mem_haarBlock n l hl s j hj.1 hj.2
  · intro j' hlow hhigh hne
    by_contra hnonzero
    exact hne (hu j'
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlow, hhigh⟩, hnonzero⟩)

/-- The tail bound: the absolute values of the first `d` entries of a row of `haarR n`
sum to at most `5 √d · 2 ^ (-n/2)`. -/
theorem haarR_row_partial_sum_le (n : ℕ) (s : Fin (2 ^ n)) (d : ℕ)
    (hd : 1 ≤ d) (hdn : d ≤ 2 ^ n) :
    ∑ j ∈ {j : Fin (2 ^ n) | (j : ℕ) < d}, |haarR n s j| ≤
      5 * Real.sqrt d * (Real.sqrt 2 ^ n)⁻¹ := by
  simpa only [haarRow_nat_scale] using
    HaarRowProof.haarR_sum_abs_le n s d hd hdn


namespace AbsorptionProof

noncomputable def haarQ (D : ℕ) (hD : 1 ≤ D) :
    Matrix (Fin D) (Fin D) ℝ :=
  Matrix.reindex
    (finSumFinEquiv.trans
      (finCongr (Nat.add_sub_cancel' (Nat.pow_log_le_self 2 (by omega)))))
    (finSumFinEquiv.trans
      (finCongr (Nat.add_sub_cancel' (Nat.pow_log_le_self 2 (by omega)))))
    (Matrix.fromBlocks (haarR (Nat.log 2 D))
      (0 : Matrix (Fin (2 ^ Nat.log 2 D)) (Fin (D - 2 ^ Nat.log 2 D)) ℝ)
      0 (1 : Matrix (Fin (D - 2 ^ Nat.log 2 D)) (Fin (D - 2 ^ Nat.log 2 D)) ℝ))

noncomputable def absorptionEquiv (D : ℕ) (hD : 1 ≤ D) :
    Fin (2 ^ Nat.log 2 D) ⊕ Fin (D - 2 ^ Nat.log 2 D) ≃ Fin D :=
  finSumFinEquiv.trans
    (finCongr (Nat.add_sub_cancel' (Nat.pow_log_le_self 2 (by omega))))

lemma absorptionEquiv_left (D : ℕ) (hD : 1 ≤ D)
    (j : Fin (2 ^ Nat.log 2 D)) :
    (absorptionEquiv D hD (Sum.inl j)).val = j.val := by
  simp [absorptionEquiv, finSumFinEquiv_apply_left]

lemma absorptionEquiv_right (D : ℕ) (hD : 1 ≤ D)
    (j : Fin (D - 2 ^ Nat.log 2 D)) :
    (absorptionEquiv D hD (Sum.inr j)).val = 2 ^ Nat.log 2 D + j.val := by
  simp [absorptionEquiv, finSumFinEquiv_apply_right, Nat.add_comm]

lemma absorptionQ_apply (D : ℕ) (hD : 1 ≤ D)
    (s j : Fin (2 ^ Nat.log 2 D) ⊕ Fin (D - 2 ^ Nat.log 2 D)) :
    haarQ D hD (absorptionEquiv D hD s) (absorptionEquiv D hD j) =
      Matrix.fromBlocks (haarR (Nat.log 2 D)) 0 0 1 s j := by
  change (Matrix.fromBlocks (haarR (Nat.log 2 D))
    (0 : Matrix (Fin (2 ^ Nat.log 2 D)) (Fin (D - 2 ^ Nat.log 2 D)) ℝ)
    0 (1 : Matrix (Fin (D - 2 ^ Nat.log 2 D)) (Fin (D - 2 ^ Nat.log 2 D)) ℝ))
    ((absorptionEquiv D hD).symm (absorptionEquiv D hD s))
    ((absorptionEquiv D hD).symm (absorptionEquiv D hD j)) = _
  simp

lemma absorptionQ_orthogonal (D : ℕ) (hD : 1 ≤ D) :
    haarQ D hD * (haarQ D hD)ᵀ = 1 := by
  have hb :
      Matrix.fromBlocks (haarR (Nat.log 2 D))
          (0 : Matrix (Fin (2 ^ Nat.log 2 D)) (Fin (D - 2 ^ Nat.log 2 D)) ℝ)
          0 (1 : Matrix (Fin (D - 2 ^ Nat.log 2 D)) (Fin (D - 2 ^ Nat.log 2 D)) ℝ) *
        (Matrix.fromBlocks (haarR (Nat.log 2 D))
          (0 : Matrix (Fin (2 ^ Nat.log 2 D)) (Fin (D - 2 ^ Nat.log 2 D)) ℝ)
          0 (1 : Matrix (Fin (D - 2 ^ Nat.log 2 D)) (Fin (D - 2 ^ Nat.log 2 D)) ℝ))ᵀ = 1 := by
    simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      haarR_mul_transpose, Matrix.fromBlocks_one]
  rw [haarQ, Matrix.transpose_reindex]
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, hb]
  exact Matrix.submatrix_one _ (absorptionEquiv D hD).symm.injective

lemma absorption_weighted (n : ℕ) (s : Fin (2 ^ n)) (d : ℕ)
    (hd : 1 ≤ d) (hdn : d ≤ 2 ^ n) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (f : Fin (2 ^ n) → ℂ)
    (hfB : ∀ j, j.val < d → ‖f j‖ ≤ B)
    (hfA : ∀ j, d ≤ j.val → ‖f j‖ ≤ A) :
    ‖∑ j, (haarR n s j : ℂ) * f j‖ ≤
      3 * A + 5 * B * Real.sqrt d * (Real.sqrt 2 ^ n)⁻¹ := by
  classical
  have hf (j : Fin (2 ^ n)) : ‖f j‖ ≤ A + (if j.val < d then B else 0) := by
    by_cases hj : j.val < d
    · rw [if_pos hj]
      exact (hfB j hj).trans (by linarith)
    · rw [if_neg hj, add_zero]
      exact hfA j (by omega)
  calc
    ‖∑ j, (haarR n s j : ℂ) * f j‖ ≤
        ∑ j, ‖(haarR n s j : ℂ) * f j‖ := norm_sum_le _ _
    _ = ∑ j, |haarR n s j| * ‖f j‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ j, |haarR n s j| * (A + (if j.val < d then B else 0)) := by
      exact Finset.sum_le_sum
        (fun j _ => mul_le_mul_of_nonneg_left (hf j) (abs_nonneg _))
    _ = A * (∑ j, |haarR n s j|) +
        B * (∑ j ∈ Finset.univ.filter (fun j : Fin (2 ^ n) => j.val < d),
          |haarR n s j|) := by
      simp only [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hp : j.val < d <;> simp [hp] <;> ring
    _ ≤ A * 3 + B * (5 * Real.sqrt d * (Real.sqrt 2 ^ n)⁻¹) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (HaarRowProof.haarR_sum_abs_total_le n s) hA)
        (mul_le_mul_of_nonneg_left (haarR_row_partial_sum_le n s d hd hdn) hB)
    _ = _ := by ring

lemma absorption_numeric_ok (n D d : ℕ) (hD : 0 < D)
    (hpow : (D : ℝ) ≤ 2 * (2 : ℝ) ^ n)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    3 * A + 5 * B * Real.sqrt d * (Real.sqrt 2 ^ n)⁻¹ ≤
      10 * A + 10 * B * Real.sqrt ((d : ℝ) / (D : ℝ)) := by
  have hs : 0 < Real.sqrt 2 ^ n := by positivity
  have hs2 : (Real.sqrt 2 ^ n) * (Real.sqrt 2 ^ n) = (2 : ℝ) ^ n := by
    rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]
  have hsq : (D : ℝ) ≤ (2 * (Real.sqrt 2 ^ n)) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt 2 ^ n)]
  have hh := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)] at hh
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hinv : (Real.sqrt 2 ^ n)⁻¹ ≤ 2 / Real.sqrt D :=
    (le_div_iff₀ (by positivity)).2
      ((inv_mul_le_iff₀ hs).2 (by simpa [mul_comm] using hh))
  calc
    _ ≤ 3 * A + 5 * B * Real.sqrt d * (2 / Real.sqrt D) :=
      add_le_add_right
        (mul_le_mul_of_nonneg_left hinv
          (mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 5 by norm_num) hB)
            (Real.sqrt_nonneg _))) _
    _ = 3 * A + 10 * B * Real.sqrt ((d : ℝ) / (D : ℝ)) := by
      rw [Real.sqrt_div (Nat.cast_nonneg d)]
      ring
    _ ≤ _ := by linarith

end AbsorptionProof

/-- **Absorption Lemma** (Olevskii). -/
theorem absorption_lemma {X : Type*} {D : ℕ} (hD : 2 ≤ D)
    (V : Submodule ℂ (X → ℂ))
    (ip : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (φ : Module.Basis (Fin D) ℂ V)
    (hφ : ∀ i j, ip (φ i) (φ j) = if i = j then 1 else 0)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (D₂ : ℕ) (hD₂ : 1 ≤ D₂) (hD₂' : 2 * D₂ ≤ D)
    (hbigB : ∀ j : Fin D, (j : ℕ) < D₂ → ∀ x : X, ‖(φ j : X → ℂ) x‖ ≤ B)
    (hbigA : ∀ j : Fin D, D₂ ≤ (j : ℕ) → ∀ x : X, ‖(φ j : X → ℂ) x‖ ≤ A) :
    ∃ ψ : Module.Basis (Fin D) ℂ V,
      (∀ i j, ip (ψ i) (ψ j) = if i = j then 1 else 0) ∧
      ∀ s : Fin D, ∀ x : X,
        ‖(ψ s : X → ℂ) x‖ ≤ 10 * A + 10 * B * Real.sqrt ((D₂ : ℝ) / (D : ℝ)) := by
  classical
  have hD1 : 1 ≤ D := by omega
  let Q := AbsorptionProof.haarQ D hD1
  let v : Fin D → V := fun s => ∑ j, (Q s j : ℂ) • φ j
  have hv : ∀ s t, ip (v s) (v t) = if s = t then 1 else 0 := by
    intro s t
    change ip (∑ j, (Q s j : ℂ) • φ j) (∑ j, (Q t j : ℂ) • φ j) = _
    simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply,
      LinearMap.smul_apply, hφ, smul_eq_mul]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Complex.conj_ofReal]
    have hst := congrArg
      (fun M : Matrix (Fin D) (Fin D) ℝ => M s t)
      (AbsorptionProof.absorptionQ_orthogonal D hD1)
    change (Q * Qᵀ) s t = (1 : Matrix (Fin D) (Fin D) ℝ) s t at hst
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hst
    calc
      _ = ((∑ j, Q s j * Q t j : ℝ) : ℂ) := by simp [mul_comm]
      _ = _ := by rw [hst]; split_ifs <;> simp
  have hvli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hi := congrArg (fun w : V => ip w (v i)) hc
    simpa [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply,
      LinearMap.smul_apply, hv, smul_eq_mul] using hi
  letI : Nonempty (Fin D) := ⟨⟨0, by omega⟩⟩
  letI : FiniteDimensional ℂ V := Module.Finite.of_basis φ
  let ψ : Module.Basis (Fin D) ℂ V :=
    basisOfLinearIndependentOfCardEqFinrank hvli (Module.finrank_eq_card_basis φ).symm
  have hψ : (ψ : Fin D → V) = v :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  refine ⟨ψ, ?_, ?_⟩
  · simpa only [hψ] using hv
  · intro s x
    change ‖V.subtype ((ψ : Fin D → V) s) x‖ ≤ _
    rw [hψ]
    have heval (s : Fin D) :
        V.subtype (v s) x =
          ∑ j, (AbsorptionProof.haarQ D hD1 s j : ℂ) * V.subtype (φ j) x := by
      simp [v, Q, map_sum, map_smul, Finset.sum_apply]
    rw [heval]
    have hupper : D < 2 ^ (Nat.log 2 D + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) D
    rw [pow_succ] at hupper
    have hdsmall : D₂ ≤ 2 ^ Nat.log 2 D := by omega
    obtain ⟨r, rfl⟩ := (AbsorptionProof.absorptionEquiv D hD1).surjective s
    rw [← (AbsorptionProof.absorptionEquiv D hD1).sum_comp,
      Fintype.sum_sum_type]
    cases r with
    | inl r =>
        simp only [AbsorptionProof.absorptionQ_apply,
          Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.zero_apply, Complex.ofReal_zero, zero_mul,
          Finset.sum_const_zero, add_zero]
        calc
          _ ≤ 3 * A +
              5 * B * Real.sqrt D₂ * (Real.sqrt 2 ^ Nat.log 2 D)⁻¹ := by
            apply AbsorptionProof.absorption_weighted _ _ _ hD₂ hdsmall A B hA hB
            · intro j hj
              exact hbigB _
                (by simpa only [AbsorptionProof.absorptionEquiv_left] using hj) x
            · intro j hj
              exact hbigA _
                (by simpa only [AbsorptionProof.absorptionEquiv_left] using hj) x
          _ ≤ _ := AbsorptionProof.absorption_numeric_ok _ D D₂ (by omega)
            (by exact_mod_cast (show D ≤ 2 * 2 ^ Nat.log 2 D by omega))
            A B hA hB
    | inr r =>
        simp only [AbsorptionProof.absorptionQ_apply,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
          Matrix.zero_apply, Complex.ofReal_zero, zero_mul,
          Finset.sum_const_zero, zero_add]
        simp only [Matrix.one_apply, apply_ite Complex.ofReal,
          Complex.ofReal_one, Complex.ofReal_zero, ite_mul, one_mul,
          zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        have hh := hbigA (AbsorptionProof.absorptionEquiv D hD1 (Sum.inr r))
          (by rw [AbsorptionProof.absorptionEquiv_right]; omega) x
        have hp : 0 ≤ 10 * B * Real.sqrt ((D₂ : ℝ) / (D : ℝ)) := by positivity
        change ‖(φ (AbsorptionProof.absorptionEquiv D hD1 (Sum.inr r)) : X → ℂ) x‖ ≤ _
        linarith


noncomputable def expTwoPiI (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

def lcmUpTo (k : ℕ) : ℕ := (Finset.Icc 1 k).lcm id

def degIdx (K N : ℕ) : Finset (Fin K → ℕ) := Finset.piAntidiag Finset.univ N

abbrev PolySpaceH (K N : ℕ) : Type := ↥(degIdx K N) → ℂ

noncomputable def polyEval (K N : ℕ) (c : PolySpaceH K N) (z : Fin K → ℂ) : ℂ :=
  ∑ n : ↥(degIdx K N), c n * ∏ s, z s ^ ((n : Fin K → ℕ) s)

noncomputable def polyInner (K N : ℕ) (c d : PolySpaceH K N) : ℂ :=
  ((Nat.choose (N + K - 1) (K - 1) : ℂ))⁻¹ *
    ∑ n : ↥(degIdx K N),
      ((Nat.multinomial Finset.univ (n : Fin K → ℕ) : ℂ))⁻¹ * c n * (starRingEnd ℂ) (d n)

def simplexS (k N : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => Finset.range (N + 1)).filter fun j => ∑ s, j s ≤ N

def boxB (k N : ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset fun s : Fin k => Finset.range (N / (k - s.val) + 1)

def polyP (k : ℕ) (L : Finset ((Fin k → ℤ) × ℤ)) : Set (Fin k → ℕ) :=
  {x | ∀ p ∈ L, 0 ≤ (∑ s, p.1 s * (x s : ℤ)) + p.2}

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

noncomputable def basisPhi (k N : ℕ) (α : ℝ) (U : (Fin k → ℕ) → Fin k → ℕ)
    (l : Fin k → ℕ) : PolySpaceH (k + 1) N :=
  fun n =>
    (Real.sqrt (Nat.multinomial Finset.univ (n : Fin (k + 1) → ℕ)) : ℂ) *
      expTwoPiI
        (α * ∑ s, ((n : Fin (k + 1) → ℕ) s : ℝ) ^ 2 +
          ∑ s : Fin k,
            (U (fun t => (n : Fin (k + 1) → ℕ) t.castSucc) s : ℝ) * (l s : ℝ)
              / ((N / (k - s.val) : ℕ) + 1))

lemma onb_exp_add (x y : ℝ) :
    expTwoPiI (x + y) = expTwoPiI x * expTwoPiI y := by
  simp only [expTwoPiI, Complex.ofReal_add, mul_add, Complex.exp_add]

lemma onb_exp_star_ok (x : ℝ) :
    (starRingEnd ℂ) (expTwoPiI x) = expTwoPiI (-x) := by
  rw [expTwoPiI, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

lemma onb_exp_sub_ok (x y : ℝ) :
    expTwoPiI x * (starRingEnd ℂ) (expTwoPiI y) = expTwoPiI (x-y) := by
  rw [onb_exp_star_ok, ← onb_exp_add, sub_eq_add_neg]

lemma onb_coeff_ok (m : ℕ) (hm : 0 < m) (x y z : ℝ) :
    (m : ℂ)⁻¹ * ((Real.sqrt m : ℂ) * expTwoPiI (x+y)) *
      (starRingEnd ℂ) ((Real.sqrt m : ℂ) * expTwoPiI (x+z)) =
        expTwoPiI (y-z) := by
  have hms : (Real.sqrt m : ℂ) * (Real.sqrt m : ℂ) = (m : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (Nat.cast_nonneg m)
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [map_mul, Complex.conj_ofReal]
  calc
    _ = ((m : ℂ)⁻¹ * ((Real.sqrt m : ℂ) * (Real.sqrt m : ℂ))) *
      (expTwoPiI (x+y) * (starRingEnd ℂ) (expTwoPiI (x+z))) := by ring
    _ = _ := by
      rw [hms, inv_mul_cancel₀ hm0, one_mul, onb_exp_sub_ok]
      congr 1
      ring

lemma onb_mem_deg (K N : ℕ) (n : Fin K → ℕ) :
    n ∈ degIdx K N ↔ ∑ i, n i = N := by
  simp [degIdx, Finset.mem_piAntidiag]

lemma onb_mem_simplex (k N : ℕ) (j : Fin k → ℕ) :
    j ∈ simplexS k N ↔ ∑ i, j i ≤ N := by
  simp only [simplexS, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    intro i
    have hi : j i ≤ ∑ t, j t :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

noncomputable def onb_degEquiv_final (k N : ℕ) :
    ↥(degIdx (k+1) N) ≃ ↥(simplexS k N) where
  toFun n := ⟨Fin.init n.1, by
    apply (onb_mem_simplex k N _).2
    have hn := (onb_mem_deg (k+1) N n.1).1 n.2
    rw [Fin.sum_univ_castSucc] at hn
    change (∑ i : Fin k, n.1 i.castSucc) ≤ N
    omega⟩
  invFun j := ⟨Fin.snoc j.1 (N - ∑ i, j.1 i), by
    apply (onb_mem_deg (k+1) N _).2
    rw [Fin.sum_snoc]
    exact Nat.add_sub_of_le ((onb_mem_simplex k N _).1 j.2)⟩
  left_inv n := by
    apply Subtype.ext
    change Fin.snoc (Fin.init n.1) (N - ∑ i, (Fin.init n.1) i) = n.1
    have hn := (onb_mem_deg (k+1) N n.1).1 n.2
    rw [Fin.sum_univ_castSucc] at hn
    have he : N - ∑ i, (Fin.init n.1) i = n.1 (Fin.last k) := by
      simpa only [Fin.init_def] using
        (show N - ∑ i : Fin k, n.1 i.castSucc = n.1 (Fin.last k) by omega)
    rw [he]
    exact Fin.snoc_init_self _
  right_inv j := by
    apply Subtype.ext
    funext i
    change (Fin.snoc (α := fun _ : Fin (k+1) => ℕ)
      j.1 (N - ∑ i, j.1 i)) i.castSucc = j.1 i
    simp

lemma onb_card (k N : ℕ) :
    Fintype.card ↥(degIdx (k+1) N) = (N+k).choose k := by
  rw [Fintype.card_coe, degIdx, ← Finset.map_sym_eq_piAntidiag,
    Finset.card_map, Finset.sym_univ, Finset.card_univ,
    Sym.card_sym_eq_choose, Fintype.card_fin]
  have he : k + 1 + N - 1 = N + k := by omega
  rw [he]
  simpa using (Nat.choose_symm (show k ≤ N+k by omega))

lemma onb_fourier_final (q a b : ℕ) (hq : 0 < q) (ha : a < q) (hb : b < q) :
    (∑ t ∈ Finset.range q, expTwoPiI ((t : ℝ) * ((a : ℝ) - b) / q)) =
      if a = b then (q : ℂ) else 0 := by
  classical
  letI : NeZero q := ⟨by omega⟩
  let e : Fin q ≃ ZMod q :=
    { toFun := fun t => (t.val : ZMod q)
      invFun := fun t => ⟨t.val, ZMod.val_lt t⟩
      left_inv := by
        intro t
        apply Fin.ext
        exact ZMod.val_cast_of_lt t.isLt
      right_inv := by intro t; exact ZMod.natCast_zmod_val t }
  have hc (t : ℕ) :
      expTwoPiI ((t : ℝ) * ((a : ℝ) - b) / q) =
        ZMod.stdAddChar ((t : ZMod q) * ((a : ZMod q) - (b : ZMod q))) := by
    rw [show (t : ZMod q) * ((a : ZMod q) - (b : ZMod q)) =
      (((t : ℤ) * ((a : ℤ) - b) : ℤ) : ZMod q) by
        simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast],
      ZMod.stdAddChar_coe]
    unfold expTwoPiI
    congr 1
    push_cast
    ring
  have hz : ((a : ZMod q) - (b : ZMod q) = 0) ↔ a = b := by
    rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff']
    simp only [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  calc
    _ = ∑ t : Fin q, expTwoPiI ((t.val : ℝ) * ((a : ℝ) - b) / q) :=
      Finset.sum_range _
    _ = ∑ t : Fin q, ZMod.stdAddChar (e t * ((a : ZMod q) - (b : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hc t.val
    _ = ∑ t : ZMod q, ZMod.stdAddChar (t * ((a : ZMod q) - (b : ZMod q))) :=
      e.sum_comp (fun t : ZMod q =>
        ZMod.stdAddChar (t * ((a : ZMod q) - (b : ZMod q))))
    _ = _ := by
      rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
      simp [hz, ZMod.card]

lemma onb_exp_sum {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    expTwoPiI (∑ i, f i) = ∏ i, expTwoPiI (f i) := by
  simp only [expTwoPiI, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]

lemma onb_box_final (k N : ℕ) (l l' : Fin k → ℕ)
    (hl : l ∈ boxB k N) (hl' : l' ∈ boxB k N) :
    (∑ t ∈ boxB k N, expTwoPiI (∑ s : Fin k,
      (t s : ℝ) * ((l s : ℝ) - l' s) / ((N / (k-s.val) : ℕ) + 1))) =
      if l = l' then ((boxB k N).card : ℂ) else 0 := by
  classical
  have hh (s : Fin k) : l s < N / (k-s.val) + 1 :=
    Finset.mem_range.mp ((Fintype.mem_piFinset.mp hl) s)
  have hh' (s : Fin k) : l' s < N / (k-s.val) + 1 :=
    Finset.mem_range.mp ((Fintype.mem_piFinset.mp hl') s)
  simp only [onb_exp_sum]
  rw [boxB, ← Finset.prod_univ_sum _ (fun (s : Fin k) (t : ℕ) =>
    expTwoPiI ((t : ℝ) * ((l s : ℝ) - l' s) / ((N / (k-s.val) : ℕ) + 1)))]
  have hf (s : Fin k) :
      (∑ t ∈ Finset.range (N / (k-s.val) + 1),
        expTwoPiI ((t : ℝ) * ((l s : ℝ) - l' s) / ((N / (k-s.val) : ℕ) + 1))) =
      if l s = l' s then ((N / (k-s.val) + 1 : ℕ) : ℂ) else 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      onb_fourier_final (N / (k-s.val) + 1) (l s) (l' s)
        (Nat.succ_pos _) (hh s) (hh' s)
  simp_rw [hf]
  by_cases he : l = l'
  · subst l'
    simp [boxB, Fintype.card_piFinset, Nat.cast_prod]
  · rw [if_neg he]
    obtain ⟨s, hs⟩ : ∃ s, l s ≠ l' s := by
      by_contra h
      apply he
      funext s
      simpa using not_exists.mp h s
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])

lemma onb_orth_final (k N : ℕ) (α : ℝ) (U : (Fin k → ℕ) → Fin k → ℕ)
    (hU : Set.BijOn U (simplexS k N : Set _) (boxB k N : Set _))
    (l l' : Fin k → ℕ) (hl : l ∈ boxB k N) (hl' : l' ∈ boxB k N) :
    polyInner (k+1) N (basisPhi k N α U l) (basisPhi k N α U l') =
      if l = l' then 1 else 0 := by
  classical
  let e : ↥(degIdx (k+1) N) ≃ ↥(boxB k N) :=
    (onb_degEquiv_final k N).trans (Set.BijOn.equiv U hU)
  have he (n : ↥(degIdx (k+1) N)) :
      (e n).val = U (fun t => n.val t.castSucc) := rfl
  have hc : (boxB k N).card = (N+k).choose k := by
    rw [← Fintype.card_coe, ← Fintype.card_congr e, onb_card]
  have hpos : 0 < (N+k).choose k := Nat.choose_pos (by omega)
  have hnz : ((N+k).choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hpos)
  unfold polyInner
  have hn : N + (k+1) - 1 = N+k := by omega
  rw [hn, Nat.add_sub_cancel]
  have hs :
      (∑ n : ↥(degIdx (k+1) N),
        ((Nat.multinomial Finset.univ n.val : ℂ))⁻¹ *
          basisPhi k N α U l n * (starRingEnd ℂ) (basisPhi k N α U l' n)) =
      ∑ t ∈ boxB k N, expTwoPiI (∑ s : Fin k,
        (t s : ℝ) * ((l s : ℝ) - l' s) / ((N / (k-s.val) : ℕ) + 1)) := by
    calc
      _ = ∑ n : ↥(degIdx (k+1) N), expTwoPiI (∑ s : Fin k,
          ((e n).val s : ℝ) * ((l s : ℝ) - l' s) / ((N / (k-s.val) : ℕ) + 1)) := by
        apply Finset.sum_congr rfl
        intro n hn
        unfold basisPhi
        rw [onb_coeff_ok _ (Nat.multinomial_pos _ _)]
        congr 1
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro s hs
        rw [he]
        ring
      _ = ∑ t : ↥(boxB k N), expTwoPiI (∑ s : Fin k,
          (t.val s : ℝ) * ((l s : ℝ) - l' s) / ((N / (k-s.val) : ℕ) + 1)) :=
        e.sum_comp (fun t : ↥(boxB k N) => expTwoPiI (∑ s : Fin k,
          (t.val s : ℝ) * ((l s : ℝ) - l' s) / ((N / (k-s.val) : ℕ) + 1)))
      _ = _ := Finset.sum_coe_sort (boxB k N)
        (fun t : Fin k → ℕ => expTwoPiI (∑ s : Fin k,
          (t s : ℝ) * ((l s : ℝ) - l' s) / ((N / (k-s.val) : ℕ) + 1)))
  rw [hs, onb_box_final k N l l' hl hl', hc]
  split_ifs <;> simp [hnz]

lemma onb_linear {ι : Type*} [Fintype ι] (K N : ℕ)
    (v : ι → PolySpaceH K N) (c : ι → ℂ) (d : PolySpaceH K N) :
    polyInner K N (∑ l, c l • v l) d = ∑ l, c l * polyInner K N (v l) d := by
  simp only [polyInner, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem thm_onbexplicit_orthonormalBasis (k : ℕ) (hk : 1 ≤ k)
    (a α : ℝ) (ha : 1 ≤ a) (hα : Irrational α)
    (hbpq : ∀ (i : ℕ) (x : ℝ), (GenContFract.of α).partDens.get? i = some x → x ≤ a)
    (R : ℕ) (U : ℕ → (Fin k → ℕ) → Fin k → ℕ)
    (hU : ∀ M : ℕ, 1 ≤ M → lcmUpTo k ∣ M → IsUNmap k R M (U M))
    (N : ℕ) (hN : 1 ≤ N) (hlcm : lcmUpTo k ∣ N) :
    (∀ l ∈ boxB k N, ∀ l' ∈ boxB k N,
        polyInner (k + 1) N (basisPhi k N α (U N) l) (basisPhi k N α (U N) l') =
          if l = l' then 1 else 0) ∧
      Submodule.span ℂ (basisPhi k N α (U N) '' (boxB k N : Set (Fin k → ℕ))) = ⊤ := by
  classical
  have hu := (hU N hN hlcm).1
  have ho := onb_orth_final k N α (U N) hu
  refine ⟨fun l hl l' hl' => ho l l' hl hl', ?_⟩
  let v : ↥(boxB k N) → PolySpaceH (k+1) N :=
    fun l => basisPhi k N α (U N) l.val
  have hv (l l' : ↥(boxB k N)) :
      polyInner (k+1) N (v l) (v l') = if l = l' then 1 else 0 := by
    simpa only [v, Subtype.coe_inj] using ho l.val l'.val l.property l'.property
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hi := congrArg (fun w => polyInner (k+1) N w (v i)) hc
    rw [onb_linear] at hi
    have hz : polyInner (k+1) N 0 (v i) = 0 := by simp [polyInner]
    rw [hz] at hi
    simpa [hv, mul_ite] using hi
  have hcard :
      Fintype.card ↥(boxB k N) = Module.finrank ℂ (PolySpaceH (k+1) N) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact (Fintype.card_congr
      ((onb_degEquiv_final k N).trans (Set.BijOn.equiv (U N) hu))).symm
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  have hr :
      Set.range v = basisPhi k N α (U N) '' (boxB k N : Set (Fin k → ℕ)) := by
    ext y
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨l.val, l.property, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, rfl⟩
  rwa [hr] at hspan


noncomputable def poissonQ (lam : ℝ) (n : ℤ) : ℝ :=
  if 0 ≤ n then
    Real.exp (-lam / 2) * lam ^ ((n : ℝ) / 2) / Real.sqrt (Nat.factorial n.toNat)
  else 0

noncomputable def poissonH (lam : ℝ) : ℝ := Real.sqrt (1 + lam)

noncomputable def poissonRho (lam : ℝ) (n : ℤ) : ℝ :=
  |(n : ℝ) - lam| / poissonH lam

lemma pq_H (lam : ℝ) (hl : 0 < lam) :
    1 ≤ poissonH lam ∧ (poissonH lam)^2 = 1+lam := by
  constructor
  · simpa [poissonH] using Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1+lam by linarith)
  · exact Real.sq_sqrt (by linarith)

lemma pq_log_poly (r : ℝ) (hr : 0 ≤ r) : Real.log (1+r) ≤ r/10+10 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (1+r)/10 by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h
  have h10 := Real.log_le_self (show (0:ℝ) ≤ 10 by norm_num)
  linarith

lemma pq_gap (a b H : ℝ) (hH0 : 0 ≤ H) (hH : H^2 = 1+b^2) :
    |a^2-b^2| ≤ H*((a-b)^2+2) := by
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs, mul_pow, hH]
  have hp := mul_nonneg (sq_nonneg (a-b)) (sq_nonneg ((a-b)*b-2))
  nlinarith only [hp, sq_nonneg b]

lemma pq_entropy_ok (lam x : ℝ) (hl : 0 < lam) (hx : 0 < x) :
    |x-lam| / poissonH lam - 2 ≤ x*Real.log x-x*Real.log lam-x+lam := by
  have ha : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hb : 0 < Real.sqrt lam := Real.sqrt_pos.2 hl
  have ha2 := Real.sq_sqrt hx.le
  have hb2 := Real.sq_sqrt hl.le
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne', Real.log_sqrt hl.le, Real.log_sqrt hx.le] at h
  have he : 2*x*(Real.sqrt lam / Real.sqrt x - 1) =
      2*Real.sqrt x*Real.sqrt lam-2*x := by
    field_simp
    nlinarith
  have hf := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*x by positivity)
  rw [he] at hf
  have hg := pq_gap (Real.sqrt x) (Real.sqrt lam) (poissonH lam)
    (by exact Real.sqrt_nonneg _) (by rw [hb2]; exact (pq_H lam hl).2)
  rw [ha2, hb2] at hg
  have hp : 0 < poissonH lam := lt_of_lt_of_le (by norm_num) (pq_H lam hl).1
  have hr : |x-lam| / poissonH lam ≤ (Real.sqrt x-Real.sqrt lam)^2+2 :=
    (div_le_iff₀ hp).2 (by simpa [mul_comm] using hg)
  nlinarith

lemma pq_scale_aux (a H r : ℝ) (ha : 1 ≤ a) (hH : 1 ≤ H) (hr : 0 ≤ r)
    (hs : H^2 ≤ a^2+r*H) : H ≤ a*(1+r) := by
  by_cases he : H ≤ a
  · nlinarith
  · have h1 := mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ H-a by linarith)
    have h2 := mul_nonneg (show 0 ≤ a-1 by linarith) (show 0 ≤ r*H by positivity)
    have h3 : H*H ≤ a*H + a*r*H := by nlinarith
    nlinarith

lemma pq_scale_final (lam : ℝ) (hl : 0 < lam) (n : ℕ) :
    poissonH lam ≤ Real.sqrt (n+1) * (1+poissonRho lam n) := by
  have hh := pq_H lam hl
  have hp : 0 < poissonH lam := by linarith [hh.1]
  have hr : 0 ≤ poissonRho lam n := by unfold poissonRho; positivity
  have ha : 1 ≤ Real.sqrt ((n:ℝ)+1) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt
      (show (1:ℝ) ≤ (n:ℝ)+1 by
        have := Nat.cast_nonneg (α := ℝ) n
        linarith)
  apply pq_scale_aux _ _ _ ha hh.1 hr
  rw [Real.sq_sqrt (by positivity), hh.2]
  have he : poissonRho lam n * poissonH lam = |(n:ℝ)-lam| := by
    simp [poissonRho, hp.ne']
  rw [he]
  nlinarith [neg_abs_le ((n:ℝ)-lam)]

lemma pq_log_scale_final (lam : ℝ) (hl : 0 < lam) (n : ℕ) :
    Real.log (poissonH lam) ≤ Real.log ((n:ℝ)+1)/2 +
      Real.log (1+poissonRho lam n) := by
  have hh := pq_H lam hl
  have hp : 0 < poissonH lam := by linarith [hh.1]
  have hr : 0 ≤ poissonRho lam n := by unfold poissonRho; positivity
  have he := Real.log_le_log hp (pq_scale_final lam hl n)
  rwa [Real.log_mul (by positivity) (by positivity), Real.log_sqrt (by positivity)] at he

lemma pq_pos (lam : ℝ) (hl : 0 < lam) (n : ℕ) : 0 < poissonQ lam n := by
  simp only [poissonQ, Int.natCast_nonneg, if_true, Int.toNat_natCast, Int.cast_natCast]
  positivity

lemma pq_log (lam : ℝ) (hl : 0 < lam) (n : ℕ) :
    Real.log (poissonQ lam n) =
      -lam/2 + (n:ℝ)/2*Real.log lam - Real.log (n.factorial:ℝ)/2 := by
  simp only [poissonQ, Int.natCast_nonneg, if_true, Int.toNat_natCast, Int.cast_natCast]
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_rpow hl,
    Real.log_sqrt (by positivity)]

lemma pq_log_bound (lam : ℝ) (hl : 0 < lam) (n : ℕ) :
    Real.log (poissonQ lam n) ≤ 2-Real.log ((n:ℝ)+1)/4-poissonRho lam n/2 := by
  rw [pq_log lam hl n]
  by_cases hn : n = 0
  · subst n
    have hh := (pq_H lam hl).1
    have hp : 0 < poissonH lam := by linarith
    have hr : poissonRho lam 0 ≤ lam := by
      simp only [poissonRho, Int.cast_zero, zero_sub, abs_neg, abs_of_pos hl]
      apply (div_le_iff₀ hp).2
      nlinarith
    simp only [Nat.cast_zero, Nat.factorial_zero, Nat.cast_one, Real.log_one,
      zero_div, zero_mul, add_zero, zero_add, sub_zero, Int.natCast_zero]
    linarith
  · have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hp : (0:ℝ) < n := by linarith
    have hs := Stirling.le_log_factorial_stirling hn
    have he := pq_entropy_ok lam n hl hp
    change poissonRho lam n - 2 ≤ _ at he
    have hpi : 0 ≤ Real.log (2*Real.pi) :=
      Real.log_nonneg (by linarith [Real.pi_gt_three])
    have hlog := Real.log_le_log (show (0:ℝ) < n+1 by positivity)
      (show (n:ℝ)+1 ≤ 2*n by linarith)
    rw [Real.log_mul (by norm_num) hp.ne'] at hlog
    have ht := Real.log_le_self (show (0:ℝ) ≤ 2 by norm_num)
    linarith

lemma pq_log_weighted_ok (lam : ℝ) (hl : 0 < lam) (n : ℕ) :
    Real.log (poissonQ lam n) + 2*Real.log (1+poissonRho lam n) ≤
      30-Real.log (poissonH lam)/2-poissonRho lam n/4 := by
  have hr : 0 ≤ poissonRho lam n := by unfold poissonRho poissonH; positivity
  have h1 := pq_log_bound lam hl n
  have h2 := pq_log_scale_final lam hl n
  have h3 := pq_log_poly (poissonRho lam n) hr
  linarith

lemma pq_succ (lam : ℝ) (hl : 0 < lam) (n : ℕ) :
    poissonQ lam ((n+1:ℕ):ℤ) =
      poissonQ lam n * Real.sqrt lam / Real.sqrt ((n:ℝ)+1) := by
  simp only [poissonQ, Int.natCast_nonneg, if_true, Int.toNat_natCast, Int.cast_natCast]
  rw [Nat.cast_add, Nat.cast_one, show ((n:ℝ)+1)/2 = (n:ℝ)/2+1/2 by ring,
    Real.rpow_add hl, ← Real.sqrt_eq_rpow, Nat.factorial_succ, Nat.cast_mul,
    Real.sqrt_mul (by positivity)]
  push_cast
  ring

lemma pq_diff_formula (lam : ℝ) (hl : 0 < lam) (n : ℕ) :
    fwdDiff (1:ℤ) (poissonQ lam) n =
      poissonQ lam n * (Real.sqrt lam - Real.sqrt ((n:ℝ)+1)) /
        Real.sqrt ((n:ℝ)+1) := by
  have ha : Real.sqrt ((n:ℝ)+1) ≠ 0 := by positivity
  change poissonQ lam ((n:ℤ)+1) - poissonQ lam n = _
  rw [← Nat.cast_add_one, pq_succ lam hl n]
  field_simp

lemma pq_sqrt_diff (lam : ℝ) (hl : 0 < lam) (n : ℕ) :
    |Real.sqrt lam - Real.sqrt ((n:ℝ)+1)| ≤ 1+poissonRho lam n := by
  have hh := pq_H lam hl
  have hp : 0 < poissonH lam := by linarith [hh.1]
  have ha : 0 ≤ Real.sqrt ((n:ℝ)+1) := Real.sqrt_nonneg _
  have hb : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
  have ha2 := Real.sq_sqrt (show 0 ≤ (n:ℝ)+1 by positivity)
  have hb2 := Real.sq_sqrt hl.le
  have hab : poissonH lam ≤ Real.sqrt lam + Real.sqrt ((n:ℝ)+1) := by
    nlinarith [mul_nonneg ha hb, Nat.cast_nonneg (α := ℝ) n, hh.2]
  have he : |Real.sqrt lam - Real.sqrt ((n:ℝ)+1)| *
      (Real.sqrt lam + Real.sqrt ((n:ℝ)+1)) = |lam-((n:ℝ)+1)| := by
    rw [← abs_of_nonneg (add_nonneg hb ha), ← abs_mul]
    congr 1
    nlinarith
  have ht : |lam-((n:ℝ)+1)| ≤ |(n:ℝ)-lam|+1 := by
    have h := abs_add_le (lam-(n:ℝ)) (-1)
    rw [abs_neg, abs_one, abs_sub_comm lam] at h
    convert h using 1 <;> congr 1 <;> ring
  have hr : poissonRho lam n * poissonH lam = |(n:ℝ)-lam| := by
    simp [poissonRho, hp.ne']
  have hm := mul_le_mul_of_nonneg_left hab
    (abs_nonneg (Real.sqrt lam - Real.sqrt ((n:ℝ)+1)))
  rw [he] at hm
  nlinarith [hh.1]

lemma pq_diff_bound (lam : ℝ) (hl : 0 < lam) (n : ℕ) :
    |fwdDiff (1:ℤ) (poissonQ lam) n| ≤
      poissonQ lam n * (1+poissonRho lam n)^2 / poissonH lam := by
  have hq := pq_pos lam hl n
  have hh := pq_H lam hl
  have hp : 0 < poissonH lam := by linarith [hh.1]
  have ha : 0 < Real.sqrt ((n:ℝ)+1) := by positivity
  have hr : 0 ≤ poissonRho lam n := by unfold poissonRho; positivity
  rw [pq_diff_formula lam hl n, abs_div, abs_mul, abs_of_pos hq, abs_of_pos ha]
  apply (div_le_iff₀ ha).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hp).2
  have h1 := pq_sqrt_diff lam hl n
  have h2 := pq_scale_final lam hl n
  have h3 : |Real.sqrt lam-Real.sqrt ((n:ℝ)+1)| * poissonH lam ≤
      (1+poissonRho lam n)^2*Real.sqrt ((n:ℝ)+1) := by
    calc
      _ ≤ (1+poissonRho lam n)*poissonH lam :=
        mul_le_mul_of_nonneg_right h1 hp.le
      _ ≤ (1+poissonRho lam n)*(Real.sqrt ((n:ℝ)+1)*(1+poissonRho lam n)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  nlinarith

lemma pq_weighted (lam : ℝ) (hl : 0 < lam) (n : ℕ) :
    poissonQ lam n * (1+poissonRho lam n)^2 ≤
      Real.exp 30 * poissonH lam ^ (-(1:ℝ)/2) * Real.exp (-poissonRho lam n/4) := by
  have hq := pq_pos lam hl n
  have hh := pq_H lam hl
  have hp : 0 < poissonH lam := by linarith [hh.1]
  have hr : 0 ≤ poissonRho lam n := by unfold poissonRho; positivity
  have h := pq_log_weighted_ok lam hl n
  have he : Real.log (poissonQ lam n * (1+poissonRho lam n)^2) ≤
      30-Real.log (poissonH lam)/2-poissonRho lam n/4 := by
    rw [Real.log_mul hq.ne' (by positivity), Real.log_pow]
    simpa using h
  have ht := Real.le_exp_of_log_le he
  convert ht using 1
  rw [Real.rpow_def_of_pos hp, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

lemma pq_nonneg_bounds (lam : ℝ) (hl : 0 < lam) (n : ℕ) :
    |poissonQ lam n| ≤
      Real.exp 30 * poissonH lam ^ (-(1:ℝ)/2) * Real.exp (-poissonRho lam n/4) ∧
    |fwdDiff (1:ℤ) (poissonQ lam) n| ≤
      Real.exp 30 * poissonH lam ^ (-(3:ℝ)/2) * Real.exp (-poissonRho lam n/4) := by
  have hq := pq_pos lam hl n
  have hh := pq_H lam hl
  have hp : 0 < poissonH lam := by linarith [hh.1]
  have hr : 0 ≤ poissonRho lam n := by unfold poissonRho; positivity
  have hw := pq_weighted lam hl n
  constructor
  · rw [abs_of_pos hq]
    exact (show poissonQ lam n ≤ poissonQ lam n * (1+poissonRho lam n)^2 by
      nlinarith [mul_nonneg hq.le hr,
        mul_nonneg hq.le (sq_nonneg (poissonRho lam n))]).trans hw
  · calc
      _ ≤ poissonQ lam n * (1+poissonRho lam n)^2 / poissonH lam :=
        pq_diff_bound lam hl n
      _ ≤ (Real.exp 30 * poissonH lam ^ (-(1:ℝ)/2) * Real.exp (-poissonRho lam n/4)) /
          poissonH lam := div_le_div_of_nonneg_right hw hp.le
      _ = _ := by
        rw [show -(3:ℝ)/2 = -(1:ℝ)/2-1 by norm_num,
          Real.rpow_sub hp, Real.rpow_one]
        ring

lemma pq_boundary (lam : ℝ) (hl : 0 < lam) :
    Real.exp (-lam/2) ≤ Real.exp 30 * poissonH lam ^ (-(3:ℝ)/2) *
      Real.exp (-poissonRho lam (-1)/4) := by
  have hh := pq_H lam hl
  have hp : 0 < poissonH lam := by linarith [hh.1]
  have hr : poissonRho lam (-1) = poissonH lam := by
    unfold poissonRho
    norm_num only [Int.cast_neg, Int.cast_one]
    rw [abs_of_neg (by linarith)]
    apply (div_eq_iff hp.ne').2
    nlinarith [hh.2]
  rw [hr, Real.rpow_def_of_pos hp, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog := Real.log_le_self hp.le
  nlinarith [hh.2, sq_nonneg (poissonH lam-2)]

theorem lem_poisson1d :
    ∃ C > 0, ∀ lam : ℝ, 0 < lam → ∀ n : ℤ,
      |poissonQ lam n| ≤
          C * poissonH lam ^ (-(1 : ℝ) / 2) * Real.exp (-poissonRho lam n / 4) ∧
        |fwdDiff (1 : ℤ) (poissonQ lam) n| ≤
          C * poissonH lam ^ (-(3 : ℝ) / 2) * Real.exp (-poissonRho lam n / 4) := by
  refine ⟨Real.exp 30, Real.exp_pos _, ?_⟩
  intro lam hl n
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact pq_nonneg_bounds lam hl m
  · have hn0 : poissonQ lam n = 0 := by simp [poissonQ, hn]
    have hh := pq_H lam hl
    have hp : 0 < poissonH lam := by linarith [hh.1]
    constructor
    · rw [hn0, abs_zero]
      positivity
    · by_cases he : n = -1
      · subst n
        simpa [fwdDiff, poissonQ, abs_of_pos (Real.exp_pos _)] using pq_boundary lam hl
      · have hn1 : ¬ 0 ≤ n+1 := by omega
        have hf : fwdDiff (1:ℤ) (poissonQ lam) n = 0 := by
          simp [fwdDiff, poissonQ, hn, hn1]
        rw [hf, abs_zero]
        positivity


noncomputable def hatEta (x : ℝ) : ℝ := max (1 - |x|) 0

noncomputable def poissonQLoc (lam : ℝ) (m : ℤ) (n : ℤ) : ℝ :=
  poissonQ lam n * hatEta ((n : ℝ) / poissonH lam - (m : ℝ))

noncomputable def seqFourier (b : ℤ → ℝ) (u : ℝ) : ℂ :=
  ∑' j : ℤ, (b j : ℂ) * expTwoPiI (-(u * (j : ℝ)))

namespace LocalizedFourierFinal

lemma lem_fouriermass_support (lam : ℝ) (hl : 0 < lam) (m n : ℤ)
    (h : poissonQLoc lam m n ≠ 0) :
    |(n : ℝ) / poissonH lam - (m : ℝ)| < 1 := by
  by_contra hn
  have he : hatEta ((n : ℝ) / poissonH lam - (m : ℝ)) = 0 := by
    unfold hatEta
    exact max_eq_right (by linarith)
  exact h (by simp [poissonQLoc, he])

lemma hatEta_partition (x : ℝ) : (∑' m : ℤ, hatEta (x - (m : ℝ))) = 1 := by
  classical
  let a : ℤ := ⌊x⌋
  have ha : (a : ℝ) ≤ x := Int.floor_le x
  have hb : x < (a : ℝ) + 1 := Int.lt_floor_add_one x
  have hz (m : ℤ) (hm : m ∉ ({a, a+1} : Finset ℤ)) :
      hatEta (x - (m : ℝ)) = 0 := by
    have hm' : m ≠ a ∧ m ≠ a+1 := by simpa using hm
    rcases le_or_gt m a with hmlo | hmhi
    · have hc : (m : ℝ) + 1 ≤ (a : ℝ) := by
        exact_mod_cast (show m+1 ≤ a by omega)
      unfold hatEta
      apply max_eq_right
      have ht := le_abs_self (x - (m : ℝ))
      linarith
    · have hc : (a : ℝ) + 2 ≤ (m : ℝ) := by
        exact_mod_cast (show a+2 ≤ m by omega)
      unfold hatEta
      apply max_eq_right
      have ht := neg_le_abs (x - (m : ℝ))
      linarith
  rw [tsum_eq_sum hz, Finset.sum_pair (by omega : a ≠ a+1)]
  simp only [hatEta, Int.cast_add, Int.cast_one]
  rw [abs_of_nonneg (by linarith : 0 ≤ x - (a : ℝ)),
    abs_of_nonpos (by linarith : x - ((a : ℝ)+1) ≤ 0)]
  rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

lemma lem_fouriermass_sum (lam : ℝ) (hl : 0 < lam) (n : ℤ) :
    ∑' m : ℤ, poissonQLoc lam m n = poissonQ lam n := by
  simp only [poissonQLoc, tsum_mul_left, hatEta_partition, mul_one]

namespace FourierMassBounds

lemma fm_exp_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℤ => Real.exp (-|(n : ℝ)| / a)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  have hs : Summable (fun n : ℕ => Real.exp ((n : ℝ) * (-1 / a))) :=
    Real.summable_exp_nat_mul_iff.mpr (div_neg_of_neg_of_pos (by norm_num) ha)
  constructor <;> convert hs using 1 <;> funext n <;>
    simp only [Int.cast_natCast, Int.cast_neg, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] <;>
    congr 1 <;> ring

lemma exp_norm (x : ℝ) : ‖expTwoPiI x‖ = 1 := by
  simp [expTwoPiI, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

lemma hatEta_nonneg (x : ℝ) : 0 ≤ hatEta x := le_max_right _ _

lemma hatEta_le_one (x : ℝ) : hatEta x ≤ 1 := by
  exact max_le (by linarith [abs_nonneg x]) (by norm_num)

lemma hatEta_lipschitz (x y : ℝ) : |hatEta x - hatEta y| ≤ |x - y| := by
  have hx : |x| ≤ |x - y| + |y| := by
    simpa only [sub_add_cancel] using abs_add_le (x - y) y
  have hy : |y| ≤ |x - y| + |x| := by
    simpa only [sub_add_cancel, abs_sub_comm y x] using abs_add_le (y - x) x
  have hu : hatEta x ≤ hatEta y + |x - y| := by
    change max (1 - |x|) 0 ≤ max (1 - |y|) 0 + |x - y|
    apply max_le
    · linarith [le_max_left (1 - |y|) 0]
    · linarith [le_max_right (1 - |y|) 0, abs_nonneg (x - y)]
  have hv : hatEta y ≤ hatEta x + |x - y| := by
    change max (1 - |y|) 0 ≤ max (1 - |x|) 0 + |x - y|
    apply max_le
    · linarith [le_max_left (1 - |x|) 0]
    · linarith [le_max_right (1 - |x|) 0, abs_nonneg (x - y)]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma poissonQLoc_diff_bound (lam : ℝ) (hl : 0 < lam) (m n : ℤ) :
    |fwdDiff (1 : ℤ) (poissonQLoc lam m) n| ≤
      |fwdDiff (1 : ℤ) (poissonQ lam) n| +
        |poissonQ lam n| / poissonH lam := by
  have hp : 0 < poissonH lam := lt_of_lt_of_le (by norm_num) (pq_H lam hl).1
  let x : ℝ := ((n + 1 : ℤ) : ℝ) / poissonH lam - (m : ℝ)
  let y : ℝ := (n : ℝ) / poissonH lam - (m : ℝ)
  have hxy : x - y = (poissonH lam)⁻¹ := by
    dsimp [x, y]
    push_cast
    ring
  have hc : |hatEta x| ≤ 1 := by
    rw [abs_of_nonneg (hatEta_nonneg x)]
    exact hatEta_le_one x
  have hd : |hatEta x - hatEta y| ≤ (poissonH lam)⁻¹ := by
    have h := hatEta_lipschitz x y
    rwa [hxy, abs_of_pos (inv_pos.mpr hp)] at h
  change |poissonQ lam (n + 1) * hatEta x - poissonQ lam n * hatEta y| ≤ _
  calc
    _ = |(poissonQ lam (n + 1) - poissonQ lam n) * hatEta x +
        poissonQ lam n * (hatEta x - hatEta y)| := by congr 1; ring
    _ ≤ |(poissonQ lam (n + 1) - poissonQ lam n) * hatEta x| +
        |poissonQ lam n * (hatEta x - hatEta y)| := abs_add_le _ _
    _ = |poissonQ lam (n + 1) - poissonQ lam n| * |hatEta x| +
        |poissonQ lam n| * |hatEta x - hatEta y| := by rw [abs_mul, abs_mul]
    _ ≤ |poissonQ lam (n + 1) - poissonQ lam n| * 1 +
        |poissonQ lam n| * (poissonH lam)⁻¹ :=
      add_le_add (mul_le_mul_of_nonneg_left hc (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hd (abs_nonneg _))
    _ = _ := by simp only [fwdDiff, mul_one, div_eq_mul_inv]

lemma ft_terms_summable_final (b : ℤ → ℝ) (hb : Summable b) (u : ℝ) :
    Summable (fun n : ℤ => (b n : ℂ) * expTwoPiI (-(u * (n : ℝ)))) := by
  apply Summable.of_norm
  simpa only [norm_mul, exp_norm, mul_one, Complex.norm_real,
    Real.norm_eq_abs] using hb.abs

lemma seqFourier_fwdDiff_final (b : ℤ → ℝ) (hb : Summable b) (u : ℝ) :
    seqFourier (fwdDiff (1 : ℤ) b) u =
      (expTwoPiI u - 1) * seqFourier b u := by
  have hshift : Summable (fun n : ℤ => b (n + 1)) :=
    (Equiv.addRight (1 : ℤ)).summable_iff.mpr hb
  have hs := ft_terms_summable_final b hb u
  have hs' := ft_terms_summable_final _ hshift u
  have he (n : ℤ) :
      (b (n + 1) : ℂ) * expTwoPiI (-(u * (n : ℝ))) =
        expTwoPiI u * ((b (n + 1) : ℂ) *
          expTwoPiI (-(u * ((n + 1 : ℤ) : ℝ)))) := by
    rw [mul_left_comm, ← onb_exp_add]
    congr 2
    push_cast
    ring
  unfold seqFourier
  simp only [fwdDiff, Complex.ofReal_sub, sub_mul]
  rw [hs'.tsum_sub hs]
  simp_rw [he]
  have hsum : (∑' n : ℤ, (b (n + 1) : ℂ) *
      expTwoPiI (-(u * ((n + 1 : ℤ) : ℝ)))) =
      ∑' n : ℤ, (b n : ℂ) * expTwoPiI (-(u * (n : ℝ))) := by
    simpa only [Equiv.subRight_apply, sub_neg_eq_add] using
      (Equiv.subRight (-1 : ℤ)).tsum_eq
        (fun n : ℤ => (b n : ℂ) * expTwoPiI (-(u * (n : ℝ))))
  rw [tsum_mul_left, hsum]
  ring

lemma fm_integral_exp_int_ok (k : ℤ) :
    (∫ u in (0 : ℝ)..1, expTwoPiI (u * (k : ℝ))) =
      if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [expTwoPiI]
  · rw [if_neg hk]
    have hc : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hk)
        (mul_ne_zero
          (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
          Complex.I_ne_zero)
    have he :
        (fun u : ℝ => expTwoPiI (u * (k : ℝ))) =
          (fun u : ℝ =>
            Complex.exp
              (((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (u : ℂ))) := by
      funext u
      unfold expTwoPiI
      congr 1
      push_cast
      ring
    rw [he, integral_exp_mul_complex hc]
    simp [Complex.exp_int_mul_two_pi_mul_I]

lemma fm_parseval_finset_ok (b : ℤ → ℝ) (s : Finset ℤ)
    (hb : ∀ n, n ∉ s → b n = 0) :
    (∫ u in (0 : ℝ)..1, ‖seqFourier b u‖ ^ 2) =
      ∑' n : ℤ, b n ^ 2 := by
  classical
  have he (u : ℝ) :
      seqFourier b u =
        ∑ n ∈ s, (b n : ℂ) * expTwoPiI (-(u * (n : ℝ))) := by
    apply tsum_eq_sum
    intro n hn
    simp [hb n hn]
  have hpair (u : ℝ) (i j : ℤ) :
      ((b i : ℂ) * expTwoPiI (-(u * (i : ℝ)))) *
          (starRingEnd ℂ)
            ((b j : ℂ) * expTwoPiI (-(u * (j : ℝ)))) =
        ((b i : ℂ) * (b j : ℂ)) *
          expTwoPiI (u * ((j - i : ℤ) : ℝ)) := by
    rw [map_mul, Complex.conj_ofReal]
    calc
      _ = ((b i : ℂ) * (b j : ℂ)) *
          (expTwoPiI (-(u * (i : ℝ))) *
            (starRingEnd ℂ) (expTwoPiI (-(u * (j : ℝ))))) := by ring
      _ = _ := by
        rw [onb_exp_sub_ok]
        congr 2
        push_cast
        ring
  have hn (u : ℝ) :
      ((‖seqFourier b u‖ ^ 2 : ℝ) : ℂ) =
        ∑ i ∈ s, ∑ j ∈ s,
          ((b i : ℂ) * (b j : ℂ)) *
            expTwoPiI (u * ((j - i : ℤ) : ℝ)) := by
    rw [← Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_conj_mul_self, mul_comm, he]
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact hpair u i j
  have hi (i j : ℤ) :
      IntervalIntegrable
        (fun u : ℝ =>
          ((b i : ℂ) * (b j : ℂ)) *
            expTwoPiI (u * ((j - i : ℤ) : ℝ)))
        MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold expTwoPiI
    fun_prop
  have his (i : ℤ) :
      IntervalIntegrable
        (fun u : ℝ => ∑ j ∈ s,
          ((b i : ℂ) * (b j : ℂ)) *
            expTwoPiI (u * ((j - i : ℤ) : ℝ)))
        MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold expTwoPiI
    fun_prop
  rw [tsum_eq_sum (s := s) (fun n hn => by simp [hb n hn])]
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hn]
  rw [intervalIntegral.integral_finsetSum (fun i _ => his i)]
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s,
        ∫ u in (0 : ℝ)..1,
          ((b i : ℂ) * (b j : ℂ)) *
            expTwoPiI (u * ((j - i : ℤ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi'
      exact intervalIntegral.integral_finsetSum (fun j _ => hi i j)
    _ = ∑ i ∈ s, ∑ j ∈ s,
        ((b i : ℂ) * (b j : ℂ)) *
          (if j - i = 0 then 1 else 0) := by
      simp_rw [intervalIntegral.integral_const_mul, fm_integral_exp_int_ok]
    _ = _ := by
      simp only [Complex.ofReal_sum, Complex.ofReal_pow]
      apply Finset.sum_congr rfl
      intro i hi'
      simp [sub_eq_zero, mul_ite, hi', pow_two]

lemma poissonQLoc_diff_support_ok (lam : ℝ) (hl : 0 < lam) (m n : ℤ)
    (h : fwdDiff (1 : ℤ) (poissonQLoc lam m) n ≠ 0) :
    |(n : ℝ) / poissonH lam - (m : ℝ)| < 2 := by
  have hp : 0 < poissonH lam := by linarith [(pq_H lam hl).1]
  have hinv : (poissonH lam)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hp]
    exact (pq_H lam hl).1
  by_cases hn : poissonQLoc lam m n = 0
  · have hs : poissonQLoc lam m (n + 1) ≠ 0 := by
      simpa only [fwdDiff, hn, sub_zero] using h
    have hs' := lem_fouriermass_support lam hl m (n + 1) hs
    have ht := abs_add_le (((n + 1 : ℤ) : ℝ) / poissonH lam - (m : ℝ))
      (-((poissonH lam)⁻¹))
    simp only [← sub_eq_add_neg, abs_neg] at ht
    have he : ((n + 1 : ℤ) : ℝ) / poissonH lam - (m : ℝ) -
        (poissonH lam)⁻¹ = (n : ℝ) / poissonH lam - (m : ℝ) := by
      push_cast
      ring
    rw [he, abs_of_pos (inv_pos.mpr hp)] at ht
    linarith
  · exact (lem_fouriermass_support lam hl m n hn).trans (by norm_num)

lemma localized_rho_bound_ok (lam : ℝ) (hl : 0 < lam) (m n : ℤ)
    (hn : |(n : ℝ) / poissonH lam - (m : ℝ)| ≤ 2) :
    Real.exp (-poissonRho lam n / 4) ≤
      Real.exp (1 / 2) * Real.exp (-|(m : ℝ) - lam / poissonH lam| / 4) := by
  have hp : 0 < poissonH lam := by linarith [(pq_H lam hl).1]
  have he : |(n : ℝ) / poissonH lam - lam / poissonH lam| =
      poissonRho lam n := by
    rw [← sub_div, abs_div, abs_of_pos hp]
    rfl
  have ht := abs_add_le ((m : ℝ) - (n : ℝ) / poissonH lam)
    ((n : ℝ) / poissonH lam - lam / poissonH lam)
  rw [sub_add_sub_cancel, he] at ht
  have ht' : |(m : ℝ) - lam / poissonH lam| ≤
      |(n : ℝ) / poissonH lam - (m : ℝ)| + poissonRho lam n := by
    simpa only [abs_sub_comm (m : ℝ) ((n : ℝ) / poissonH lam)] using ht
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

lemma localized_envelopes_ok :
    ∃ C > 0, ∀ lam : ℝ, 0 < lam → ∀ m n : ℤ,
      |poissonQLoc lam m n| ≤ C * poissonH lam ^ (-(1 : ℝ) / 2) *
        Real.exp (-|(m : ℝ) - lam / poissonH lam| / 4) ∧
      |fwdDiff (1 : ℤ) (poissonQLoc lam m) n| ≤
        C * poissonH lam ^ (-(3 : ℝ) / 2) *
          Real.exp (-|(m : ℝ) - lam / poissonH lam| / 4) := by
  obtain ⟨C, hC, h⟩ := lem_poisson1d
  refine ⟨2 * C * Real.exp (1 / 2), by positivity, ?_⟩
  intro lam hl m n
  have hp : 0 < poissonH lam := by linarith [(pq_H lam hl).1]
  have hn := h lam hl n
  constructor
  · by_cases hz : poissonQLoc lam m n = 0
    · rw [hz, abs_zero]
      positivity
    have he := localized_rho_bound_ok lam hl m n
      (le_trans (lem_fouriermass_support lam hl m n hz).le (by norm_num))
    have hq : |poissonQLoc lam m n| ≤ |poissonQ lam n| := by
      rw [poissonQLoc, abs_mul, abs_of_nonneg (hatEta_nonneg _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hatEta_le_one _)
    calc
      _ ≤ C * poissonH lam ^ (-(1 : ℝ) / 2) *
          Real.exp (-poissonRho lam n / 4) := hq.trans hn.1
      _ ≤ C * poissonH lam ^ (-(1 : ℝ) / 2) *
          (Real.exp (1 / 2) * Real.exp (-|(m : ℝ) - lam / poissonH lam| / 4)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ _ := by
        have hh : 0 ≤ C * poissonH lam ^ (-(1 : ℝ) / 2) *
          (Real.exp (1 / 2) *
            Real.exp (-|(m : ℝ) - lam / poissonH lam| / 4)) := by positivity
        nlinarith only [hh]
  · by_cases hz : fwdDiff (1 : ℤ) (poissonQLoc lam m) n = 0
    · rw [hz, abs_zero]
      positivity
    have he := localized_rho_bound_ok lam hl m n
      (poissonQLoc_diff_support_ok lam hl m n hz).le
    have hr : poissonH lam ^ (-(1 : ℝ) / 2) / poissonH lam =
        poissonH lam ^ (-(3 : ℝ) / 2) := by
      rw [show -(3 : ℝ) / 2 = -(1 : ℝ) / 2 - 1 by norm_num,
        Real.rpow_sub hp, Real.rpow_one]
    calc
      _ ≤ |fwdDiff (1 : ℤ) (poissonQ lam) n| +
          |poissonQ lam n| / poissonH lam := poissonQLoc_diff_bound lam hl m n
      _ ≤ C * poissonH lam ^ (-(3 : ℝ) / 2) * Real.exp (-poissonRho lam n / 4) +
          (C * poissonH lam ^ (-(1 : ℝ) / 2) * Real.exp (-poissonRho lam n / 4)) /
            poissonH lam := add_le_add hn.2 (div_le_div_of_nonneg_right hn.1 hp.le)
      _ = 2 * C * poissonH lam ^ (-(3 : ℝ) / 2) *
          Real.exp (-poissonRho lam n / 4) := by
        rw [show
          (C * poissonH lam ^ (-(1 : ℝ) / 2) * Real.exp (-poissonRho lam n / 4)) /
            poissonH lam =
          C * (poissonH lam ^ (-(1 : ℝ) / 2) / poissonH lam) *
            Real.exp (-poissonRho lam n / 4) by ring, hr]
        ring
      _ ≤ 2 * C * poissonH lam ^ (-(3 : ℝ) / 2) *
          (Real.exp (1 / 2) * Real.exp (-|(m : ℝ) - lam / poissonH lam| / 4)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by ring

lemma fm_shifted_exp_bound :
    ∃ C > 0, ∀ x : ℝ,
      Summable (fun m : ℤ => Real.exp (-|(m : ℝ) - x| / 4)) ∧
      (∑' m : ℤ, Real.exp (-|(m : ℝ) - x| / 4)) ≤ C := by
  let S : ℝ := ∑' n : ℤ, Real.exp (-|(n : ℝ)| / 4)
  have hS : 0 ≤ S := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  refine ⟨Real.exp (1 / 4) * S + 1, by positivity, ?_⟩
  intro x
  let a : ℤ := ⌊x⌋
  have ha : (a : ℝ) ≤ x := Int.floor_le x
  have ha' : x < (a : ℝ) + 1 := Int.lt_floor_add_one x
  have hs :
      Summable (fun m : ℤ => Real.exp (-|(m : ℝ) - (a : ℝ)| / 4)) := by
    simpa only [Function.comp_def, Equiv.subRight_apply, Int.cast_sub] using
      (Equiv.subRight a).summable_iff.mpr
        (fm_exp_summable 4 (by norm_num))
  have he :
      (∑' m : ℤ, Real.exp (-|(m : ℝ) - (a : ℝ)| / 4)) = S := by
    simpa only [Equiv.subRight_apply, Int.cast_sub] using
      (Equiv.subRight a).tsum_eq
        (fun n : ℤ => Real.exp (-|(n : ℝ)| / 4))
  have hb (m : ℤ) :
      Real.exp (-|(m : ℝ) - x| / 4) ≤
        Real.exp (1 / 4) * Real.exp (-|(m : ℝ) - (a : ℝ)| / 4) := by
    have ht : |(m : ℝ) - (a : ℝ)| ≤ |(m : ℝ) - x| + 1 := by
      have h := abs_add_le ((m : ℝ) - x) (x - (a : ℝ))
      rw [sub_add_sub_cancel, abs_of_nonneg (sub_nonneg.mpr ha)] at h
      linarith
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hs' := hs.mul_left (Real.exp (1 / 4))
  have hf :
      Summable (fun m : ℤ => Real.exp (-|(m : ℝ) - x| / 4)) :=
    Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hb hs'
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∑' m : ℤ,
        Real.exp (1 / 4) * Real.exp (-|(m : ℝ) - (a : ℝ)| / 4) :=
      Summable.tsum_le_tsum hb hf hs'
    _ = Real.exp (1 / 4) * S := by rw [tsum_mul_left, he]
    _ ≤ Real.exp (1 / 4) * S + 1 := by linarith

end FourierMassBounds

lemma fm_continuous_finite (b : ℤ → ℝ) (s : Finset ℤ)
    (hb : ∀ n, n ∉ s → b n = 0) : Continuous (seqFourier b) := by
  classical
  have he (u : ℝ) : seqFourier b u =
      ∑ n ∈ s, (b n : ℂ) * expTwoPiI (-(u * (n : ℝ))) := by
    apply tsum_eq_sum
    intro n hn
    simp [hb n hn]
  change Continuous (fun u => seqFourier b u)
  simp_rw [he]
  unfold expTwoPiI
  fun_prop

lemma fm_weighted_parseval_ok (b : ℤ → ℝ) (s t : Finset ℤ)
    (hb : ∀ n, n ∉ s → b n = 0)
    (hd : ∀ n, n ∉ t → fwdDiff (1 : ℤ) b n = 0) (H : ℝ) :
    (∫ u in (0 : ℝ)..1, (1 + H^2 * ‖expTwoPiI u - 1‖^2) *
      ‖seqFourier b u‖^2) =
      (∑' n : ℤ, b n ^ 2) + H^2 * (∑' n : ℤ, fwdDiff (1 : ℤ) b n ^ 2) := by
  have hs : Summable b := summable_of_hasFiniteSupport
    ((s.finite_toSet).subset (fun n hn => by
      by_contra h
      exact hn (hb n h)))
  have he (u : ℝ) : (1 + H^2 * ‖expTwoPiI u - 1‖^2) *
      ‖seqFourier b u‖^2 = ‖seqFourier b u‖^2 +
        H^2 * ‖seqFourier (fwdDiff (1 : ℤ) b) u‖^2 := by
    rw [FourierMassBounds.seqFourier_fwdDiff_final b hs, norm_mul, mul_pow]
    ring
  simp_rw [he]
  have hi : IntervalIntegrable (fun u => ‖seqFourier b u‖^2) MeasureTheory.volume 0 1 :=
    ((fm_continuous_finite b s hb).norm.pow 2).intervalIntegrable 0 1
  have hj : IntervalIntegrable (fun u => H^2 * ‖seqFourier (fwdDiff (1 : ℤ) b) u‖^2)
      MeasureTheory.volume 0 1 :=
    (continuous_const.mul ((fm_continuous_finite _ t hd).norm.pow 2)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hi hj, intervalIntegral.integral_const_mul,
    FourierMassBounds.fm_parseval_finset_ok b s hb,
    FourierMassBounds.fm_parseval_finset_ok _ t hd]

lemma fm_support_energy (H x B : ℝ) (hH : 1 ≤ H) (hB : 0 ≤ B)
    (b : ℤ → ℝ) (hs : ∀ n, b n ≠ 0 → |(n : ℝ) / H - x| < 2)
    (hb : ∀ n, |b n| ≤ B) :
    (∑' n : ℤ, b n ^ 2) ≤ 7 * H * B ^ 2 := by
  classical
  have hp : 0 < H := by linarith
  let a : ℤ := ⌊(x - 2) * H⌋
  let z : ℤ := ⌈(x + 2) * H⌉
  let S : Finset ℤ := Finset.Icc a z
  have ha : (a : ℝ) ≤ (x - 2) * H := Int.floor_le _
  have ha' : (x - 2) * H < (a : ℝ) + 1 := Int.lt_floor_add_one _
  have hz : (x + 2) * H ≤ (z : ℝ) := Int.le_ceil _
  have hz' : (z : ℝ) < (x + 2) * H + 1 := Int.ceil_lt_add_one _
  have haz : a ≤ z := by exact_mod_cast (show (a : ℝ) ≤ z by nlinarith)
  have hc : (S.card : ℝ) = (z : ℝ) + 1 - (a : ℝ) := by
    dsimp [S]
    rw [Int.card_Icc]
    exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ z + 1 - a by omega))
  have hc' : (S.card : ℝ) ≤ 7 * H := by rw [hc]; nlinarith
  have hzero (n : ℤ) (hn : n ∉ S) : b n = 0 := by
    by_contra h
    have hnn := abs_lt.mp (hs n h)
    have hlo : (x - 2) * H < (n : ℝ) :=
      (lt_div_iff₀ hp).mp (by linarith [hnn.1])
    have hhi : (n : ℝ) < (x + 2) * H :=
      (div_lt_iff₀ hp).mp (by linarith [hnn.2])
    apply hn
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast (ha.trans hlo.le)
    · exact_mod_cast (hhi.le.trans hz)
  rw [tsum_eq_sum (s := S) (fun n hn => by rw [hzero n hn]; simp)]
  calc
    _ ≤ ∑ n ∈ S, B ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (b n)) hB).2 (hb n)
    _ = (S.card : ℝ) * B ^ 2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc' (sq_nonneg B)

lemma fm_finite_support (H x : ℝ) (hp : 0 < H)
    (b : ℤ → ℝ) (hs : ∀ n, b n ≠ 0 → |(n : ℝ) / H - x| < 2) :
    ∃ S : Finset ℤ, ∀ n, n ∉ S → b n = 0 := by
  refine ⟨Finset.Icc ⌊(x-2)*H⌋ ⌈(x+2)*H⌉, ?_⟩
  intro n hn
  by_contra h
  have hnn := abs_lt.mp (hs n h)
  have hlo : (x - 2) * H < (n : ℝ) :=
    (lt_div_iff₀ hp).mp (by linarith [hnn.1])
  have hhi : (n : ℝ) < (x + 2) * H :=
    (div_lt_iff₀ hp).mp (by linarith [hnn.2])
  apply hn
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast ((Int.floor_le ((x-2)*H)).trans hlo.le)
  · exact_mod_cast (hhi.le.trans (Int.le_ceil ((x+2)*H)))

lemma fm_rpow_half_sq_ok (H : ℝ) (hp : 0 < H) :
    (H ^ (-(1 : ℝ)/2)) ^ 2 = H⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  norm_num [Real.rpow_neg_one]

lemma fm_rpow_threehalf_sq_ok (H : ℝ) (hp : 0 < H) :
    (H ^ (-(3 : ℝ)/2)) ^ 2 = (H^3)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  norm_num [Real.rpow_neg, Real.rpow_natCast]

lemma fm_energy_algebra_ok (H C E a d : ℝ) (hp : 0 < H)
    (ha : a ≤ 7 * H * (C * H ^ (-(1 : ℝ)/2) * E)^2)
    (hd : d ≤ 7 * H * (C * H ^ (-(3 : ℝ)/2) * E)^2) :
    a + H^2 * d ≤ 14 * C^2 * E^2 := by
  have he : 7 * H * (C * H ^ (-(1 : ℝ)/2) * E)^2 +
      H^2 * (7 * H * (C * H ^ (-(3 : ℝ)/2) * E)^2) = 14 * C^2 * E^2 := by
    simp only [mul_pow, fm_rpow_half_sq_ok H hp, fm_rpow_threehalf_sq_ok H hp]
    field_simp
    <;> ring
  calc
    _ ≤ 7 * H * (C * H ^ (-(1 : ℝ)/2) * E)^2 +
      H^2 * (7 * H * (C * H ^ (-(3 : ℝ)/2) * E)^2) :=
        add_le_add ha (mul_le_mul_of_nonneg_left hd (sq_nonneg H))
    _ = _ := he

lemma fm_weighted_cs (F W : ℝ → ℝ) (hF : Continuous F)
    (hW : Continuous W) (hWp : ∀ u, 0 < W u) :
    (∫ u in (0 : ℝ)..1, F u) ^ 2 ≤
      (∫ u in (0 : ℝ)..1, (W u)⁻¹) *
        (∫ u in (0 : ℝ)..1, W u * F u ^ 2) := by
  let A : ℝ := ∫ u in (0 : ℝ)..1, (W u)⁻¹
  let L : ℝ := ∫ u in (0 : ℝ)..1, F u
  let B : ℝ := ∫ u in (0 : ℝ)..1, W u * F u ^ 2
  have hWi : Continuous (fun u => (W u)⁻¹) :=
    hW.inv₀ (fun u => (hWp u).ne')
  have hA : 0 < A := by
    apply intervalIntegral.integral_pos (by norm_num) hWi.continuousOn
    · intro u hu
      exact (inv_pos.mpr (hWp u)).le
    · exact ⟨0, by norm_num, inv_pos.mpr (hWp 0)⟩
  let t : ℝ := L / A
  have h1 : IntervalIntegrable (fun u => W u * F u ^ 2)
      MeasureTheory.volume 0 1 :=
    (hW.mul (hF.pow 2)).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun u => (2 * t) * F u)
      MeasureTheory.volume 0 1 :=
    (continuous_const.mul hF).intervalIntegrable 0 1
  have h3 : IntervalIntegrable (fun u => t ^ 2 * (W u)⁻¹)
      MeasureTheory.volume 0 1 :=
    (continuous_const.mul hWi).intervalIntegrable 0 1
  have he (u : ℝ) : W u * (F u - t / W u) ^ 2 =
      W u * F u ^ 2 - (2 * t) * F u + t ^ 2 * (W u)⁻¹ := by
    field_simp [(hWp u).ne'] <;> ring
  have hn : 0 ≤ ∫ u in (0 : ℝ)..1, W u * (F u - t / W u) ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    exact mul_nonneg (hWp u).le (sq_nonneg _)
  simp_rw [he] at hn
  rw [intervalIntegral.integral_add (h1.sub h2) h3,
    intervalIntegral.integral_sub h1 h2,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hn
  change 0 ≤ B - (2 * t) * L + t ^ 2 * A at hn
  have halg : (B - (2 * t) * L + t ^ 2 * A) * A = B * A - L ^ 2 := by
    dsimp only [t]
    field_simp [hA.ne'] <;> ring
  have hh := mul_nonneg hn hA.le
  rw [halg] at hh
  change L ^ 2 ≤ A * B
  nlinarith only [hh]

lemma fm_phase_norm (u : ℝ) :
    ‖expTwoPiI u - 1‖ = 2 * |Real.sin (Real.pi * u)| := by
  have he : expTwoPiI u =
      Complex.exp (Complex.I * ((2 * Real.pi * u : ℝ) : ℂ)) := by
    unfold expTwoPiI
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    show (2 * Real.pi * u) / 2 = Real.pi * u by ring, abs_mul]
  norm_num

lemma fm_sin_lower_half (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1 / 2) :
    2 * u ≤ Real.sin (Real.pi * u) := by
  have h := Real.le_sin_mul (x := 2 * u) (by linarith) (by linarith)
  rwa [show Real.pi / 2 * (2 * u) = Real.pi * u by ring] at h

lemma fm_reciprocal_weight_bound (H : ℝ) (hH : 0 < H) :
    (∫ u in (0 : ℝ)..1,
      (1 + H ^ 2 * ‖expTwoPiI u - 1‖ ^ 2)⁻¹) ≤ H⁻¹ := by
  let k : ℝ → ℝ := fun u => (1 + (4 * H * u) ^ 2)⁻¹
  have hk : Continuous k := by
    dsimp [k]
    apply Continuous.inv₀
    · fun_prop
    · intro u
      positivity
  have hw : Continuous (fun u : ℝ =>
      (1 + H ^ 2 * ‖expTwoPiI u - 1‖ ^ 2)⁻¹) := by
    apply Continuous.inv₀
    · unfold expTwoPiI
      fun_prop
    · intro u
      positivity
  have hkr : Continuous (fun u : ℝ => k (1 - u)) := by
    fun_prop
  have hpoint (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      (1 + H ^ 2 * ‖expTwoPiI u - 1‖ ^ 2)⁻¹ ≤ k u + k (1 - u) := by
    have haux (t : ℝ) (ht : 0 ≤ t)
        (hb : 4 * t ≤ ‖expTwoPiI u - 1‖) :
        (1 + H ^ 2 * ‖expTwoPiI u - 1‖ ^ 2)⁻¹ ≤ k t := by
      have hs : (4 * H * t) ^ 2 ≤ H ^ 2 * ‖expTwoPiI u - 1‖ ^ 2 := by
        calc
          _ = H ^ 2 * (4 * t) ^ 2 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            ((sq_le_sq₀ (by positivity) (norm_nonneg _)).2 hb) (sq_nonneg H)
      dsimp [k]
      exact (inv_le_inv₀ (by positivity) (by positivity)).2 (by linarith)
    by_cases hh : u ≤ 1 / 2
    · have hb : 4 * u ≤ ‖expTwoPiI u - 1‖ := by
        rw [fm_phase_norm]
        have hs := fm_sin_lower_half u hu.1 hh
        linarith [le_abs_self (Real.sin (Real.pi * u))]
      exact (haux u hu.1 hb).trans
        (le_add_of_nonneg_right (by dsimp [k]; positivity))
    · have hs := fm_sin_lower_half (1 - u) (by linarith [hu.2]) (by linarith)
      rw [show Real.pi * (1 - u) = Real.pi - Real.pi * u by ring,
        Real.sin_pi_sub] at hs
      have hb : 4 * (1 - u) ≤ ‖expTwoPiI u - 1‖ := by
        rw [fm_phase_norm]
        linarith [le_abs_self (Real.sin (Real.pi * u))]
      exact (haux (1 - u) (by linarith [hu.2]) hb).trans
        (le_add_of_nonneg_left (by dsimp [k]; positivity))
  have hik : (∫ u in (0 : ℝ)..1, k u) =
      (4 * H)⁻¹ * Real.arctan (4 * H) := by
    change (∫ u in (0 : ℝ)..1, (1 + (4 * H * u) ^ 2)⁻¹) = _
    rw [intervalIntegral.integral_comp_mul_left
      (fun x : ℝ => (1 + x ^ 2)⁻¹) (by positivity : 4 * H ≠ 0),
      integral_inv_one_add_sq]
    simp
  have hikr : (∫ u in (0 : ℝ)..1, k (1 - u)) =
      (4 * H)⁻¹ * Real.arctan (4 * H) := by
    rw [intervalIntegral.integral_comp_sub_left k 1]
    simpa using hik
  calc
    _ ≤ ∫ u in (0 : ℝ)..1, k u + k (1 - u) :=
      intervalIntegral.integral_mono_on (by norm_num)
        (hw.intervalIntegrable 0 1)
        ((hk.add hkr).intervalIntegrable 0 1) hpoint
    _ = 2 * ((4 * H)⁻¹ * Real.arctan (4 * H)) := by
      rw [intervalIntegral.integral_add (hk.intervalIntegrable 0 1)
        (hkr.intervalIntegrable 0 1), hik, hikr]
      ring
    _ ≤ 2 * ((4 * H)⁻¹ * 2) := by
      have ha : Real.arctan (4 * H) ≤ 2 := by
        linarith [Real.arctan_lt_pi_div_two (4 * H), Real.pi_lt_four]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ha (by positivity)) (by norm_num)
    _ = H⁻¹ := by
      field_simp
      <;> ring

lemma fm_local_complete : ∃ A > 0, ∀ lam : ℝ, 0 < lam → ∀ m : ℤ,
    (∫ u in (0 : ℝ)..1, ‖seqFourier (poissonQLoc lam m) u‖) ≤
      A * poissonH lam ^ (-(1 : ℝ) / 2) *
        Real.exp (-|(m : ℝ) - lam / poissonH lam| / 4) := by
  obtain ⟨C, hC, henv⟩ := FourierMassBounds.localized_envelopes_ok
  refine ⟨4*C, by positivity, ?_⟩
  intro lam hl m
  let H := poissonH lam
  let E := Real.exp (-|(m : ℝ) - lam / poissonH lam| / 4)
  let b := poissonQLoc lam m
  have hH : 1 ≤ H := (pq_H lam hl).1
  have hp : 0 < H := by linarith
  have hE : 0 < E := Real.exp_pos _
  have hb : ∀ n, b n ≠ 0 → |(n : ℝ)/H - (m : ℝ)| < 2 :=
    fun n hn => (lem_fouriermass_support lam hl m n hn).trans (by norm_num)
  have hd : ∀ n, fwdDiff (1 : ℤ) b n ≠ 0 → |(n : ℝ)/H - (m : ℝ)| < 2 :=
    fun n hn => FourierMassBounds.poissonQLoc_diff_support_ok lam hl m n hn
  obtain ⟨s, hs⟩ := fm_finite_support H m hp b hb
  obtain ⟨t, ht⟩ := fm_finite_support H m hp (fwdDiff (1 : ℤ) b) hd
  have h1 := fm_support_energy H (m : ℝ) (C * H ^ (-(1 : ℝ)/2) * E)
    hH (by positivity) b hb (fun n => (henv lam hl m n).1)
  have h2 := fm_support_energy H (m : ℝ) (C * H ^ (-(3 : ℝ)/2) * E)
    hH (by positivity) (fwdDiff (1 : ℤ) b) hd (fun n => (henv lam hl m n).2)
  have he := fm_energy_algebra_ok H C E _ _ hp h1 h2
  let W : ℝ → ℝ := fun u => 1 + H^2 * ‖expTwoPiI u - 1‖^2
  have hW : Continuous W := by unfold W expTwoPiI; fun_prop
  have hWp : ∀ u, 0 < W u := by intro u; dsimp [W]; positivity
  have hcs := fm_weighted_cs (fun u => ‖seqFourier b u‖) W
    (fm_continuous_finite b s hs).norm hW hWp
  have hparse : (∫ u in (0 : ℝ)..1, W u * ‖seqFourier b u‖^2) =
      (∑' n : ℤ, b n^2) + H^2*(∑' n : ℤ, fwdDiff (1 : ℤ) b n^2) :=
    fm_weighted_parseval_ok b s t hs ht H
  have henergy : (∫ u in (0 : ℝ)..1, W u * ‖seqFourier b u‖^2) ≤
      14*C^2*E^2 := by rw [hparse]; exact he
  have hn : 0 ≤ (∫ u in (0 : ℝ)..1, W u * ‖seqFourier b u‖^2) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    exact mul_nonneg (hWp u).le (sq_nonneg _)
  have hh : (∫ u in (0 : ℝ)..1, ‖seqFourier b u‖)^2 ≤ H⁻¹*(14*C^2*E^2) :=
    hcs.trans (mul_le_mul (fm_reciprocal_weight_bound H hp) henergy hn (by positivity))
  have hsq : (4*C*H^(-(1:ℝ)/2)*E)^2 = 16*C^2*E^2*H⁻¹ := by
    simp only [mul_pow, fm_rpow_half_sq_ok H hp]
    ring
  have hn' : 0 ≤ 4*C*H^(-(1:ℝ)/2)*E := by positivity
  change (∫ u in (0 : ℝ)..1, ‖seqFourier b u‖) ≤ 4*C*H^(-(1:ℝ)/2)*E
  nlinarith [mul_nonneg (sq_nonneg (C*E)) (inv_nonneg.mpr hp.le)]

end LocalizedFourierFinal

theorem lem_fouriermass :
    ∃ C > 0, ∀ lam : ℝ, 0 < lam →
      (∀ n : ℤ, HasSum (fun m : ℤ => poissonQLoc lam m n) (poissonQ lam n)) ∧
      (∀ m n : ℤ, 1 ≤ |(n : ℝ) / poissonH lam - (m : ℝ)| → poissonQLoc lam m n = 0) ∧
      (Summable fun m : ℤ => ∫ u in (0:ℝ)..1, ‖seqFourier (poissonQLoc lam m) u‖) ∧
      (∑' m : ℤ, ∫ u in (0:ℝ)..1, ‖seqFourier (poissonQLoc lam m) u‖) ≤
        C * poissonH lam ^ (-(1 : ℝ) / 2) := by
  obtain ⟨A, hA, ha⟩ := LocalizedFourierFinal.fm_local_complete
  obtain ⟨B, hB, hb⟩ := LocalizedFourierFinal.FourierMassBounds.fm_shifted_exp_bound
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro lam hl
  have hp : 0 < poissonH lam := by linarith [(pq_H lam hl).1]
  have hx := hb (lam / poissonH lam)
  have hs : Summable (fun m : ℤ =>
      ∫ u in (0 : ℝ)..1, ‖seqFourier (poissonQLoc lam m) u‖) := by
    apply Summable.of_nonneg_of_le _ (ha lam hl) (hx.1.mul_left _)
    intro m
    exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => norm_nonneg _)
  refine ⟨?_, ?_, hs, ?_⟩
  · intro n
    obtain ⟨S, hS⟩ := LocalizedFourierFinal.fm_finite_support 1
      ((n : ℝ) / poissonH lam) (by norm_num)
      (fun m => poissonQLoc lam m n) (by
        intro m hm
        simpa only [div_one, abs_sub_comm] using
          (LocalizedFourierFinal.lem_fouriermass_support lam hl m n hm).trans
            (by norm_num : (1 : ℝ) < 2))
    have hsum : Summable (fun m : ℤ => poissonQLoc lam m n) :=
      summable_of_ne_finset_zero hS
    simpa only [LocalizedFourierFinal.lem_fouriermass_sum lam hl n] using hsum.hasSum
  · intro m n hn
    by_contra h
    exact (not_lt_of_ge hn) (LocalizedFourierFinal.lem_fouriermass_support lam hl m n h)
  · calc
      _ ≤ ∑' m : ℤ, A * poissonH lam ^ (-(1 : ℝ) / 2) *
          Real.exp (-|(m : ℝ) - lam / poissonH lam| / 4) :=
        Summable.tsum_le_tsum (ha lam hl) hs (hx.1.mul_left _)
      _ = A * poissonH lam ^ (-(1 : ℝ) / 2) *
          ∑' m : ℤ, Real.exp (-|(m : ℝ) - lam / poissonH lam| / 4) := tsum_mul_left
      _ ≤ A * poissonH lam ^ (-(1 : ℝ) / 2) * B :=
        mul_le_mul_of_nonneg_left hx.2 (by positivity)
      _ = _ := by ring


def boxZ (k : ℕ) (lo hi : Fin k → ℤ) : Finset (Fin k → ℤ) :=
  Fintype.piFinset fun s => Finset.Icc (lo s) (hi s)

def boxSide (k : ℕ) (lo hi : Fin k → ℤ) (s : Fin k) : ℕ :=
  (Finset.Icc (lo s) (hi s)).card

def boxVol (k : ℕ) (lo hi : Fin k → ℤ) : ℕ :=
  ∏ s, boxSide k lo hi s

def boxLen (k : ℕ) (w : Fin k → ℤ) (lo hi : Fin k → ℤ) : ℕ :=
  max 1 ((Finset.univ.filter fun s : Fin k => w s ≠ 0).sup (boxSide k lo hi))

noncomputable def boxSect (k : ℕ) (w : Fin k → ℤ) (lo hi : Fin k → ℤ) : ℝ :=
  (boxVol k lo hi : ℝ) / (boxLen k w lo hi : ℝ)

def polyBoxZ (k : ℕ) (L : Finset ((Fin k → ℤ) × ℤ)) (lo hi : Fin k → ℤ) :
    Finset (Fin k → ℤ) :=
  (boxZ k lo hi).filter fun x => ∀ p ∈ L, 0 ≤ (∑ s, p.1 s * x s) + p.2

noncomputable def quadExpSum (k : ℕ) (α : ℝ) (c : Fin k → ℕ) (θ : Fin k → ℝ)
    (S : Finset (Fin k → ℤ)) : ℂ :=
  ∑ n ∈ S, expTwoPiI (α * ∑ j, (c j : ℝ) * (n j : ℝ) ^ 2 + ∑ j, θ j * (n j : ℝ))

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

def PropUNmap : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ (R : ℕ) (U : ℕ → (Fin k → ℕ) → Fin k → ℕ),
    ∀ M : ℕ, 1 ≤ M → lcmUpTo k ∣ M → IsUNmap k R M (U M)

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

namespace ShiftedBoundProof

lemma section_le_product (k : ℕ) (w : Fin k → ℤ) (lo hi : Fin k → ℤ)
    (q : Fin k) (hq : w q ≠ 0) :
    boxSect k w lo hi ≤ ∏ s ∈ Finset.univ.erase q, (boxSide k lo hi s : ℝ) := by
  classical
  have hlen : 0 < (boxLen k w lo hi : ℝ) := by
    have : 1 ≤ boxLen k w lo hi := le_max_left _ _
    exact_mod_cast (show 0 < boxLen k w lo hi by omega)
  have hside : boxSide k lo hi q ≤ boxLen k w lo hi :=
    (Finset.le_sup (f := boxSide k lo hi)
      (s := Finset.univ.filter (fun s : Fin k => w s ≠ 0))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩)).trans
      (le_max_right _ _)
  unfold boxSect
  apply (div_le_iff₀ hlen).2
  have hprod : (boxVol k lo hi : ℝ) =
      (∏ s ∈ Finset.univ.erase q, (boxSide k lo hi s : ℝ)) * boxSide k lo hi q := by
    unfold boxVol
    rw [Nat.cast_prod]
    exact (Finset.prod_erase_mul _ _ (Finset.mem_univ q)).symm
  rw [hprod]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hside)
    (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))

end ShiftedBoundProof

lemma shifted_fourier_inversion (b : ℤ → ℝ) (S : Finset ℤ)
    (hb : ∀ m, m ∉ S → b m = 0) (n : ℤ) :
    (∫ u in (0 : ℝ)..1, seqFourier b u * expTwoPiI (u * (n : ℝ))) = (b n : ℂ) := by
  classical
  have he (u : ℝ) : seqFourier b u =
      ∑ m ∈ S, (b m : ℂ) * expTwoPiI (-(u * (m : ℝ))) := by
    apply tsum_eq_sum
    intro m hm
    simp [hb m hm]
  have hp (u : ℝ) (m : ℤ) :
      ((b m : ℂ) * expTwoPiI (-(u * (m : ℝ)))) * expTwoPiI (u * (n : ℝ)) =
        (b m : ℂ) * expTwoPiI (u * ((n - m : ℤ) : ℝ)) := by
    rw [mul_assoc, ← onb_exp_add]
    congr 2
    push_cast
    ring
  have hi (m : ℤ) : IntervalIntegrable
      (fun u : ℝ => (b m : ℂ) * expTwoPiI (u * ((n-m : ℤ) : ℝ)))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold expTwoPiI
    fun_prop
  simp_rw [he, Finset.sum_mul, hp]
  rw [intervalIntegral.integral_finsetSum (fun m _ => hi m)]
  simp_rw [intervalIntegral.integral_const_mul,
    LocalizedFourierFinal.FourierMassBounds.fm_integral_exp_int_ok]
  by_cases hn : n ∈ S
  · simp [sub_eq_zero, mul_ite, hn]
  · simp [sub_eq_zero, mul_ite, hn, hb n hn]

lemma shifted_choose_bound_ok (M b k : ℕ) :
    (M + b + k).choose k ≤ (b + 1)^k * (M + k).choose k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h₁ := Nat.add_one_mul_choose_eq (M + b + k) k
    have h₂ := Nat.add_one_mul_choose_eq (M + k) k
    apply Nat.le_of_mul_le_mul_right (c := k + 1) _ (Nat.succ_pos k)
    calc
      (M + b + (k + 1)).choose (k + 1) * (k + 1) =
          (M + b + k + 1) * (M + b + k).choose k := by
            simpa [Nat.add_assoc] using h₁.symm
      _ ≤ (M + b + k + 1) * ((b + 1)^k * (M + k).choose k) :=
        Nat.mul_le_mul_left _ ih
      _ ≤ ((b + 1) * (M + k + 1)) * ((b + 1)^k * (M + k).choose k) := by
        apply Nat.mul_le_mul_right
        nlinarith
      _ = ((b + 1)^(k + 1) * (M + (k + 1)).choose (k + 1)) * (k + 1) := by
        rw [pow_succ]
        calc
          _ = ((b + 1)^k * (b + 1)) * ((M + k + 1) * (M + k).choose k) := by ring
          _ = _ := by rw [h₂]; ring_nf

lemma shifted_ratio_bound_checked (k N : ℕ) :
    (((N + k).choose k : ℝ) /
      ((N - N % lcmUpTo k + k).choose k : ℝ)) ≤
        ((lcmUpTo k : ℝ) + 1)^k := by
  have hl : 0 < lcmUpTo k := by
    apply Nat.pos_of_ne_zero
    intro hz
    obtain ⟨x, hx, hx0⟩ := Finset.lcm_eq_zero_iff.mp hz
    have hx1 := (Finset.mem_Icc.mp hx).1
    change x = 0 at hx0
    omega
  have hb := Nat.mod_lt N hl
  have hs := shifted_choose_bound_ok (N - N % lcmUpTo k) (N % lcmUpTo k) k
  rw [Nat.sub_add_cancel (Nat.mod_le N _)] at hs
  have hc : (0 : ℝ) < (N - N % lcmUpTo k + k).choose k := by
    exact_mod_cast (Nat.choose_pos (show k ≤ N - N % lcmUpTo k + k by omega))
  apply (div_le_iff₀ hc).2
  have hs' : ((N + k).choose k : ℝ) ≤
      (((N % lcmUpTo k : ℕ) : ℝ) + 1)^k * ((N - N % lcmUpTo k + k).choose k : ℝ) := by
    exact_mod_cast hs
  apply hs'.trans
  apply mul_le_mul_of_nonneg_right _ hc.le
  gcongr

lemma shifted_fourier_transfer_step {ι : Type*} (s : Finset ι)
    (x : ι → ℤ) (f : ι → ℂ) (b : ℤ → ℝ) (S : Finset ℤ)
    (hb : ∀ m, m ∉ S → b m = 0) (B : ℝ)
    (hB : ∀ u : ℝ, ‖∑ n ∈ s, expTwoPiI (u * (x n : ℝ)) * f n‖ ≤ B) :
    ‖∑ n ∈ s, (b (x n) : ℂ) * f n‖ ≤
      (∫ u in (0 : ℝ)..1, ‖seqFourier b u‖) * B := by
  classical
  have hc := LocalizedFourierFinal.fm_continuous_finite b S hb
  have hi (n : ι) : IntervalIntegrable
      (fun u : ℝ => seqFourier b u * expTwoPiI (u * (x n : ℝ)) * f n)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.mul _ continuous_const
    apply Continuous.mul hc
    unfold expTwoPiI
    fun_prop
  have he : (∑ n ∈ s, (b (x n) : ℂ) * f n) =
      ∫ u in (0 : ℝ)..1,
        seqFourier b u * (∑ n ∈ s, expTwoPiI (u * (x n : ℝ)) * f n) := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [intervalIntegral.integral_finsetSum (fun n _ => hi n)]
    apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_mul_const, shifted_fourier_inversion b S hb]
  rw [he]
  calc
    _ ≤ ∫ u in (0 : ℝ)..1, ‖seqFourier b u‖ * B := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      · filter_upwards [] with u hu
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB u) (norm_nonneg _)
      · exact (hc.norm.mul continuous_const).intervalIntegrable 0 1
    _ = _ := intervalIntegral.integral_mul_const _ _

lemma shifted_fourier_transfer_product {ι κ : Type*} [Fintype κ]
    (s : Finset ι) (x : ι → κ → ℤ) (b : κ → ℤ → ℝ)
    (S : κ → Finset ℤ) (hb : ∀ j m, m ∉ S j → b j m = 0)
    (t : Finset κ) (f : ι → ℂ) (B : ℝ)
    (hB : ∀ θ : κ → ℝ,
      ‖∑ n ∈ s, expTwoPiI (∑ j, θ j * (x n j : ℝ)) * f n‖ ≤ B) :
    ‖∑ n ∈ s, (∏ j ∈ t, (b j (x n j) : ℂ)) * f n‖ ≤
      (∏ j ∈ t, ∫ u in (0 : ℝ)..1, ‖seqFourier (b j) u‖) * B := by
  classical
  induction t using Finset.induction_on generalizing f with
  | empty =>
      simpa [expTwoPiI] using hB (fun _ => 0)
  | @insert q t hqt ih =>
      have he : (∑ n ∈ s, (∏ j ∈ insert q t, (b j (x n j) : ℂ)) * f n) =
          ∑ n ∈ s, (b q (x n q) : ℂ) * ((∏ j ∈ t, (b j (x n j) : ℂ)) * f n) := by
        simp only [Finset.prod_insert hqt, mul_assoc]
      rw [he, Finset.prod_insert hqt]
      calc
        _ ≤ (∫ u in (0 : ℝ)..1, ‖seqFourier (b q) u‖) *
            ((∏ j ∈ t, ∫ u in (0 : ℝ)..1, ‖seqFourier (b j) u‖) * B) := by
          apply shifted_fourier_transfer_step s (fun n => x n q)
            (fun n => (∏ j ∈ t, (b j (x n j) : ℂ)) * f n) (b q) (S q) (hb q)
          intro u
          have ht := ih (fun n => expTwoPiI (u * (x n q : ℝ)) * f n) (by
            intro θ
            have hv := hB (fun j => θ j + if j = q then u else 0)
            have hp (n : ι) :
                (∑ j, (θ j + if j = q then u else 0) * (x n j : ℝ)) =
                  (∑ j, θ j * (x n j : ℝ)) + u * (x n q : ℝ) := by
              simp [add_mul, Finset.sum_add_distrib, ite_mul]
            simp_rw [hp, onb_exp_add, mul_assoc] at hv
            exact hv)
          convert ht using 1
          congr 1
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = _ := by ring

lemma shifted_localized_box_bound (hbox : ThmBox)
    (K r V h : ℕ) (a : ℝ) (hK : 1 ≤ K) (hV : 1 ≤ V)
    (hh : 1 ≤ h) (ha : 1 ≤ a) :
    ∃ C > 0, ∀ α : ℝ, Irrational α →
      (∀ (i : ℕ) (x : ℝ), (GenContFract.of α).partDens.get? i = some x → x ≤ a) →
      ∀ c : Fin K → ℕ, (∀ j, 1 ≤ c j) → (∀ j, c j ≤ h) →
      ∀ lo hi : Fin K → ℤ, (∀ j, lo j ≤ hi j) →
      ∀ L : Finset ((Fin K → ℤ) × ℤ), L.card ≤ r →
        (∀ p ∈ L, ∑ j, |p.1 j| ≤ (V : ℤ)) →
      ∀ (w : Fin K → ℤ) (d : ℤ), w ≠ 0 → (w, d) ∈ L → (-w, -d) ∈ L →
      ∀ (θ lam : Fin K → ℝ), (∀ j, 0 < lam j) → ∀ m : Fin K → ℤ,
      ‖∑ n ∈ polyBoxZ K L lo hi,
        (∏ j, (poissonQLoc (lam j) (m j) (n j) : ℂ)) *
          expTwoPiI (α * ∑ j, (c j : ℝ) * (n j : ℝ)^2 +
            ∑ j, θ j * (n j : ℝ))‖ ≤
        C * Real.sqrt (boxSect K w lo hi) *
          ∏ j, ∫ u in (0 : ℝ)..1, ‖seqFourier (poissonQLoc (lam j) (m j)) u‖ := by
  classical
  obtain ⟨C, hC, hbound⟩ := hbox K r V h a hK hV hh ha
  refine ⟨C, hC, ?_⟩
  intro α hα hαa c hc hc' lo hi hlo L hL hL' w d hw hwd hneg θ lam hlam m
  have hsup (j : Fin K) : ∃ S : Finset ℤ,
      ∀ n, n ∉ S → poissonQLoc (lam j) (m j) n = 0 := by
    apply LocalizedFourierFinal.fm_finite_support (poissonH (lam j)) (m j)
      (lt_of_lt_of_le (by norm_num) (pq_H (lam j) (hlam j)).1)
    intro n hn
    exact (LocalizedFourierFinal.lem_fouriermass_support (lam j) (hlam j) (m j) n hn).trans
      (by norm_num)
  choose S hS using hsup
  have ht := shifted_fourier_transfer_product
    (polyBoxZ K L lo hi) (fun n => n) (fun j => poissonQLoc (lam j) (m j)) S hS
    Finset.univ
    (fun n => expTwoPiI (α * ∑ j, (c j : ℝ) * (n j : ℝ)^2 + ∑ j, θ j * (n j : ℝ)))
    (C * Real.sqrt (boxSect K w lo hi)) (by
      intro u
      have hphase (n : Fin K → ℤ) :
          expTwoPiI (∑ j, u j * (n j : ℝ)) *
            expTwoPiI (α * ∑ j, (c j : ℝ) * (n j : ℝ)^2 + ∑ j, θ j * (n j : ℝ)) =
          expTwoPiI (α * ∑ j, (c j : ℝ) * (n j : ℝ)^2 +
            ∑ j, (θ j + u j) * (n j : ℝ)) := by
        rw [← onb_exp_add]
        congr 1
        simp only [add_mul, Finset.sum_add_distrib]
        ring
      simp_rw [hphase]
      exact (hbound α hα hαa c hc hc' lo hi hlo L hL hL' (fun j => θ j + u j)).2
        w d hw hwd hneg)
  simpa only [mul_comm] using ht

lemma shifted_log_factorial_upper (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N.factorial : ℝ) ≤ (N : ℝ) * Real.log N - N + Real.log N / 2 + 1 := by
  have hp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs := Stirling.log_stirlingSeq'_antitone (show 0 ≤ N - 1 by omega)
  change Real.log (Stirling.stirlingSeq ((N - 1) + 1)) ≤ Real.log (Stirling.stirlingSeq 1) at hs
  rw [Nat.sub_add_cancel hN, Stirling.stirlingSeq_one,
    Stirling.log_stirlingSeq_formula] at hs
  rw [Real.log_div (Real.exp_ne_zero 1) (by positivity : Real.sqrt (2 : ℝ) ≠ 0),
    Real.log_exp, Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp.ne',
    Real.log_div hp.ne' (Real.exp_ne_zero 1), Real.log_exp] at hs
  nlinarith

lemma shifted_poisson_constant_bound (N : ℕ) (hN : 1 ≤ N) :
    Real.exp ((N : ℝ) / 2) * Real.sqrt (N.factorial : ℝ) /
        (N : ℝ) ^ ((N : ℝ) / 2) ≤
      Real.exp (1 / 2) * (N : ℝ) ^ ((1 : ℝ) / 4) := by
  have hp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hlog : Real.log (Real.exp ((N : ℝ) / 2) * Real.sqrt (N.factorial : ℝ) /
      (N : ℝ) ^ ((N : ℝ) / 2)) ≤ 1 / 2 + Real.log N / 4 := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_exp,
      Real.log_sqrt hf.le, Real.log_rpow hp]
    linarith [shifted_log_factorial_upper N hN]
  have hh := Real.le_exp_of_log_le hlog
  convert hh using 1
  rw [Real.rpow_def_of_pos hp, ← Real.exp_add]
  congr 1
  ring

lemma shifted_poisson_factorization_ok (K N : ℕ) (hN : 1 ≤ N)
    (r : Fin K → ℝ) (hr : ∀ j, 0 < r j) (hs : ∑ j, r j = 1)
    (n : Fin K → ℕ) (hn : ∑ j, n j = N) :
    Real.sqrt (Nat.multinomial Finset.univ n : ℝ) *
      (∏ j, (r j) ^ ((n j : ℝ) / 2)) =
    (Real.exp ((N : ℝ) / 2) * Real.sqrt (N.factorial : ℝ) /
      (N : ℝ) ^ ((N : ℝ) / 2)) * ∏ j, poissonQ ((N : ℝ) * r j) (n j) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm : (0 : ℝ) < Nat.multinomial Finset.univ n := by
    exact_mod_cast Nat.multinomial_pos Finset.univ n
  have hf (j : Fin K) : (0 : ℝ) < (n j).factorial := by
    exact_mod_cast Nat.factorial_pos (n j)
  have hq (j : Fin K) : 0 < poissonQ ((N : ℝ) * r j) (n j) :=
    pq_pos _ (mul_pos hNp (hr j)) _
  have hpR : 0 < ∏ j, (r j) ^ ((n j : ℝ) / 2) :=
    Finset.prod_pos (fun j _ => Real.rpow_pos_of_pos (hr j) _)
  have hpQ : 0 < ∏ j, poissonQ ((N : ℝ) * r j) (n j) :=
    Finset.prod_pos (fun j _ => hq j)
  have hpF : 0 < ∏ j, ((n j).factorial : ℝ) :=
    Finset.prod_pos (fun j _ => hf j)
  have hnr : (∑ j, (n j : ℝ)) = N := by exact_mod_cast hn
  have hmfact : (∏ j, ((n j).factorial : ℝ)) *
      (Nat.multinomial Finset.univ n : ℝ) = (N.factorial : ℝ) := by
    exact_mod_cast (show (∏ j, (n j).factorial) *
      Nat.multinomial Finset.univ n = N.factorial by
        rw [Nat.multinomial_spec, hn])
  have hmlog : (∑ j, Real.log ((n j).factorial : ℝ)) +
      Real.log (Nat.multinomial Finset.univ n : ℝ) = Real.log (N.factorial : ℝ) := by
    have he := congrArg Real.log hmfact
    rw [Real.log_mul (by positivity) hm.ne', Real.log_prod (fun j _ => (hf j).ne')] at he
    exact he
  have he : Real.log (Real.sqrt (Nat.multinomial Finset.univ n : ℝ) *
      (∏ j, (r j) ^ ((n j : ℝ) / 2))) =
    Real.log ((Real.exp ((N : ℝ) / 2) * Real.sqrt (N.factorial : ℝ) /
      (N : ℝ) ^ ((N : ℝ) / 2)) * ∏ j, poissonQ ((N : ℝ) * r j) (n j)) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_sqrt hm.le,
      Real.log_prod (fun j _ => (Real.rpow_pos_of_pos (hr j) _).ne')]
    simp_rw [Real.log_rpow (hr _)]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_exp,
      Real.log_sqrt (by positivity), Real.log_rpow hNp,
      Real.log_prod (fun j _ => (hq j).ne')]
    simp_rw [pq_log _ (mul_pos hNp (hr _)), Real.log_mul hNp.ne' (hr _).ne']
    have hsum : (∑ j : Fin K, (-(N : ℝ) * r j / 2 +
        (n j : ℝ) / 2 * (Real.log N + Real.log (r j)) -
          Real.log ((n j).factorial : ℝ) / 2)) =
        -(N : ℝ) / 2 + (N : ℝ) / 2 * Real.log N +
          (∑ j, (n j : ℝ) / 2 * Real.log (r j)) -
          (∑ j, Real.log ((n j).factorial : ℝ)) / 2 := by
      simp only [mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul, hs, hnr]
      ring
    simp only [neg_mul] at hsum
    rw [hsum]
    linarith
  have he' := congrArg Real.exp he
  rwa [Real.exp_log (by positivity), Real.exp_log (by positivity)] at he'

lemma shifted_scale_cancel_ok (N K H : ℝ) (hN : 0 < N) (hK : 0 < K)
    (hH : 0 < H) (h : N ≤ K * H ^ 2) :
    N ^ ((1 : ℝ) / 4) * H ^ (-(1 : ℝ) / 2) ≤ K ^ ((1 : ℝ) / 4) := by
  have hl := Real.log_le_log hN h
  rw [Real.log_mul hK.ne' (pow_ne_zero 2 hH.ne'), Real.log_pow] at hl
  rw [Real.rpow_def_of_pos hN, Real.rpow_def_of_pos hH,
    ← Real.exp_add, Real.rpow_def_of_pos hK]
  apply Real.exp_le_exp.mpr
  norm_num at hl ⊢
  linarith

lemma shifted_local_box_geometry_ok (K : ℕ) (H : Fin K → ℝ)
    (hH : ∀ j, 1 ≤ H j) (m : Fin K → ℤ) :
    let lo := fun j => ⌊((m j : ℝ) - 1) * H j⌋
    let hi := fun j => ⌈((m j : ℝ) + 1) * H j⌉
    (∀ j, lo j ≤ hi j) ∧
    (∀ j, (boxSide K lo hi j : ℝ) ≤ 5 * H j) ∧
    (∀ n : Fin K → ℤ, (∀ j, |(n j : ℝ) / H j - m j| < 1) → n ∈ boxZ K lo hi) := by
  dsimp only
  have hp (j) : 0 < H j := by linarith [hH j]
  have hlh (j) : ⌊((m j : ℝ) - 1) * H j⌋ ≤ ⌈((m j : ℝ) + 1) * H j⌉ := by
    exact_mod_cast (show (⌊((m j : ℝ) - 1) * H j⌋ : ℝ) ≤
      ⌈((m j : ℝ) + 1) * H j⌉ by
      have := Int.floor_le (((m j : ℝ) - 1) * H j)
      have := Int.le_ceil (((m j : ℝ) + 1) * H j)
      nlinarith [hH j])
  refine ⟨hlh, ?_, ?_⟩
  · intro j
    unfold boxSide
    rw [Int.card_Icc]
    have hnonneg : 0 ≤ ⌈((m j : ℝ) + 1) * H j⌉ + 1 - ⌊((m j : ℝ) - 1) * H j⌋ := by
      have := hlh j
      omega
    have hc : ((⌈((m j : ℝ) + 1) * H j⌉ + 1 - ⌊((m j : ℝ) - 1) * H j⌋).toNat : ℝ) =
        (⌈((m j : ℝ) + 1) * H j⌉ : ℝ) + 1 - ⌊((m j : ℝ) - 1) * H j⌋ := by
      exact_mod_cast (Int.toNat_of_nonneg hnonneg)
    rw [hc]
    push_cast
    have := Int.lt_floor_add_one (((m j : ℝ) - 1) * H j)
    have := Int.ceil_lt_add_one (((m j : ℝ) + 1) * H j)
    nlinarith [hH j]
  · intro n hn
    apply Fintype.mem_piFinset.mpr
    intro j
    apply Finset.mem_Icc.mpr
    obtain ⟨hlo, hhi⟩ := abs_lt.mp (hn j)
    have hl : ((m j : ℝ) - 1) * H j < n j :=
      (lt_div_iff₀ (hp j)).mp (by linarith)
    have hh : (n j : ℝ) < ((m j : ℝ) + 1) * H j :=
      (div_lt_iff₀ (hp j)).mp (by linarith)
    constructor
    · exact_mod_cast (Int.floor_le (((m j : ℝ) - 1) * H j)).trans hl.le
    · exact_mod_cast hh.le.trans (Int.le_ceil (((m j : ℝ) + 1) * H j))

lemma shifted_local_box_section_checked (K : ℕ) (H : Fin K → ℝ)
    (hH : ∀ j, 1 ≤ H j) (m : Fin K → ℤ) (q : Fin K) :
    let lo := fun j => ⌊((m j : ℝ) - 1) * H j⌋
    let hi := fun j => ⌈((m j : ℝ) + 1) * H j⌉
    Real.sqrt (boxSect K (fun _ => 1) lo hi) ≤
      ∏ j ∈ Finset.univ.erase q, Real.sqrt (5 * H j) := by
  classical
  dsimp only
  calc
    _ ≤ Real.sqrt (∏ j ∈ Finset.univ.erase q,
        (boxSide K (fun j => ⌊((m j : ℝ) - 1) * H j⌋)
          (fun j => ⌈((m j : ℝ) + 1) * H j⌉) j : ℝ)) :=
      Real.sqrt_le_sqrt (ShiftedBoundProof.section_le_product K (fun _ => 1) _ _ q (by norm_num))
    _ ≤ Real.sqrt (∏ j ∈ Finset.univ.erase q, 5 * H j) := by
      apply Real.sqrt_le_sqrt
      apply Finset.prod_le_prod₀
      · intro j hj; positivity
      · intro j hj
        exact (shifted_local_box_geometry_ok K H hH m).2.1 j
    _ = _ := Real.sqrt_prod _ (fun j _ => by linarith [hH j])

lemma shifted_finite_localization_bound {ι κ : Type*} [Fintype κ]
    (s : Finset ι) (S : κ → Finset ℤ)
    (q : κ → ι → ℂ) (b : κ → ℤ → ι → ℂ) (f : ι → ℂ)
    (g : κ → ℤ → ℝ) (M : κ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hq : ∀ n ∈ s, ∀ j, q j n = ∑ m ∈ S j, b j m n)
    (hg : ∀ j m, 0 ≤ g j m)
    (hM : ∀ j, ∑ m ∈ S j, g j m ≤ M j)
    (hloc : ∀ m : κ → ℤ,
      ‖∑ n ∈ s, (∏ j, b j (m j) n) * f n‖ ≤ B * ∏ j, g j (m j)) :
    ‖∑ n ∈ s, (∏ j, q j n) * f n‖ ≤ B * ∏ j, M j := by
  classical
  have he : (∑ n ∈ s, (∏ j, q j n) * f n) =
      ∑ m ∈ Fintype.piFinset S, ∑ n ∈ s, (∏ j, b j (m j) n) * f n := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    simp_rw [hq n hn]
    rw [Finset.prod_univ_sum, Finset.sum_mul]
  rw [he]
  calc
    _ ≤ ∑ m ∈ Fintype.piFinset S,
        ‖∑ n ∈ s, (∏ j, b j (m j) n) * f n‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Fintype.piFinset S, B * ∏ j, g j (m j) :=
      Finset.sum_le_sum (fun m _ => hloc m)
    _ = B * ∏ j, ∑ m ∈ S j, g j m := by
      rw [← Finset.mul_sum, ← Finset.prod_univ_sum]
    _ ≤ B * ∏ j, M j := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg (fun m _ => hg j m))
        (fun j _ => hM j)

lemma shifted_poisson_localization_bound {ι κ : Type*} [Fintype κ]
    (s : Finset ι) (x : ι → κ → ℤ) (lam : κ → ℝ)
    (hlam : ∀ j, 0 < lam j) (f : ι → ℂ) (B C : ℝ) (hB : 0 ≤ B)
    (hmass : ∀ j,
      Summable (fun m : ℤ => ∫ u in (0 : ℝ)..1, ‖seqFourier (poissonQLoc (lam j) m) u‖) ∧
      (∑' m : ℤ, ∫ u in (0 : ℝ)..1, ‖seqFourier (poissonQLoc (lam j) m) u‖) ≤
        C * poissonH (lam j) ^ (-(1 : ℝ) / 2))
    (hloc : ∀ m : κ → ℤ,
      ‖∑ n ∈ s, (∏ j, (poissonQLoc (lam j) (m j) (x n j) : ℂ)) * f n‖ ≤
        B * ∏ j, ∫ u in (0 : ℝ)..1, ‖seqFourier (poissonQLoc (lam j) (m j)) u‖) :
    ‖∑ n ∈ s, (∏ j, (poissonQ (lam j) (x n j) : ℂ)) * f n‖ ≤
      B * ∏ j, C * poissonH (lam j) ^ (-(1 : ℝ) / 2) := by
  classical
  have hs (j : κ) (n : ι) : ∃ T : Finset ℤ,
      ∀ m, m ∉ T → poissonQLoc (lam j) m (x n j) = 0 := by
    apply LocalizedFourierFinal.fm_finite_support 1
      ((x n j : ℝ) / poissonH (lam j)) (by norm_num)
    intro m hm
    simpa only [div_one, abs_sub_comm] using
      (LocalizedFourierFinal.lem_fouriermass_support (lam j) (hlam j) m (x n j) hm).trans
        (by norm_num : (1 : ℝ) < 2)
  choose T hT using hs
  let S (j : κ) := s.biUnion (T j)
  have hS (j : κ) (n : ι) (hn : n ∈ s) (m : ℤ) (hm : m ∉ S j) :
      poissonQLoc (lam j) m (x n j) = 0 := by
    apply hT j n m
    intro ht
    exact hm (Finset.mem_biUnion.mpr ⟨n, hn, ht⟩)
  apply shifted_finite_localization_bound s S
    (fun j n => (poissonQ (lam j) (x n j) : ℂ))
    (fun j m n => (poissonQLoc (lam j) m (x n j) : ℂ)) f
    (fun j m => ∫ u in (0 : ℝ)..1, ‖seqFourier (poissonQLoc (lam j) m) u‖)
    (fun j => C * poissonH (lam j) ^ (-(1 : ℝ) / 2)) B hB
  · intro n hn j
    have he : poissonQ (lam j) (x n j) = ∑ m ∈ S j, poissonQLoc (lam j) m (x n j) := by
      rw [← LocalizedFourierFinal.lem_fouriermass_sum (lam j) (hlam j) (x n j)]
      exact tsum_eq_sum (hS j n hn)
    exact_mod_cast he
  · intro j m
    exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => norm_nonneg _)
  · intro j
    exact (Summable.sum_le_tsum (S j) (fun m _ =>
      intervalIntegral.integral_nonneg (by norm_num) (fun u _ => norm_nonneg _))
      (hmass j).1).trans (hmass j).2
  · exact hloc

lemma shifted_extend_nonzero {K : ℕ}
    (F G : (Fin K → ℂ) → ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (h : ∀ z, (∀ j, z j ≠ 0) → F z ≤ G z) :
    ∀ z, F z ≤ G z := by
  have hd0 : Dense ({0}ᶜ : Set ℂ) := by
    rw [dense_iff_closure_eq, closure_compl_singleton]
  have hd : Dense {z : Fin K → ℂ | ∀ j, z j ≠ 0} := by
    simpa [Set.pi] using
      dense_pi (Set.univ : Set (Fin K)) (fun _ _ => hd0)
  exact hd.induction (fun z hz => h z hz) (isClosed_le hF hG)

lemma shifted_poly_homogeneous (K N : ℕ)
    (c : PolySpaceH K N) (t : ℂ) (z : Fin K → ℂ) :
    polyEval K N c (fun j => t * z j) =
      t ^ N * polyEval K N c z := by
  unfold polyEval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum,
    (onb_mem_deg K N n.val).mp n.property]
  ring

lemma shifted_sphere_boundary_ok (K N : ℕ) (hK : 1 ≤ K)
    (c : PolySpaceH K N) (A : ℝ)
    (h : ∀ z : Fin K → ℂ, (∀ j, z j ≠ 0) →
      ∑ j, ‖z j‖ ^ 2 = 1 → ‖polyEval K N c z‖ ≤ A) :
    ∀ z : Fin K → ℂ, ∑ j, ‖z j‖ ^ 2 = 1 → ‖polyEval K N c z‖ ≤ A := by
  have he : ∀ z : Fin K → ℂ, ‖polyEval K N c z‖ ≤
      A * (Real.sqrt (∑ j, ‖z j‖ ^ 2)) ^ N := by
    apply shifted_extend_nonzero
    · unfold polyEval; fun_prop
    · fun_prop
    intro z hz
    let r := Real.sqrt (∑ j, ‖z j‖ ^ 2)
    have hs : 0 < ∑ j, ‖z j‖ ^ 2 := by
      let q : Fin K := ⟨0, by omega⟩
      have hq : 0 < ‖z q‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (hz q))
      exact hq.trans_le (Finset.single_le_sum (fun j _ => sq_nonneg ‖z j‖) (Finset.mem_univ q))
    have hr : 0 < r := Real.sqrt_pos.mpr hs
    have hr2 : r ^ 2 = ∑ j, ‖z j‖ ^ 2 := Real.sq_sqrt hs.le
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    let v : Fin K → ℂ := fun j => (r : ℂ)⁻¹ * z j
    have hv : ∀ j, v j ≠ 0 := fun j => mul_ne_zero (inv_ne_zero hrc) (hz j)
    have hvnorm (j) : ‖v j‖ = r⁻¹ * ‖z j‖ := by
      simp [v, norm_mul, norm_inv, Complex.norm_real, abs_of_pos hr]
    have hvunit : ∑ j, ‖v j‖ ^ 2 = 1 := by
      simp_rw [hvnorm, mul_pow]
      rw [← Finset.mul_sum, ← hr2, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
    have hscale : (fun j => (r : ℂ) * v j) = z := by
      funext j
      simp [v, hrc]
    have hp := shifted_poly_homogeneous K N c (r : ℂ) v
    rw [hscale] at hp
    rw [hp, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (h v hv hvunit) (pow_nonneg hr.le N)
  intro z hz
  simpa [hz] using he z

lemma shifted_poisson_polytope_bound (hbox : ThmBox)
    (K r V h : ℕ) (a : ℝ) (hK : 1 ≤ K) (hV : 1 ≤ V)
    (hh : 1 ≤ h) (ha : 1 ≤ a) :
    ∃ C > 0, ∀ α : ℝ, Irrational α →
      (∀ (i : ℕ) (x : ℝ), (GenContFract.of α).partDens.get? i = some x → x ≤ a) →
      ∀ c : Fin K → ℕ, (∀ j, 1 ≤ c j) → (∀ j, c j ≤ h) →
      ∀ L : Finset ((Fin K → ℤ) × ℤ), L.card ≤ r →
        (∀ p ∈ L, ∑ j, |p.1 j| ≤ (V : ℤ)) →
      ∀ d : ℤ, ((fun _ => 1), d) ∈ L → ((fun _ => -1), -d) ∈ L →
      ∀ S : Finset (Fin K → ℤ),
        (∀ n, n ∈ S ↔ ∀ p ∈ L, 0 ≤ (∑ j, p.1 j * n j) + p.2) →
      ∀ θ lam : Fin K → ℝ, (∀ j, 0 < lam j) → ∀ q : Fin K,
      ‖∑ n ∈ S, (∏ j, (poissonQ (lam j) (n j) : ℂ)) *
        expTwoPiI (α * ∑ j, (c j : ℝ) * (n j : ℝ)^2 + ∑ j, θ j * (n j : ℝ))‖ ≤
        C * (∏ j ∈ Finset.univ.erase q, Real.sqrt (5 * poissonH (lam j))) *
          ∏ j, poissonH (lam j) ^ (-(1 : ℝ) / 2) := by
  classical
  obtain ⟨C, hC, hc⟩ := shifted_localized_box_bound hbox K r V h a hK hV hh ha
  obtain ⟨D, hD, hd⟩ := lem_fouriermass
  refine ⟨C * D ^ K, by positivity, ?_⟩
  intro α hα hαa c hc1 hc2 L hL hL1 d hd1 hd2 S hS θ lam hlam q
  let F : (Fin K → ℤ) → ℂ := fun n =>
    expTwoPiI (α * ∑ j, (c j : ℝ) * (n j : ℝ)^2 + ∑ j, θ j * (n j : ℝ))
  let B : ℝ := C * ∏ j ∈ Finset.univ.erase q, Real.sqrt (5 * poissonH (lam j))
  have hB : 0 ≤ B := mul_nonneg hC.le (Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _))
  have hmass (j : Fin K) := (hd (lam j) (hlam j)).2.2
  have hb := shifted_poisson_localization_bound S (fun n => n) lam hlam F B D hB hmass
  have hlocal (m : Fin K → ℤ) :
      ‖∑ n ∈ S, (∏ j, (poissonQLoc (lam j) (m j) (n j) : ℂ)) * F n‖ ≤
        B * ∏ j, ∫ u in (0 : ℝ)..1, ‖seqFourier (poissonQLoc (lam j) (m j)) u‖ := by
    let lo := fun j => ⌊((m j : ℝ) - 1) * poissonH (lam j)⌋
    let hi := fun j => ⌈((m j : ℝ) + 1) * poissonH (lam j)⌉
    have hgeo := shifted_local_box_geometry_ok K (fun j => poissonH (lam j))
      (fun j => (pq_H (lam j) (hlam j)).1) m
    have hsub : polyBoxZ K L lo hi ⊆ S := by
      intro n hn
      exact (hS n).2 (Finset.mem_filter.mp hn).2
    have he : (∑ n ∈ polyBoxZ K L lo hi,
        (∏ j, (poissonQLoc (lam j) (m j) (n j) : ℂ)) * F n) =
        ∑ n ∈ S, (∏ j, (poissonQLoc (lam j) (m j) (n j) : ℂ)) * F n := by
      apply Finset.sum_subset hsub
      intro n hn hn'
      by_contra hne
      have hp := (mul_ne_zero_iff.mp hne).1
      have hnonzero (j : Fin K) : poissonQLoc (lam j) (m j) (n j) ≠ 0 := by
        have := Finset.prod_ne_zero_iff.mp hp j (Finset.mem_univ j)
        exact_mod_cast this
      apply hn'
      exact Finset.mem_filter.mpr ⟨hgeo.2.2 n (fun j =>
        LocalizedFourierFinal.lem_fouriermass_support (lam j) (hlam j) (m j) (n j) (hnonzero j)),
        (hS n).1 hn⟩
    rw [← he]
    have hw : (fun _ : Fin K => (1 : ℤ)) ≠ 0 := by
      intro hz
      have := congrFun hz (⟨0, by omega⟩ : Fin K)
      norm_num at this
    have hh := hc α hα hαa c hc1 hc2 lo hi hgeo.1 L hL hL1
      (fun _ => 1) d hw hd1 hd2 θ lam hlam m
    apply hh.trans
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left
        (shifted_local_box_section_checked K (fun j => poissonH (lam j))
          (fun j => (pq_H (lam j) (hlam j)).1) m q) hC.le
    · apply Finset.prod_nonneg
      intro j hj
      exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => norm_nonneg _)
  have hout := hb hlocal
  simpa only [B, F, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, mul_assoc, mul_left_comm, mul_comm] using hout

lemma shifted_product_scale_cancel (K : ℕ) (H : Fin K → ℝ)
    (hH : ∀ j, 0 < H j) (q : Fin K) :
    (∏ j ∈ Finset.univ.erase q, Real.sqrt (5 * H j)) *
      (∏ j, H j ^ (-(1 : ℝ) / 2)) =
      (Real.sqrt 5) ^ (K - 1) * H q ^ (-(1 : ℝ) / 2) := by
  classical
  have he (j) : Real.sqrt (H j) * H j ^ (-(1 : ℝ) / 2) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (hH j)]
    norm_num
  have hprod := Finset.prod_erase_mul (Finset.univ : Finset (Fin K))
    (fun j => H j ^ (-(1 : ℝ) / 2)) (Finset.mem_univ q)
  rw [← hprod, ← mul_assoc, ← Finset.prod_mul_distrib]
  simp_rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5), mul_assoc, he, mul_one]
  simp

lemma shifted_poisson_max_scale (K N : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N)
    (r : Fin K → ℝ) (hr : ∀ j, 0 < r j) (hs : ∑ j, r j = 1) :
    ∃ q : Fin K, (N : ℝ) ^ ((1 : ℝ) / 4) *
        poissonH ((N : ℝ) * r q) ^ (-(1 : ℝ) / 2) ≤
      (K : ℝ) ^ ((1 : ℝ) / 4) := by
  classical
  obtain ⟨q, hq, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin K)) r
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  refine ⟨q, ?_⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hKp : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hsum : (1 : ℝ) ≤ (K : ℝ) * r q := by
    calc
      _ = ∑ j, r j := hs.symm
      _ ≤ ∑ _ : Fin K, r q := Finset.sum_le_sum (fun j hj => hmax j hj)
      _ = _ := by simp
  have hl := mul_pos hNp (hr q)
  have hHp : 0 < poissonH ((N : ℝ) * r q) := by linarith [(pq_H _ hl).1]
  apply shifted_scale_cancel_ok (N : ℝ) K _ hNp hKp hHp
  rw [(pq_H _ hl).2]
  nlinarith [mul_le_mul_of_nonneg_left hsum hNp.le]

noncomputable def shiftedLiftConstraints (k N b : ℕ)
    (L : Finset ((Fin k → ℤ) × ℤ)) :
    Finset ((Fin (k + 1) → ℤ) × ℤ) := by
  classical
  exact L.image (fun p => (Fin.snoc p.1 0, p.2)) ∪
    ((Finset.univ.image fun j : Fin (k + 1) =>
      ((fun s => if s = j then (1 : ℤ) else 0),
        -(if j = Fin.last k then (b : ℤ) else 0))) ∪
      {((fun _ => (1 : ℤ)), -(N : ℤ)),
       ((fun _ => (-1 : ℤ)), (N : ℤ))})

lemma shifted_lift_constraints_iff_final (k N b : ℕ)
    (L : Finset ((Fin k → ℤ) × ℤ))
    (x : Fin (k + 1) → ℤ) :
    (∀ p ∈ shiftedLiftConstraints k N b L,
      0 ≤ (∑ s, p.1 s * x s) + p.2) ↔
    (∀ p ∈ L, 0 ≤ (∑ s : Fin k, p.1 s * x s.castSucc) + p.2) ∧
      (∀ j, (if j = Fin.last k then (b : ℤ) else 0) ≤ x j) ∧
      ∑ s, x s = (N : ℤ) := by
  classical
  have hlift (p : (Fin k → ℤ) × ℤ) :
      (∑ s, (Fin.snoc (α := fun _ => ℤ) p.1 0) s * x s) =
        ∑ s : Fin k, p.1 s * x s.castSucc := by
    rw [Fin.sum_univ_castSucc]
    simp
  simp only [shiftedLiftConstraints, Finset.forall_mem_union, Finset.forall_mem_image,
    Finset.forall_mem_insert, Finset.mem_singleton, forall_eq, Finset.mem_univ, forall_const]
  simp only [hlift, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, neg_one_mul, Finset.sum_neg_distrib]
  constructor
  · rintro ⟨hL, hlo, hsum₁, hsum₂⟩
    refine ⟨hL, fun j => by have := @hlo j; split_ifs at * <;> omega, ?_⟩
    omega
  · rintro ⟨hL, hlo, hsum⟩
    refine ⟨hL, fun j => by have := @hlo j; split_ifs at * <;> omega, ?_, ?_⟩ <;> omega

lemma shifted_nat_lift_constraints_iff_ok (k N b : ℕ)
    (L : Finset ((Fin k → ℤ) × ℤ))
    (n : Fin (k + 1) → ℕ) :
    (∀ p ∈ shiftedLiftConstraints k N b L,
      0 ≤ (∑ s, p.1 s * (n s : ℤ)) + p.2) ↔
      (fun s : Fin k => n s.castSucc) ∈ polyP k L ∧
        b ≤ n (Fin.last k) ∧
        ∑ s, n s = N := by
  rw [shifted_lift_constraints_iff_final]
  constructor
  · rintro ⟨hL, hlo, hsum⟩
    refine ⟨hL, ?_, ?_⟩
    · have hlast := hlo (Fin.last k)
      simp only [if_pos rfl] at hlast
      exact_mod_cast hlast
    · exact_mod_cast hsum
  · rintro ⟨hL, hlast, hsum⟩
    refine ⟨hL, ?_, ?_⟩
    · intro j
      by_cases hj : j = Fin.last k
      · subst j
        simp only [if_pos rfl]
        exact_mod_cast hlast
      · simp only [if_neg hj]
        exact Nat.cast_nonneg _
    · exact_mod_cast hsum

noncomputable def shiftedNatPiece (k N b : ℕ) (L : Finset ((Fin k → ℤ) × ℤ)) :
    Finset (Fin (k+1) → ℕ) := by
  classical
  exact (degIdx (k+1) N).filter fun n =>
    (fun s : Fin k => n s.castSucc) ∈ polyP k L ∧ b ≤ n (Fin.last k)

noncomputable def shiftedIntPiece (k N b : ℕ) (L : Finset ((Fin k → ℤ) × ℤ)) :
    Finset (Fin (k+1) → ℤ) := by
  classical
  exact (shiftedNatPiece k N b L).image (fun n j => (n j : ℤ))

lemma shifted_int_piece_iff_ok (k N b : ℕ) (L : Finset ((Fin k → ℤ) × ℤ))
    (x : Fin (k+1) → ℤ) :
    x ∈ shiftedIntPiece k N b L ↔
      ∀ p ∈ shiftedLiftConstraints k N b L, 0 ≤ (∑ j, p.1 j * x j) + p.2 := by
  classical
  constructor
  · intro hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hn, hp, hb⟩ := Finset.mem_filter.mp hn
    exact (shifted_nat_lift_constraints_iff_ok k N b L n).2
      ⟨hp, hb, (onb_mem_deg (k+1) N n).1 hn⟩
  · intro hx
    obtain ⟨hp, hlo, hsum⟩ := (shifted_lift_constraints_iff_final k N b L x).1 hx
    have hnonneg (j) : 0 ≤ x j := by
      have := hlo j
      split_ifs at this <;> omega
    let n : Fin (k+1) → ℕ := fun j => (x j).toNat
    have hncast : (fun j => (n j : ℤ)) = x := by
      funext j
      exact Int.toNat_of_nonneg (hnonneg j)
    apply Finset.mem_image.mpr
    refine ⟨n, ?_, hncast⟩
    have hn := (shifted_nat_lift_constraints_iff_ok k N b L n).1 (by
      simpa only [show ∀ j, (n j : ℤ) = x j from congrFun hncast] using hx)
    exact Finset.mem_filter.mpr ⟨(onb_mem_deg (k+1) N n).2 hn.2.2, hn.1, hn.2.1⟩

lemma shifted_piece_sum_cast_ok (k N b : ℕ) (L : Finset ((Fin k → ℤ) × ℤ))
    (f : (Fin (k+1) → ℤ) → ℂ) :
    (∑ x ∈ shiftedIntPiece k N b L, f x) =
      ∑ n ∈ shiftedNatPiece k N b L, f (fun j => (n j : ℤ)) := by
  classical
  apply Finset.sum_image
  intro n hn m hm he
  funext j
  exact_mod_cast (show (n j : ℤ) = (m j : ℤ) from congrFun he j)

lemma shiftedLiftConstraints_card (k N b : ℕ)
    (L : Finset ((Fin k → ℤ) × ℤ)) :
    (shiftedLiftConstraints k N b L).card ≤ L.card + k + 3 := by
  classical
  let I := L.image (fun p => (Fin.snoc (α := fun _ => ℤ) p.1 0, p.2))
  let J : Finset ((Fin (k + 1) → ℤ) × ℤ) :=
    Finset.univ.image fun j : Fin (k + 1) =>
      ((fun s => if s = j then (1 : ℤ) else 0),
        -(if j = Fin.last k then (b : ℤ) else 0))
  let E : Finset ((Fin (k + 1) → ℤ) × ℤ) :=
    {((fun _ => (1 : ℤ)), -(N : ℤ)),
     ((fun _ => (-1 : ℤ)), (N : ℤ))}
  have hI : I.card ≤ L.card := Finset.card_image_le
  have hJ : J.card ≤ k + 1 := by
    exact Finset.card_image_le.trans (by simp)
  have hE : E.card ≤ 2 := Finset.card_le_two
  have h₁ := Finset.card_union_le I (J ∪ E)
  have h₂ := Finset.card_union_le J E
  change (I ∪ (J ∪ E)).card ≤ L.card + k + 3
  omega

lemma shiftedLiftConstraints_coeff_bound (k N b R : ℕ)
    (L : Finset ((Fin k → ℤ) × ℤ))
    (hL : ∀ p ∈ L, ∑ s, |p.1 s| ≤ (R : ℤ)) :
    ∀ p ∈ shiftedLiftConstraints k N b L,
      ∑ s, |p.1 s| ≤ (max R (k + 1) : ℕ) := by
  classical
  have hleft : (R : ℤ) ≤ (max R (k + 1) : ℕ) := by
    exact_mod_cast (le_max_left R (k + 1))
  have hright : ((k + 1 : ℕ) : ℤ) ≤ (max R (k + 1) : ℕ) := by
    exact_mod_cast (le_max_right R (k + 1))
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    change (∑ s, |(Fin.snoc (α := fun _ => ℤ) q.1 0) s|) ≤ _
    rw [Fin.sum_univ_castSucc]
    simpa using (hL q hq).trans hleft
  · rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
      change (∑ s : Fin (k + 1),
        |if s = j then (1 : ℤ) else 0|) ≤ _
      have hsum :
          (∑ s : Fin (k + 1),
            |if s = j then (1 : ℤ) else 0|) = 1 := by
        simp [apply_ite abs]
      rw [hsum]
      exact (show (1 : ℤ) ≤ (k+1 : ℕ) by omega).trans hright
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · simpa using hright
      · simpa using hright

lemma shifted_exp_nat_pow (x : ℝ) (n : ℕ) :
    expTwoPiI x ^ n = expTwoPiI (x * (n : ℝ)) := by
  unfold expTwoPiI
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma shifted_polar_coordinate (z : ℂ) (n : ℕ) :
    z ^ n =
      (((‖z‖ ^ 2) ^ ((n : ℝ) / 2) : ℝ) : ℂ) *
        expTwoPiI (z.arg / (2 * Real.pi) * (n : ℝ)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have he :
      expTwoPiI (z.arg / (2 * Real.pi)) =
        Complex.exp ((z.arg : ℂ) * Complex.I) := by
    unfold expTwoPiI
    congr 1
    push_cast
    field_simp [hpi]
    <;> ring
  have hz : z = (‖z‖ : ℂ) * expTwoPiI (z.arg / (2 * Real.pi)) := by
    rw [he]
    exact (Complex.norm_mul_exp_arg_mul_I z).symm
  have hr : (‖z‖ ^ 2) ^ ((n : ℝ) / 2) = ‖z‖ ^ n := by
    calc
      _ = ‖z‖ ^ ((2 : ℝ) * ((n : ℝ) / 2)) := by
        simpa using
          (Real.rpow_natCast_mul (norm_nonneg z) 2 ((n : ℝ) / 2)).symm
      _ = ‖z‖ ^ (n : ℝ) := by
        congr 1
        ring
      _ = ‖z‖ ^ n := Real.rpow_natCast _ _
  calc
    z ^ n = ((‖z‖ : ℂ) * expTwoPiI (z.arg / (2 * Real.pi))) ^ n :=
      congrArg (fun w : ℂ => w ^ n) hz
    _ = _ := by
      rw [mul_pow, shifted_exp_nat_pow, hr, Complex.ofReal_pow]

lemma shifted_polar_poisson_factorization_ok
    (K N : ℕ) (hN : 1 ≤ N)
    (z : Fin K → ℂ) (hz : ∀ j, z j ≠ 0)
    (hs : ∑ j, ‖z j‖ ^ 2 = 1)
    (n : Fin K → ℕ) (hn : ∑ j, n j = N) :
    (Real.sqrt (Nat.multinomial Finset.univ n : ℝ) : ℂ) *
        (∏ j, z j ^ n j) =
      ((Real.exp ((N : ℝ) / 2) * Real.sqrt (N.factorial : ℝ) /
        (N : ℝ) ^ ((N : ℝ) / 2) : ℝ) : ℂ) *
      (∏ j, (poissonQ ((N : ℝ) * ‖z j‖ ^ 2) (n j) : ℂ)) *
      expTwoPiI (∑ j, (z j).arg / (2 * Real.pi) * (n j : ℝ)) := by
  have hr : ∀ j, 0 < ‖z j‖ ^ 2 := by
    intro j
    exact sq_pos_of_pos (norm_pos_iff.mpr (hz j))
  have hf := shifted_poisson_factorization_ok K N hN
    (fun j => ‖z j‖ ^ 2) hr hs n hn
  have hp :
      (∏ j, z j ^ n j) =
        ((∏ j, (‖z j‖ ^ 2) ^ ((n j : ℝ) / 2) : ℝ) : ℂ) *
          expTwoPiI (∑ j, (z j).arg / (2 * Real.pi) * (n j : ℝ)) := by
    simp_rw [shifted_polar_coordinate]
    rw [Finset.prod_mul_distrib, ← onb_exp_sum]
    simp only [Complex.ofReal_prod]
  rw [hp, ← mul_assoc, ← Complex.ofReal_mul, hf]
  simp only [Complex.ofReal_mul, Complex.ofReal_prod]

lemma shifted_piece_bound_ok (hbox : ThmBox) (k R : ℕ) (a : ℝ) (ha : 1 ≤ a) :
    ∃ C > 0, ∀ α : ℝ, Irrational α →
      (∀ (i : ℕ) (x : ℝ), (GenContFract.of α).partDens.get? i = some x → x ≤ a) →
      ∀ N : ℕ, 1 ≤ N → ∀ b : ℕ,
      ∀ L : Finset ((Fin k → ℤ) × ℤ), L.card ≤ R →
        (∀ p ∈ L, ∑ j, |p.1 j| ≤ (R : ℤ)) →
      ∀ θ : Fin (k+1) → ℝ, ∀ z : Fin (k+1) → ℂ,
      (∀ j, z j ≠ 0) → ∑ j, ‖z j‖ ^ 2 = 1 →
      ‖∑ n ∈ shiftedNatPiece k N b L,
        (Real.sqrt (Nat.multinomial Finset.univ n : ℝ) : ℂ) *
        (∏ j, z j ^ n j) *
        expTwoPiI (α * ∑ j, (n j : ℝ)^2 + ∑ j, θ j * (n j : ℝ))‖ ≤ C := by
  classical
  obtain ⟨C, hC, hc⟩ := shifted_poisson_polytope_bound hbox (k+1) (R+k+3)
    (max R (k+1)) 1 a (by omega) (by omega) (by omega) ha
  refine ⟨C * Real.sqrt 5 ^ k * Real.exp (1/2) *
    ((k+1 : ℕ) : ℝ) ^ ((1 : ℝ)/4), by positivity, ?_⟩
  intro α hα hαa N hN b L hL hL1 θ z hz hs
  let cN := Real.exp ((N : ℝ)/2) * Real.sqrt (N.factorial : ℝ) /
    (N : ℝ) ^ ((N : ℝ)/2)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcn : 0 ≤ cN := by dsimp [cN]; positivity
  let lam := fun j => (N : ℝ) * ‖z j‖ ^ 2
  have hlam (j) : 0 < lam j := mul_pos hNp (sq_pos_of_pos (norm_pos_iff.mpr (hz j)))
  let theta := fun j => θ j + (z j).arg / (2 * Real.pi)
  let F := fun n : Fin (k+1) → ℤ => (∏ j, (poissonQ (lam j) (n j) : ℂ)) *
    expTwoPiI (α * ∑ j, (n j : ℝ)^2 + ∑ j, theta j * (n j : ℝ))
  have he : (∑ n ∈ shiftedNatPiece k N b L,
        (Real.sqrt (Nat.multinomial Finset.univ n : ℝ) : ℂ) *
        (∏ j, z j ^ n j) *
        expTwoPiI (α * ∑ j, (n j : ℝ)^2 + ∑ j, θ j * (n j : ℝ))) =
      (cN : ℂ) * ∑ n ∈ shiftedIntPiece k N b L, F n := by
    rw [shifted_piece_sum_cast_ok, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hdeg := (onb_mem_deg (k+1) N n).1 (Finset.mem_filter.mp hn).1
    rw [shifted_polar_poisson_factorization_ok (k+1) N hN z hz hs n hdeg]
    dsimp [F, cN, lam, theta]
    push_cast
    rw [mul_assoc, mul_assoc, ← onb_exp_add]
    congr 3
    simp only [add_mul, Finset.sum_add_distrib]
    ring
  obtain ⟨q, hq⟩ := shifted_poisson_max_scale (k+1) N (by omega) hN
    (fun j => ‖z j‖^2) (fun j => sq_pos_of_pos (norm_pos_iff.mpr (hz j))) hs
  have hh := hc α hα hαa (fun _ => 1) (by simp) (by simp)
    (shiftedLiftConstraints k N b L)
    ((shiftedLiftConstraints_card k N b L).trans (by omega))
    (shiftedLiftConstraints_coeff_bound k N b R L hL1) (-(N : ℤ))
    (by simp [shiftedLiftConstraints]) (by simp [shiftedLiftConstraints])
    (shiftedIntPiece k N b L) (shifted_int_piece_iff_ok k N b L) theta lam hlam q
  have hbound : ‖∑ n ∈ shiftedIntPiece k N b L, F n‖ ≤
      C * Real.sqrt 5 ^ k * poissonH (lam q) ^ (-(1 : ℝ)/2) := by
    have halg := shifted_product_scale_cancel (k+1) (fun j => poissonH (lam j))
      (fun j => lt_of_lt_of_le (by norm_num) (pq_H (lam j) (hlam j)).1) q
    simpa only [Nat.add_sub_cancel, ← mul_assoc, F, Nat.cast_one, one_mul, halg,
      mul_assoc] using hh
  have hHp : 0 < poissonH (lam q) := lt_of_lt_of_le (by norm_num) (pq_H _ (hlam q)).1
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcn]
  calc
    _ ≤ cN * (C * Real.sqrt 5 ^ k * poissonH (lam q) ^ (-(1 : ℝ)/2)) :=
      mul_le_mul_of_nonneg_left hbound hcn
    _ ≤ (Real.exp (1/2) * (N : ℝ) ^ ((1 : ℝ)/4)) *
        (C * Real.sqrt 5 ^ k * poissonH (lam q) ^ (-(1 : ℝ)/2)) :=
      mul_le_mul_of_nonneg_right (shifted_poisson_constant_bound N hN) (by positivity)
    _ = (C * Real.sqrt 5 ^ k * Real.exp (1/2)) *
        ((N : ℝ) ^ ((1 : ℝ)/4) * poissonH (lam q) ^ (-(1 : ℝ)/2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hq (by positivity)

lemma shifted_affine_phase_ok (k : ℕ) (U : (Fin k → ℕ) → Fin k → ℕ)
    (A : Matrix (Fin k) (Fin k) ℤ) (c : Fin k → ℤ)
    (x : Fin k → ℕ) (D : Fin k → ℝ)
    (hU : ∀ s, (U x s : ℤ) = Matrix.mulVec A (fun t => (x t : ℤ)) s + c s) :
    ∑ s, (U x s : ℝ) * D s =
      (∑ s, (c s : ℝ) * D s) +
      ∑ t, (∑ s, (A s t : ℝ) * D s) * (x t : ℝ) := by
  have he (s) : (U x s : ℝ) = (∑ t, (A s t : ℝ) * (x t : ℝ)) + c s := by
    exact_mod_cast hU s
  simp_rw [he, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro s hs
  ring

lemma shifted_assembly_bound_ok (k R N b : ℕ) (hbN : b ≤ N)
    (α : ℝ) (U : (Fin k → ℕ) → Fin k → ℕ)
    (hU : IsUNmap k R (N-b) U) (l : Fin k → ℕ)
    (z : Fin (k+1) → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hpiece : ∀ L : Finset ((Fin k → ℤ) × ℤ), L.card ≤ R →
      (∀ p ∈ L, ∑ j, |p.1 j| ≤ (R : ℤ)) → ∀ θ : Fin (k+1) → ℝ,
      ‖∑ n ∈ shiftedNatPiece k N b L,
        (Real.sqrt (Nat.multinomial Finset.univ n : ℝ) : ℂ) *
        (∏ j, z j ^ n j) *
        expTwoPiI (α * ∑ j, (n j : ℝ)^2 + ∑ j, θ j * (n j : ℝ))‖ ≤ C) :
    ‖polyEval (k+1) N (shiftedBasisPhi k N b α U l) z‖ ≤
      Real.sqrt (((N+k).choose k : ℝ) / ((N-b+k).choose k : ℝ)) * ((R : ℝ) * C) := by
  classical
  obtain ⟨r, L, A, c, hr, hL, hL1, hdet, hA, hpartition, haff⟩ := hU.2
  let D : Fin k → ℝ := fun s => (l s : ℝ) / (((N-b)/(k-s.val) : ℕ)+1)
  let F : (Fin (k+1) → ℕ) → ℂ := fun n =>
    (Real.sqrt (Nat.multinomial Finset.univ n : ℝ) : ℂ) * (∏ j, z j ^ n j) *
      expTwoPiI (α * ∑ j, (n j : ℝ)^2 +
        ∑ s, (U (fun t => n t.castSucc) s : ℝ) * D s)
  let scale := Real.sqrt (((N+k).choose k : ℝ) / ((N-b+k).choose k : ℝ))
  have heval : polyEval (k+1) N (shiftedBasisPhi k N b α U l) z =
      (scale : ℂ) * ∑ n ∈ degIdx (k+1) N, if b ≤ n (Fin.last k) then F n else 0 := by
    unfold polyEval
    rw [Finset.mul_sum, ← Finset.sum_coe_sort (degIdx (k+1) N)
      (fun n => (scale : ℂ) * if b ≤ n (Fin.last k) then F n else 0)]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [shiftedBasisPhi]
    split_ifs with hb
    · dsimp [F, scale, D]
      simp only [mul_div_assoc]
      ring
    · simp
  have hdecomp : (∑ n ∈ degIdx (k+1) N, if b ≤ n (Fin.last k) then F n else 0) =
      ∑ i : Fin r, ∑ n ∈ shiftedNatPiece k N b (L i), F n := by
    simp only [shiftedNatPiece, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hb : b ≤ n (Fin.last k)
    · have hdeg := (onb_mem_deg (k+1) N n).1 hn
      rw [Fin.sum_univ_castSucc] at hdeg
      have hsimplex : (fun t : Fin k => n t.castSucc) ∈ simplexS k (N-b) :=
        (onb_mem_simplex _ _ _).2 (by omega)
      obtain ⟨i, hi, hu⟩ := (hpartition _).1 hsimplex
      rw [if_pos hb]
      symm
      rw [Finset.sum_eq_single i]
      · simp [hi, hb]
      · intro j hj hji
        have hp : (fun t : Fin k => n t.castSucc) ∉ polyP k (L j) := by
          intro hp
          exact hji (hu j hp)
        simp [hp]
      · simp
    · simp [hb]
  have hinner (i : Fin r) : ‖∑ n ∈ shiftedNatPiece k N b (L i), F n‖ ≤ C := by
    let t : ℝ := ∑ s, (c i s : ℝ) * D s
    let theta : Fin (k+1) → ℝ :=
      Fin.snoc (fun j => ∑ s, (A i s j : ℝ) * D s) 0
    have he : (∑ n ∈ shiftedNatPiece k N b (L i), F n) =
        expTwoPiI t * ∑ n ∈ shiftedNatPiece k N b (L i),
          (Real.sqrt (Nat.multinomial Finset.univ n : ℝ) : ℂ) *
          (∏ j, z j ^ n j) *
          expTwoPiI (α * ∑ j, (n j : ℝ)^2 + ∑ j, theta j * (n j : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hnL := (Finset.mem_filter.mp hn).2.1
      have hphase := shifted_affine_phase_ok k U (A i) (c i)
        (fun j => n j.castSucc) D (haff i _ hnL)
      have htheta : (∑ j, theta j * (n j : ℝ)) =
          ∑ j : Fin k, (∑ s, (A i s j : ℝ) * D s) * (n j.castSucc : ℝ) := by
        rw [Fin.sum_univ_castSucc]
        simp [theta]
      dsimp [F]
      rw [hphase, htheta, show α * (∑ j, (n j : ℝ)^2) +
          ((∑ s, (c i s : ℝ) * D s) +
            ∑ j : Fin k, (∑ s, (A i s j : ℝ) * D s) * (n j.castSucc : ℝ)) =
          t + (α * (∑ j, (n j : ℝ)^2) +
            ∑ j : Fin k, (∑ s, (A i s j : ℝ) * D s) * (n j.castSucc : ℝ)) by dsimp [t]; ring,
        onb_exp_add]
      ring
    rw [he, norm_mul, LocalizedFourierFinal.FourierMassBounds.exp_norm, one_mul]
    exact hpiece (L i) (hL i) (hL1 i) theta
  rw [heval, hdecomp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  calc
    _ ≤ ∑ i : Fin r, ‖∑ n ∈ shiftedNatPiece k N b (L i), F n‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin r, C := Finset.sum_le_sum (fun i _ => hinner i)
    _ = (r : ℝ) * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hr) hC

lemma shifted_crude_bound_ok (k N b : ℕ) (α : ℝ)
    (U : (Fin k → ℕ) → Fin k → ℕ) (l : Fin k → ℕ)
    (z : Fin (k+1) → ℂ) (hz : ∑ j, ‖z j‖ ^ 2 = 1) :
    ‖polyEval (k+1) N (shiftedBasisPhi k N b α U l) z‖ ≤
      Real.sqrt (((N+k).choose k : ℝ) / ((N-b+k).choose k : ℝ)) *
        ∑ n : ↥(degIdx (k+1) N), Real.sqrt (Nat.multinomial Finset.univ n.val : ℝ) := by
  have hz1 (j) : ‖z j‖ ≤ 1 := by
    have hj : ‖z j‖ ^ 2 ≤ ∑ s, ‖z s‖ ^ 2 :=
      Finset.single_le_sum (fun s _ => sq_nonneg ‖z s‖) (Finset.mem_univ j)
    rw [hz] at hj
    nlinarith [norm_nonneg (z j)]
  have hprod (n : Fin (k+1) → ℕ) : ‖∏ j, z j ^ n j‖ ≤ 1 := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _ : Fin (k+1), (1 : ℝ) := by
        apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
        intro j hj
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (hz1 j)
      _ = 1 := by simp
  unfold polyEval
  calc
    _ ≤ ∑ n : ↥(degIdx (k+1) N),
        ‖shiftedBasisPhi k N b α U l n * ∏ j, z j ^ n.val j‖ := norm_sum_le _ _
    _ ≤ ∑ n : ↥(degIdx (k+1) N),
        Real.sqrt (((N+k).choose k : ℝ) / ((N-b+k).choose k : ℝ)) *
          Real.sqrt (Nat.multinomial Finset.univ n.val : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      by_cases hb : b ≤ n.val (Fin.last k)
      · have hcoeff : ‖shiftedBasisPhi k N b α U l n‖ =
            Real.sqrt (((N+k).choose k : ℝ) / ((N-b+k).choose k : ℝ)) *
              Real.sqrt (Nat.multinomial Finset.univ n.val : ℝ) := by
          simp [shiftedBasisPhi, hb, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), LocalizedFourierFinal.FourierMassBounds.exp_norm]
        rw [hcoeff]
        exact mul_le_of_le_one_right (by positivity) (hprod n.val)
      · simp [shiftedBasisPhi, hb]
        positivity
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem prop_shiftedbound (hbox : ThmBox) (hUN : PropUNmap) (k : ℕ) (hk : 1 ≤ k)
    (a : ℝ) (ha : 1 ≤ a) :
    ∃ A > 0, ∃ R : ℕ,
      (∃ U : ℕ → (Fin k → ℕ) → Fin k → ℕ,
          ∀ M : ℕ, 1 ≤ M → lcmUpTo k ∣ M → IsUNmap k R M (U M)) ∧
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
  obtain ⟨R, U₀, hU₀⟩ := hUN k hk
  obtain ⟨C, hC, hc⟩ := shifted_piece_bound_ok hbox k R a ha
  let T : ℝ := ∑ N ∈ Finset.range (lcmUpTo k),
    ∑ n : ↥(degIdx (k+1) N), Real.sqrt (Nat.multinomial Finset.univ n.val : ℝ)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun N _ =>
    Finset.sum_nonneg (fun n _ => Real.sqrt_nonneg _))
  let Q : ℝ := Real.sqrt (((lcmUpTo k : ℝ)+1)^k)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨Q * ((R : ℝ) * C + T + 1), by positivity, R, ⟨U₀, hU₀⟩, ?_⟩
  intro U hU α hα hαa N l hl
  apply shifted_sphere_boundary_ok (k+1) N (by omega)
  intro z hz hs
  have hscale : Real.sqrt (((N+k).choose k : ℝ) /
      ((N-N % lcmUpTo k+k).choose k : ℝ)) ≤ Q :=
    Real.sqrt_le_sqrt (shifted_ratio_bound_checked k N)
  by_cases hM : 1 ≤ N-N % lcmUpTo k
  · have hu := hU (N-N % lcmUpTo k) hM (Nat.dvd_sub_mod N)
    have hbound := shifted_assembly_bound_ok k R N (N % lcmUpTo k)
      (Nat.mod_le N _) α (U (N-N % lcmUpTo k)) hu l z C hC.le
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
      have := Nat.mod_lt N hlcm
      have := Nat.mod_le N (lcmUpTo k)
      omega
    have hsum : (∑ n : ↥(degIdx (k+1) N),
        Real.sqrt (Nat.multinomial Finset.univ n.val : ℝ)) ≤ T :=
      Finset.single_le_sum (f := fun M => ∑ n : ↥(degIdx (k+1) M),
        Real.sqrt (Nat.multinomial Finset.univ n.val : ℝ))
        (fun M _ => Finset.sum_nonneg (fun n _ => Real.sqrt_nonneg _))
        (Finset.mem_range.mpr hNsmall)
    apply (shifted_crude_bound_ok k N (N % lcmUpTo k) α
      (U (N-N % lcmUpTo k)) l z hs).trans
    apply mul_le_mul hscale
    · have hRC : 0 ≤ (R : ℝ) * C := mul_nonneg (Nat.cast_nonneg _) hC.le
      linarith
    · exact Finset.sum_nonneg (fun n _ => Real.sqrt_nonneg _)
    · exact hQ.le


namespace UniformBoundUnit

def cSphere (K : ℕ) : Set (Fin K → ℂ) := {z | ∑ s, ‖z s‖ ^ 2 = 1}

def BddPartQuot (a α : ℝ) : Prop :=
  Irrational α ∧
    ∀ (i : ℕ) (x : ℝ), (GenContFract.of α).partDens.get? i = some x → x ≤ a

def latticePtsZ (k : ℕ) (L : Finset ((Fin k → ℤ) × ℤ)) (lo hi : Fin k → ℤ) :
    Finset (Fin k → ℤ) :=
  (Fintype.piFinset fun j => Finset.Icc (lo j) (hi j)).filter
    fun n => ∀ p ∈ L, 0 ≤ (∑ s, p.1 s * n s) + p.2

def boxVolZ (k : ℕ) (lo hi : Fin k → ℤ) : ℕ :=
  ∏ j, (Finset.Icc (lo j) (hi j)).card

def boxLenZ (k : ℕ) (w : Fin k → ℤ) (lo hi : Fin k → ℤ) : ℕ :=
  max 1 ((Finset.univ.filter fun j => w j ≠ 0).sup fun j =>
    (Finset.Icc (lo j) (hi j)).card)

noncomputable def boxSectZ (k : ℕ) (w : Fin k → ℤ) (lo hi : Fin k → ℤ) : ℝ :=
  (boxVolZ k lo hi : ℝ) / (boxLenZ k w lo hi : ℝ)

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

def PropUNmap (k : ℕ) : Prop :=
  ∃ R : ℕ, ∀ N : ℕ, 1 ≤ N → lcmUpTo k ∣ N →
    ∃ U : (Fin k → ℕ) → Fin k → ℕ, IsUNmap k R N U

theorem thm_onbexplicit_uniformBound (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : 1 ≤ a)
    (hbox : ThmBox) (hUN : PropUNmap k) :
    ∃ (R : ℕ) (A : ℝ), 0 < A ∧
      (∀ N : ℕ, 1 ≤ N → lcmUpTo k ∣ N →
          ∃ U₀ : (Fin k → ℕ) → Fin k → ℕ, IsUNmap k R N U₀) ∧
      ∀ α : ℝ, BddPartQuot a α →
        ∀ U : ℕ → (Fin k → ℕ) → Fin k → ℕ,
          (∀ M : ℕ, 1 ≤ M → lcmUpTo k ∣ M → IsUNmap k R M (U M)) →
          ∀ N : ℕ, 1 ≤ N → lcmUpTo k ∣ N →
            ∀ l ∈ boxB k N, ∀ z ∈ cSphere (k + 1),
              ‖polyEval (k + 1) N (basisPhi k N α (U N) l) z‖ ≤ A := by
  classical
  have hbox' : _root_.ThmBox := by
    intro K r V h a hK hV hh ha
    obtain ⟨C, hC, hc⟩ := hbox K r V h hK hV hh a ha
    refine ⟨C, hC, ?_⟩
    intro α hα hαa c hc1 hc2 lo hi hlo L hL hL1 θ
    exact hc α ⟨hα, hαa⟩ c (fun j => ⟨hc1 j, hc2 j⟩) lo hi L hL hL1 θ
  obtain ⟨R, hR⟩ := hUN
  obtain ⟨C, hC, hc⟩ := shifted_piece_bound_ok hbox' k R a ha
  refine ⟨R, (R : ℝ) * C + 1, by positivity, hR, ?_⟩
  intro α hα U hU N hN hdiv l hl
  have he : shiftedBasisPhi k N 0 α (U N) l = basisPhi k N α (U N) l := by
    have hn : ((N+k).choose k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (show k ≤ N+k by omega)))
    funext n
    simp [shiftedBasisPhi, basisPhi, hn]
  rw [← he]
  apply shifted_sphere_boundary_ok (k+1) N (by omega)
  intro z hz hs
  have hb := shifted_assembly_bound_ok k R N 0 (by omega) α (U N)
    (by simpa using hU N hN hdiv) l z C hC.le
    (fun L hL hL1 θ => hc α hα.1 hα.2 N hN 0 L hL hL1 θ z hz hs)
  have hn : ((N+k).choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (show k ≤ N+k by omega)))
  simp only [Nat.sub_zero, div_self hn, Real.sqrt_one, one_mul] at hb
  exact hb.trans (by linarith)

end UniformBoundUnit


lemma allDegreesProof_basis_of_orth (k N : ℕ)
    (v : Fin ((N+k).choose k) → PolySpaceH (k+1) N)
    (hv : ∀ i j, polyInner (k+1) N (v i) (v j) = if i=j then 1 else 0) :
    ∃ ψ : Module.Basis (Fin ((N+k).choose k)) ℂ (PolySpaceH (k+1) N),
      ∀ i, ψ i = v i := by
  classical
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hi := congrArg (fun w => polyInner (k+1) N w (v i)) hc
    rw [onb_linear] at hi
    have hz : polyInner (k+1) N 0 (v i) = 0 := by simp [polyInner]
    rw [hz] at hi
    simpa [hv, mul_ite] using hi
  have hcard : Fintype.card (Fin ((N+k).choose k)) =
      Module.finrank ℂ (PolySpaceH (k+1) N) := by
    rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, onb_card]
  let : Nonempty (Fin ((N+k).choose k)) :=
    ⟨⟨0, Nat.choose_pos (by omega)⟩⟩
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard,
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) i⟩

lemma allDegreesProof_zero_inner_ok (k : ℕ) :
    polyInner (k+1) 0 (fun _ => 1) (fun _ => 1) = 1 := by
  simp only [polyInner, zero_add, Nat.add_sub_cancel, Nat.choose_self,
    Nat.cast_one, inv_one, one_mul, map_one, mul_one]
  rw [Finset.sum_coe_sort (degIdx (k+1) 0)
    (fun n => (Nat.multinomial Finset.univ n : ℂ)⁻¹)]
  have hm : Nat.multinomial Finset.univ (0 : Fin (k+1) → ℕ) = 1 := by
    simpa using Nat.multinomial_spec Finset.univ (0 : Fin (k+1) → ℕ)
  simp [degIdx, hm]

lemma allDegreesProof_zero_eval (k : ℕ) (z : Fin (k+1) → ℂ) :
    polyEval (k+1) 0 (fun _ => 1) z = 1 := by
  simp only [polyEval, one_mul]
  rw [Finset.sum_coe_sort (degIdx (k+1) 0) (fun n => ∏ s, z s ^ n s)]
  simp [degIdx]

namespace UniformBoundUnit

lemma allDegreesProof_divisible (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : 1 ≤ a)
    (hbox : ThmBox) (hUN : PropUNmap k) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, BddPartQuot a α → ∀ N : ℕ,
      lcmUpTo k ∣ N →
      ∃ ψ : Module.Basis (Fin ((N+k).choose k)) ℂ (PolySpaceH (k+1) N),
        (∀ i j, polyInner (k+1) N (ψ i) (ψ j) = if i=j then 1 else 0) ∧
        ∀ ν, ∀ z ∈ cSphere (k+1), ‖polyEval (k+1) N (ψ ν) z‖ ≤ C := by
  classical
  obtain ⟨R, A, hA, hR, hbound⟩ := thm_onbexplicit_uniformBound k hk a ha hbox hUN
  let U (M : ℕ) : (Fin k → ℕ) → Fin k → ℕ :=
    if h : 1 ≤ M ∧ lcmUpTo k ∣ M then Classical.choose (hR M h.1 h.2)
    else fun _ => 0
  have hU (M : ℕ) (hM : 1 ≤ M) (hd : lcmUpTo k ∣ M) : IsUNmap k R M (U M) := by
    dsimp only [U]
    rw [dif_pos ⟨hM, hd⟩]
    exact Classical.choose_spec (hR M hM hd)
  refine ⟨A+1, by linarith, ?_⟩
  intro α hα N hd
  by_cases hN : N = 0
  · subst N
    let v : Fin ((0+k).choose k) → PolySpaceH (k+1) 0 := fun _ _ => 1
    have hv : ∀ i j, polyInner (k+1) 0 (v i) (v j) = if i=j then 1 else 0 := by
      intro i j
      have he : i=j := by
        apply Fin.ext
        have hi := i.isLt
        have hj := j.isLt
        simp at hi hj
        omega
      rw [if_pos he]
      exact allDegreesProof_zero_inner_ok k
    obtain ⟨ψ, hψ⟩ := allDegreesProof_basis_of_orth k 0 v hv
    refine ⟨ψ, ?_, ?_⟩
    · intro i j
      rw [hψ, hψ]
      exact hv i j
    · intro ν z hz
      rw [hψ]
      change ‖polyEval (k+1) 0 (fun _ => 1) z‖ ≤ A+1
      rw [allDegreesProof_zero_eval, norm_one]
      linarith
  · have hpos : 1 ≤ N := by omega
    have hu := (hU N hpos hd).1
    have hc : Fintype.card ↥(boxB k N) = (N+k).choose k := by
      rw [← onb_card k N]
      exact (Fintype.card_congr
        ((onb_degEquiv_final k N).trans (Set.BijOn.equiv (U N) hu))).symm
    let e : Fin ((N+k).choose k) ≃ ↥(boxB k N) :=
      (Fintype.equivFinOfCardEq hc).symm
    let v : Fin ((N+k).choose k) → PolySpaceH (k+1) N :=
      fun i => basisPhi k N α (U N) (e i).val
    have hv : ∀ i j, polyInner (k+1) N (v i) (v j) = if i=j then 1 else 0 := by
      intro i j
      simpa only [v, Subtype.coe_inj, e.injective.eq_iff] using
        onb_orth_final k N α (U N) hu (e i).val (e j).val (e i).property (e j).property
    obtain ⟨ψ, hψ⟩ := allDegreesProof_basis_of_orth k N v hv
    refine ⟨ψ, ?_, ?_⟩
    · intro i j
      rw [hψ, hψ]
      exact hv i j
    · intro ν z hz
      rw [hψ]
      exact (hbound α hα U hU N hpos hd (e ν).val (e ν).property z hz).trans
        (by linarith)

end UniformBoundUnit

namespace AllDegreesProof

noncomputable def goodEquiv (k N b : ℕ) (hb : b ≤ N) :
    ↥((degIdx (k+1) N).filter (fun n => b ≤ n (Fin.last k))) ≃
      ↥(simplexS k (N-b)) where
  toFun n := ⟨Fin.init n.1, by
    apply (onb_mem_simplex k (N-b) _).2
    have hn := (onb_mem_deg (k+1) N n.1).1 (Finset.mem_filter.mp n.2).1
    have hn' := (Finset.mem_filter.mp n.2).2
    rw [Fin.sum_univ_castSucc] at hn
    change (∑ i : Fin k, n.1 i.castSucc) ≤ N-b
    omega⟩
  invFun j := ⟨Fin.snoc j.1 (N - ∑ i, j.1 i), by
    apply Finset.mem_filter.mpr
    have hj := (onb_mem_simplex k (N-b) j.1).1 j.2
    constructor
    · apply (onb_mem_deg (k+1) N _).2
      rw [Fin.sum_snoc]
      exact Nat.add_sub_of_le (by omega)
    · simp only [Fin.snoc_last]
      omega⟩
  left_inv n := by
    apply Subtype.ext
    change Fin.snoc (Fin.init n.1) (N - ∑ i, (Fin.init n.1) i) = n.1
    have hn := (onb_mem_deg (k+1) N n.1).1 (Finset.mem_filter.mp n.2).1
    rw [Fin.sum_univ_castSucc] at hn
    have he : N - ∑ i, (Fin.init n.1) i = n.1 (Fin.last k) := by
      simpa only [Fin.init_def] using
        (show N - ∑ i : Fin k, n.1 i.castSucc = n.1 (Fin.last k) by omega)
    rw [he]
    exact Fin.snoc_init_self _
  right_inv j := by
    apply Subtype.ext
    funext i
    change (Fin.snoc (α := fun _ : Fin (k+1) => ℕ)
      j.1 (N - ∑ i, j.1 i)) i.castSucc = j.1 i
    simp

lemma shifted_orth (k N b : ℕ) (hb : b ≤ N) (α : ℝ)
    (U : (Fin k → ℕ) → Fin k → ℕ)
    (hU : Set.BijOn U (simplexS k (N-b) : Set _) (boxB k (N-b) : Set _))
    (l l' : Fin k → ℕ) (hl : l ∈ boxB k (N-b)) (hl' : l' ∈ boxB k (N-b)) :
    polyInner (k+1) N (shiftedBasisPhi k N b α U l)
      (shiftedBasisPhi k N b α U l') = if l=l' then 1 else 0 := by
  classical
  let S : Finset (Fin (k+1) → ℕ) := (degIdx (k+1) N).filter (fun n => b ≤ n (Fin.last k))
  let e : ↥S ≃ ↥(boxB k (N-b)) :=
    (goodEquiv k N b hb).trans (Set.BijOn.equiv U hU)
  let f : (Fin k → ℕ) → ℂ := fun t => expTwoPiI (∑ s : Fin k,
    (t s : ℝ) * ((l s : ℝ)-l' s) / (((N-b)/(k-s.val) : ℕ)+1))
  have he (n : ↥S) : (e n).val = U (fun t => n.val t.castSucc) := rfl
  have hc : (boxB k (N-b)).card = (N-b+k).choose k := by
    rw [← Fintype.card_coe, ← onb_card k (N-b)]
    exact (Fintype.card_congr (Set.BijOn.equiv U hU)).symm.trans
      (Fintype.card_congr (onb_degEquiv_final k (N-b))).symm
  have hs : (∑ n : ↥(degIdx (k+1) N),
      if b ≤ n.val (Fin.last k) then f (U (fun t => n.val t.castSucc)) else 0) =
      if l=l' then ((N-b+k).choose k : ℂ) else 0 := by
    rw [Finset.sum_coe_sort (degIdx (k+1) N)
      (fun n => if b ≤ n (Fin.last k) then f (U (fun t => n t.castSucc)) else 0),
      ← Finset.sum_filter]
    change (∑ n ∈ S, f (U (fun t => n t.castSucc))) = _
    rw [← Finset.sum_coe_sort S]
    change (∑ n : ↥S, f (e n).val) = _
    rw [e.sum_comp (fun t : ↥(boxB k (N-b)) => f t.val), Finset.sum_coe_sort]
    dsimp only [f]
    rw [onb_box_final k (N-b) l l' hl hl', hc]
  let q : ℝ := ((N+k).choose k : ℝ) / ((N-b+k).choose k : ℝ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq2 : (Real.sqrt q : ℂ) * (Real.sqrt q : ℂ) = (q : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hq
  have hterm (n : ↥(degIdx (k+1) N)) :
      ((Nat.multinomial Finset.univ n.val : ℂ))⁻¹ *
        shiftedBasisPhi k N b α U l n *
        (starRingEnd ℂ) (shiftedBasisPhi k N b α U l' n) =
      (q : ℂ) * (if b ≤ n.val (Fin.last k) then f (U (fun t => n.val t.castSucc)) else 0) := by
    by_cases hn : b ≤ n.val (Fin.last k)
    · simp only [shiftedBasisPhi, if_pos hn, map_mul, Complex.conj_ofReal]
      change _ = (q : ℂ) * f (U (fun t => n.val t.castSucc))
      calc
        _ = ((Real.sqrt q : ℂ) * (Real.sqrt q : ℂ)) *
          (((Nat.multinomial Finset.univ n.val : ℂ))⁻¹ *
            ((Real.sqrt (Nat.multinomial Finset.univ n.val) : ℂ) *
              expTwoPiI (α * ∑ s, (n.val s : ℝ)^2 +
                ∑ s : Fin k, (U (fun t => n.val t.castSucc) s : ℝ) * (l s : ℝ) /
                  (((N-b)/(k-s.val) : ℕ)+1))) *
            (starRingEnd ℂ) ((Real.sqrt (Nat.multinomial Finset.univ n.val) : ℂ) *
              expTwoPiI (α * ∑ s, (n.val s : ℝ)^2 +
                ∑ s : Fin k, (U (fun t => n.val t.castSucc) s : ℝ) * (l' s : ℝ) /
                  (((N-b)/(k-s.val) : ℕ)+1)))) := by
            simp only [map_mul, Complex.conj_ofReal]
            dsimp only [q]
            ring
        _ = _ := by
          rw [hq2, onb_coeff_ok _ (Nat.multinomial_pos _ _)]
          congr 2
          congr 1
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro s hs
          ring
    · simp [shiftedBasisPhi, hn]
  unfold polyInner
  simp only [show N+(k+1)-1=N+k by omega, Nat.add_sub_cancel]
  simp_rw [hterm]
  rw [← Finset.mul_sum, hs]
  have hd : ((N+k).choose k : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (show k ≤ N+k by omega)))
  have hd' : ((N-b+k).choose k : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (show k ≤ N-b+k by omega)))
  split_ifs <;> simp [q, hd, hd', mul_assoc]

lemma multinomial_face (k N i : ℕ) (n : Fin (k+1) → ℕ)
    (hn : ∑ j, n j = N) (hi : n (Fin.last k) = i) :
    Nat.multinomial Finset.univ n = N.choose i * Nat.multinomial Finset.univ (Fin.init n) := by
  have hs : ∑ j : Fin k, (Fin.init n) j = N-i := by
    rw [Fin.sum_univ_castSucc, hi] at hn
    simpa only [Fin.init_def] using (show (∑ j : Fin k, n j.castSucc) = N-i by omega)
  have hiN : i ≤ N := by
    rw [Fin.sum_univ_castSucc, hi] at hn
    omega
  have hbig := Nat.multinomial_spec Finset.univ n
  rw [Fin.prod_univ_castSucc, hn, hi] at hbig
  have hsmall := Nat.multinomial_spec Finset.univ (Fin.init n)
  rw [hs] at hsmall
  have hc := Nat.choose_mul_factorial_mul_factorial hiN
  apply Nat.eq_of_mul_eq_mul_left (n := (∏ j : Fin k, (n j.castSucc).factorial) * i.factorial)
    (mul_pos (Finset.prod_pos (fun j _ => Nat.factorial_pos _)) (Nat.factorial_pos i))
  calc
    _ = N.factorial := hbig
    _ = N.choose i * i.factorial * ((∏ j : Fin k, (n j.castSucc).factorial) *
        Nat.multinomial Finset.univ (Fin.init n)) := by
      rw [show (∏ j : Fin k, (n j.castSucc).factorial) *
        Nat.multinomial Finset.univ (Fin.init n) = (N-i).factorial from hsmall]
      exact hc.symm
    _ = _ := by ring

lemma face_count_mul (k N b : ℕ) (hk : 1 ≤ k) :
    (N+k) * (∑ i ∈ Finset.range b, (N-i+k-1).choose (k-1)) ≤
      (b*k) * (N+k).choose k := by
  have hs : (∑ i ∈ Finset.range b, (N-i+k-1).choose (k-1)) ≤
      b * (N+k-1).choose (k-1) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range b, (N+k-1).choose (k-1) :=
        Finset.sum_le_sum (fun i _ => Nat.choose_le_choose _ (by omega))
      _ = _ := by simp
  have hr : (N+k) * (N+k-1).choose (k-1) = (N+k).choose k * k := by
    have hn : N+k-1+1 = N+k := by omega
    have hk' : k-1+1 = k := by omega
    simpa only [hn, hk'] using Nat.add_one_mul_choose_eq (N+k-1) (k-1)
  calc
    _ ≤ (N+k) * (b * (N+k-1).choose (k-1)) := Nat.mul_le_mul_left _ hs
    _ = b * ((N+k) * (N+k-1).choose (k-1)) := by ring
    _ = _ := by rw [hr]; ring

lemma face_count_half (k N b : ℕ) (hk : 1 ≤ k) (hN : 2*k*b ≤ N) :
    2 * (∑ i ∈ Finset.range b, (N-i+k-1).choose (k-1)) ≤ (N+k).choose k := by
  have hm := face_count_mul k N b hk
  have hp : 0 < N+k := by omega
  have ht : 2*(b*k) ≤ N+k := by nlinarith
  have ht' := Nat.mul_le_mul_right ((N+k).choose k) ht
  nlinarith

lemma binomial_bound (N i : ℕ) (hi : i ≤ N) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x+y=1) :
    x^i * y^(N-i) * (N.choose i : ℝ) ≤ 1 := by
  have h := Finset.single_le_sum (s := Finset.range (N+1))
    (f := fun j => x^j * y^(N-j) * (N.choose j : ℝ))
    (fun j _ => by positivity) (Finset.mem_range.mpr (by omega : i<N+1))
  rw [← add_pow, hxy, one_pow] at h
  exact h

lemma shifted_uniform (k : ℕ) (a : ℝ) (ha : 1 ≤ a)
    (hbox : UniformBoundUnit.ThmBox) (hUN : UniformBoundUnit.PropUNmap k) :
    ∃ (R : ℕ) (U : ℕ → (Fin k → ℕ) → Fin k → ℕ) (A : ℝ), 0 < A ∧
      (∀ M : ℕ, 1 ≤ M → lcmUpTo k ∣ M → IsUNmap k R M (U M)) ∧
      ∀ α : ℝ, UniformBoundUnit.BddPartQuot a α →
      ∀ N : ℕ, 1 ≤ N-N % lcmUpTo k → ∀ l : Fin k → ℕ,
      ∀ z ∈ UniformBoundUnit.cSphere (k+1),
        ‖polyEval (k+1) N (shiftedBasisPhi k N (N % lcmUpTo k) α
          (U (N-N % lcmUpTo k)) l) z‖ ≤ A := by
  classical
  have hbox' : _root_.ThmBox := by
    intro K r V h a hK hV hh ha
    obtain ⟨C, hC, hc⟩ := hbox K r V h hK hV hh a ha
    refine ⟨C, hC, ?_⟩
    intro α hα hαa c hc1 hc2 lo hi hlo L hL hL1 θ
    exact hc α ⟨hα, hαa⟩ c (fun j => ⟨hc1 j, hc2 j⟩) lo hi L hL hL1 θ
  obtain ⟨R, hR⟩ := hUN
  let U (M : ℕ) : (Fin k → ℕ) → Fin k → ℕ :=
    if h : 1 ≤ M ∧ lcmUpTo k ∣ M then Classical.choose (hR M h.1 h.2)
    else fun _ => 0
  have hU (M : ℕ) (hM : 1 ≤ M) (hd : lcmUpTo k ∣ M) :
      IsUNmap k R M (U M) := by
    dsimp only [U]
    rw [dif_pos ⟨hM, hd⟩]
    exact Classical.choose_spec (hR M hM hd)
  obtain ⟨C, hC, hc⟩ := shifted_piece_bound_ok hbox' k R a ha
  let Q : ℝ := Real.sqrt (((lcmUpTo k : ℝ)+1)^k)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨R, U, Q*((R : ℝ)*C+1), by positivity, hU, ?_⟩
  intro α hα N hN l
  apply shifted_sphere_boundary_ok (k+1) N (by omega)
  intro z hz hs
  have hscale : Real.sqrt (((N+k).choose k : ℝ) /
      ((N-N % lcmUpTo k+k).choose k : ℝ)) ≤ Q :=
    Real.sqrt_le_sqrt (shifted_ratio_bound_checked k N)
  have hu := hU (N-N % lcmUpTo k) hN (Nat.dvd_sub_mod N)
  have hb := shifted_assembly_bound_ok k R N (N % lcmUpTo k)
    (Nat.mod_le N _) α (U (N-N % lcmUpTo k)) hu l z C hC.le
    (fun L hL hL1 θ => hc α hα.1 hα.2 N (by omega) (N % lcmUpTo k)
      L hL hL1 θ z hz hs)
  exact hb.trans (mul_le_mul hscale (by linarith)
    (mul_nonneg (Nat.cast_nonneg R) hC.le) hQ.le)

noncomputable def faceEquiv (k N i : ℕ) (hi : i ≤ N) :
    ↥((degIdx (k+1) N).filter (fun n => n (Fin.last k) = i)) ≃ ↥(degIdx k (N-i)) where
  toFun n := ⟨Fin.init n.1, by
    apply (onb_mem_deg _ _ _).2
    have hn := (onb_mem_deg (k+1) N n.1).1 (Finset.mem_filter.mp n.2).1
    have hn' := (Finset.mem_filter.mp n.2).2
    rw [Fin.sum_univ_castSucc, hn'] at hn
    change (∑ j : Fin k, n.1 j.castSucc) = N-i
    omega⟩
  invFun n := ⟨Fin.snoc n.1 i, by
    apply Finset.mem_filter.mpr
    constructor
    · apply (onb_mem_deg _ _ _).2
      rw [Fin.sum_snoc, (onb_mem_deg _ _ _).1 n.2]
      omega
    · simp⟩
  left_inv n := by
    apply Subtype.ext
    change Fin.snoc (Fin.init n.1) i = n.1
    simpa only [(Finset.mem_filter.mp n.2).2] using Fin.snoc_init_self n.1
  right_inv n := by
    apply Subtype.ext
    funext j
    simp [Fin.init_def]

noncomputable def faceInc (k N i : ℕ) (hi : i ≤ N)
    (n : ↥(degIdx k (N-i))) : ↥(degIdx (k+1) N) :=
  ⟨((faceEquiv k N i hi).symm n).1, (Finset.mem_filter.mp ((faceEquiv k N i hi).symm n).2).1⟩

lemma face_sum (k N i : ℕ) (hi : i ≤ N)
    (f : ↥(degIdx (k+1) N) → ℂ)
    (hf : ∀ n, n.val (Fin.last k) ≠ i → f n = 0) :
    ∑ n, f n = ∑ n, f (faceInc k N i hi n) := by
  classical
  let S := (degIdx (k+1) N).filter (fun n => n (Fin.last k) = i)
  have h : (∑ n : ↥(degIdx (k+1) N), f n) =
      ∑ n : ↥S, f ⟨n.val, (Finset.mem_filter.mp n.property).1⟩ := by
    apply Finset.sum_bij_ne_zero (fun n _ hn =>
      (⟨n.val, Finset.mem_filter.mpr ⟨n.property, by
        by_contra hi'
        exact hn (hf n hi')⟩⟩ : ↥S))
    · intros; exact Finset.mem_univ _
    · intros a _ _ b _ _ hab
      exact Subtype.ext (congrArg (fun n : ↥S => n.val) hab)
    · intro b _ hb
      exact ⟨⟨b.val, (Finset.mem_filter.mp b.property).1⟩,
        Finset.mem_univ _, hb, rfl⟩
    · intros; rfl
  rw [h]
  exact ((faceEquiv k N i hi).symm.sum_comp
    (fun n : ↥S => f ⟨n.val, (Finset.mem_filter.mp n.property).1⟩)).symm

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

lemma faceLift_inc (k N i : ℕ) (hi : i ≤ N) (c : ℂ)
    (v : PolySpaceH k (N-i)) (n : ↥(degIdx k (N-i))) :
    faceLift k N i c v (faceInc k N i hi n) = c * v n := by
  simp only [faceLift, faceInc, faceEquiv, Equiv.coe_fn_symm_mk, Fin.snoc_last, ↓reduceDIte]
  congr 2
  apply Subtype.ext
  funext j
  simp [Fin.init_def]

lemma faceLift_eval (k N i : ℕ) (hi : i ≤ N) (c : ℂ)
    (v : PolySpaceH k (N-i)) (z : Fin (k+1) → ℂ) :
    polyEval (k+1) N (faceLift k N i c v) z =
      c * z (Fin.last k)^i * polyEval k (N-i) v (Fin.init z) := by
  unfold polyEval
  rw [face_sum k N i hi _ (by
    intro n hn
    simp [faceLift, hn])]
  simp_rw [faceLift_inc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  change c * v n * (∏ j, z j ^ (Fin.snoc n.val i) j) = _
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.init_def]
  ring

lemma faceLift_inner (k N i : ℕ) (hi : i ≤ N) (c d : ℂ)
    (v w : PolySpaceH k (N-i)) :
    polyInner (k+1) N (faceLift k N i c v) (faceLift k N i d w) =
      ((N+k).choose k : ℂ)⁻¹ * (N.choose i : ℂ)⁻¹ * c * (starRingEnd ℂ) d *
        ∑ n : ↥(degIdx k (N-i)),
          (Nat.multinomial Finset.univ n.val : ℂ)⁻¹ * v n * (starRingEnd ℂ) (w n) := by
  unfold polyInner
  simp only [show N+(k+1)-1=N+k by omega, Nat.add_sub_cancel]
  rw [face_sum k N i hi _ (by
    intro n hn
    simp [faceLift, hn])]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [faceLift_inc, faceLift_inc, map_mul]
  have hm := multinomial_face k N i (faceInc k N i hi n).val
    ((onb_mem_deg _ _ _).1 (faceInc k N i hi n).property) (by simp [faceInc, faceEquiv])
  have he : Fin.init (faceInc k N i hi n).val = n.val := by
    funext j
    simp [faceInc, faceEquiv, Fin.init_def]
  rw [he] at hm
  rw [hm, Nat.cast_mul, mul_inv_rev]
  ring

lemma faceLift_cross (k N i j : ℕ) (hij : i ≠ j) (c d : ℂ)
    (v : PolySpaceH k (N-i)) (w : PolySpaceH k (N-j)) :
    polyInner (k+1) N (faceLift k N i c v) (faceLift k N j d w) = 0 := by
  unfold polyInner
  have hterm (n : ↥(degIdx (k+1) N)) :
      (Nat.multinomial Finset.univ n.val : ℂ)⁻¹ * faceLift k N i c v n *
        (starRingEnd ℂ) (faceLift k N j d w n) = 0 := by
    by_cases h : n.val (Fin.last k) = i
    · have hj : n.val (Fin.last k) ≠ j := by omega
      simp [faceLift, hj]
    · simp [faceLift, h]
  simp only [hterm, Finset.sum_const_zero, mul_zero]

noncomputable def faceScale (k N i : ℕ) : ℝ :=
  Real.sqrt (((N+k).choose k : ℝ) * (N.choose i : ℝ) /
    ((N-i+k-1).choose (k-1) : ℝ))

lemma face_norm_inner (k N i : ℕ) (hi : i ≤ N)
    (v w : PolySpaceH k (N-i)) :
    polyInner (k+1) N (faceLift k N i (faceScale k N i) v)
      (faceLift k N i (faceScale k N i) w) = polyInner k (N-i) v w := by
  rw [faceLift_inner k N i hi, Complex.conj_ofReal]
  unfold polyInner
  congr 1
  have hD : ((N+k).choose k : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show k ≤ N+k by omega)).ne'
  have hB : (N.choose i : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi).ne'
  have hE : ((N-i+k-1).choose (k-1) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show k-1 ≤ N-i+k-1 by omega)).ne'
  have hs : (faceScale k N i : ℂ) * (faceScale k N i : ℂ) =
      ((N+k).choose k : ℂ) * (N.choose i : ℂ) / ((N-i+k-1).choose (k-1) : ℂ) := by
    unfold faceScale
    have hnonneg : (0 : ℝ) ≤ ((N+k).choose k : ℝ) * (N.choose i : ℝ) /
        ((N-i+k-1).choose (k-1) : ℝ) := by positivity
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast] using
      congrArg Complex.ofReal (Real.mul_self_sqrt hnonneg)
  calc
    _ = ((N+k).choose k : ℂ)⁻¹ * (N.choose i : ℂ)⁻¹ *
      ((faceScale k N i : ℂ) * (faceScale k N i : ℂ)) := by ring
    _ = _ := by rw [hs]; field_simp

lemma face_shift_cross (k N i b : ℕ) (hib : i < b) (c : ℂ)
    (v : PolySpaceH k (N-i)) (α : ℝ)
    (U : (Fin k → ℕ) → Fin k → ℕ) (l : Fin k → ℕ) :
    polyInner (k+1) N (faceLift k N i c v) (shiftedBasisPhi k N b α U l) = 0 := by
  unfold polyInner
  have hterm (n : ↥(degIdx (k+1) N)) :
      (Nat.multinomial Finset.univ n.val : ℂ)⁻¹ * faceLift k N i c v n *
        (starRingEnd ℂ) (shiftedBasisPhi k N b α U l n) = 0 := by
    by_cases h : n.val (Fin.last k) = i
    · have hj : ¬ b ≤ n.val (Fin.last k) := by omega
      simp [shiftedBasisPhi, hj]
    · simp [faceLift, h]
  simp only [hterm, Finset.sum_const_zero, mul_zero]

end AllDegreesProof

lemma allDegreesProof_small_ok (k T : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, N < T →
      ∃ ψ : Module.Basis (Fin ((N+k).choose k)) ℂ (PolySpaceH (k+1) N),
        (∀ i j, polyInner (k+1) N (ψ i) (ψ j) = if i=j then 1 else 0) ∧
        ∀ i z, z ∈ UniformBoundUnit.cSphere (k+1) →
          ‖polyEval (k+1) N (ψ i) z‖ ≤ C := by
  classical
  let B (N : ℕ) : ℝ := ∑ n : ↥(degIdx (k+1) N),
    Real.sqrt ((N+k).choose k : ℝ) * Real.sqrt (Nat.multinomial Finset.univ n.val : ℝ)
  have hB (N) : 0 ≤ B N := Finset.sum_nonneg (fun _ _ => by positivity)
  refine ⟨(∑ N ∈ Finset.range T, B N)+1, by positivity, ?_⟩
  intro N hN
  let e := (Fintype.equivFinOfCardEq (onb_card k N)).symm
  let v : Fin ((N+k).choose k) → PolySpaceH (k+1) N := fun i n =>
    if n = e i then (Real.sqrt ((N+k).choose k : ℝ) : ℂ) *
      (Real.sqrt (Nat.multinomial Finset.univ n.val : ℝ) : ℂ) else 0
  have hd : ((N+k).choose k : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show k ≤ N+k by omega)).ne'
  have hd2 : (Real.sqrt ((N+k).choose k : ℝ) : ℂ)^2 = ((N+k).choose k : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg ((N+k).choose k))
  have hm2 (n : ↥(degIdx (k+1) N)) :
      (Real.sqrt (Nat.multinomial Finset.univ n.val : ℝ) : ℂ)^2 =
      (Nat.multinomial Finset.univ n.val : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg _)
  have hv : ∀ i j, polyInner (k+1) N (v i) (v j) = if i=j then 1 else 0 := by
    intro i j
    have hm : (Nat.multinomial Finset.univ (e i).val : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.multinomial_pos Finset.univ (e i).val).ne'
    unfold polyInner
    simp only [show N+(k+1)-1=N+k by omega, Nat.add_sub_cancel]
    simp only [v, mul_ite, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hij : i=j
    · subst j
      simp only [ite_true, map_mul, Complex.conj_ofReal]
      calc
        _ = ((N+k).choose k : ℂ)⁻¹ *
          ((Nat.multinomial Finset.univ (e i).val : ℂ)⁻¹ *
            ((Real.sqrt ((N+k).choose k : ℝ) : ℂ)^2 *
             (Real.sqrt (Nat.multinomial Finset.univ (e i).val : ℝ) : ℂ)^2)) := by ring
        _ = 1 := by rw [hd2, hm2]; field_simp
    · simp [e.injective.ne hij, hij]
  obtain ⟨ψ, hψ⟩ := allDegreesProof_basis_of_orth k N v hv
  refine ⟨ψ, by simpa only [hψ] using hv, ?_⟩
  intro i z hz
  rw [hψ]
  have hz1 (j) : ‖z j‖ ≤ 1 := by
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => ‖z j‖^2) (fun j _ => sq_nonneg ‖z j‖) (Finset.mem_univ j)
    change ∑ j, ‖z j‖^2 = 1 at hz
    rw [hz] at hh
    nlinarith [norm_nonneg (z j)]
  have hp : ‖∏ j, z j ^ (e i).val j‖ ≤ 1 := by
    rw [norm_prod]
    apply (Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ =>
      show ‖z j ^ (e i).val j‖ ≤ (1 : ℝ) from by
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hz1 j))).trans
    simp
  have heval : polyEval (k+1) N (v i) z =
      (Real.sqrt ((N+k).choose k : ℝ) : ℂ) *
      (Real.sqrt (Nat.multinomial Finset.univ (e i).val : ℝ) : ℂ) *
      ∏ j, z j ^ (e i).val j := by simp [polyEval, v, ite_mul]
  rw [heval, norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hn : Real.sqrt ((N+k).choose k : ℝ) *
      Real.sqrt (Nat.multinomial Finset.univ (e i).val : ℝ) ≤ B N :=
    Finset.single_le_sum (f := fun n : ↥(degIdx (k+1) N) =>
      Real.sqrt ((N+k).choose k : ℝ) * Real.sqrt (Nat.multinomial Finset.univ n.val : ℝ))
      (fun _ _ => by positivity) (Finset.mem_univ (e i))
  have hnt : B N ≤ ∑ M ∈ Finset.range T, B M :=
    Finset.single_le_sum (fun M _ => hB M) (Finset.mem_range.mpr hN)
  exact (mul_le_of_le_one_right (by positivity) hp).trans (by linarith)

lemma allDegreesProof_right_linear {ι : Type*} [Fintype ι] (K N : ℕ)
    (v : ι → PolySpaceH K N) (c : ι → ℂ) (d : PolySpaceH K N) :
    polyInner K N d (∑ l, c l • v l) =
      ∑ l, (starRingEnd ℂ) (c l) * polyInner K N d (v l) := by
  simp only [polyInner, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro n hn
  ring

lemma allDegreesProof_eval_linear {ι : Type*} [Fintype ι] (K N : ℕ)
    (v : ι → PolySpaceH K N) (c : ι → ℂ) (z : Fin K → ℂ) :
    polyEval K N (∑ l, c l • v l) z =
      ∑ l, c l * polyEval K N (v l) z := by
  simp only [polyEval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro n hn
  ring

lemma allDegreesProof_absorption_ok (k N : ℕ)
    (φ : Fin ((N+k).choose k) → PolySpaceH (k+1) N)
    (hφ : ∀ i j, polyInner (k+1) N (φ i) (φ j) = if i=j then 1 else 0)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (d : ℕ) (hd : 1 ≤ d) (hdD : 2*d ≤ (N+k).choose k)
    (hbigB : ∀ j : Fin ((N+k).choose k), j.val < d →
      ∀ z ∈ UniformBoundUnit.cSphere (k+1),
        ‖polyEval (k+1) N (φ j) z‖ ≤ B)
    (hbigA : ∀ j : Fin ((N+k).choose k), d ≤ j.val →
      ∀ z ∈ UniformBoundUnit.cSphere (k+1),
        ‖polyEval (k+1) N (φ j) z‖ ≤ A) :
    ∃ ψ : Module.Basis (Fin ((N+k).choose k)) ℂ (PolySpaceH (k+1) N),
      (∀ i j, polyInner (k+1) N (ψ i) (ψ j) = if i=j then 1 else 0) ∧
      ∀ s, ∀ z ∈ UniformBoundUnit.cSphere (k+1),
        ‖polyEval (k+1) N (ψ s) z‖ ≤
          10*A + 10*B*Real.sqrt ((d : ℝ) / ((N+k).choose k : ℝ)) := by
  classical
  let D := (N+k).choose k
  have hD1 : 1 ≤ D := by dsimp [D]; omega
  let Q := AbsorptionProof.haarQ D hD1
  let v : Fin D → PolySpaceH (k+1) N :=
    fun s => ∑ j, (Q s j : ℂ) • φ j
  have hv : ∀ s t, polyInner (k+1) N (v s) (v t) =
      if s=t then 1 else 0 := by
    intro s t
    change polyInner (k+1) N (∑ j, (Q s j : ℂ) • φ j)
      (∑ j, (Q t j : ℂ) • φ j) = _
    rw [onb_linear]
    simp_rw [allDegreesProof_right_linear, hφ]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Complex.conj_ofReal]
    have hst := congrArg
      (fun M : Matrix (Fin D) (Fin D) ℝ => M s t)
      (AbsorptionProof.absorptionQ_orthogonal D hD1)
    change (Q * Qᵀ) s t = (1 : Matrix (Fin D) (Fin D) ℝ) s t at hst
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hst
    calc
      _ = ((∑ j, Q s j * Q t j : ℝ) : ℂ) := by simp [mul_comm]
      _ = _ := by rw [hst]; split_ifs <;> simp
  obtain ⟨ψ, hψ⟩ := allDegreesProof_basis_of_orth k N v hv
  refine ⟨ψ, ?_, ?_⟩
  · intro i j
    rw [hψ, hψ]
    exact hv i j
  · intro s z hz
    rw [hψ]
    change ‖polyEval (k+1) N (∑ j, (Q s j : ℂ) • φ j) z‖ ≤ _
    rw [allDegreesProof_eval_linear]
    change ‖∑ j, (AbsorptionProof.haarQ D hD1 s j : ℂ) *
      polyEval (k+1) N (φ j) z‖ ≤ _
    have hupper : D < 2 ^ (Nat.log 2 D + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) D
    rw [pow_succ] at hupper
    have hdsmall : d ≤ 2 ^ Nat.log 2 D := by
      change 2*d ≤ D at hdD
      omega
    obtain ⟨r, rfl⟩ := (AbsorptionProof.absorptionEquiv D hD1).surjective s
    rw [← (AbsorptionProof.absorptionEquiv D hD1).sum_comp,
      Fintype.sum_sum_type]
    cases r with
    | inl r =>
        simp only [AbsorptionProof.absorptionQ_apply,
          Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.zero_apply, Complex.ofReal_zero, zero_mul,
          Finset.sum_const_zero, add_zero]
        calc
          _ ≤ 3*A + 5*B*Real.sqrt d*(Real.sqrt 2 ^ Nat.log 2 D)⁻¹ := by
            apply AbsorptionProof.absorption_weighted _ _ _ hd hdsmall A B hA hB
            · intro j hj
              exact hbigB _
                (by simpa only [AbsorptionProof.absorptionEquiv_left] using hj) z hz
            · intro j hj
              exact hbigA _
                (by simpa only [AbsorptionProof.absorptionEquiv_left] using hj) z hz
          _ ≤ _ := AbsorptionProof.absorption_numeric_ok _ D d (by omega)
            (by exact_mod_cast (show D ≤ 2 * 2 ^ Nat.log 2 D by omega))
            A B hA hB
    | inr r =>
        simp only [AbsorptionProof.absorptionQ_apply,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
          Matrix.zero_apply, Complex.ofReal_zero, zero_mul,
          Finset.sum_const_zero, zero_add]
        simp only [Matrix.one_apply, apply_ite Complex.ofReal,
          Complex.ofReal_one, Complex.ofReal_zero, ite_mul, one_mul,
          zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        have hh := hbigA (AbsorptionProof.absorptionEquiv D hD1 (Sum.inr r))
          (by
            rw [AbsorptionProof.absorptionEquiv_right]
            change d ≤ 2 ^ Nat.log 2 D + r.val
            omega) z hz
        have hp : 0 ≤ 10*B*Real.sqrt ((d : ℝ) / (D : ℝ)) := by positivity
        change ‖polyEval (k+1) N
          (φ (AbsorptionProof.absorptionEquiv D hD1 (Sum.inr r))) z‖ ≤ _
        linarith

lemma allDegreesProof_hom_bound (K m : ℕ) (hK : 1 ≤ K) (v : PolySpaceH K m) (C : ℝ)
    (hv : ∀ z ∈ UniformBoundUnit.cSphere K, ‖polyEval K m v z‖ ≤ C) :
    ∀ w, ‖polyEval K m v w‖ ≤ C * (Real.sqrt (∑ j, ‖w j‖ ^ 2)) ^ m := by
  apply shifted_extend_nonzero
  · unfold polyEval; fun_prop
  · fun_prop
  intro w hw
  let r := Real.sqrt (∑ j, ‖w j‖ ^ 2)
  have hs : 0 < ∑ j, ‖w j‖ ^ 2 := by
    let q : Fin K := ⟨0, by omega⟩
    exact (sq_pos_of_pos (norm_pos_iff.mpr (hw q))).trans_le
      (Finset.single_le_sum (fun j _ => sq_nonneg ‖w j‖) (Finset.mem_univ q))
  have hr : 0 < r := Real.sqrt_pos.mpr hs
  have hr2 : r ^ 2 = ∑ j, ‖w j‖ ^ 2 := Real.sq_sqrt hs.le
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let z : Fin K → ℂ := fun j => (r : ℂ)⁻¹ * w j
  have hznorm (j) : ‖z j‖ = r⁻¹ * ‖w j‖ := by
    simp [z, norm_mul, norm_inv, Complex.norm_real, abs_of_pos hr]
  have hzunit : ∑ j, ‖z j‖ ^ 2 = 1 := by
    simp_rw [hznorm, mul_pow]
    rw [← Finset.mul_sum, ← hr2, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
  have hscale : (fun j => (r : ℂ) * z j) = w := by
    funext j; simp [z, hrc]
  have hp := shifted_poly_homogeneous K m v (r : ℂ) z
  rw [hscale] at hp
  rw [hp, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hv z hzunit) (pow_nonneg hr.le m)

namespace AllDegreesProof

lemma face_ratio_bound (k N i : ℕ) (hk : 1 ≤ k) (hi : i ≤ N) :
    ((N+k).choose k : ℝ) / ((N-i+k-1).choose (k-1) : ℝ) ≤
      ((N+k : ℕ) : ℝ) * ((i+1 : ℕ) : ℝ)^(k-1) := by
  have hs := shifted_choose_bound_ok (N-i) i (k-1)
  have he₁ : N-i+i+(k-1) = N+k-1 := by omega
  have he₂ : N-i+(k-1) = N-i+k-1 := by omega
  rw [he₁, he₂] at hs
  have hm : (N+k) * (N+k-1).choose (k-1) = (N+k).choose k * k := by
    have hn : N+k-1+1=N+k := by omega
    have hk' : k-1+1=k := by omega
    simpa only [hn, hk'] using Nat.add_one_mul_choose_eq (N+k-1) (k-1)
  have ht := Nat.mul_le_mul_left (N+k) hs
  rw [hm] at ht
  have hd : (N+k).choose k ≤ (N+k).choose k * k := by nlinarith
  have hnat : (N+k).choose k ≤
      ((N+k) * (i+1)^(k-1)) * (N-i+k-1).choose (k-1) := by
    nlinarith only [hd, ht]
  have hp : (0 : ℝ) < (N-i+k-1).choose (k-1) := by
    exact_mod_cast Nat.choose_pos (show k-1 ≤ N-i+k-1 by omega)
  apply (div_le_iff₀ hp).2
  exact_mod_cast hnat

lemma face_eval_bound (k N i : ℕ) (hk : 1 ≤ k) (hi : i ≤ N)
    (v : PolySpaceH k (N-i)) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ z ∈ UniformBoundUnit.cSphere k, ‖polyEval k (N-i) v z‖ ≤ C)
    (z : Fin (k+1) → ℂ) (hz : z ∈ UniformBoundUnit.cSphere (k+1)) :
    ‖polyEval (k+1) N (faceLift k N i (faceScale k N i) v) z‖ ≤
      C * Real.sqrt (((N+k).choose k : ℝ) / ((N-i+k-1).choose (k-1) : ℝ)) := by
  let r : ℝ := Real.sqrt (∑ j : Fin k, ‖(Fin.init z) j‖^2)
  let q : ℝ := ‖z (Fin.last k)‖^i * r^(N-i)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr2 : r^2 = ∑ j : Fin k, ‖(Fin.init z) j‖^2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hxy : ‖z (Fin.last k)‖^2 + r^2 = 1 := by
    change ∑ j, ‖z j‖^2 = 1 at hz
    rw [Fin.sum_univ_castSucc] at hz
    simp only [Fin.init_def] at hr2
    linarith
  have hb : (N.choose i : ℝ) * q^2 ≤ 1 := by
    have ht := binomial_bound N i hi (‖z (Fin.last k)‖^2) (r^2)
      (sq_nonneg _) (sq_nonneg _) hxy
    simpa only [q, mul_pow, ← pow_mul, Nat.mul_comm,
      mul_comm, mul_left_comm, mul_assoc] using ht
  have hs : 0 ≤ faceScale k N i := Real.sqrt_nonneg _
  have hs2 : (faceScale k N i)^2 =
      ((N+k).choose k : ℝ) * (N.choose i : ℝ) /
        ((N-i+k-1).choose (k-1) : ℝ) := by
    unfold faceScale
    exact Real.sq_sqrt (by positivity)
  have hp : 0 ≤ ((N+k).choose k : ℝ) / ((N-i+k-1).choose (k-1) : ℝ) := by positivity
  have hsq : (faceScale k N i * q)^2 ≤
      ((N+k).choose k : ℝ) / ((N-i+k-1).choose (k-1) : ℝ) := by
    rw [mul_pow, hs2]
    calc
      _ = (((N+k).choose k : ℝ) / ((N-i+k-1).choose (k-1) : ℝ)) *
          ((N.choose i : ℝ) * q^2) := by ring
      _ ≤ _ := mul_le_of_le_one_right hp hb
  have hh := (Real.le_sqrt (mul_nonneg hs hq) hp).2 hsq
  have hv' := allDegreesProof_hom_bound k (N-i) hk v C hv (Fin.init z)
  change ‖polyEval k (N-i) v (Fin.init z)‖ ≤ C*r^(N-i) at hv'
  rw [faceLift_eval k N i hi, norm_mul, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  calc
    _ ≤ (faceScale k N i * ‖z (Fin.last k)‖^i) * (C*r^(N-i)) :=
      mul_le_mul_of_nonneg_left hv' (by positivity)
    _ = C * (faceScale k N i * q) := by dsimp [q]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh hC

lemma face_card_split_done (k N b : ℕ) (hk : 1 ≤ k) (hb : b ≤ N) :
    (∑ i ∈ Finset.range b, (N-i+k-1).choose (k-1)) +
      (N-b+k).choose k = (N+k).choose k := by
  induction b generalizing N with
  | zero => simp
  | succ b ih =>
    have ih' := ih N (by omega)
    rw [Finset.sum_range_succ]
    have hp : (N-b+k).choose k =
        (N-b+k-1).choose (k-1) + (N-(b+1)+k).choose k := by
      have hp := Nat.choose_succ_succ' (N-(b+1)+k) (k-1)
      rw [show N-(b+1)+k+1 = N-b+k by omega,
        show k-1+1 = k by omega,
        show N-(b+1)+k = N-b+k-1 by omega] at hp
      simpa only [show N-(b+1)+k = N-b+k-1 by omega] using hp
    omega

lemma polyInner_swap (K N : ℕ) (v w : PolySpaceH K N) :
    polyInner K N v w = (starRingEnd ℂ) (polyInner K N w v) := by
  simp [polyInner, mul_comm, mul_left_comm, mul_assoc]

set_option maxHeartbeats 2000000 in
lemma assemble_faces_clean
    (k N b : ℕ) (hk : 1 ≤ k) (hb : b ≤ N)
    (α : ℝ) (U : (Fin k → ℕ) → Fin k → ℕ)
    (hU : Set.BijOn U (simplexS k (N-b) : Set _) (boxB k (N-b) : Set _))
    (F : ∀ i : Fin b,
      Fin ((N-i.val+k-1).choose (k-1)) → PolySpaceH k (N-i.val))
    (hF : ∀ i s t, polyInner k (N-i.val) (F i s) (F i t) =
      if s=t then 1 else 0)
    (A B : ℝ)
    (hFB : ∀ i s z, z ∈ UniformBoundUnit.cSphere (k+1) →
      ‖polyEval (k+1) N
        (faceLift k N i.val (faceScale k N i.val) (F i s)) z‖ ≤ B)
    (hGA : ∀ l ∈ boxB k (N-b), ∀ z ∈ UniformBoundUnit.cSphere (k+1),
      ‖polyEval (k+1) N (shiftedBasisPhi k N b α U l) z‖ ≤ A) :
    ∃ v : Fin ((N+k).choose k) → PolySpaceH (k+1) N,
      (∀ s t, polyInner (k+1) N (v s) (v t) = if s=t then 1 else 0) ∧
      (∀ s : Fin ((N+k).choose k),
        s.val < (∑ i ∈ Finset.range b, (N-i+k-1).choose (k-1)) →
        ∀ z ∈ UniformBoundUnit.cSphere (k+1), ‖polyEval (k+1) N (v s) z‖ ≤ B) ∧
      (∀ s : Fin ((N+k).choose k),
        (∑ i ∈ Finset.range b, (N-i+k-1).choose (k-1)) ≤ s.val →
        ∀ z ∈ UniformBoundUnit.cSphere (k+1), ‖polyEval (k+1) N (v s) z‖ ≤ A) := by
  classical
  let S := Σ i : Fin b, Fin ((N-i.val+k-1).choose (k-1))
  let G := ↥(boxB k (N-b))
  let d := ∑ i ∈ Finset.range b, (N-i+k-1).choose (k-1)
  let g := (N-b+k).choose k
  have hS : Fintype.card S = d := by
    simp only [S, Fintype.card_sigma, Fintype.card_fin, d]
    exact Fin.sum_univ_eq_sum_range (fun i => (N-i+k-1).choose (k-1)) b
  have hG : Fintype.card G = g := by
    dsimp only [g]
    rw [← onb_card k (N-b)]
    exact (Fintype.card_congr
      ((onb_degEquiv_final k (N-b)).trans (Set.BijOn.equiv U hU))).symm
  let eF : S ≃ Fin d := Fintype.equivFinOfCardEq hS
  let eG : G ≃ Fin g := Fintype.equivFinOfCardEq hG
  let e : S ⊕ G ≃ Fin ((N+k).choose k) :=
    (Equiv.sumCongr eF eG).trans
      (finSumFinEquiv.trans (finCongr (face_card_split_done k N b hk hb)))
  let w : S ⊕ G → PolySpaceH (k+1) N :=
    Sum.elim
      (fun x => faceLift k N x.1.val (faceScale k N x.1.val) (F x.1 x.2))
      (fun l => shiftedBasisPhi k N b α U l.val)
  have hi (i : Fin b) : i.val ≤ N := by have := i.isLt; omega
  have hw : ∀ s t, polyInner (k+1) N (w s) (w t) = if s=t then 1 else 0 := by
    intro s t
    cases s with
    | inl s =>
      cases t with
      | inl t =>
        rcases s with ⟨i,s⟩
        rcases t with ⟨j,t⟩
        by_cases hij : i=j
        · subst j
          have he : (Sigma.mk i s : S) = Sigma.mk i t ↔ s = t := by
            constructor
            · intro h
              exact Fin.ext (congrArg (fun x : S => x.2.val) h)
            · intro h
              subst t
              rfl
          simp only [w, Sum.elim_inl, face_norm_inner k N i.val (hi i), hF,
            Sum.inl.injEq, he]
        · have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
          have hst : (Sigma.mk i s : S) ≠ Sigma.mk j t :=
            fun h => hij (congrArg Sigma.fst h)
          simpa [w, hst] using
            faceLift_cross k N i.val j.val hij'
              (faceScale k N i.val) (faceScale k N j.val) (F i s) (F j t)
      | inr t =>
        simpa [w] using
          face_shift_cross k N s.1.val b s.1.isLt
            (faceScale k N s.1.val) (F s.1 s.2) α U t.val
    | inr s =>
      cases t with
      | inl t =>
        rw [polyInner_swap]
        have hzero := face_shift_cross k N t.1.val b t.1.isLt
          (faceScale k N t.1.val) (F t.1 t.2) α U s.val
        simpa [w, hzero]
      | inr t =>
        simpa [w, Subtype.coe_inj] using
          shifted_orth k N b hb α U hU s.val t.val s.property t.property
  let v : Fin ((N+k).choose k) → PolySpaceH (k+1) N := fun s => w (e.symm s)
  refine ⟨v, ?_, ?_, ?_⟩
  · intro s t
    simpa only [v, e.symm.injective.eq_iff] using hw (e.symm s) (e.symm t)
  · intro s hs z hz
    obtain ⟨x, rfl⟩ := e.surjective s
    cases x with
    | inl x =>
      simpa [v, w] using hFB x.1 x.2 z hz
    | inr x =>
      have hge : d ≤ (e (Sum.inr x)).val := by
        change d ≤ d + (eG x).val
        exact Nat.le_add_right d (eG x).val
      change (e (Sum.inr x)).val < d at hs
      omega
  · intro s hs z hz
    obtain ⟨x, rfl⟩ := e.surjective s
    cases x with
    | inl x =>
      have hlt : (e (Sum.inl x)).val < d := by
        change (eF x).val < d
        exact (eF x).isLt
      change d ≤ (e (Sum.inl x)).val at hs
      omega
    | inr x =>
      simpa [v, w] using hGA x.val x.property z hz

end AllDegreesProof

lemma allDegreesProof_cancel (k N b L : ℕ) (hk : 1 ≤ k) (hb : b ≤ L) :
    Real.sqrt (((N+k : ℕ) : ℝ) * ((L+1 : ℕ) : ℝ)^(k-1)) *
      Real.sqrt (((∑ i ∈ Finset.range b, (N-i+k-1).choose (k-1) : ℕ) : ℝ) /
        ((N+k).choose k : ℝ)) ≤
    Real.sqrt (((L+1 : ℕ) : ℝ)^(k-1) * (L*k : ℕ)) := by
  have hd : (0 : ℝ) < (N+k).choose k := by
    exact_mod_cast Nat.choose_pos (show k ≤ N+k by omega)
  have hh : ((N+k : ℕ) : ℝ) *
      ((∑ i ∈ Finset.range b, (N-i+k-1).choose (k-1) : ℕ) : ℝ) ≤
      (L*k : ℕ) * ((N+k).choose k : ℝ) := by
    exact_mod_cast (AllDegreesProof.face_count_mul k N b hk).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right k hb))
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have hdiv : ((N+k : ℕ) : ℝ) *
      (((∑ i ∈ Finset.range b, (N-i+k-1).choose (k-1) : ℕ) : ℝ) /
        ((N+k).choose k : ℝ)) ≤ (L*k : ℕ) := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hd).2 hh
  convert mul_le_mul_of_nonneg_left hdiv
    (show (0 : ℝ) ≤ ((L+1 : ℕ) : ℝ)^(k-1) by positivity) using 1 <;> ring

namespace UniformBoundUnit

set_option maxHeartbeats 2000000 in
theorem thm_onbexplicit_allDegrees (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : 1 ≤ a)
    (hbox : ThmBox) (hUN : ∀ j : ℕ, 1 ≤ j → j ≤ k → PropUNmap j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α : ℝ, BddPartQuot a α →
        ∀ N : ℕ,
          ∃ ψ : Module.Basis (Fin ((N + k).choose k)) ℂ (PolySpaceH (k + 1) N),
            (∀ i j, polyInner (k + 1) N (ψ i) (ψ j) = if i = j then 1 else 0) ∧
            ∀ ν, ∀ z ∈ cSphere (k + 1), ‖polyEval (k + 1) N (ψ ν) z‖ ≤ C := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk1 : k = 1
    · subst k
      obtain ⟨C, hC, h⟩ := allDegreesProof_divisible 1 (by omega) a ha hbox
        (hUN 1 (by omega) (by omega))
      exact ⟨C, hC, fun α hα N => h α hα N (by simp [lcmUpTo])⟩
    have hk2 : 2 ≤ k := by omega
    obtain ⟨Cp, hCp, hprev⟩ := ih (k-1) (by omega) (by omega)
      (fun j hj hjk => hUN j hj (by omega))
    obtain ⟨R, U, A, hA, hU, hbound⟩ :=
      AllDegreesProof.shifted_uniform k a ha hbox (hUN k hk le_rfl)
    let L := lcmUpTo k
    have hL : 0 < L := by
      apply Nat.pos_of_ne_zero
      intro hzero
      obtain ⟨x,hx,hx0⟩ := Finset.lcm_eq_zero_iff.mp hzero
      have hx1 := (Finset.mem_Icc.mp hx).1
      change x = 0 at hx0
      omega
    let T : ℝ := ((L+1 : ℕ) : ℝ)^(k-1)
    have hT : 0 ≤ T := by dsimp [T]; positivity
    obtain ⟨Cs, hCs, hsmall⟩ := allDegreesProof_small_ok k (2*k*L)
    let C := Cs + 10*A + 10*Cp*Real.sqrt (T*(L*k : ℕ)) + 1
    have hgain : 0 ≤ 10*Cp*Real.sqrt (T*(L*k : ℕ)) := by positivity
    have hAC : A ≤ C := by dsimp [C]; linarith
    have hCsC : Cs ≤ C := by dsimp [C]; linarith
    refine ⟨C, by dsimp [C]; positivity, ?_⟩
    intro α hα N
    by_cases hsmallN : N < 2*k*L
    · obtain ⟨ψ, hψ, hb⟩ := hsmall N hsmallN
      exact ⟨ψ, hψ, fun ν z hz => (hb ν z hz).trans hCsC⟩
    let b := N % L
    have hbL : b < L := Nat.mod_lt N hL
    have hbN : b ≤ N := Nat.mod_le N L
    have hM : 1 ≤ N-b := by
      have hh : L ≤ 2*k*L := by nlinarith
      omega
    have hu := (hU (N-b) hM (Nat.dvd_sub_mod N)).1
    have hp : ∀ M : ℕ,
        ∃ ψ : Module.Basis (Fin ((M+k-1).choose (k-1))) ℂ (PolySpaceH k M),
          (∀ s t, polyInner k M (ψ s) (ψ t) = if s=t then 1 else 0) ∧
          ∀ s, ∀ z ∈ cSphere k, ‖polyEval k M (ψ s) z‖ ≤ Cp := by
      intro M
      have hh := hprev α hα M
      rw [show k-1+1 = k by omega,
        show M+(k-1) = M+k-1 by omega] at hh
      exact hh
    choose F hF hFB using hp
    let B := Cp * Real.sqrt (((N+k : ℕ) : ℝ)*T)
    have hface : ∀ i : Fin b, ∀ s, ∀ z ∈ cSphere (k+1),
        ‖polyEval (k+1) N
          (AllDegreesProof.faceLift k N i.val
            (AllDegreesProof.faceScale k N i.val) (F (N-i.val) s)) z‖ ≤ B := by
      intro i s z hz
      have hi : i.val ≤ N := by have := i.isLt; omega
      apply (AllDegreesProof.face_eval_bound k N i.val hk hi _ Cp hCp.le
        (hFB (N-i.val) s) z hz).trans
      apply mul_le_mul_of_nonneg_left _ hCp.le
      apply Real.sqrt_le_sqrt
      apply (AllDegreesProof.face_ratio_bound k N i.val hk hi).trans
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      dsimp [T]
      gcongr
      exact_mod_cast (show i.val ≤ L by have := i.isLt; omega)
    obtain ⟨v,hv,hvB,hvA⟩ := AllDegreesProof.assemble_faces_clean k N b hk hbN
      α (U (N-b)) hu (fun i s => F (N-i.val) s)
      (fun i => hF (N-i.val)) A B hface
      (fun l hl z hz => hbound α hα N hM l z hz)
    let d := ∑ i ∈ Finset.range b, (N-i+k-1).choose (k-1)
    by_cases hd : d=0
    · obtain ⟨ψ,hψ⟩ := allDegreesProof_basis_of_orth k N v hv
      refine ⟨ψ, ?_, ?_⟩
      · simpa only [hψ] using hv
      · intro ν z hz
        rw [hψ]
        exact (hvA ν (by change d ≤ ν.val; omega) z hz).trans hAC
    have hdhalf : 2*d ≤ (N+k).choose k :=
      AllDegreesProof.face_count_half k N b hk (by
        have := Nat.mul_le_mul_left (2*k) hbL.le
        omega)
    obtain ⟨ψ,hψ,hψbound⟩ := allDegreesProof_absorption_ok k N v hv A B hA.le
      (by dsimp [B]; positivity) d (by omega) hdhalf hvB hvA
    refine ⟨ψ,hψ, ?_⟩
    intro ν z hz
    apply (hψbound ν z hz).trans
    have hh := allDegreesProof_cancel k N b L hk hbL.le
    change Real.sqrt (((N+k : ℕ) : ℝ)*T) *
      Real.sqrt ((d : ℝ)/((N+k).choose k : ℝ)) ≤
      Real.sqrt (T*(L*k : ℕ)) at hh
    have hg := mul_le_mul_of_nonneg_left hh (show 0 ≤ 10*Cp by positivity)
    dsimp only [B,C]
    nlinarith

end UniformBoundUnit


lemma sqrtTwo_floor_aux : ⌊Real.sqrt 2⌋ = (1 : ℤ) := by
  apply Int.floor_eq_iff.mpr
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> norm_num <;> nlinarith

theorem sqrtTwo_contFract_h : (GenContFract.of (Real.sqrt 2)).h = 1 := by
  rw [GenContFract.of_h_eq_floor, sqrtTwo_floor_aux]
  norm_num

lemma sqrtTwo_fr_aux : Int.fract (Real.sqrt 2) = Real.sqrt 2 - 1 := by
  simp [Int.fract, sqrtTwo_floor_aux]

lemma sqrtTwo_inv_aux : (Real.sqrt 2 - 1)⁻¹ = Real.sqrt 2 + 1 := by
  apply inv_eq_of_mul_eq_one_right
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

lemma sqrtTwo_add_floor_aux : ⌊Real.sqrt 2 + 1⌋ = (2 : ℤ) := by
  rw [Int.floor_add_one, sqrtTwo_floor_aux]
  norm_num

lemma sqrtTwo_add_fr_aux : Int.fract (Real.sqrt 2 + 1) = Real.sqrt 2 - 1 := by
  rw [Int.fract, sqrtTwo_add_floor_aux]
  norm_num
  ring

lemma sqrtTwo_sub_ne_aux : Real.sqrt 2 - 1 ≠ 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  intro h
  nlinarith

theorem sqrtTwo_contFract_partDens (i : ℕ) :
    (GenContFract.of (Real.sqrt 2)).partDens.get? i = some 2 := by
  have hn : Int.fract (Real.sqrt 2 + 1) ≠ 0 := by
    rw [sqrtTwo_add_fr_aux]
    exact sqrtTwo_sub_ne_aux
  have hs (j : ℕ) :
      GenContFract.IntFractPair.stream (Real.sqrt 2 + 1) j =
        some (GenContFract.IntFractPair.of (Real.sqrt 2 + 1)) := by
    induction j with
    | zero => exact GenContFract.IntFractPair.stream_zero _
    | succ j ih =>
        rw [GenContFract.IntFractPair.stream_succ hn,
          sqrtTwo_add_fr_aux, sqrtTwo_inv_aux]
        exact ih
  have h0 : Int.fract (Real.sqrt 2) ≠ 0 := by
    rw [sqrtTwo_fr_aux]
    exact sqrtTwo_sub_ne_aux
  have hi : GenContFract.IntFractPair.stream (Real.sqrt 2) (i + 1) =
      some (GenContFract.IntFractPair.of (Real.sqrt 2 + 1)) := by
    rw [GenContFract.IntFractPair.stream_succ h0, sqrtTwo_fr_aux, sqrtTwo_inv_aux]
    exact hs i
  have hp := GenContFract.partDen_eq_s_b
    (GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream hi)
  simpa [GenContFract.IntFractPair.of, sqrtTwo_add_floor_aux,
    sqrtTwo_floor_aux] using hp

theorem bddPartQuot_two_sqrtTwo : UniformBoundUnit.BddPartQuot 2 (Real.sqrt 2) := by
  refine ⟨irrational_sqrt_two, ?_⟩
  intro i x hx
  rw [sqrtTwo_contFract_partDens] at hx
  have h : (2 : ℝ) = x := Option.some.inj hx
  exact h ▸ le_refl 2

theorem exists_bddPartQuot : ∃ α : ℝ, UniformBoundUnit.BddPartQuot 2 α := by
  exact ⟨Real.sqrt 2, bddPartQuot_two_sqrtTwo⟩


/-- An `R`-balanced pair `(L, I)`, where the box `I = ∏ⱼ Iⱼ ⊂ ℤ^k` is given by its
coordinatewise endpoints `lo`, `hi` (so `Iⱼ = [lo j, hi j] ∩ ℤ`).  The conditions are
`#L ≤ R`, `0 < |v|₁ ≤ R` for every constraint `(v, b) ∈ L`, and `#Iᵢ ≤ R · #Iⱼ` for
all `i, j`.  The locations of the intervals and the constants `b` are unrestricted. -/
def IsBalancedPair (k R : ℕ) (L : Finset ((Fin k → ℤ) × ℤ)) (lo hi : Fin k → ℤ) : Prop :=
  L.card ≤ R ∧
    (∀ p ∈ L, 0 < ∑ s, |p.1 s| ∧ ∑ s, |p.1 s| ≤ (R : ℤ)) ∧
    ∀ i j : Fin k, boxSide k lo hi i ≤ R * boxSide k lo hi j


theorem Int.sign_two_mul_add_one (t : ℤ) :
    Int.sign (2 * t + 1) = if 0 ≤ t then 1 else -1 := by
  by_cases ht : 0 ≤ t
  · rw [if_pos ht]
    exact Int.sign_eq_one_of_pos (by omega)
  · rw [if_neg ht]
    exact Int.sign_eq_neg_one_of_neg (by omega)

theorem indicator_nonneg_eq_half_one_add_sign (t : ℤ) :
    (if 0 ≤ t then (1 : ℝ) else 0) = (1 + (Int.sign (2 * t + 1) : ℝ)) / 2 := by
  rw [Int.sign_two_mul_add_one]
  split_ifs <;> norm_num

private lemma agent4_indicator_product {ι : Type*} (S : Finset ι) (f : ι → ℤ) :
    (if ∀ i ∈ S, 0 ≤ f i then (1 : ℝ) else 0) =
      (1 / 2 ^ S.card) * ∏ i ∈ S, (1 + (Int.sign (2 * f i + 1) : ℝ)) := by
  classical
  by_cases h : ∀ i ∈ S, 0 ≤ f i
  · rw [if_pos h]
    have he : (∏ i ∈ S, (1 + (Int.sign (2 * f i + 1) : ℝ))) = 2 ^ S.card := by
      calc
        _ = ∏ _i ∈ S, (2 : ℝ) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [Int.sign_two_mul_add_one, if_pos (h i hi)]
          norm_num
        _ = _ := by simp
    rw [he]
    simp
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi, hneg⟩ := h
    have he : (∏ i ∈ S, (1 + (Int.sign (2 * f i + 1) : ℝ))) = 0 := by
      apply Finset.prod_eq_zero hi
      rw [Int.sign_two_mul_add_one, if_neg (not_le_of_gt hneg)]
      norm_num
    rw [he, mul_zero]

theorem indicator_forall_nonneg_eq_prod {k r : ℕ}
    (w : Fin r → Fin k → ℤ) (B : Fin r → ℤ) (m : Fin k → ℤ) :
    (if ∀ i, 0 ≤ (∑ s, w i s * m s) - B i then (1 : ℝ) else 0) =
      (1 / 2 ^ r) *
        ∏ i, (1 + (Int.sign (2 * ((∑ s, w i s * m s) - B i) + 1) : ℝ)) := by
  simpa using agent4_indicator_product Finset.univ
    (fun i : Fin r => (∑ s, w i s * m s) - B i)

theorem indicator_polyP_eq_prod (k : ℕ) (L : Finset ((Fin k → ℤ) × ℤ))
    (m : Fin k → ℤ) :
    (if ∀ p ∈ L, 0 ≤ (∑ s, p.1 s * m s) + p.2 then (1 : ℝ) else 0) =
      (1 / 2 ^ L.card) *
        ∏ p ∈ L, (1 + (Int.sign (2 * ((∑ s, p.1 s * m s) + p.2) + 1) : ℝ)) := by
  exact agent4_indicator_product L (fun p => (∑ s, p.1 s * m s) + p.2)


noncomputable def sgnCotWeight (L : ℕ) (x : ℝ) : ℝ :=
  2 / (L : ℝ) * Real.cot (Real.pi * x / (L : ℝ))

noncomputable def sgnCoeff (L : ℕ) (l : ℤ) : ℂ :=
  if Odd l then -Complex.I * (sgnCotWeight L (l : ℝ) : ℂ) else 0

def sgnIndex (L : ℕ) : Finset ℤ :=
  (Finset.Ioo (-((L : ℤ) / 2)) ((L : ℤ) / 2)).filter fun l => Odd l

namespace Agent4SignAux

private def sgnFreq (L : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Ioo (-((L : ℤ) / 2)) ((L : ℤ) / 2)).filter fun l => Odd l

private noncomputable def sgnCoeffHat (L : ℕ) (l : ℤ) : ℂ :=
  -(2 * Complex.I) / (L : ℂ) * (Real.cot (Real.pi * (l : ℝ) / (L : ℝ)) : ℂ)

private lemma sgnFreq_mem_iff (L : ℕ) (l : ℤ) :
    l ∈ sgnFreq L ↔ (0 < |l| ∧ |l| < (L : ℤ) / 2) ∧ Odd l := by
  simp only [sgnFreq, Finset.mem_filter, Finset.mem_Ioo, abs_lt]
  constructor
  · rintro ⟨h, ho⟩
    refine ⟨⟨?_, h⟩, ho⟩
    obtain ⟨j, hj⟩ := ho
    have hn : l ≠ 0 := by omega
    exact abs_pos.mpr hn
  · exact fun h => ⟨h.1.2, h.2⟩

private lemma sgnCoeffHat_ratio_ok (L : ℕ) (l : ℤ) :
    sgnCoeffHat L l =
      -(2 / (L : ℂ)) * (expTwoPiI ((l : ℝ)/(L : ℝ)) + 1) /
        (1 - expTwoPiI ((l : ℝ)/(L : ℝ))) := by
  unfold sgnCoeffHat
  rw [Complex.ofReal_cot, Complex.cot_eq_exp_ratio]
  have he : Complex.exp (2 * Complex.I * ((Real.pi * (l : ℝ) / (L : ℝ) : ℝ) : ℂ)) =
      expTwoPiI ((l : ℝ)/(L : ℝ)) := by
    unfold expTwoPiI
    congr 1
    push_cast
    ring
  rw [he]
  simp only [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
  ring_nf
  simp [Complex.I_sq]
  ring

private lemma sgn_exp_ne_ok (L : ℕ) (hL : 0 < L) (l : ℤ) (hl0 : l ≠ 0)
    (hl : |l| < (L : ℤ)) : expTwoPiI ((l : ℝ) / L) ≠ 1 := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  intro he
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
  have hn' := congrArg Complex.im hn
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im] at hn'
  norm_num at hn'
  have hrat : (l : ℝ) / L = (n : ℝ) := by nlinarith [Real.pi_pos]
  have hnabs : |(n : ℝ)| < 1 := by
    rw [← hrat, abs_div, abs_of_pos hLp]
    exact (div_lt_one hLp).2 (by exact_mod_cast hl)
  have hn0 : n = 0 := by
    have : |n| < (1 : ℤ) := by exact_mod_cast hnabs
    have := abs_lt.mp this
    omega
  subst n
  simp only [Int.cast_zero, div_eq_zero_iff] at hrat
  rcases hrat with h | h
  · exact hl0 (by exact_mod_cast h)
  · exact hLp.ne' h

private lemma sgnCoeffHat_neg_ok (L : ℕ) (l : ℤ) :
    sgnCoeffHat L (-l) = -sgnCoeffHat L l := by
  simp only [sgnCoeffHat, Int.cast_neg, mul_neg, neg_div, Real.cot_eq_cos_div_sin,
    Real.cos_neg, Real.sin_neg, div_neg, Complex.ofReal_neg, mul_neg]

private lemma sgn_sum_neg_final (L : ℕ) (h : ℤ) :
    (∑ l ∈ sgnFreq L, sgnCoeffHat L l * expTwoPiI ((l : ℝ) * (-h : ℤ) / L)) =
      -(∑ l ∈ sgnFreq L, sgnCoeffHat L l * expTwoPiI ((l : ℝ) * (h : ℝ) / L)) := by
  classical
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_nbij (fun l => -l)
  · intro l hl
    change -l ∈ sgnFreq L
    simpa only [sgnFreq_mem_iff, abs_neg, odd_neg] using (show l ∈ sgnFreq L from hl)
  · intro a ha b hb he
    exact neg_injective he
  · intro l hl
    refine ⟨-l, ?_, by simp⟩
    change -l ∈ sgnFreq L
    simpa only [sgnFreq_mem_iff, abs_neg, odd_neg] using (show l ∈ sgnFreq L from hl)
  · intro l hl
    rw [sgnCoeffHat_neg_ok]
    push_cast
    simp only [neg_mul, mul_neg, neg_div, neg_neg]

private lemma sgn_sum_zero_final (L : ℕ) :
    (∑ l ∈ sgnFreq L, sgnCoeffHat L l * expTwoPiI ((l : ℝ) * (0 : ℝ) / L)) = 0 := by
  have h := sgn_sum_neg_final L 0
  simp only [neg_zero, Int.cast_zero] at h
  linear_combination (1/2 : ℂ) * h

private lemma sgn_coeff_step_ok (L : ℕ) (hL : 0 < L) (l : ℤ) (hl : l ∈ sgnFreq L) :
    sgnCoeffHat L l * (expTwoPiI ((l : ℝ)/L) - 1) =
      (2 / (L : ℂ)) * (expTwoPiI ((l : ℝ)/L) + 1) := by
  have hh := (sgnFreq_mem_iff L l).1 hl
  have hn := sgn_exp_ne_ok L hL l (abs_pos.mp hh.1.1) (by omega)
  rw [sgnCoeffHat_ratio_ok]
  field_simp
  <;> ring

private lemma sgn_odd_reindex_ok (M : ℕ) (g : ℤ → ℂ) (hg : g (-(M : ℤ)) = 0) :
    (∑ l ∈ sgnFreq (2*M), g l) =
      ∑ t ∈ Finset.range M,
        g ((if Odd (M : ℤ) then -(M : ℤ) else 1-(M : ℤ)) + 2*(t : ℤ)) := by
  classical
  let a : ℤ := if Odd (M : ℤ) then -(M : ℤ) else 1-(M : ℤ)
  have ha : -(M : ℤ) ≤ a ∧ a ≤ 1-(M : ℤ) := by
    dsimp [a]
    split_ifs <;> omega
  have hao : a % 2 = 1 := by
    dsimp [a]
    split_ifs with h
    · have := Int.odd_iff.mp h
      omega
    · have := Int.not_odd_iff.mp h
      omega
  have hhalf : ((2*M : ℕ) : ℤ) / 2 = (M : ℤ) := by
    push_cast
    omega
  have hsub : sgnFreq (2*M) ⊆ (Finset.Ico (-(M : ℤ)) (M : ℤ)).filter Odd := by
    intro l hl
    simp only [sgnFreq, hhalf, Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Ico] at hl ⊢
    exact ⟨⟨hl.1.1.le, hl.1.2⟩, hl.2⟩
  calc
    _ = ∑ l ∈ (Finset.Ico (-(M : ℤ)) (M : ℤ)).filter Odd, g l := by
      apply Finset.sum_subset hsub
      intro l hl hn
      simp only [sgnFreq, hhalf, Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Ico] at hl hn
      have he : l = -(M : ℤ) := by
        by_contra he
        exact hn ⟨⟨by omega, hl.1.2⟩, hl.2⟩
      simpa only [he] using hg
    _ = ∑ t ∈ Finset.range M, g (a + 2*(t : ℤ)) := by
      symm
      apply Finset.sum_bij (fun (t : ℕ) _ => a + 2*(t : ℤ))
      · intro t ht
        have ht' : (t : ℤ) < M := by exact_mod_cast Finset.mem_range.mp ht
        have ht0 : (0 : ℤ) ≤ t := Int.natCast_nonneg t
        simp only [Finset.mem_filter, Finset.mem_Ico, Int.odd_iff]
        omega
      · intro t ht u hu he
        omega
      · intro l hl
        simp only [Finset.mem_filter, Finset.mem_Ico, Int.odd_iff] at hl
        let t : ℕ := ((l-a)/2).toNat
        have hn : 0 ≤ (l-a)/2 := by omega
        have he : (t : ℤ) = (l-a)/2 := Int.toNat_of_nonneg hn
        have ht : t < M := by omega
        exact ⟨t, Finset.mem_range.mpr ht, by omega⟩
      · intro t ht
        rfl

private lemma sgn_odd_char_sum_ok (M : ℕ) (hM : 0 < M) (a : ℤ) (h : ℕ) (hh : h < M) :
    (∑ t ∈ Finset.range M,
      expTwoPiI (((a + 2*(t : ℤ) : ℤ) : ℝ) * (h : ℝ) / (2*M : ℕ))) =
      if h = 0 then (M : ℂ) else 0 := by
  have hMp : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have he (t : ℕ) :
      (((a + 2*(t : ℤ) : ℤ) : ℝ) * (h : ℝ) / (2*M : ℕ)) =
      (a : ℝ) * h / (2*M : ℕ) + (t : ℝ) * ((h : ℝ)-0) / M := by
    push_cast
    field_simp
    <;> ring
  simp_rw [he, onb_exp_add]
  have hsum := onb_fourier_final M h 0 hM hh hM
  simp only [Nat.cast_zero] at hsum
  rw [← Finset.mul_sum, hsum]
  split_ifs with he
  · subst h
    simp [expTwoPiI]
  · simp

private lemma sgn_odd_pair_sum_ok (M : ℕ) (hM : 0 < M) (h : ℕ) (hh : h+1 < M) :
    (∑ l ∈ sgnFreq (2*M),
      (expTwoPiI ((l : ℝ) * ((h+1 : ℕ) : ℝ) / (2*M : ℕ)) +
        expTwoPiI ((l : ℝ) * (h : ℝ) / (2*M : ℕ)))) =
      if h = 0 then (M : ℂ) else 0 := by
  have hMp : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hz : expTwoPiI (-(1:ℝ)/2) = -1 := by
    unfold expTwoPiI
    have he : 2 * (Real.pi : ℂ) * Complex.I * ((-(1:ℝ)/2 : ℝ) : ℂ) =
        -((Real.pi : ℂ) * Complex.I) := by push_cast; ring
    rw [he, Complex.exp_neg_pi_mul_I]
  have hg : expTwoPiI (((-(M : ℤ) : ℤ) : ℝ) * ((h+1 : ℕ) : ℝ) / (2*M : ℕ)) +
      expTwoPiI (((-(M : ℤ) : ℤ) : ℝ) * (h : ℝ) / (2*M : ℕ)) = 0 := by
    have he : (((-(M : ℤ) : ℤ) : ℝ) * ((h+1 : ℕ) : ℝ) / (2*M : ℕ)) =
        -(1:ℝ)/2 + (((-(M : ℤ) : ℤ) : ℝ) * (h : ℝ) / (2*M : ℕ)) := by
      push_cast
      field_simp
      <;> ring
    rw [he, onb_exp_add, hz]
    ring
  rw [sgn_odd_reindex_ok M _ hg, Finset.sum_add_distrib,
    sgn_odd_char_sum_ok M hM _ (h+1) hh, sgn_odd_char_sum_ok M hM _ h (by omega)]
  simp

private lemma sgn_sum_step_checked (M : ℕ) (hM : 0 < M) (h : ℕ) (hh : h+1 < M) :
    (∑ l ∈ sgnFreq (2*M), sgnCoeffHat (2*M) l *
      expTwoPiI ((l : ℝ) * ((h+1 : ℕ) : ℝ) / (2*M : ℕ))) -
    (∑ l ∈ sgnFreq (2*M), sgnCoeffHat (2*M) l *
      expTwoPiI ((l : ℝ) * (h : ℝ) / (2*M : ℕ))) =
      if h = 0 then 1 else 0 := by
  have hterm (l : ℤ) (hl : l ∈ sgnFreq (2*M)) :
      sgnCoeffHat (2*M) l * expTwoPiI ((l : ℝ) * ((h+1 : ℕ) : ℝ) / (2*M : ℕ)) -
        sgnCoeffHat (2*M) l * expTwoPiI ((l : ℝ) * (h : ℝ) / (2*M : ℕ)) =
      (2 / (2*M : ℕ) : ℂ) *
        (expTwoPiI ((l : ℝ) * ((h+1 : ℕ) : ℝ) / (2*M : ℕ)) +
          expTwoPiI ((l : ℝ) * (h : ℝ) / (2*M : ℕ))) := by
    have he : (l : ℝ) * ((h+1 : ℕ) : ℝ) / (2*M : ℕ) =
        (l : ℝ) / (2*M : ℕ) + (l : ℝ) * (h : ℝ) / (2*M : ℕ) := by
      push_cast
      ring
    rw [he, onb_exp_add]
    have hs := sgn_coeff_step_ok (2*M) (by omega) l hl
    linear_combination expTwoPiI ((l : ℝ) * (h : ℝ) / (2*M : ℕ)) * hs
  rw [← Finset.sum_sub_distrib]
  simp_rw [Finset.sum_congr rfl hterm]
  rw [← Finset.mul_sum, sgn_odd_pair_sum_ok M hM h hh]
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  split_ifs <;> push_cast <;> field_simp <;> ring

private lemma sgn_sum_nat_checked (M : ℕ) (hM : 0 < M) (h : ℕ) (hh : h < M) :
    (∑ l ∈ sgnFreq (2*M), sgnCoeffHat (2*M) l *
      expTwoPiI ((l : ℝ) * (h : ℝ) / (2*M : ℕ))) =
      if h = 0 then 0 else 1 := by
  induction h with
  | zero => simpa using sgn_sum_zero_final (2*M)
  | succ h ih =>
    have hs := sgn_sum_step_checked M hM h hh
    have hi := ih (by omega)
    rw [hi] at hs
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
    split_ifs at hs <;> linear_combination hs

private theorem lem_sgn (L : ℕ) (hL : 4 ≤ L) (hLeven : Even L) (h : ℤ)
    (hh : |h| < (L : ℤ) / 2) :
    ((Int.sign h : ℤ) : ℂ) =
      ∑ l ∈ sgnFreq L,
        sgnCoeffHat L l * expTwoPiI ((l : ℝ) * (h : ℝ) / (L : ℝ)) := by
  obtain ⟨M, hLM⟩ := hLeven
  have he : L = 2*M := by omega
  clear hLM
  subst L
  have hM : 0 < M := by omega
  have hhalf : ((2*M : ℕ) : ℤ) / 2 = (M : ℤ) := by push_cast; omega
  rw [hhalf] at hh
  have hpos (n : ℕ) (hn : n < M) :
      ((Int.sign (n : ℤ) : ℤ) : ℂ) =
        ∑ l ∈ sgnFreq (2*M), sgnCoeffHat (2*M) l *
          expTwoPiI ((l : ℝ) * ((n : ℤ) : ℝ) / (2*M : ℕ)) := by
    rw [Int.cast_natCast, sgn_sum_nat_checked M hM n hn]
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp [hn0, Int.sign_natCast_of_ne_zero hn0]
  by_cases hh0 : 0 ≤ h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hh0
    apply hpos
    simpa using hh
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -h by omega)
    have he : h = -(n : ℤ) := by omega
    rw [he, Int.sign_neg, Int.cast_neg, sgn_sum_neg_final]
    congr 1
    apply hpos
    rw [he, abs_neg, abs_of_nonneg (Int.natCast_nonneg n)] at hh
    exact_mod_cast hh

end Agent4SignAux

theorem mem_sgnIndex_iff (L : ℕ) (hL : 4 ≤ L) (hLe : Even L) (l : ℤ) :
    l ∈ sgnIndex L ↔ Odd l ∧ 2 * |l| < (L : ℤ) := by
  classical
  obtain ⟨q, hq⟩ := hLe
  have hq' : (L : ℤ) = (q : ℤ) + (q : ℤ) := by exact_mod_cast hq
  have hhalf : (L : ℤ) / 2 = (q : ℤ) := by omega
  have hlt : 2 * |l| < (L : ℤ) ↔ |l| < (q : ℤ) := by omega
  simp only [sgnIndex, Finset.mem_filter, Finset.mem_Ioo, hhalf, hlt, abs_lt]
  tauto

theorem sgnCoeff_of_odd (L : ℕ) (l : ℤ) (hl : Odd l) :
    sgnCoeff L l =
      -(2 * Complex.I / (L : ℂ)) * (Real.cot (Real.pi * (l : ℝ) / (L : ℝ)) : ℂ) := by
  simp only [sgnCoeff, if_pos hl, sgnCotWeight, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_natCast]
  ring

theorem sgnCoeff_of_even (L : ℕ) (l : ℤ) (hl : Even l) : sgnCoeff L l = 0 := by
  have hn : ¬ Odd l := by
    rintro ⟨s, hs⟩
    obtain ⟨t, ht⟩ := hl
    omega
  simp [sgnCoeff, hn]

theorem sgnCoeff_mul_I_of_odd (L : ℕ) (l : ℤ) (hl : Odd l) :
    Complex.I * sgnCoeff L l = (sgnCotWeight L (l : ℝ) : ℂ) := by
  simp [sgnCoeff, hl, ← mul_assoc]

theorem sgnCoeff_mul_I_im (L : ℕ) (l : ℤ) : (Complex.I * sgnCoeff L l).im = 0 := by
  by_cases hl : Odd l
  · rw [sgnCoeff_mul_I_of_odd L l hl]
    rfl
  · simp [sgnCoeff, hl]

theorem abs_sgnCotWeight_le (L : ℕ) (hL : 4 ≤ L) (l : ℤ) (hl : l ≠ 0)
    (hlL : 2 * |l| < (L : ℤ)) :
    |sgnCotWeight L (l : ℝ)| ≤ 2 / (Real.pi * |(l : ℝ)|) := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hlr : (l : ℝ) ≠ 0 := by exact_mod_cast hl
  have hhalf : 2 * |(l : ℝ)| < (L : ℝ) := by exact_mod_cast hlL
  let x : ℝ := Real.pi * (l : ℝ) / (L : ℝ)
  have hab : |x| = Real.pi * |(l : ℝ)| / (L : ℝ) := by
    simp only [x, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hLp]
  have hxp : 0 < |x| := by rw [hab]; positivity
  have hxhalf : |x| < Real.pi / 2 := by
    rw [hab]
    apply (div_lt_iff₀ hLp).2
    nlinarith [mul_pos Real.pi_pos (show 0 < (L : ℝ) - 2 * |(l : ℝ)| by linarith)]
  have ht := Real.le_tan (abs_nonneg x) hxhalf
  have htabs : |Real.tan x| = Real.tan |x| := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx] at ht ⊢
      exact abs_of_nonneg (hx.trans ht)
    · have hx' : x < 0 := lt_of_not_ge hx
      rw [abs_of_neg hx', Real.tan_neg] at ht ⊢
      exact abs_of_nonpos (by linarith)
  have hcot : |Real.cot x| ≤ |x|⁻¹ := by
    rw [← Real.tan_inv_eq_cot, abs_inv, htabs]
    exact inv_anti₀ hxp ht
  calc
    |sgnCotWeight L (l : ℝ)| = (2 / (L : ℝ)) * |Real.cot x| := by
      rw [sgnCotWeight, abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) / L)]
    _ ≤ (2 / (L : ℝ)) * |x|⁻¹ :=
      mul_le_mul_of_nonneg_left hcot (by positivity)
    _ = 2 / (Real.pi * |(l : ℝ)|) := by
      rw [hab]
      field_simp

theorem norm_sgnCoeff_le (L : ℕ) (hL : 4 ≤ L) (l : ℤ) (hl : l ≠ 0)
    (hlL : 2 * |l| < (L : ℤ)) :
    ‖sgnCoeff L l‖ ≤ 2 / (Real.pi * |(l : ℝ)|) := by
  by_cases ho : Odd l
  · simpa only [sgnCoeff, if_pos ho, norm_mul, norm_neg, Complex.norm_I,
      one_mul, Complex.norm_real, Real.norm_eq_abs] using
      abs_sgnCotWeight_le L hL l hl hlL
  · simp only [sgnCoeff, if_neg ho, norm_zero]
    positivity

theorem norm_sgnCoeff_le_dyadic (L : ℕ) (hL : 4 ≤ L) (l : ℤ) (J : ℕ)
    (hJ : (2 : ℤ) ^ J ≤ |l|) (hlL : 2 * |l| < (L : ℤ)) :
    ‖sgnCoeff L l‖ ≤ 2 / 2 ^ J := by
  have hpow : (0 : ℤ) < 2 ^ J := by positivity
  have hl : l ≠ 0 := by
    intro he
    subst l
    simp only [abs_zero] at hJ
    omega
  have hJr : (2 : ℝ) ^ J ≤ |(l : ℝ)| := by exact_mod_cast hJ
  apply (norm_sgnCoeff_le L hL l hl hlL).trans
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  nlinarith [mul_nonneg (sub_nonneg.mpr hpi) (abs_nonneg (l : ℝ))]

private lemma agent4_sign_pair_ok (M : ℕ) (hM : 0 < M) (f : ℤ → ℂ) :
    (∑ h ∈ Finset.Ioo (-(M : ℤ)) (M : ℤ), (Int.sign h : ℂ) * f h) =
      (∑ n ∈ Finset.range M, f (n : ℤ)) - ∑ n ∈ Finset.range M, f (-(n : ℤ)) := by
  classical
  let P := (Finset.range (M-1)).image (fun n : ℕ => (n : ℤ)+1)
  let Q := (Finset.range (M-1)).image (fun n : ℕ => -((n : ℤ)+1))
  have hzero : (0 : ℤ) ∉ P ∪ Q := by
    simp only [P, Q, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    omega
  have hdis : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro h hp hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hq
    omega
  have hset : Finset.Ioo (-(M : ℤ)) (M : ℤ) = insert 0 (P ∪ Q) := by
    ext h
    simp only [P, Q, Finset.mem_Ioo, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image, Finset.mem_range]
    constructor
    · intro hh
      by_cases hz : h = 0
      · exact Or.inl hz
      by_cases hp : 0 < h
      · exact Or.inr (Or.inl ⟨h.toNat-1, by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨(-h).toNat-1, by omega, by omega⟩)
    · rintro (rfl | ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩) <;> omega
  rw [hset, Finset.sum_insert hzero, Finset.sum_union hdis]
  simp only [Int.sign_zero, Int.cast_zero, zero_mul, zero_add]
  have hpos : (∑ h ∈ P, (Int.sign h : ℂ) * f h) =
      ∑ n ∈ Finset.range (M-1), f ((n : ℤ)+1) := by
    dsimp only [P]
    rw [Finset.sum_image (by intro a ha b hb hab; dsimp at hab; omega)]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Int.sign_eq_one_of_pos (by omega)]
    simp
  have hneg : (∑ h ∈ Q, (Int.sign h : ℂ) * f h) =
      -(∑ n ∈ Finset.range (M-1), f (-((n : ℤ)+1))) := by
    dsimp only [Q]
    rw [Finset.sum_image (by intro a ha b hb hab; dsimp at hab; omega),
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Int.sign_eq_neg_one_of_neg (by omega)]
    simp
  rw [hpos, hneg]
  have he : M = (M-1)+1 := by omega
  conv_rhs => rw [he, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, neg_zero]
  ring

private lemma agent4_exp_int (t : ℤ) : expTwoPiI (t : ℝ) = 1 := by
  unfold expTwoPiI
  push_cast
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
    (t : ℂ) * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I t

private lemma agent4_exp_half (l : ℤ) :
    expTwoPiI ((l : ℝ)/2) = if Odd l then -1 else 1 := by
  have hh : expTwoPiI (1/2) = -1 := by
    unfold expTwoPiI
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ((1/2 : ℝ) : ℂ) =
      (Real.pi : ℂ) * Complex.I by push_cast; ring]
    exact Complex.exp_pi_mul_I
  by_cases hl : Odd l
  · rw [if_pos hl]
    obtain ⟨t, rfl⟩ := hl
    rw [show (((2*t+1 : ℤ) : ℝ)/2) = (t : ℝ)+1/2 by push_cast; ring,
      onb_exp_add, agent4_exp_int, hh, one_mul]
  · rw [if_neg hl]
    obtain ⟨t, rfl⟩ := Int.not_odd_iff_even.mp hl
    rw [show (((t+t : ℤ) : ℝ)/2) = (t : ℝ) by push_cast; ring]
    exact agent4_exp_int t

private lemma agent4_exp_pow_half (M : ℕ) (hM : 0 < M) (l : ℤ) :
    expTwoPiI ((l : ℝ)/(2*M : ℕ)) ^ M = if Odd l then -1 else 1 := by
  rw [shifted_exp_nat_pow]
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [show (l : ℝ)/(2*M : ℕ)*(M : ℝ) = (l : ℝ)/2 by
    push_cast; field_simp]
  exact agent4_exp_half l

private lemma agent4_geom_difference (M : ℕ) (z : ℂ) (l : ℤ)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hp : z ^ M = if Odd l then -1 else 1) :
    (∑ t ∈ Finset.range M, z⁻¹ ^ t) - (∑ t ∈ Finset.range M, z ^ t) =
      if Odd l then -2 * (z + 1) / (1 - z) else 0 := by
  rw [geom_sum_inv hz1 hz0 M, geom_sum_eq hz1 M]
  simp only [inv_pow, hp]
  split_ifs <;> norm_num
  field_simp [sub_ne_zero.mpr hz1, sub_ne_zero.mpr (Ne.symm hz1)]
  <;> ring

theorem sgnCoeff_eq_fourierTransform (L : ℕ) (hL : 4 ≤ L) (hLe : Even L) (l : ℤ) :
    ((L : ℂ))⁻¹ *
        ∑ h ∈ Finset.Ioo (-((L : ℤ) / 2)) ((L : ℤ) / 2),
          (Int.sign h : ℂ) * expTwoPiI (-(((l * h : ℤ) : ℝ) / (L : ℝ))) =
      sgnCoeff L l := by
  obtain ⟨M, hLM⟩ := hLe
  have he : L = 2*M := by omega
  clear hLM
  subst L
  have hM : 0 < M := by omega
  have hhalf : ((2*M : ℕ) : ℤ) / 2 = (M : ℤ) := by push_cast; omega
  rw [hhalf, agent4_sign_pair_ok M hM]
  let z := expTwoPiI ((l : ℝ)/(2*M : ℕ))
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hp : z^M = if Odd l then -1 else 1 := agent4_exp_pow_half M hM l
  have hnegexp (x : ℝ) : expTwoPiI (-x) = (expTwoPiI x)⁻¹ := by
    simp [expTwoPiI, Complex.exp_neg]
  have hfpos (n : ℕ) :
      expTwoPiI (-(((l*(n:ℤ):ℤ):ℝ)/(2*M:ℕ))) = (z⁻¹)^n := by
    rw [← hnegexp, shifted_exp_nat_pow]
    congr 1
    push_cast
    ring
  have hfneg (n : ℕ) :
      expTwoPiI (-(((l*(-(n:ℤ)):ℤ):ℝ)/(2*M:ℕ))) = z^n := by
    rw [shifted_exp_nat_pow]
    congr 1
    push_cast
    ring
  simp_rw [hfpos, hfneg]
  by_cases hz1 : z = 1
  · have hn : ¬ Odd l := by
      intro ho
      rw [hz1, one_pow, if_pos ho] at hp
      norm_num at hp
    simp [hz1, sgnCoeff, hn]
  · rw [agent4_geom_difference M z l hz0 hz1 hp]
    by_cases ho : Odd l
    · rw [if_pos ho, sgnCoeff_of_odd _ _ ho]
      rw [show -(2 * Complex.I / ((2*M : ℕ) : ℂ)) *
        (Real.cot (Real.pi * (l : ℝ) / (2*M : ℕ)) : ℂ) =
        Agent4SignAux.sgnCoeffHat (2*M) l by
          unfold Agent4SignAux.sgnCoeffHat; ring]
      rw [Agent4SignAux.sgnCoeffHat_ratio_ok]
      dsimp only [z]
      ring
    · simp [ho, sgnCoeff]

theorem lem_sgn (L : ℕ) (hL : 4 ≤ L) (hLe : Even L) (h : ℤ) (hh : 2 * |h| < (L : ℤ)) :
    (Int.sign h : ℂ) =
      ∑ l ∈ sgnIndex L, sgnCoeff L l * expTwoPiI (((l * h : ℤ) : ℝ) / (L : ℝ)) := by
  have he : |h| < (L : ℤ) / 2 := by
    obtain ⟨M, hM⟩ := hLe
    have he : (L : ℤ) = 2 * (M : ℤ) := by exact_mod_cast (show L = 2*M by omega)
    omega
  rw [Agent4SignAux.lem_sgn L hL hLe h he]
  apply Finset.sum_congr rfl
  intro l hl
  have ho : Odd l := (Finset.mem_filter.mp hl).2
  simp only [sgnCoeff, if_pos ho, sgnCotWeight, Agent4SignAux.sgnCoeffHat,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_natCast, Int.cast_mul]
  ring

theorem sgnCotWeight_antitoneOn_pos (L : ℕ) (hL : 4 ≤ L) :
    AntitoneOn (sgnCotWeight L) (Set.Ioo (0 : ℝ) ((L : ℝ) / 2)) := by
  have hp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hangle (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) ((L : ℝ) / 2)) :
      0 < Real.pi * x / L ∧ Real.pi * x / L < Real.pi / 2 := by
    constructor
    · exact div_pos (mul_pos Real.pi_pos hx.1) hp
    · apply (div_lt_iff₀ hp).2
      have hh := mul_lt_mul_of_pos_left hx.2 Real.pi_pos
      nlinarith
  intro x hx y hy hxy
  have hx' := hangle x hx
  have hy' := hangle y hy
  have ht : Real.tan (Real.pi * x / L) ≤ Real.tan (Real.pi * y / L) :=
    Real.strictMonoOn_tan.monotoneOn
      ⟨by linarith [Real.pi_pos], hx'.2⟩
      ⟨by linarith [Real.pi_pos], hy'.2⟩
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hxy Real.pi_pos.le) hp.le)
  unfold sgnCotWeight
  rw [← Real.tan_inv_eq_cot, ← Real.tan_inv_eq_cot]
  exact mul_le_mul_of_nonneg_left
    (inv_anti₀ (Real.tan_pos_of_pos_of_lt_pi_div_two hx'.1 hx'.2) ht)
    (by positivity)

theorem sgnCotWeight_antitoneOn_neg (L : ℕ) (hL : 4 ≤ L) :
    AntitoneOn (sgnCotWeight L) (Set.Ioo (-((L : ℝ) / 2)) 0) := by
  have he (x : ℝ) : sgnCotWeight L (-x) = -sgnCotWeight L x := by
    unfold sgnCotWeight
    rw [mul_neg, neg_div, ← Real.tan_inv_eq_cot,
      ← Real.tan_inv_eq_cot, Real.tan_neg, inv_neg, mul_neg]
  intro x hx y hy hxy
  have hh := sgnCotWeight_antitoneOn_pos L hL
    (show -y ∈ Set.Ioo (0 : ℝ) ((L : ℝ) / 2) by
      constructor <;> linarith [hy.1, hy.2])
    (show -x ∈ Set.Ioo (0 : ℝ) ((L : ℝ) / 2) by
      constructor <;> linarith [hx.1, hx.2])
    (neg_le_neg hxy)
  rw [he, he] at hh
  linarith

theorem sgnCotWeight_anti_int_pos (L : ℕ) (hL : 4 ≤ L) (l l' : ℤ) (hl : 0 < l)
    (hll' : l ≤ l') (hl' : 2 * l' < (L : ℤ)) :
    sgnCotWeight L (l' : ℝ) ≤ sgnCotWeight L (l : ℝ) := by
  have h₁ : (0 : ℝ) < l := by exact_mod_cast hl
  have h₂ : (l : ℝ) ≤ l' := by exact_mod_cast hll'
  have h₃ : 2 * (l' : ℝ) < L := by exact_mod_cast hl'
  exact sgnCotWeight_antitoneOn_pos L hL
    ⟨h₁, by linarith⟩ ⟨by linarith, by linarith⟩ h₂

theorem sgnCotWeight_anti_int_neg (L : ℕ) (hL : 4 ≤ L) (l l' : ℤ) (hl' : l' < 0)
    (hll' : l ≤ l') (hl : -(L : ℤ) < 2 * l) :
    sgnCotWeight L (l' : ℝ) ≤ sgnCotWeight L (l : ℝ) := by
  have h₁ : (l' : ℝ) < 0 := by exact_mod_cast hl'
  have h₂ : (l : ℝ) ≤ l' := by exact_mod_cast hll'
  have h₃ : -(L : ℝ) < 2 * (l : ℝ) := by exact_mod_cast hl
  exact sgnCotWeight_antitoneOn_neg L hL
    ⟨by linarith, by linarith⟩ ⟨by linarith, h₁⟩ h₂
noncomputable def quadPhase (a b : ℤ) (q : ℕ) (_hq : 0 < q) (x : ℤ) : ℂ :=
  expTwoPiI (((a * x ^ 2 + b * x : ℤ) : ℝ) / (q : ℝ))

noncomputable def quadGaussSum (a b : ℤ) (q : ℕ) (hq : 0 < q) : ℂ :=
  ∑ x ∈ Finset.range q, quadPhase a b q hq (x : ℤ)

private lemma agent4_quad_char (a b : ℤ) (q : ℕ) [NeZero q]
    (hq : 0 < q) (x : ℤ) :
    quadPhase a b q hq x =
      ZMod.stdAddChar ((a : ZMod q) * (x : ZMod q)^2 +
        (b : ZMod q) * (x : ZMod q)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [show (a : ZMod q) * (x : ZMod q)^2 + (b : ZMod q) * (x : ZMod q) =
    ((a*x^2+b*x : ℤ) : ZMod q) by push_cast; rfl, ZMod.stdAddChar_coe]
  unfold quadPhase expTwoPiI
  push_cast
  congr 1
  ring

theorem quadPhase_of_modEq (a b : ℤ) (q : ℕ) (hq : 0 < q) (x y : ℤ)
    (h : x ≡ y [ZMOD (q : ℤ)]) : quadPhase a b q hq x = quadPhase a b q hq y := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [agent4_quad_char, agent4_quad_char, (ZMod.intCast_eq_intCast_iff x y q).2 h]

private lemma agent4_quad_sum_zmod (a b : ℤ) (q : ℕ) [NeZero q] (hq : 0 < q) :
    quadGaussSum a b q hq = ∑ y : ZMod q,
      ZMod.stdAddChar ((a : ZMod q)*y^2+(b : ZMod q)*y) := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  unfold quadGaussSum
  apply Finset.sum_bij (fun (x : ℕ) _ => (x : ZMod q))
  · intros
    exact Finset.mem_univ _
  · intro x hx y hy he
    have hv := congrArg ZMod.val he
    simpa [ZMod.val_cast_of_lt (Finset.mem_range.mp hx),
      ZMod.val_cast_of_lt (Finset.mem_range.mp hy)] using hv
  · intro y hy
    exact ⟨y.val, Finset.mem_range.mpr (ZMod.val_lt y), ZMod.natCast_zmod_val y⟩
  · intro x hx
    simpa using agent4_quad_char a b q hq (x : ℤ)

theorem quadGaussSum_eq_sum_of_residueSystem (a b : ℤ) (q : ℕ) (hq : 0 < q)
    (s : Finset ℤ) (hs : ∀ y : ZMod q, ∃! x : ℤ, x ∈ s ∧ (x : ZMod q) = y) :
    ∑ x ∈ s, quadPhase a b q hq x = quadGaussSum a b q hq := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  rw [agent4_quad_sum_zmod]
  apply Finset.sum_bij (fun (x : ℤ) _ => (x : ZMod q))
  · intros
    exact Finset.mem_univ _
  · intro x hx y hy he
    obtain ⟨z, hz, hu⟩ := hs (x : ZMod q)
    exact (hu x ⟨hx, rfl⟩).trans (hu y ⟨hy, he.symm⟩).symm
  · intro y hy
    obtain ⟨x, hx, hu⟩ := hs y
    exact ⟨x, hx.1, hx.2⟩
  · intro x hx
    exact agent4_quad_char a b q hq x

theorem quadGaussSum_eq_sum_shift (a b : ℤ) (q : ℕ) (hq : 0 < q) (c : ℤ) :
    ∑ x ∈ Finset.range q, quadPhase a b q hq (c + (x : ℤ)) = quadGaussSum a b q hq := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  rw [agent4_quad_sum_zmod]
  apply Finset.sum_bij (fun (x : ℕ) _ => (c : ZMod q) + (x : ZMod q))
  · intros
    exact Finset.mem_univ _
  · intro x hx y hy he
    have hv := congrArg ZMod.val (add_left_cancel he)
    simpa [ZMod.val_cast_of_lt (Finset.mem_range.mp hx),
      ZMod.val_cast_of_lt (Finset.mem_range.mp hy)] using hv
  · intro y hy
    refine ⟨(y - (c : ZMod q)).val, Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
    rw [ZMod.natCast_zmod_val]
    exact add_sub_cancel _ _
  · intro x hx
    simpa only [Int.cast_add, Int.cast_natCast] using
      agent4_quad_char a b q hq (c + (x : ℤ))
/-- A smooth cutoff: `U : ℝ → ℂ` is `C^∞` and supported in `[-2,2]`. -/
def IsSmoothCutoff (U : ℝ → ℂ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U ∧
    Function.support U ⊆ Set.Icc (-2 : ℝ) 2

/-- The oscillatory integral attached to a cutoff `U`,
`W_U(λ; ξ) = ∫_ℝ U(t) e(λ t² + ξ t) dt`, where `e(x) = e^{2πix}`. -/
noncomputable def oscIntegralW (U : ℝ → ℂ) (lam xi : ℝ) : ℂ :=
  ∫ t : ℝ, U t * expTwoPiI (lam * t ^ 2 + xi * t)

/-- For a smooth cutoff the integrand defining `W_U(λ; ξ)` is integrable, so the
definition is meaningful. -/
theorem integrable_oscIntegralW_integrand (U : ℝ → ℂ) (hU : IsSmoothCutoff U)
    (lam xi : ℝ) :
    MeasureTheory.Integrable
      (fun t : ℝ => U t * expTwoPiI (lam * t ^ 2 + xi * t)) := by
  have hc : Continuous (fun t : ℝ => U t * expTwoPiI (lam * t ^ 2 + xi * t)) := by
    apply hU.1.continuous.mul
    unfold expTwoPiI
    fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro t ht
  apply hU.2
  exact fun hz => ht (by simp [hz])

/-- `W_U(λ; ξ)` is the integral of `U(t) e(λ t² + ξ t)` over the support interval
`[-2,2]`. -/
theorem oscIntegralW_eq_intervalIntegral (U : ℝ → ℂ) (hU : IsSmoothCutoff U)
    (lam xi : ℝ) :
    oscIntegralW U lam xi =
      ∫ t in (-2 : ℝ)..2, U t * expTwoPiI (lam * t ^ 2 + xi * t) := by
  unfold oscIntegralW
  rw [intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  symm
  apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have hz : U t = 0 := by
    by_contra hn
    exact ht (hU.2 hn)
  simp [hz]
private lemma agent4PoissonFinal_summable (f : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℤ => f (n : ℝ)) := by
  apply summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : 1 < (2:ℝ)))
  convert (f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite using 1 <;>
    simp [Function.comp_def, Real.norm_eq_abs]

private lemma agent4PoissonFinal_schwartz (U : ℝ → ℂ) (hU : IsSmoothCutoff U)
    (N q : ℝ) (hN : 0 < N) (hq : 0 < q) (δ θ : ℝ) :
    ∃ f : SchwartzMap ℝ ℂ, ∀ t, f t =
      U (q*t/N) * expTwoPiI (δ*(q*t)^2+θ*(q*t)) := by
  let g := fun t : ℝ => U (q*t/N) * expTwoPiI (δ*(q*t)^2+θ*(q*t))
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
    apply ContDiff.mul
    · exact hU.1.comp (by fun_prop)
    · unfold expTwoPiI
      apply Complex.contDiff_exp.comp
      apply ContDiff.mul contDiff_const
      exact Complex.ofRealCLM.contDiff.comp
        ((contDiff_const.mul ((contDiff_const.mul contDiff_id).pow 2)).add
          (contDiff_const.mul (contDiff_const.mul contDiff_id)))
  have hs : HasCompactSupport g := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc : IsCompact (Set.Icc (-2*N/q) (2*N/q)))
    intro t ht
    have hn : U (q*t/N) ≠ 0 := by
      intro hz
      exact ht (by simp [g, hz])
    obtain ⟨hlo,hhi⟩ := hU.2 hn
    constructor
    · apply (div_le_iff₀ hq).2
      have := (le_div_iff₀ hN).1 hlo
      nlinarith
    · apply (le_div_iff₀ hq).2
      have := (div_le_iff₀ hN).1 hhi
      nlinarith
  exact ⟨hs.toSchwartzMap hc, fun _ => rfl⟩

private lemma agent4PoissonFinal_fourier (U : ℝ → ℂ)
    (N q : ℝ) (hN : 0 < N) (hq : 0 < q)
    (δ θ l : ℝ) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ t, f t = U (q*t/N) * expTwoPiI (δ*(q*t)^2+θ*(q*t))) :
    (FourierTransform.fourier f) l =
      ((N/q : ℝ) : ℂ) * oscIntegralW U (δ*N^2) (N*(θ-l/q)) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  have he (t : ℝ) :
      Complex.exp (((-2*Real.pi*t*l : ℝ) : ℂ)*Complex.I) • f t =
      U ((q/N)*t) *
        expTwoPiI ((δ*N^2)*((q/N)*t)^2 + (N*(θ-l/q))*((q/N)*t)) := by
    rw [hf]
    have hex :
        Complex.exp (((-2*Real.pi*t*l : ℝ) : ℂ)*Complex.I) = expTwoPiI (-t*l) := by
      unfold expTwoPiI
      congr 1
      push_cast
      ring
    rw [hex, smul_eq_mul, mul_left_comm, ← onb_exp_add]
    congr 2
    · ring
    · field_simp
      <;> ring
  simp_rw [he]
  rw [MeasureTheory.Measure.integral_comp_mul_left
    (fun s : ℝ => U s * expTwoPiI (δ*N^2*s^2 + N*(θ-l/q)*s)) (q/N)]
  rw [abs_of_pos (inv_pos.mpr (div_pos hq hN))]
  simp only [inv_div, Complex.real_smul, Complex.ofReal_div]
  rfl

private lemma agent4PoissonFinal_residue
    (q : ℕ) (hq : 0 < q) (f : ℤ → ℂ) (hf : Summable f) :
    (∑' n, f n) = ∑ x : Fin q, ∑' m : ℤ, f ((x.val : ℤ)+(q : ℤ)*m) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let e : Fin q × ℤ ≃ ℤ := (Equiv.prodComm _ _).trans (Int.divModEquiv q).symm
  have hs : Summable (fun p : Fin q × ℤ => f (e p)) := e.summable_iff.mpr hf
  calc
    _ = ∑' p : Fin q × ℤ, f (e p) := (e.tsum_eq f).symm
    _ = _ := by
      rw [hs.tsum_prod, tsum_fintype]
      simp [e, Int.divModEquiv_symm_apply, add_comm, mul_comm]

private lemma agent4PoissonFinal_twist (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    Summable (fun l : ℤ => (FourierTransform.fourier f) (l : ℝ) *
      expTwoPiI ((l : ℝ)*x)) := by
  apply (agent4PoissonFinal_summable (FourierTransform.fourier f)).norm.of_norm_bounded
  intro l
  simp only [norm_mul, LocalizedFourierFinal.FourierMassBounds.exp_norm,
    mul_one, le_refl]

private lemma agent4PoissonFinal_class (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (∑' m : ℤ, f (x+(m : ℝ))) =
      ∑' l : ℤ, (FourierTransform.fourier f) (l : ℝ) * expTwoPiI ((l : ℝ)*x) := by
  rw [f.tsum_eq_tsum_fourier]
  apply tsum_congr
  intro l
  congr 1
  rw [fourier_coe_apply]
  unfold expTwoPiI
  push_cast
  simp only [div_one]
  congr 1
  ring

private lemma agent4PoissonFinal_gauss_collect
    (a b : ℤ) (q : ℕ) (hq : 0 < q) (l : ℤ) :
    (∑ x : Fin q, quadPhase a b q hq (x.val : ℤ) *
      expTwoPiI ((l : ℝ)*((x.val : ℝ)/(q : ℝ)))) =
      quadGaussSum a (b+l) q hq := by
  unfold quadGaussSum
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro x hx
  unfold quadPhase
  rw [← onb_exp_add]
  congr 1
  push_cast
  ring

private lemma agent4PoissonFinal_phase (U : ℝ → ℂ) (N : ℝ) (q : ℕ) (hq : 0 < q)
    (δ θ : ℝ) (a b : ℤ) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ t, f t = U ((q : ℝ)*t/N) *
      expTwoPiI (δ*((q : ℝ)*t)^2+θ*((q : ℝ)*t)))
    (x : Fin q) (m : ℤ) :
    expTwoPiI (((a : ℝ)/(q : ℝ)+δ)*(((x.val : ℤ)+(q : ℤ)*m : ℤ) : ℝ)^2 +
      ((b : ℝ)/(q : ℝ)+θ)*(((x.val : ℤ)+(q : ℤ)*m : ℤ) : ℝ)) *
        U ((((x.val : ℤ)+(q : ℤ)*m : ℤ) : ℝ)/N) =
      quadPhase a b q hq (x.val : ℤ) * f ((x.val : ℝ)/(q : ℝ)+(m : ℝ)) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have he (n : ℤ) :
      expTwoPiI (((a : ℝ)/(q : ℝ)+δ)*(n : ℝ)^2 +
        ((b : ℝ)/(q : ℝ)+θ)*(n : ℝ)) =
        quadPhase a b q hq n * expTwoPiI (δ*(n : ℝ)^2+θ*(n : ℝ)) := by
    unfold quadPhase
    rw [← onb_exp_add]
    congr 1
    push_cast
    ring
  rw [he, quadPhase_of_modEq a b q hq _ _ Int.modEq_add_fac_self, hf]
  have ht : (q : ℝ)*((x.val : ℝ)/(q : ℝ)+(m : ℝ)) =
      (((x.val : ℤ)+(q : ℤ)*m : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [ht]
  ring

/-- **Poisson summation for a smoothly truncated quadratic exponential sum**
(first half of Lemma `lem:poisson`).  For a smooth cutoff `U` supported in `[-2,2]`,
any `N ≥ 1`, any modulus `q ≥ 1`, any `δ, θ ∈ ℝ` and any `a, b ∈ ℤ`,
`∑_{n ∈ ℤ} e((a/q + δ) n² + (b/q + θ) n) U(n/N)
  = (N/q) ∑_{ℓ ∈ ℤ} G(a, b+ℓ; q) W_U(δN²; N(θ - ℓ/q))`,
the family on the right being summable. -/
theorem lem_poisson_summation (U : ℝ → ℂ) (hU : IsSmoothCutoff U)
    (N : ℝ) (hN : 1 ≤ N) (q : ℕ) (hq : 0 < q)
    (δ θ : ℝ) (a b : ℤ) :
    Summable (fun l : ℤ =>
        quadGaussSum a (b + l) q hq *
          oscIntegralW U (δ * N ^ 2) (N * (θ - (l : ℝ) / (q : ℝ)))) ∧
      ∑' n : ℤ,
          expTwoPiI (((a : ℝ) / (q : ℝ) + δ) * (n : ℝ) ^ 2 +
            ((b : ℝ) / (q : ℝ) + θ) * (n : ℝ)) * U ((n : ℝ) / N) =
        ((N : ℂ) / (q : ℂ)) *
          ∑' l : ℤ,
            quadGaussSum a (b + l) q hq *
              oscIntegralW U (δ * N ^ 2) (N * (θ - (l : ℝ) / (q : ℝ))) := by
  classical
  have hNp : 0 < N := by linarith
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨f, hf⟩ := agent4PoissonFinal_schwartz U hU N q hNp hqp δ θ
  let F (l : ℤ) := (FourierTransform.fourier f) (l : ℝ)
  let W (l : ℤ) := oscIntegralW U (δ*N^2) (N*(θ-(l : ℝ)/q))
  let c : ℂ := (N : ℂ)/(q : ℂ)
  have hc : c ≠ 0 :=
    div_ne_zero (by exact_mod_cast hNp.ne') (by exact_mod_cast hq.ne')
  have hFW (l : ℤ) : F l = c * W l := by
    simpa only [F, W, c, Complex.ofReal_div, Complex.ofReal_natCast] using
      agent4PoissonFinal_fourier U N q hNp hqp δ θ l f hf
  let H (x : Fin q) (l : ℤ) :=
    quadPhase a b q hq (x.val : ℤ) *
      (F l * expTwoPiI ((l : ℝ)*((x.val : ℝ)/(q : ℝ))))
  have hH (x : Fin q) : Summable (H x) :=
    (agent4PoissonFinal_twist f ((x.val : ℝ)/(q : ℝ))).mul_left _
  have hcollect (l : ℤ) : (∑ x : Fin q, H x l) =
      quadGaussSum a (b+l) q hq * F l := by
    rw [← agent4PoissonFinal_gauss_collect a b q hq l, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [H]
    ring
  have hsum : Summable (fun l : ℤ => quadGaussSum a (b+l) q hq * F l) := by
    simpa only [hcollect] using
      summable_sum (fun x (_ : x ∈ (Finset.univ : Finset (Fin q))) => hH x)
  have htarget : Summable (fun l : ℤ => quadGaussSum a (b+l) q hq * W l) := by
    convert hsum.mul_left c⁻¹ using 1
    funext l
    rw [hFW]
    field_simp
  refine ⟨htarget, ?_⟩
  obtain ⟨g,hg⟩ := agent4PoissonFinal_schwartz U hU N 1 hNp (by norm_num)
    ((a : ℝ)/(q : ℝ)+δ) ((b : ℝ)/(q : ℝ)+θ)
  have hgS : Summable (fun n : ℤ =>
      expTwoPiI (((a : ℝ)/(q : ℝ)+δ)*(n : ℝ)^2 +
        ((b : ℝ)/(q : ℝ)+θ)*(n : ℝ)) * U ((n : ℝ)/N)) := by
    simpa only [hg, one_mul, mul_one, mul_comm] using agent4PoissonFinal_summable g
  rw [agent4PoissonFinal_residue q hq _ hgS]
  simp_rw [agent4PoissonFinal_phase U N q hq δ θ a b f hf,
    tsum_mul_left, agent4PoissonFinal_class]
  change (∑ x : Fin q, quadPhase a b q hq (x.val : ℤ) *
    ∑' l : ℤ, F l * expTwoPiI ((l : ℝ)*((x.val : ℝ)/(q : ℝ)))) = _
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum
    (fun x (_ : x ∈ (Finset.univ : Finset (Fin q))) => hH x)]
  simp_rw [hcollect, hFW]
  apply tsum_congr
  intro l
  dsimp [c, W]
  ring
private lemma agent4Decay_supp (U : ℝ → ℂ) (hU : IsSmoothCutoff U) :
    HasCompactSupport U :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc hU.2

private lemma agent4Decay_l1 (U : ℝ → ℂ) (hU : IsSmoothCutoff U) :
    (∫ t : ℝ, ‖U t‖) ≤ 4 * (∫ t : ℝ, ‖deriv U t‖) := by
  have hs := agent4Decay_supp U hU
  have hd := (contDiff_infty_iff_deriv.mp hU.1).2
  have hi : MeasureTheory.Integrable (deriv U) :=
    hd.continuous.integrable_of_hasCompactSupport hs.deriv
  have hb (t : ℝ) : ‖U t‖ ≤ ∫ x : ℝ, ‖deriv U x‖ := by
    rw [← HasCompactSupport.integral_Iic_deriv_eq (hU.1.of_le (by norm_num)) hs t]
    exact (MeasureTheory.norm_integral_le_integral_norm _).trans
      (MeasureTheory.integral_mono_measure MeasureTheory.Measure.restrict_le_self
        (MeasureTheory.ae_of_all _ (fun _ => norm_nonneg _)) hi.norm)
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Icc (-2 : ℝ) 2) (fun t ht => by
      have hz : U t = 0 := by
        by_contra hn
        exact ht (hU.2 hn)
      simp [hz])]
  calc
    _ ≤ ∫ t in Set.Icc (-2 : ℝ) 2, (∫ x : ℝ, ‖deriv U x‖) :=
      MeasureTheory.integral_mono
        ((hU.1.continuous.integrable_of_hasCompactSupport hs).norm.restrict)
        (MeasureTheory.integrableOn_const (by norm_num)) hb
    _ = _ := by norm_num [MeasureTheory.integral_const, Real.volume_Icc]

private lemma agent4Decay_ft_norm (f : ℝ → ℂ) (x : ℝ) :
    ‖FourierTransform.fourier f x‖ ≤ ∫ t : ℝ, ‖f t‖ := by
  rw [Real.fourier_eq]
  exact (MeasureTheory.norm_integral_le_integral_norm _).trans_eq
    (by simp only [Circle.norm_smul])

private lemma agent4Decay_ft_decay (f : ℝ → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hs : HasCompactSupport f) (x : ℝ) :
    (1 + |x|^2) * ‖FourierTransform.fourier f x‖ ≤
      (∫ t : ℝ, ‖f t‖) + (∫ t : ℝ, ‖deriv (deriv f) t‖) := by
  have h1 := (contDiff_infty_iff_deriv.mp hf).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  have hi : MeasureTheory.Integrable f :=
    hf.continuous.integrable_of_hasCompactSupport hs
  have hi1 : MeasureTheory.Integrable (deriv f) :=
    h1.continuous.integrable_of_hasCompactSupport hs.deriv
  have hi2 : MeasureTheory.Integrable (deriv (deriv f)) :=
    h2.continuous.integrable_of_hasCompactSupport hs.deriv.deriv
  have he := congrFun
    (Real.fourier_deriv hi1 (contDiff_infty_iff_deriv.mp h1).1 hi2) x
  rw [Real.fourier_deriv hi (contDiff_infty_iff_deriv.mp hf).1 hi1] at he
  have hn := congrArg norm he
  simp only [smul_eq_mul, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_ofNat, abs_of_pos Real.pi_pos, mul_one] at hn
  have hb := agent4Decay_ft_norm (deriv (deriv f)) x
  rw [hn] at hb
  have hp : 1 ≤ (2 * Real.pi)^2 := by nlinarith [Real.pi_gt_three]
  have hnon : 0 ≤ |x|^2 * ‖FourierTransform.fourier f x‖ := by positivity
  have hbig := mul_nonneg (sub_nonneg.mpr hp) hnon
  have hzero := agent4Decay_ft_norm f x
  nlinarith

private lemma agent4Decay_phase (lam t : ℝ) :
    HasDerivAt (fun s : ℝ => expTwoPiI (lam*s^2))
      ((4 * (Real.pi : ℂ) * Complex.I * (lam : ℂ)) *
        (t : ℂ) * expTwoPiI (lam*t^2)) t := by
  convert ((((hasDerivAt_id t).pow 2).const_mul lam).ofReal_comp.const_mul
    (2 * (Real.pi : ℂ) * Complex.I)).cexp using 1 <;>
    (try funext s) <;>
    simp only [expTwoPiI, Pi.pow_apply, Pi.mul_apply, id_eq, Complex.ofReal_one] <;>
    push_cast <;> ring

private lemma agent4Decay_phase_second (lam t : ℝ) :
    let a : ℂ := 4 * (Real.pi : ℂ) * Complex.I * (lam : ℂ)
    HasDerivAt (fun s : ℝ => a * (s : ℂ) * expTwoPiI (lam*s^2))
      ((a + (a * (t : ℂ))^2) * expTwoPiI (lam*t^2)) t := by
  dsimp only
  convert (((hasDerivAt_id t).ofReal_comp.const_mul
    (4 * (Real.pi : ℂ) * Complex.I * (lam : ℂ))).mul
      (agent4Decay_phase lam t)) using 1 <;>
    (try funext s) <;> dsimp only [id_eq, Pi.mul_apply] <;> push_cast <;> ring

private lemma agent4Decay_amp_deriv2 (U : ℝ → ℂ) (hU : IsSmoothCutoff U)
    (lam t : ℝ) :
    let a : ℂ := 4 * (Real.pi : ℂ) * Complex.I * (lam : ℂ)
    deriv (deriv (fun s : ℝ => U s * expTwoPiI (lam*s^2))) t =
      deriv (deriv U) t * expTwoPiI (lam*t^2) +
      2 * deriv U t * (a * (t : ℂ) * expTwoPiI (lam*t^2)) +
      U t * ((a + (a * (t : ℂ))^2) * expTwoPiI (lam*t^2)) := by
  dsimp only
  have hd := (contDiff_infty_iff_deriv.mp hU.1).1
  have hd' := (contDiff_infty_iff_deriv.mp
    (contDiff_infty_iff_deriv.mp hU.1).2).1
  have he : deriv (fun s : ℝ => U s * expTwoPiI (lam*s^2)) =
      fun s => deriv U s * expTwoPiI (lam*s^2) +
        U s * ((4 * (Real.pi : ℂ) * Complex.I * (lam : ℂ)) *
          (s : ℂ) * expTwoPiI (lam*s^2)) := by
    funext s
    exact ((hd s).hasDerivAt.mul (agent4Decay_phase lam s)).deriv
  rw [he]
  convert (((hd' t).hasDerivAt.mul (agent4Decay_phase lam t)).add
    ((hd t).hasDerivAt.mul (agent4Decay_phase_second lam t))).deriv using 1 <;> ring

private lemma agent4Decay_norm_alg (u0 u1 u2 e a : ℂ) (t P : ℝ)
    (he : ‖e‖=1) (ha : ‖a‖≤P) (ht : |t|≤2) :
    ‖u2*e + 2*u1*(a*(t:ℂ)*e) + u0*((a+(a*(t:ℂ))^2)*e)‖ ≤
      ‖u2‖+4*P*‖u1‖+(P+4*P^2)*‖u0‖ := by
  have hP : 0 ≤ P := (norm_nonneg a).trans ha
  have hat : ‖a*(t:ℂ)‖ ≤ 2*P := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [mul_le_mul ha ht (abs_nonneg t) hP]
  have hc : ‖a+(a*(t:ℂ))^2‖ ≤ P+4*P^2 := by
    apply (norm_add_le _ _).trans
    rw [norm_pow]
    nlinarith [norm_nonneg (a*(t:ℂ))]
  calc
    _ ≤ ‖u2*e‖ + ‖2*u1*(a*(t:ℂ)*e)‖ + ‖u0*((a+(a*(t:ℂ))^2)*e)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖u2‖+2*‖u1‖*‖a*(t:ℂ)‖+‖u0‖*‖a+(a*(t:ℂ))^2‖ := by
      simp only [norm_mul, he, mul_one, Complex.norm_ofNat]
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_left hat (norm_nonneg u1),
        mul_le_mul_of_nonneg_left hc (norm_nonneg u0)]

private lemma agent4Decay_amp_bound (U : ℝ → ℂ) (hU : IsSmoothCutoff U)
    (lam Λ : ℝ) (hl : |lam| ≤ Λ) (t : ℝ) :
    ‖deriv (deriv (fun s : ℝ => U s * expTwoPiI (lam*s^2))) t‖ ≤
      ‖deriv (deriv U) t‖ + 4*(4*Real.pi*Λ)*‖deriv U t‖ +
        ((4*Real.pi*Λ)+4*(4*Real.pi*Λ)^2)*‖U t‖ := by
  rw [agent4Decay_amp_deriv2 U hU lam t]
  by_cases ht : |t| ≤ 2
  · apply agent4Decay_norm_alg _ _ _ _ _ t (4*Real.pi*Λ)
    · exact LocalizedFourierFinal.FourierMassBounds.exp_norm _
    · simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
      exact mul_le_mul_of_nonneg_left hl (by positivity)
    · exact ht
  · have hout : t ∉ Set.Icc (-2 : ℝ) 2 := by
      simpa only [Set.mem_Icc, ← abs_le] using ht
    have hz : U t = 0 := by
      by_contra hn
      exact hout (hU.2 hn)
    have hsub : tsupport U ⊆ Set.Icc (-2 : ℝ) 2 :=
      closure_minimal hU.2 isClosed_Icc
    have hz1 : deriv U t = 0 := by
      by_contra hn
      exact hout (hsub (support_deriv_subset hn))
    simp only [hz, hz1, mul_zero, zero_mul, add_zero,
      norm_mul, LocalizedFourierFinal.FourierMassBounds.exp_norm,
      mul_one, norm_zero, zero_add, le_refl]

private lemma agent4Decay_amp_smooth (U : ℝ → ℂ) (hU : IsSmoothCutoff U)
    (lam : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => U t * expTwoPiI (lam*t^2)) := by
  apply hU.1.mul
  unfold expTwoPiI
  apply Complex.contDiff_exp.comp
  apply ContDiff.mul contDiff_const
  exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_id.pow 2))

private lemma agent4Decay_osc_fourier (U : ℝ → ℂ) (lam xi : ℝ) :
    oscIntegralW U lam xi =
      FourierTransform.fourier (fun t : ℝ => U t * expTwoPiI (lam*t^2)) (-xi) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  have he : Complex.exp (((-2*Real.pi*t*(-xi) : ℝ) : ℂ)*Complex.I) =
      expTwoPiI (xi*t) := by
    unfold expTwoPiI
    congr 1
    push_cast
    ring
  rw [he, smul_eq_mul, mul_left_comm, ← onb_exp_add]
  congr 2
  ring

private lemma agent4Decay_total_bound (U : ℝ → ℂ) (hU : IsSmoothCutoff U)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hl : |lam| ≤ Λ) :
    let P := 4*Real.pi*Λ
    (∫ t : ℝ, ‖U t * expTwoPiI (lam*t^2)‖) +
      (∫ t : ℝ, ‖deriv (deriv (fun s : ℝ => U s * expTwoPiI (lam*s^2))) t‖) ≤
      (5+8*P+16*P^2) *
        (1+(∫ t : ℝ, ‖deriv U t‖)+(∫ t : ℝ, ‖deriv (deriv U) t‖)) := by
  let P := 4*Real.pi*Λ
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hs := agent4Decay_supp U hU
  have hd := (contDiff_infty_iff_deriv.mp hU.1).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have hi : MeasureTheory.Integrable (fun t => ‖U t‖) :=
    (hU.1.continuous.integrable_of_hasCompactSupport hs).norm
  have hi1 : MeasureTheory.Integrable (fun t => ‖deriv U t‖) :=
    (hd.continuous.integrable_of_hasCompactSupport hs.deriv).norm
  have hi2 : MeasureTheory.Integrable (fun t => ‖deriv (deriv U) t‖) :=
    (hdd.continuous.integrable_of_hasCompactSupport hs.deriv.deriv).norm
  have hfs : HasCompactSupport (fun t : ℝ => U t * expTwoPiI (lam*t^2)) := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro t ht
    apply hU.2
    intro hz
    exact ht (by simp [hz])
  have hfd := (contDiff_infty_iff_deriv.mp
    (contDiff_infty_iff_deriv.mp (agent4Decay_amp_smooth U hU lam)).2).2
  have hfi : MeasureTheory.Integrable
      (fun t => ‖deriv (deriv (fun s : ℝ => U s * expTwoPiI (lam*s^2))) t‖) :=
    (hfd.continuous.integrable_of_hasCompactSupport hfs.deriv.deriv).norm
  have hb := MeasureTheory.integral_mono hfi
    ((hi2.add (hi1.const_mul (4*P))).add (hi.const_mul (P+4*P^2)))
    (agent4Decay_amp_bound U hU lam Λ hl)
  simp only [Pi.add_apply] at hb
  have hi21 : MeasureTheory.Integrable
      (fun t => ‖deriv (deriv U) t‖ + 4*P*‖deriv U t‖) :=
    hi2.add (hi1.const_mul (4*P))
  rw [MeasureTheory.integral_add hi21 (hi.const_mul (P+4*P^2)),
    MeasureTheory.integral_add hi2 (hi1.const_mul (4*P)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hb
  simp only [norm_mul, LocalizedFourierFinal.FourierMassBounds.exp_norm, mul_one]
  have h0 := agent4Decay_l1 U hU
  have h1 : 0 ≤ ∫ t : ℝ, ‖deriv U t‖ :=
    MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  have h2 : 0 ≤ ∫ t : ℝ, ‖deriv (deriv U) t‖ :=
    MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  have hc : 0 ≤ P+4*P^2 := by positivity
  have hm := mul_le_mul_of_nonneg_left h0 hc
  change _ ≤ (5+8*P+16*P^2) * (1+_+_)
  nlinarith [mul_nonneg hP h1, mul_nonneg (sq_nonneg P) h1,
    mul_nonneg hP h2, mul_nonneg (sq_nonneg P) h2]

/-- **Decay of the oscillatory integral** (second half of Lemma `lem:poisson`).
For every `Λ ≥ 1` there is a constant `C`, depending only on `Λ`, such that for every
smooth cutoff `U` supported in `[-2,2]`, every `λ` with `|λ| ≤ Λ` and every `ξ ∈ ℝ`,
`|W_U(λ; ξ)| ≤ C · (1 + ‖U'‖_{L¹} + ‖U''‖_{L¹}) / (1 + |ξ|²)`. -/
theorem lem_poisson_decay (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C > 0, ∀ U : ℝ → ℂ, IsSmoothCutoff U →
      ∀ lam : ℝ, |lam| ≤ Λ → ∀ xi : ℝ,
        ‖oscIntegralW U lam xi‖ ≤
          C * (1 + (∫ t : ℝ, ‖deriv U t‖) + (∫ t : ℝ, ‖deriv (deriv U) t‖)) /
            (1 + |xi| ^ 2) := by
  let P := 4*Real.pi*Λ
  refine ⟨5+8*P+16*P^2, by dsimp [P]; positivity, ?_⟩
  intro U hU lam hlam xi
  have hs : HasCompactSupport (fun t : ℝ => U t * expTwoPiI (lam*t^2)) := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro t ht
    apply hU.2
    intro hz
    exact ht (by simp [hz])
  have hb := (agent4Decay_ft_decay _ (agent4Decay_amp_smooth U hU lam) hs (-xi)).trans
    (agent4Decay_total_bound U hU lam Λ hΛ hlam)
  rw [abs_neg, ← agent4Decay_osc_fourier] at hb
  apply (le_div_iff₀ (by positivity : 0 < 1+|xi|^2)).2
  simpa only [P, mul_comm] using hb
private lemma agent4Gauss_cancel_unit (a : ℤ) (c q : ℕ)
    (ha : Int.gcd a q = 1) (x : ZMod q) :
    2 * ((c : ZMod q) * (a : ZMod q)) * x = 0 ↔
      ((2*c : ℕ) : ZMod q) * x = 0 := by
  have hu : IsUnit (a : ZMod q) :=
    (ZMod.coe_int_isUnit_iff_isCoprime a q).2
      (Int.isCoprime_iff_gcd_eq_one.mpr ha).symm
  rw [show 2 * ((c : ZMod q) * (a : ZMod q)) * x =
    (((2*c : ℕ) : ZMod q) * x) * (a : ZMod q) by push_cast; ring]
  exact hu.mul_left_eq_zero

private lemma agent4Gauss_kernel_card_ok (m q : ℕ) (hq : 0 < q) :
    letI : NeZero q := ⟨hq.ne'⟩
    (Finset.univ.filter (fun x : ZMod q => (m : ZMod q)*x=0)).card ≤
      Nat.gcd m q := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  have he (x : ZMod q) : (Nat.gcd m q) • x = 0 ↔ (m : ZMod q)*x=0 := by
    rw [gcd_nsmul_eq_zero, (ZModModule.char_nsmul_eq_zero q x),
      eq_self, and_true, nsmul_eq_mul]
  have hg : 0 < Nat.gcd m q := Nat.gcd_pos_of_pos_right m hq
  simpa only [he] using
    (IsAddCyclic.card_nsmul_eq_zero_le (α := ZMod q) hg)

private lemma agent4Gauss_gcd_bound (c q : ℕ) (hc : 1 ≤ c) :
    (q : ℝ) * (Nat.gcd (2*c) q : ℝ) ≤ 2*(c : ℝ)*(q : ℝ) := by
  have hg : (Nat.gcd (2*c) q : ℝ) ≤ 2*(c : ℝ) := by
    exact_mod_cast (Nat.gcd_le_left q (show 0 < 2*c by omega))
  nlinarith [mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg (α := ℝ) q)]

private lemma agent4Gauss_square_bound_ok (q : ℕ) [NeZero q] (A B : ZMod q) :
    ‖∑ x : ZMod q, ZMod.stdAddChar (A*x^2+B*x)‖^2 ≤
      (q : ℝ) * ((Finset.univ.filter (fun h : ZMod q => 2*A*h=0)).card : ℝ) := by
  classical
  let ψ : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  have he : ((‖∑ x : ZMod q, ψ (A*x^2+B*x)‖^2 : ℝ) : ℂ) =
      ∑ h : ZMod q, ψ (A*h^2+B*h) * (if 2*A*h=0 then (q : ℂ) else 0) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ z : ZMod q, ∑ x : ZMod q, ψ (A*x^2+B*x-(A*z^2+B*z)) := by
        apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro x hx
        rw [← ψ.map_neg_eq_conj, ← ψ.map_add_eq_mul]
        congr 1
        ring
      _ = ∑ z : ZMod q, ∑ h : ZMod q, ψ (A*h^2+B*h) * ψ (z*(2*A*h)) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [← Equiv.sum_comp (Equiv.addRight z)
          (fun x : ZMod q => ψ (A*x^2+B*x-(A*z^2+B*z)))]
        apply Finset.sum_congr rfl
        intro h hh
        rw [← ψ.map_add_eq_mul]
        congr 1
        change A*(h+z)^2+B*(h+z)-(A*z^2+B*z) = _
        ring
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro h hh
        rw [← Finset.mul_sum,
          AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
        simp [ZMod.card]
  change ‖∑ x : ZMod q, ψ (A*x^2+B*x)‖^2 ≤ _
  calc
    _ = ‖∑ h : ZMod q, ψ (A*h^2+B*h) *
        (if 2*A*h=0 then (q : ℂ) else 0)‖ := by
      rw [← he]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_sq]
    _ ≤ ∑ h : ZMod q, ‖ψ (A*h^2+B*h) *
        (if 2*A*h=0 then (q : ℂ) else 0)‖ := norm_sum_le _ _
    _ = _ := by
      simp [norm_mul, AddChar.norm_apply, apply_ite norm,
        ← Finset.sum_filter, mul_comm]

theorem quadGaussSum_normSq_le_gcd (a b : ℤ) (c q : ℕ) (hc : 1 ≤ c) (hq : 0 < q)
    (ha : Int.gcd a q = 1) :
    ‖quadGaussSum ((c : ℤ) * a) b q hq‖ ^ 2 ≤ (q : ℝ) * (Nat.gcd (2 * c) q : ℝ) ∧
      (q : ℝ) * (Nat.gcd (2 * c) q : ℝ) ≤ 2 * (c : ℝ) * (q : ℝ) := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  refine ⟨?_, agent4Gauss_gcd_bound c q hc⟩
  rw [agent4_quad_sum_zmod]
  simp only [Int.cast_mul, Int.cast_natCast]
  apply (agent4Gauss_square_bound_ok q
    ((c : ZMod q) * (a : ZMod q)) (b : ZMod q)).trans
  simp_rw [agent4Gauss_cancel_unit a c q ha]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
  exact_mod_cast agent4Gauss_kernel_card_ok (2*c) q hq
theorem quadGaussSum_linear_shift (a abar y : ℤ) (c q : ℕ) (hc : 1 ≤ c) (hq : 0 < q)
    (ha : Int.gcd a q = 1) (habar : a * abar ≡ 1 [ZMOD (q : ℤ)]) :
    quadGaussSum ((c : ℤ) * a) (y + 2 * (c : ℤ)) q hq =
      expTwoPiI (-(((y + (c : ℤ)) * abar : ℤ) : ℝ) / (q : ℝ)) *
        quadGaussSum ((c : ℤ) * a) y q hq := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  have hinv : (a : ZMod q) * (abar : ZMod q) = 1 := by
    simpa only [Int.cast_mul, Int.cast_one] using
      (ZMod.intCast_eq_intCast_iff (a * abar) 1 q).2 habar
  have hphase (x : ZMod q) :
      (c : ZMod q) * a * (x - abar)^2 + (y + 2 * (c : ZMod q)) * (x - abar) =
        -((y + (c : ZMod q)) * abar) + ((c : ZMod q) * a * x^2 + y*x) := by
    linear_combination (c : ZMod q) * ((abar : ZMod q) - 2*x) * hinv
  have hconst : ZMod.stdAddChar (-(((y + (c : ℤ)) * abar : ℤ) : ZMod q)) =
      expTwoPiI (-(((y + (c : ℤ)) * abar : ℤ) : ℝ) / (q : ℝ)) := by
    rw [← Int.cast_neg, ZMod.stdAddChar_coe]
    unfold expTwoPiI
    push_cast
    congr 1
    ring
  rw [agent4_quad_sum_zmod, agent4_quad_sum_zmod]
  simp only [Int.cast_mul, Int.cast_add, Int.cast_ofNat, Int.cast_natCast]
  rw [← Equiv.sum_comp (Equiv.subRight (abar : ZMod q))]
  simp only [Equiv.subRight_apply, hphase, AddChar.map_add_eq_mul]
  rw [← Finset.mul_sum]
  rw [show -(((y + (c : ℤ)) * abar : ℤ) : ZMod q) =
      -(((y : ZMod q) + c) * abar) by push_cast; rfl] at hconst
  rw [hconst]
  push_cast
  rfl
noncomputable def gaussPhasePhi (a abar : ℤ) (c q : ℕ) (hq : 0 < q) (x : ℤ) : ℂ :=
  (Real.sqrt (q : ℝ) : ℂ)⁻¹ * quadGaussSum ((c : ℤ) * a) x q hq *
    expTwoPiI ((abar : ℝ) * (x : ℝ) ^ 2 / (4 * (c : ℝ) * (q : ℝ)))

theorem lem_gaussphase (a abar : ℤ) (c q : ℕ) (hc : 1 ≤ c) (hq : 0 < q)
    (ha : Int.gcd a q = 1) (habar : a * abar ≡ 1 [ZMOD (q : ℤ)]) :
    (∀ b : ℤ,
        quadGaussSum ((c : ℤ) * a) b q hq =
          (Real.sqrt (q : ℝ) : ℂ) * gaussPhasePhi a abar c q hq b *
            expTwoPiI (-((abar : ℝ) * (b : ℝ) ^ 2) / (4 * (c : ℝ) * (q : ℝ)))) ∧
      (∀ x : ℤ,
        gaussPhasePhi a abar c q hq (x + 2 * (c : ℤ)) = gaussPhasePhi a abar c q hq x) ∧
      (∀ x : ℤ, ‖gaussPhasePhi a abar c q hq x‖ ≤ Real.sqrt (2 * (c : ℝ))) := by
  have hp : (0 : ℝ) < q := by exact_mod_cast hq
  have hs : (Real.sqrt (q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hp).ne'
  refine ⟨?_, ?_, ?_⟩
  · intro b
    unfold gaussPhasePhi
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hs, one_mul, mul_assoc,
      ← onb_exp_add]
    rw [show (abar : ℝ) * (b : ℝ)^2 / (4*(c : ℝ)*(q : ℝ)) +
      -((abar : ℝ)*(b : ℝ)^2)/(4*(c : ℝ)*(q : ℝ)) = 0 by ring]
    simp [expTwoPiI]
  · intro x
    have hc0 : (c : ℝ) ≠ 0 := by
      exact_mod_cast (show c ≠ 0 by omega)
    have hq0 : (q : ℝ) ≠ 0 := hp.ne'
    have he :
        -(((x + (c : ℤ)) * abar : ℤ) : ℝ) / (q : ℝ) +
          (abar : ℝ) * ((x + 2 * (c : ℤ) : ℤ) : ℝ)^2 /
            (4 * (c : ℝ) * (q : ℝ)) =
        (abar : ℝ) * (x : ℝ)^2 / (4 * (c : ℝ) * (q : ℝ)) := by
      push_cast
      field_simp [hc0, hq0]
      <;> ring
    unfold gaussPhasePhi
    rw [quadGaussSum_linear_shift a abar x c q hc hq ha habar]
    calc
      _ = (Real.sqrt (q : ℝ) : ℂ)⁻¹ *
          quadGaussSum ((c : ℤ) * a) x q hq *
          (expTwoPiI (-(((x + (c : ℤ)) * abar : ℤ) : ℝ) / (q : ℝ)) *
            expTwoPiI ((abar : ℝ) * ((x + 2 * (c : ℤ) : ℤ) : ℝ)^2 /
              (4 * (c : ℝ) * (q : ℝ)))) := by ring
      _ = _ := by rw [← onb_exp_add, he]
  · intro x
    have hb := quadGaussSum_normSq_le_gcd a x c q hc hq ha
    have hg : ‖quadGaussSum ((c : ℤ)*a) x q hq‖ ≤
        Real.sqrt (q : ℝ) * Real.sqrt (2*(c : ℝ)) := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      rw [mul_pow, Real.sq_sqrt hp.le, Real.sq_sqrt (by positivity)]
      nlinarith [hb.1.trans hb.2]
    simp only [gaussPhasePhi, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      LocalizedFourierFinal.FourierMassBounds.exp_norm, mul_one]
    exact (inv_mul_le_iff₀ (Real.sqrt_pos.mpr hp)).2 hg
namespace ContFracConvergents

noncomputable def cfPartQuot (α : ℝ) : ℕ → ℝ
  | 0 => (GenContFract.of α).h
  | i + 1 => ((GenContFract.of α).partDens.get? i).getD 0

noncomputable def finCFEval : List ℝ → ℝ
  | [] => 0
  | b :: bs => 1 / (b + finCFEval bs)

noncomputable def cfRevQuots (α : ℝ) (i : ℕ) : List ℝ :=
  ((List.range i).map fun j => cfPartQuot α (j + 1)).reverse

private lemma agent4_den_pos (α : ℝ) (n : ℕ) :
    0 < (GenContFract.of α).dens n := by
  induction n with
  | zero => simp [GenContFract.zeroth_den_eq_one]
  | succ n ih => exact ih.trans_le GenContFract.of_den_mono

private lemma agent4_pair_exists (α : ℝ) (hα : Irrational α) (i : ℕ) :
    ∃ p, (GenContFract.of α).s.get? i = some p := by
  cases hs : (GenContFract.of α).s.get? i with
  | none =>
    obtain ⟨q, hq⟩ := GenContFract.exists_rat_eq_of_terminates
      ⟨i, (GenContFract.terminatedAt_iff_s_none).2 hs⟩
    exact False.elim (hα ⟨q, hq.symm⟩)
  | some p => exact ⟨p, rfl⟩

theorem cf_convergent_determinant (α : ℝ) (hα : Irrational α) (i : ℕ) :
    ((GenContFract.of α).contsAux (i + 1)).a * ((GenContFract.of α).contsAux i).b -
        ((GenContFract.of α).contsAux i).a * ((GenContFract.of α).contsAux (i + 1)).b
      = (-1) ^ (i + 1) := by
  induction i with
  | zero =>
    simp [GenContFract.first_contAux_eq_h_one, GenContFract.zeroth_contAux_eq_one_zero]
  | succ i ih =>
    obtain ⟨p, hs⟩ := agent4_pair_exists α hα i
    have hp := GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a hs)
    rw [GenContFract.contsAux_recurrence hs rfl rfl]
    simp only [hp, one_mul]
    rw [pow_succ]
    nlinarith [ih]

private lemma agent4_pair (α : ℝ) (hα : Irrational α) (i : ℕ) :
    ∃ p, (GenContFract.of α).s.get? i = some p ∧ p.a = 1 ∧
      p.b = cfPartQuot α (i+1) := by
  obtain ⟨p, hs⟩ := agent4_pair_exists α hα i
  refine ⟨p, hs, GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a hs), ?_⟩
  simp [cfPartQuot, GenContFract.partDen_eq_s_b hs]

private lemma agent4_rev_succ (α : ℝ) (i : ℕ) :
    cfRevQuots α (i+1) = cfPartQuot α (i+1) :: cfRevQuots α i := by
  simp [cfRevQuots, List.range_succ, List.map_append, List.reverse_append]

theorem cf_den_ratio_eq_finCFEval_reverse (α : ℝ) (hα : Irrational α) (m : ℕ) :
    (GenContFract.of α).dens m / (GenContFract.of α).dens (m + 1)
      = finCFEval (cfRevQuots α (m + 1)) := by
  induction m with
  | zero =>
    obtain ⟨p, hs, ha, hb⟩ := agent4_pair α hα 0
    rw [GenContFract.zeroth_den_eq_one, GenContFract.first_den_eq hs, hb]
    simp [cfRevQuots, finCFEval]
  | succ m ih =>
    obtain ⟨p, hs, ha, hb⟩ := agent4_pair α hα (m+1)
    have hr := GenContFract.dens_recurrence hs rfl rfl
    rw [ha, hb, one_mul] at hr
    rw [agent4_rev_succ, finCFEval, ← ih, hr]
    rw [add_div' _ _ _ (agent4_den_pos α (m+1)).ne', one_div_div]

end ContFracConvergents
namespace ContFracConvergents

structure IsIntConvergentData (α : ℝ) (s : ℕ) (p q p' q' : ℤ) : Prop where
  num_eq : (p : ℝ) = (GenContFract.of α).nums s
  den_eq : (q : ℝ) = (GenContFract.of α).dens s
  num_pred_eq : (p' : ℝ) = (GenContFract.of α).nums (s - 1)
  den_pred_eq : (q' : ℝ) = (GenContFract.of α).dens (s - 1)

theorem cf_det_relation_int (α : ℝ) (hα : Irrational α) (s : ℕ) (hs : 1 ≤ s)
    (p q p' q' : ℤ) (h : IsIntConvergentData α s p q p' q') :
    p * q' - p' * q = (-1) ^ (s - 1) := by
  have ht := cf_convergent_determinant α hα s
  have he : s - 1 + 1 = s := by omega
  have hr : (p : ℝ) * q' - p' * q = (-1 : ℝ) ^ (s - 1) := by
    rw [h.num_eq, h.den_eq, h.num_pred_eq, h.den_pred_eq]
    simp only [GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b,
      GenContFract.nth_cont_eq_succ_nth_contAux, he]
    rw [show s + 1 = (s - 1) + 1 + 1 by omega, pow_succ, pow_succ] at ht
    simpa only [he, mul_neg, mul_one, neg_neg] using ht
  exact_mod_cast hr

theorem cf_inv_pred_den_and_contFrac (α : ℝ) (hα : Irrational α) (s : ℕ) (hs : 1 ≤ s)
    (p q p' q' : ℤ) (h : IsIntConvergentData α s p q p' q')
    (abar : ℤ) (habar : p * abar ≡ 1 [ZMOD q]) :
    (abar ≡ q' [ZMOD q] ∨ abar ≡ -q' [ZMOD q]) ∧
      (q' : ℝ) / (q : ℝ) = finCFEval (cfRevQuots α s) := by
  constructor
  · have hdet := cf_det_relation_int α hα s hs p q p' q' h
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp habar
    rcases neg_one_pow_eq_or ℤ (s - 1) with he | he
    · rw [he] at hdet
      left
      apply Int.modEq_iff_dvd.mpr
      refine ⟨t * q' + abar * p', ?_⟩
      linear_combination abar * hdet + q' * ht
    · rw [he] at hdet
      right
      apply Int.modEq_iff_dvd.mpr
      refine ⟨-(t * q' + abar * p'), ?_⟩
      linear_combination -abar * hdet - q' * ht
  · rw [h.den_pred_eq, h.den_eq]
    simpa only [Nat.sub_add_cancel hs] using
      cf_den_ratio_eq_finCFEval_reverse α hα (s - 1)

theorem cf_pred_den_div_den_eq_finCFEval (α : ℝ) (hα : Irrational α) (s : ℕ) (hs : 1 ≤ s) :
    (GenContFract.of α).dens (s - 1) / (GenContFract.of α).dens s =
      finCFEval (cfRevQuots α s) := by
  simpa only [Nat.sub_add_cancel hs] using
    cf_den_ratio_eq_finCFEval_reverse α hα (s - 1)

end ContFracConvergents
/-- The distance to the nearest integer. -/
noncomputable def intDist (x : ℝ) : ℝ := |x - round x|

private lemma agent4_best_core (Q R e f r : ℝ) (hQ : 0 < Q) (hR : 0 < R)
    (he : 0 < e) (hf : 0 ≤ f) (hr : 0 < r) (hrR : r < R)
    (u v : ℤ) (hrep : r = (u:ℝ)*Q+(v:ℝ)*R) :
    e ≤ |(u:ℝ)*e-(v:ℝ)*f| := by
  rcases lt_trichotomy u 0 with hu | hu | hu
  · have hu1 : (u:ℝ) ≤ -1 := by exact_mod_cast (show u ≤ -1 by omega)
    have hu0 : (u:ℝ) ≤ 0 := by linarith
    have hv0 : (0:ℝ) ≤ v := by
      by_contra hv
      have hn := mul_nonpos_of_nonpos_of_nonneg hu0 hQ.le
      have hn' := mul_nonpos_of_nonpos_of_nonneg (lt_of_not_ge hv).le hR.le
      linarith
    have hprod := mul_le_mul_of_nonneg_right hu1 he.le
    have hprod' := mul_nonneg hv0 hf
    exact (show e ≤ -((u:ℝ)*e-(v:ℝ)*f) by linarith).trans (neg_le_abs _)
  · subst u
    simp only [Int.cast_zero, zero_mul, zero_add] at hrep
    have hv : 0 < v := by
      by_contra hv
      have hv0 : (v:ℝ) ≤ 0 := by exact_mod_cast (show v ≤ 0 by omega)
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hv0 hR.le]
    have hv1 : (1:ℝ) ≤ v := by exact_mod_cast (show 1 ≤ v by omega)
    nlinarith [mul_le_mul_of_nonneg_right hv1 hR.le]
  · have hu1 : (1:ℝ) ≤ u := by exact_mod_cast (show 1 ≤ u by omega)
    have hu0 : (0:ℝ) ≤ u := by linarith
    have hv0 : (v:ℝ) ≤ 0 := by
      by_contra hv
      have hvz : 0 < v := by exact_mod_cast (lt_of_not_ge hv)
      have hv1 : (1:ℝ) ≤ v := by exact_mod_cast (show 1 ≤ v by omega)
      have hn := mul_nonneg hu0 hQ.le
      have hn' := mul_le_mul_of_nonneg_right hv1 hR.le
      linarith
    have hprod := mul_le_mul_of_nonneg_right hu1 he.le
    have hprod' := mul_nonpos_of_nonpos_of_nonneg hv0 hf
    exact (show e ≤ (u:ℝ)*e-(v:ℝ)*f by linarith).trans (le_abs_self _)

private lemma agent4_rational_errors_final (P Q : ℕ → ℤ) (b : ℕ → ℝ)
    (hQ : ∀ j, 0 < (Q j : ℝ)) (hb : ∀ j, 1 ≤ b j)
    (hrecP : ∀ j, (P (j+2) : ℝ) = b (j+1)*(P (j+1):ℝ)+P j)
    (hrecQ : ∀ j, (Q (j+2) : ℝ) = b (j+1)*(Q (j+1):ℝ)+Q j)
    (hdet : ∀ j, P (j+1)*Q j-P j*Q (j+1)=(-1:ℤ)^j)
    (s : ℕ) (hs : 1 ≤ s) :
    let x : ℝ := (P s : ℝ)/Q s
    let E : ℕ → ℝ := fun j => (-1:ℝ)^j*((Q j:ℝ)*x-P j)
    (∀ j, E j*(Q (j+1):ℝ)+E (j+1)*(Q j:ℝ)=1) ∧
    ∀ j, j < s → 0 < E j ∧ 0 ≤ E (j+1) ∧ E (j+1) ≤ E j := by
  dsimp only
  let x : ℝ := (P s : ℝ)/Q s
  let E : ℕ → ℝ := fun j => (-1:ℝ)^j*((Q j:ℝ)*x-P j)
  have hsq (j : ℕ) : (-1:ℝ)^j * (-1:ℝ)^j = 1 := by
    rw [← mul_pow]
    norm_num
  have hd (j : ℕ) : E j*(Q (j+1):ℝ)+E (j+1)*(Q j:ℝ)=1 := by
    have ht : (P (j+1):ℝ)*Q j-(P j:ℝ)*Q (j+1)=(-1:ℝ)^j := by
      exact_mod_cast hdet j
    calc
      _ = (-1:ℝ)^j*((P (j+1):ℝ)*Q j-(P j:ℝ)*Q (j+1)) := by
        dsimp [E]
        rw [pow_succ]
        ring
      _ = 1 := by rw [ht, hsq]
  refine ⟨hd, ?_⟩
  have hz : E s = 0 := by
    dsimp [E, x]
    field_simp [(hQ s).ne']
    ring
  have hr (j : ℕ) : E j = b (j+1)*E (j+1)+E (j+2) := by
    dsimp [E]
    rw [hrecP, hrecQ, show j+2=j+1+1 by omega, pow_succ, pow_succ]
    ring
  have hall : ∀ j, j ≤ s-1 → 0 < E j ∧ 0 ≤ E (j+1) ∧ E (j+1) ≤ E j := by
    intro j hj
    apply Nat.decreasingInduction (n := s-1) (motive := fun j _ =>
      0 < E j ∧ 0 ≤ E (j+1) ∧ E (j+1) ≤ E j) ?_ ?_ hj
    · intro i hi ih
      have hm := mul_le_mul_of_nonneg_right (hb (i+1)) ih.1.le
      rw [one_mul] at hm
      have he := hr i
      exact ⟨by linarith [ih.2.1], ih.1.le, by linarith [ih.2.1]⟩
    · have he : s-1+1=s := by omega
      have hh := hd (s-1)
      rw [he, hz, zero_mul, add_zero] at hh
      have hpos : 0 < E (s-1) := by nlinarith [hQ s]
      exact ⟨hpos, by simpa [he, hz], by simpa [he, hz] using hpos.le⟩
  intro j hj
  exact hall j (by omega)

private lemma agent4_crossing (Q : ℕ → ℤ) (r : ℤ) (h0 : Q 0 ≤ r)
    (s : ℕ) (hs : r < Q s) : ∃ j, j < s ∧ Q j ≤ r ∧ r < Q (j+1) := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases h : r < Q s
    · obtain ⟨j,hj,hlo,hhi⟩ := ih h
      exact ⟨j, by omega, hlo, hhi⟩
    · exact ⟨s, by omega, by omega, hs⟩

private lemma agent4_rational_lower_ok (P Q : ℕ → ℤ) (b : ℕ → ℝ)
    (hQ : ∀ j, 0 < (Q j : ℝ)) (hQ0 : Q 0 = 1) (hb : ∀ j, 1 ≤ b j)
    (hrecP : ∀ j, (P (j+2) : ℝ) = b (j+1)*(P (j+1):ℝ)+P j)
    (hrecQ : ∀ j, (Q (j+2) : ℝ) = b (j+1)*(Q (j+1):ℝ)+Q j)
    (hdet : ∀ j, P (j+1)*Q j-P j*Q (j+1)=(-1:ℤ)^j)
    (A : ℝ) (hA : 1 ≤ A) (hgrowth : ∀ j, (Q (j+1):ℝ) ≤ (A+1)*(Q j:ℝ))
    (s : ℕ) (hs : 1 ≤ s) (r n : ℤ) (hr : 1 ≤ r) (hrs : r < Q s) :
    1 ≤ (A+2)*(r:ℝ)*|(r:ℝ)*((P s:ℝ)/Q s)-n| := by
  obtain ⟨j,hjs,hjr,hrj⟩ := agent4_crossing Q r (by omega) s hrs
  let x : ℝ := (P s:ℝ)/Q s
  let E : ℕ → ℝ := fun j => (-1:ℝ)^j*((Q j:ℝ)*x-P j)
  have herr := agent4_rational_errors_final P Q b hQ hb hrecP hrecQ hdet s hs
  change (∀ j, E j*(Q (j+1):ℝ)+E (j+1)*(Q j:ℝ)=1) ∧
    ∀ j, j < s → 0 < E j ∧ 0 ≤ E (j+1) ∧ E (j+1) ≤ E j at herr
  obtain ⟨he,hf,hfe⟩ := herr.2 j hjs
  let D : ℤ := (-1)^j
  let u : ℤ := D*(P (j+1)*r-Q (j+1)*n)
  let v : ℤ := D*(Q j*n-P j*r)
  have hD : D*D=1 := by
    dsimp [D]
    rw [← mul_pow]
    norm_num
  have hrep : r=u*Q j+v*Q (j+1) := by
    calc
      _ = D*D*r := by rw [hD, one_mul]
      _ = D*(P (j+1)*Q j-P j*Q (j+1))*r := by rw [hdet]
      _ = _ := by dsimp [u,v]; ring
  have hrepn : n=u*P j+v*P (j+1) := by
    calc
      _ = D*D*n := by rw [hD, one_mul]
      _ = D*(P (j+1)*Q j-P j*Q (j+1))*n := by rw [hdet]
      _ = _ := by dsimp [u,v]; ring
  have hrreal : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hbest := agent4_best_core (Q j) (Q (j+1)) (E j) (E (j+1)) r
    (hQ j) (hQ (j+1)) he hf hrreal (by exact_mod_cast hrj) u v
    (by exact_mod_cast hrep)
  have habs : |(u:ℝ)*E j-(v:ℝ)*E (j+1)| = |(r:ℝ)*x-n| := by
    have hr' : (r:ℝ)=(u:ℝ)*Q j+(v:ℝ)*Q (j+1) := by exact_mod_cast hrep
    have hn' : (n:ℝ)=(u:ℝ)*P j+(v:ℝ)*P (j+1) := by exact_mod_cast hrepn
    have heq : (u:ℝ)*E j-(v:ℝ)*E (j+1) = (-1:ℝ)^j*((r:ℝ)*x-n) := by
      dsimp [E]
      rw [pow_succ, hr', hn']
      ring
    rw [heq, abs_mul, abs_pow]
    norm_num
  rw [habs] at hbest
  have hg := hgrowth j
  have hjr' : (Q j:ℝ) ≤ r := by exact_mod_cast hjr
  calc
    1 = E j*(Q (j+1):ℝ)+E (j+1)*(Q j:ℝ) := (herr.1 j).symm
    _ ≤ E j*((Q (j+1):ℝ)+(Q j:ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_right hfe (hQ j).le]
    _ ≤ E j*((A+2)*(r:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ he.le
      nlinarith [mul_le_mul_of_nonneg_left hjr' (show 0 ≤ A+2 by linarith)]
    _ ≤ _ := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_right hbest (show 0 ≤ (A+2)*(r:ℝ) by positivity)

private lemma agent4_cf_ints (α : ℝ) (hα : Irrational α) (n : ℕ) :
    ∃ p q : ℤ, (p : ℝ) = (GenContFract.of α).nums n ∧
      (q : ℝ) = (GenContFract.of α).dens n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      exact ⟨⌊α⌋, 1, by simp [GenContFract.zeroth_num_eq_h,
        GenContFract.of_h_eq_floor], by simp [GenContFract.zeroth_den_eq_one]⟩
    | succ n =>
      cases n with
      | zero =>
        obtain ⟨g,hg⟩ := ContFracConvergents.agent4_pair_exists α hα 0
        have hga := GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a hg)
        obtain ⟨b,hb⟩ := GenContFract.exists_int_eq_of_partDen
          (GenContFract.partDen_eq_s_b hg)
        refine ⟨b * ⌊α⌋ + 1, b, ?_, ?_⟩
        · rw [GenContFract.first_num_eq hg, hga, hb, GenContFract.of_h_eq_floor]
          push_cast
          rfl
        · rw [GenContFract.first_den_eq hg, hb]
      | succ n =>
        obtain ⟨p,q,hp,hq⟩ := ih n (by omega)
        obtain ⟨p',q',hp',hq'⟩ := ih (n+1) (by omega)
        obtain ⟨g,hg⟩ := ContFracConvergents.agent4_pair_exists α hα (n+1)
        have hga := GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a hg)
        obtain ⟨b,hb⟩ := GenContFract.exists_int_eq_of_partDen
          (GenContFract.partDen_eq_s_b hg)
        refine ⟨b*p'+p, b*q'+q, ?_, ?_⟩
        · rw [GenContFract.nums_recurrence hg rfl rfl, hga, hb, ← hp, ← hp']
          push_cast
          ring
        · rw [GenContFract.dens_recurrence hg rfl rfl, hga, hb, ← hq, ← hq']
          push_cast
          ring

private lemma agent4_cf_lower (A α : ℝ) (hA : 1 ≤ A) (hα : Irrational α)
    (hbpq : ∀ i x, (GenContFract.of α).partDens.get? i = some x → x ≤ A)
    (s : ℕ) (hs : 1 ≤ s) (a q : ℤ)
    (hnum : (a:ℝ) = (GenContFract.of α).nums s)
    (hden : (q:ℝ) = (GenContFract.of α).dens s)
    (r n : ℤ) (hr : 1 ≤ r) (hrq : r < q) :
    1 ≤ (A+2)*(r:ℝ)*|(r:ℝ)*((a:ℝ)/q)-n| := by
  classical
  choose P Q hP hQ using agent4_cf_ints α hα
  have hpair (j : ℕ) := ContFracConvergents.agent4_pair α hα j
  choose g hg hga hgb using hpair
  let b : ℕ → ℝ := fun j => (g j).b
  have hb (j : ℕ) : 1 ≤ b j :=
    GenContFract.of_one_le_get?_partDen (GenContFract.partDen_eq_s_b (hg j))
  have hbA (j : ℕ) : b j ≤ A :=
    hbpq j _ (GenContFract.partDen_eq_s_b (hg j))
  have hpos (j : ℕ) : 0 < (Q j:ℝ) := by
    rw [hQ]
    exact ContFracConvergents.agent4_den_pos α j
  have hzero : Q 0 = 1 := by
    have hh := hQ 0
    rw [GenContFract.zeroth_den_eq_one] at hh
    exact_mod_cast hh
  have hmono (j : ℕ) : (Q j:ℝ) ≤ Q (j+1) := by
    rw [hQ, hQ]
    exact GenContFract.of_den_mono
  have hp (j : ℕ) : (P (j+2):ℝ)=b (j+1)*(P (j+1):ℝ)+P j := by
    rw [hP, hP, hP, GenContFract.nums_recurrence (hg (j+1)) rfl rfl, hga]
    simp only [one_mul, b]
  have hq (j : ℕ) : (Q (j+2):ℝ)=b (j+1)*(Q (j+1):ℝ)+Q j := by
    rw [hQ, hQ, hQ, GenContFract.dens_recurrence (hg (j+1)) rfl rfl, hga]
    simp only [one_mul, b]
  have hdet (j : ℕ) : P (j+1)*Q j-P j*Q (j+1)=(-1:ℤ)^j := by
    have ht := ContFracConvergents.cf_convergent_determinant α hα (j+1)
    have he : (P (j+1):ℝ)*Q j-(P j:ℝ)*Q (j+1)=(-1:ℝ)^j := by
      rw [hP, hP, hQ, hQ]
      simp only [GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b,
        GenContFract.nth_cont_eq_succ_nth_contAux]
      simpa only [pow_succ, mul_neg, mul_one, neg_neg] using ht
    exact_mod_cast he
  have hgr (j : ℕ) : (Q (j+1):ℝ) ≤ (A+1)*(Q j:ℝ) := by
    cases j with
    | zero =>
      rw [hQ, GenContFract.first_den_eq (hg 0), hzero]
      norm_num
      linarith [hbA 0]
    | succ j =>
      rw [show j+1+1=j+2 by omega, hq]
      have hh := mul_le_mul_of_nonneg_right (hbA (j+1)) (hpos (j+1)).le
      nlinarith [hmono j]
  have heP : P s=a := by exact_mod_cast (hP s).trans hnum.symm
  have heQ : Q s=q := by exact_mod_cast (hQ s).trans hden.symm
  have hh := agent4_rational_lower_ok P Q b hpos hzero hb hp hq hdet A hA hgr
    s hs r n hr (by rwa [heQ])
  simpa only [heP, heQ] using hh

/-
The preceding lemmas prove the finite-convergent best-approximation estimate.
The modular inverse transfers it to the required estimate by exchanging the
denominator and the integer error of an approximation.
-/
theorem intDist_inverse_convergent_ge (A α : ℝ) (hA : 1 ≤ A) (hα : Irrational α)
    (hbpq : ∀ (i : ℕ) (x : ℝ),
      (GenContFract.of α).partDens.get? i = some x → x ≤ A)
    (s : ℕ) (hs : 1 ≤ s) (a q : ℤ)
    (hnum : (a : ℝ) = (GenContFract.of α).nums s)
    (hden : (q : ℝ) = (GenContFract.of α).dens s)
    (abar : ℤ) (habar : a * abar ≡ 1 [ZMOD q])
    (t : ℤ) (ht : 1 ≤ t) (htq : t < q) :
    1 / ((A + 2) * (t : ℝ)) ≤ intDist ((t : ℝ) * (abar : ℝ) / (q : ℝ)) := by
  have hq : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have htpos : (0:ℝ)<t := by exact_mod_cast (show 0<t by omega)
  let z : ℤ := round ((t:ℝ)*(abar:ℝ)/(q:ℝ))
  let r : ℤ := t*abar-z*q
  obtain ⟨v,hv⟩ := Int.modEq_iff_dvd.mp habar
  let n : ℤ := -t*v-a*z
  have he : a*r-n*q=t := by
    dsimp [r,n]
    linear_combination -t*hv
  have hrneq : r ≠ 0 := by
    intro hz
    have hd : q ∣ t := ⟨-n, by rw [← he, hz]; ring⟩
    have hh := Int.le_of_dvd (show 0<t by omega) hd
    omega
  have hreal : (t:ℝ)*(abar:ℝ)/(q:ℝ)-(z:ℝ)=(r:ℝ)/(q:ℝ) := by
    dsimp [r]
    push_cast
    field_simp
    <;> ring
  have hdist : intDist ((t:ℝ)*(abar:ℝ)/(q:ℝ))= |(r:ℝ)|/(q:ℝ) := by
    change |(t:ℝ)*(abar:ℝ)/(q:ℝ)-(z:ℝ)| = _
    rw [hreal, abs_div, abs_of_pos hq]
  have hsmall : |(r:ℝ)|/(q:ℝ) ≤ 1/2 := by
    rw [← hdist]
    exact abs_sub_round _
  have hrq : |r| < q := by
    have hh := (div_le_iff₀ hq).1 hsmall
    have hh' : |(r:ℝ)| < (q:ℝ) := by linarith
    exact_mod_cast hh'
  have happrox : |(r:ℝ)*((a:ℝ)/q)-(n:ℝ)|=(t:ℝ)/(q:ℝ) := by
    have he' : (a:ℝ)*(r:ℝ)-(n:ℝ)*q=t := by exact_mod_cast he
    have hh : (r:ℝ)*((a:ℝ)/q)-(n:ℝ)=(t:ℝ)/(q:ℝ) := by
      apply (eq_div_iff hq.ne').2
      field_simp
      nlinarith [he']
    rw [hh, abs_of_pos (div_pos htpos hq)]
  have hb : 1 ≤ (A+2)*|(r:ℝ)| * |(r:ℝ)*((a:ℝ)/q)-(n:ℝ)| := by
    by_cases hr : 0 ≤ r
    · have hh := agent4_cf_lower A α hA hα hbpq s hs a q hnum hden
        r n (by omega) (by rwa [abs_of_nonneg hr] at hrq)
      simpa only [abs_of_nonneg (show (0:ℝ)≤r by exact_mod_cast hr)] using hh
    · have hh := agent4_cf_lower A α hA hα hbpq s hs a q hnum hden
        (-r) (-n) (by omega) (by rwa [abs_of_neg (by omega)] at hrq)
      rw [abs_of_neg (show (r:ℝ)<0 by exact_mod_cast (show r<0 by omega))]
      have heq : ((-r:ℤ):ℝ)*((a:ℝ)/q)-((-n:ℤ):ℝ) =
          -((r:ℝ)*((a:ℝ)/q)-(n:ℝ)) := by push_cast; ring
      rw [heq, abs_neg] at hh
      simpa only [Int.cast_neg] using hh
  rw [happrox] at hb
  rw [hdist]
  apply (div_le_iff₀ (show 0 < (A+2)*(t:ℝ) by positivity)).2
  convert hb using 1 <;> ring
private lemma agent4_min_integral (α : ℝ) (hα : Irrational α) (n : ℕ) :
    ∃ p q : ℤ, (p : ℝ) = (GenContFract.of α).nums n ∧
      (q : ℝ) = (GenContFract.of α).dens n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      exact ⟨⌊α⌋, 1, by simp [GenContFract.zeroth_num_eq_h,
        GenContFract.of_h_eq_floor], by simp [GenContFract.zeroth_den_eq_one]⟩
    | succ n =>
      cases n with
      | zero =>
        obtain ⟨g, hg⟩ := ContFracConvergents.agent4_pair_exists α hα 0
        have hga := GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a hg)
        obtain ⟨b, hb⟩ := GenContFract.exists_int_eq_of_partDen
          (GenContFract.partDen_eq_s_b hg)
        refine ⟨b * ⌊α⌋ + 1, b, ?_, ?_⟩
        · rw [GenContFract.first_num_eq hg, hga, hb, GenContFract.of_h_eq_floor]
          push_cast
          rfl
        · rw [GenContFract.first_den_eq hg, hb]
      | succ n =>
        obtain ⟨p, q, hp, hq⟩ := ih n (by omega)
        obtain ⟨p', q', hp', hq'⟩ := ih (n+1) (by omega)
        obtain ⟨g, hg⟩ := ContFracConvergents.agent4_pair_exists α hα (n+1)
        have hga := GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a hg)
        obtain ⟨b, hb⟩ := GenContFract.exists_int_eq_of_partDen
          (GenContFract.partDen_eq_s_b hg)
        refine ⟨b*p'+p, b*q'+q, ?_, ?_⟩
        · rw [GenContFract.nums_recurrence hg rfl rfl, hga, hb, ← hp, ← hp']
          push_cast
          ring
        · rw [GenContFract.dens_recurrence hg rfl rfl, hga, hb, ← hq, ← hq']
          push_cast
          ring

private lemma agent4_min_growth (R α : ℝ) (hR : 1 ≤ R) (hα : Irrational α)
    (hbpq : ∀ i x, (GenContFract.of α).partDens.get? i = some x → x ≤ R)
    (j : ℕ) :
    (GenContFract.of α).dens (j+1) ≤ (R+1)*(GenContFract.of α).dens j := by
  obtain ⟨p, hp, hpa, hpb⟩ := ContFracConvergents.agent4_pair α hα j
  have hb := hbpq j p.b (GenContFract.partDen_eq_s_b hp)
  cases j with
  | zero =>
    rw [GenContFract.first_den_eq hp, GenContFract.zeroth_den_eq_one]
    linarith
  | succ j =>
    rw [GenContFract.dens_recurrence hp rfl rfl, hpa, one_mul]
    have hm : (GenContFract.of α).dens j ≤ (GenContFract.of α).dens (j+1) :=
      GenContFract.of_den_mono
    have hh := mul_le_mul_of_nonneg_right hb
      (ContFracConvergents.agent4_den_pos α (j+1)).le
    nlinarith

private lemma agent4_min_coprime (α : ℝ) (hα : Irrational α) (s : ℕ)
    (hs : 1 ≤ s) (a q : ℤ)
    (ha : (a : ℝ) = (GenContFract.of α).nums s)
    (hq : (q : ℝ) = (GenContFract.of α).dens s) : Int.gcd a q = 1 := by
  obtain ⟨p', q', hp', hq'⟩ := agent4_min_integral α hα (s-1)
  have hd := ContFracConvergents.cf_det_relation_int α hα s hs a q p' q'
    ⟨ha, hq, hp', hq'⟩
  apply Int.gcd_eq_one_iff.mpr
  intro c hca hcq
  have hc : c ∣ a*q'-p'*q := dvd_sub (dvd_mul_of_dvd_left hca q')
    (dvd_mul_of_dvd_right hcq p')
  rw [hd] at hc
  rcases neg_one_pow_eq_or ℤ (s-1) with he | he
  · rwa [he] at hc
  · rw [he] at hc
    exact dvd_neg.mp hc

private lemma agent4_min_exists (α T : ℝ) (hα : Irrational α) :
    ∃ n, T ≤ (GenContFract.of α).dens n := by
  have hnt (j : ℕ) : ¬ (GenContFract.of α).TerminatedAt j := by
    intro ht
    obtain ⟨v, hv⟩ := GenContFract.exists_rat_eq_of_terminates ⟨j, ht⟩
    exact hα ⟨v, hv.symm⟩
  obtain ⟨n, hn⟩ := exists_nat_gt T
  refine ⟨n+5, ?_⟩
  have hf := GenContFract.succ_nth_fib_le_of_nth_den (v := α)
    (n := n+5) (Or.inr (hnt _))
  have hnat : ((n+5+1 : ℕ) : ℝ) ≤ (Nat.fib (n+5+1) : ℝ) := by
    exact_mod_cast Nat.le_fib_self (show 5 ≤ n+5+1 by omega)
  have hn' : (n : ℝ) ≤ ((n+5+1 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact hn.le.trans (hn'.trans (hnat.trans hf))

theorem convergent_smallest_den_le (R H α : ℝ) (hR : 1 ≤ R) (hH : 1 ≤ H)
    (hα : Irrational α)
    (hbpq : ∀ (i : ℕ) (x : ℝ),
      (GenContFract.of α).partDens.get? i = some x → x ≤ R) :
    ∃ (s : ℕ) (a q : ℤ),
      (a : ℝ) = (GenContFract.of α).nums s ∧
      (q : ℝ) = (GenContFract.of α).dens s ∧
      Int.gcd a q = 1 ∧
      12 * R ^ 2 * H ≤ (q : ℝ) ∧
      (∀ n : ℕ, 12 * R ^ 2 * H ≤ (GenContFract.of α).dens n →
        (q : ℝ) ≤ (GenContFract.of α).dens n) ∧
      (q : ℝ) ≤ 100 * R ^ 3 * H := by
  classical
  have hex := agent4_min_exists α (12*R^2*H) hα
  let s := Nat.find hex
  have hs : 12*R^2*H ≤ (GenContFract.of α).dens s := Nat.find_spec hex
  have hT : 1 < 12*R^2*H := by
    have hsq : 1 ≤ R^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hH (show 0 ≤ 12*R^2 by positivity)
    nlinarith
  have hspos : 1 ≤ s := by
    by_contra hn
    have hz : s = 0 := by omega
    rw [hz, GenContFract.zeroth_den_eq_one] at hs
    linarith
  obtain ⟨a, q, ha, hq⟩ := agent4_min_integral α hα s
  refine ⟨s, a, q, ha, hq, agent4_min_coprime α hα s hspos a q ha hq,
    by rwa [hq], ?_, ?_⟩
  · intro n hn
    rw [hq]
    exact (monotone_nat_of_le_succ (fun j =>
      (GenContFract.of_den_mono (v := α) (n := j)))) (Nat.find_min' hex hn)
  · have hprev : (GenContFract.of α).dens (s-1) < 12*R^2*H :=
      lt_of_not_ge (Nat.find_min hex (show s-1 < s by omega))
    have hg := agent4_min_growth R α hR hα hbpq (s-1)
    rw [Nat.sub_add_cancel hspos] at hg
    rw [hq]
    calc
      _ ≤ (R+1)*(GenContFract.of α).dens (s-1) := hg
      _ ≤ (R+1)*(12*R^2*H) :=
        mul_le_mul_of_nonneg_left hprev.le (by positivity)
      _ ≤ (2*R)*(12*R^2*H) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 24*R^3*H := by ring
      _ ≤ 100*R^3*H := by
        have : 0 ≤ R^3*H := by positivity
        nlinarith
private lemma agent4WeylFreshVerified_mul (j : ℤ) (x : ℝ) :
    intDist ((j : ℝ)*x) ≤ |(j : ℝ)| * intDist x := by
  apply (round_le ((j : ℝ)*x) (j * round x)).trans_eq
  simp only [Int.cast_mul, intDist, ← abs_mul]
  congr 1
  ring

private lemma agent4WeylFreshVerified_neg (x : ℝ) : intDist (-x) = intDist x := by
  have h1 := agent4WeylFreshVerified_mul (-1) x
  have h2 := agent4WeylFreshVerified_mul (-1) (-x)
  norm_num at h1 h2
  exact le_antisymm h1 h2

private lemma agent4WeylFreshVerified_abs (j : ℤ) (x : ℝ) :
    intDist ((|j| : ℤ) * x) = intDist ((j : ℝ)*x) := by
  by_cases hj : 0 ≤ j
  · rw [abs_of_nonneg hj]
  · rw [abs_of_neg (lt_of_not_ge hj), Int.cast_neg, neg_mul, agent4WeylFreshVerified_neg]

/-- **A badly approximable rational rotation at all scales below `q`.**
Let `A, M ≥ 1`, let `α` be irrational with partial quotients bounded by `A`, let `a / q`
be a convergent of `α` with `q ≥ 16 M`, let `abar ∈ [0, q)` be the modular inverse of `a`
modulo `q`, and let `m, n` be integers with `1 ≤ |m|, |n| ≤ M`.  Setting
`α' = (m / n) · (abar / (4 q))` and `c = 1 / (12 A M²)`, one has
`‖t α'‖ ≥ c / |t|` for every integer `t` with `1 ≤ |t| ≤ q / (2 M)`. -/
theorem intDist_weyl_freq_ge (A M α : ℝ) (hA : 1 ≤ A) (hM : 1 ≤ M)
    (hα : Irrational α)
    (hbpq : ∀ (i : ℕ) (x : ℝ),
      (GenContFract.of α).partDens.get? i = some x → x ≤ A)
    (s : ℕ) (hs : 1 ≤ s) (a q : ℤ)
    (hnum : (a : ℝ) = (GenContFract.of α).nums s)
    (hden : (q : ℝ) = (GenContFract.of α).dens s)
    (hq : 16 * M ≤ (q : ℝ))
    (abar : ℤ) (habar : a * abar ≡ 1 [ZMOD q])
    (habar0 : 0 ≤ abar) (habarq : abar < q)
    (m n : ℤ) (hm : 1 ≤ |m|) (hmM : (|m| : ℝ) ≤ M)
    (hn : 1 ≤ |n|) (hnM : (|n| : ℝ) ≤ M)
    (t : ℤ) (ht : 1 ≤ |t|) (htq : (|t| : ℝ) ≤ (q : ℝ) / (2 * M)) :
    1 / (12 * A * M ^ 2) / (|t| : ℝ) ≤
      intDist ((t : ℝ) * ((m : ℝ) / (n : ℝ) * ((abar : ℝ) / (4 * (q : ℝ))))) := by
  have hMp : 0 < M := by linarith
  have hAp : 0 < A := by linarith
  have hqp : (0 : ℝ) < q := by linarith
  have htr : (1 : ℝ) ≤ |(t : ℝ)| := by exact_mod_cast ht
  have hmr : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast hm
  have hnr : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := abs_pos.mp (by linarith)
  have htm : 1 ≤ |t*m| := by rw [abs_mul]; nlinarith
  have htmq : |t*m| < q := by
    have hmul := (le_div_iff₀ (show 0 < 2*M by positivity)).1 htq
    have hb := mul_le_mul_of_nonneg_left hmM (abs_nonneg (t : ℝ))
    have hh : |((t*m : ℤ) : ℝ)| < (q : ℝ) := by
      rw [Int.cast_mul, abs_mul]
      nlinarith
    exact_mod_cast hh
  have hlower := intDist_inverse_convergent_ge A α hA hα hbpq s hs a q
    hnum hden abar habar |t*m| htm htmq
  have he : intDist ((|t*m| : ℤ) * ((abar : ℝ)/(q : ℝ))) =
      intDist ((t : ℝ)*(m : ℝ)*(abar : ℝ)/(q : ℝ)) := by
    rw [agent4WeylFreshVerified_abs]
    congr 1
    push_cast
    ring
  rw [mul_div_assoc, he] at hlower
  let y : ℝ := (t : ℝ)*((m : ℝ)/(n : ℝ)*((abar : ℝ)/(4*(q : ℝ))))
  have hscale := agent4WeylFreshVerified_mul (4*n) y
  have hy : ((4*n : ℤ) : ℝ)*y = (t : ℝ)*(m : ℝ)*(abar : ℝ)/(q : ℝ) := by
    dsimp [y]
    push_cast
    field_simp
    <;> ring
  rw [hy] at hscale
  simp only [Int.cast_mul, Int.cast_ofNat, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at hscale
  have hlow : 1 / ((A+2)* (|(t : ℝ)| *|(m : ℝ)|)) ≤
      (4*|(n : ℝ)|)*intDist y := by
    simpa only [Int.cast_abs, Int.cast_mul, abs_mul] using hlower.trans hscale
  have hprod : |(m : ℝ)| *|(n : ℝ)| ≤ M^2 := by
    nlinarith [mul_le_mul hmM hnM (abs_nonneg (n : ℝ)) hMp.le]
  have hcoef : ((A+2)*(|(t : ℝ)| *|(m : ℝ)|))*(4*|(n : ℝ)|) ≤
      (12*A*M^2)*|(t : ℝ)| := by
    have hAM : (A+2)*(|(m : ℝ)| *|(n : ℝ)|) ≤ (3*A)*M^2 :=
      mul_le_mul (by linarith) hprod (by positivity) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hAM (show 0 ≤ 4*|(t : ℝ)| by positivity)]
  have hnon : 0 ≤ intDist y := abs_nonneg _
  have hfinal : 1 ≤ ((12*A*M^2)*|(t : ℝ)|)*intDist y := by
    have hh := (div_le_iff₀
      (show 0 < (A+2)*(|(t : ℝ)| *|(m : ℝ)|) by positivity)).1 hlow
    nlinarith [mul_le_mul_of_nonneg_right hcoef hnon]
  rw [div_div]
  exact (div_le_iff₀ (by positivity)).2
    (by simpa only [y, mul_comm] using hfinal)
private lemma agent4Diff_phase (a b : ℝ) (d h : ℕ) :
    expTwoPiI (a * ((h+d : ℕ) : ℝ)^2 + b * (h+d : ℕ)) *
      (starRingEnd ℂ) (expTwoPiI (a * (h : ℝ)^2 + b * h)) =
    expTwoPiI (a * (d : ℝ)^2 + b * d) * expTwoPiI ((2*(d : ℝ)*a)*(h : ℝ)) := by
  rw [onb_exp_sub_ok, ← onb_exp_add]
  congr 1
  push_cast
  ring

private lemma agent4Diff_phase_lower (x : ℝ) :
    4 * intDist x ≤ ‖expTwoPiI x - 1‖ := by
  have he : expTwoPiI x = expTwoPiI (x - (round x : ℝ)) := by
    calc
      _ = expTwoPiI ((x - (round x : ℝ)) + (round x : ℝ)) := by
        congr 1
        ring
      _ = _ := by rw [onb_exp_add, agent4_exp_int, mul_one]
  rw [he, LocalizedFourierFinal.fm_phase_norm]
  have hh : |Real.pi * (x - (round x : ℝ))| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left (abs_sub_round x) Real.pi_pos.le]
  have hs := Real.mul_abs_le_abs_sin hh
  rw [abs_mul, abs_of_pos Real.pi_pos] at hs
  have halg : 2 / Real.pi * (Real.pi * |x - (round x : ℝ)|) = 2 * intDist x := by
    unfold intDist
    field_simp
  rw [halg] at hs
  linarith

private lemma agent4Diff_geom_ok (x : ℝ) (n : ℕ) (hx : intDist x ≠ 0) :
    ‖∑ j ∈ Finset.range n, expTwoPiI (x * (j : ℝ))‖ ≤ (intDist x)⁻¹ / 2 := by
  have hp : 0 < intDist x := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hx)
  have he := congrArg norm (geom_sum_mul (expTwoPiI x) n)
  rw [norm_mul] at he
  have ht : ‖expTwoPiI x ^ n - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖expTwoPiI x ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [norm_pow, LocalizedFourierFinal.FourierMassBounds.exp_norm]
        norm_num
  rw [← he] at ht
  have hb := mul_le_mul_of_nonneg_left (agent4Diff_phase_lower x)
    (norm_nonneg (∑ j ∈ Finset.range n, expTwoPiI x ^ j))
  have hs : (∑ j ∈ Finset.range n, expTwoPiI x ^ j) =
      ∑ j ∈ Finset.range n, expTwoPiI (x * (j : ℝ)) := by
    simp_rw [shifted_exp_nat_pow]
  rw [hs] at ht hb
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hp).2
  nlinarith

private lemma agent4Diff_triangle (F : ℕ → ℕ → ℝ)
    (hF : ∀ i j, F i j = F j i) (R : ℕ) :
    (∑ i ∈ Finset.range R, ∑ j ∈ Finset.range R, F i j) =
      (∑ i ∈ Finset.range R, F i i) +
        2 * ∑ i ∈ Finset.range R, ∑ j ∈ Finset.range i, F i j := by
  induction R with
  | zero => simp
  | succ R ih =>
    have hs : (∑ j ∈ Finset.range R, F j R) =
        ∑ j ∈ Finset.range R, F R j :=
      Finset.sum_congr rfl (fun j _ => hF j R)
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
    rw [ih, hs]
    ring

private lemma agent4Diff_lags (F : ℕ → ℕ → ℝ) (R : ℕ) :
    (∑ i ∈ Finset.range R, ∑ j ∈ Finset.range (i+1), F i j) =
      ∑ d ∈ Finset.range R, ∑ h ∈ Finset.range (R-d), F (h+d) h := by
  rw [← Finset.sum_range_diag_flip]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_flip (fun j => F i j)]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ i := by
    have := Finset.mem_range.mp hj
    omega
  rw [Nat.sub_add_cancel hj']

private lemma agent4Diff_expand_final (f : ℕ → ℂ) (hf : ∀ i, ‖f i‖ = 1)
    (R : ℕ) (hR : 1 ≤ R) :
    ‖∑ i ∈ Finset.range R, f i‖^2 = (R : ℝ) +
      2 * ∑ d ∈ Finset.Ico 1 R,
        (∑ h ∈ Finset.range (R-d), f (h+d) * (starRingEnd ℂ) (f h)).re := by
  let F : ℕ → ℕ → ℝ := fun i j => (f i * (starRingEnd ℂ) (f j)).re
  have hsym : ∀ i j, F i j = F j i := by
    intro i j
    simp only [F, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hdiag (i : ℕ) : F i i = 1 := by
    dsimp [F]
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq, hf]
  have hfull : (∑ i ∈ Finset.range R, ∑ j ∈ Finset.range R, F i j) =
      ‖∑ i ∈ Finset.range R, f i‖^2 := by
    dsimp [F]
    simp_rw [← Complex.re_sum, ← Finset.mul_sum, ← map_sum]
    rw [← Finset.sum_mul, mul_comm, ← Complex.normSq_eq_conj_mul_self]
    simp only [Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow, Complex.ofReal_re]
  have ht := agent4Diff_triangle F hsym R
  rw [hfull] at ht
  simp only [hdiag, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at ht
  have hl := agent4Diff_lags F R
  simp_rw [Finset.sum_range_succ] at hl
  rw [Finset.sum_add_distrib] at hl
  simp only [hdiag, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hl
  conv_rhs at hl => rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < R)]
  simp only [Nat.sub_zero, Nat.add_zero, hdiag, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one] at hl
  have he : (∑ d ∈ Finset.Ico 1 R, ∑ h ∈ Finset.range (R-d), F (h+d) h) =
      ∑ d ∈ Finset.Ico 1 R,
        (∑ h ∈ Finset.range (R-d), f (h+d) * (starRingEnd ℂ) (f h)).re := by
    simp [F, Complex.re_sum]
  rw [he] at hl
  linarith

/-- The quadratic exponential sum `S = ∑_{0 ≤ h < R} e(α' h² + β h)`,
where `e(x) = e^{2πix}`. -/
noncomputable def weylQuadSum (alpha' beta : ℝ) (R : ℕ) : ℂ :=
  ∑ h ∈ Finset.range R, expTwoPiI (alpha' * (h : ℝ) ^ 2 + beta * (h : ℝ))

/-- **One step of Weyl differencing.**  Let `α', β ∈ ℝ` and let `R ≥ 1` be an integer,
and put `S = ∑_{0 ≤ h < R} e(α' h² + β h)`.  If `‖2 d α'‖ ≠ 0` for every integer
`1 ≤ d < R`, where `‖·‖` denotes the distance to the nearest integer, then
`|S|² ≤ R + ∑_{1 ≤ d < R} ‖2 d α'‖⁻¹`. -/
theorem weyl_differencing_normSq_le (alpha' beta : ℝ) (R : ℕ) (hR : 1 ≤ R)
    (hnz : ∀ d : ℕ, 1 ≤ d → d < R → intDist (2 * (d : ℝ) * alpha') ≠ 0) :
    ‖weylQuadSum alpha' beta R‖ ^ 2 ≤
      (R : ℝ) + ∑ d ∈ Finset.Ico 1 R, (intDist (2 * (d : ℝ) * alpha'))⁻¹ := by
  unfold weylQuadSum
  rw [agent4Diff_expand_final _
    (fun i => LocalizedFourierFinal.FourierMassBounds.exp_norm _) R hR]
  rw [Finset.mul_sum]
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro d hd
  have he : (∑ h ∈ Finset.range (R-d),
      expTwoPiI (alpha' * ((h+d : ℕ) : ℝ)^2 + beta * (h+d : ℕ)) *
        (starRingEnd ℂ) (expTwoPiI (alpha' * (h : ℝ)^2 + beta * h))) =
      expTwoPiI (alpha' * (d : ℝ)^2 + beta * d) *
        ∑ h ∈ Finset.range (R-d), expTwoPiI ((2*(d : ℝ)*alpha')*(h : ℝ)) := by
    simp_rw [agent4Diff_phase]
    rw [Finset.mul_sum]
  rw [he]
  have hg := agent4Diff_geom_ok (2*(d : ℝ)*alpha') (R-d)
    (hnz d (Finset.mem_Ico.mp hd).1 (Finset.mem_Ico.mp hd).2)
  have hr := Complex.re_le_norm (expTwoPiI (alpha' * (d : ℝ)^2 + beta * d) *
    ∑ h ∈ Finset.range (R-d), expTwoPiI ((2*(d : ℝ)*alpha')*(h : ℝ)))
  rw [norm_mul, LocalizedFourierFinal.FourierMassBounds.exp_norm, one_mul] at hr
  linarith
private lemma agent4Spacing_sorted_final (S : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hbase : ∀ y ∈ S, δ ≤ y)
    (hsep : ∀ y ∈ S, ∀ z ∈ S, y ≠ z → δ ≤ |y-z|) :
    ∑ y ∈ S, y⁻¹ ≤ δ⁻¹ * ∑ i ∈ Finset.range S.card, ((i : ℝ)+1)⁻¹ := by
  classical
  let e : Fin S.card ≃o ↥S := S.orderIsoOfFin rfl
  have hlower : ∀ (i : ℕ) (hi : i < S.card), δ*((i : ℝ)+1) ≤ (e ⟨i,hi⟩).val := by
    intro i
    induction i with
    | zero => intro hi; simpa using hbase _ (e ⟨0,hi⟩).property
    | succ i ih =>
      intro hi
      have hip : i < S.card := by omega
      have he : (e ⟨i,hip⟩).val < (e ⟨i+1,hi⟩).val :=
        e.strictMono (show (⟨i,hip⟩ : Fin S.card) < ⟨i+1,hi⟩ by simp)
      have hs := hsep _ (e ⟨i+1,hi⟩).property _ (e ⟨i,hip⟩).property (ne_of_gt he)
      rw [abs_of_pos (sub_pos.mpr he)] at hs
      have hh := ih hip
      push_cast
      linarith
  rw [← Finset.sum_coe_sort S (fun y : ℝ => y⁻¹),
    ← e.toEquiv.sum_comp (fun y : ↥S => y.val⁻¹),
    ← Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ)+1)⁻¹), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ ≤ (δ*((i.val : ℝ)+1))⁻¹ := inv_anti₀ (by positivity) (hlower i.val i.isLt)
    _ = _ := by rw [mul_inv]

private lemma agent4Spacing_positive_final {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (R : ℕ) (hcard : S.card ≤ R) (δ : ℝ) (hδ : 0 < δ)
    (hbase : ∀ i ∈ S, δ ≤ f i)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |f i-f j|) :
    ∑ i ∈ S, (f i)⁻¹ ≤ δ⁻¹ * (1+Real.log R) := by
  classical
  have hinj : Set.InjOn f (S : Set ι) := by
    intro i hi j hj he
    by_contra hn
    have hh := hsep i hi j hj hn
    rw [he, sub_self, abs_zero] at hh
    linarith
  rw [← Finset.sum_image hinj]
  apply (agent4Spacing_sorted_final (S.image f) δ hδ ?_ ?_).trans
  · apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hδ.le)
    calc
      _ ≤ ∑ i ∈ Finset.range R, ((i : ℝ)+1)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Finset.card_image_le.trans hcard)) (by intros; positivity)
      _ ≤ 1+Real.log R := by
        simpa [harmonic] using harmonic_le_one_add_log R
  · intro y hy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    exact hbase i hi
  · intro y hy z hz hne
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
    exact hsep i hi j hj (fun h => hne (congrArg f h))

theorem sum_inv_intDist_le_of_separated
    (R : ℕ) (hR : 1 ≤ R) (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (x : ℕ → ℝ)
    (hx : ∀ d : ℕ, 1 ≤ d → d < R → c / (2 * (d : ℝ)) ≤ intDist (x d))
    (hsep : ∀ d d' : ℕ, 1 ≤ d → d < d' → d' < R →
      c / (2 * ((d' : ℝ) - (d : ℝ))) ≤ intDist (x d' - x d)) :
    ∑ d ∈ Finset.Ico 1 R, (intDist (x d))⁻¹ ≤
      4 * (R : ℝ) / c * (1 + Real.log R) := by
  classical
  let S := Finset.Ico 1 R
  let y : ℕ → ℝ := fun d => x d - (round (x d) : ℝ)
  let δ : ℝ := c / (2*(R : ℝ))
  have hRp : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hδ : 0 < δ := div_pos hc0 (by positivity)
  have hbase (d : ℕ) (hd : d ∈ S) : δ ≤ intDist (x d) := by
    obtain ⟨hd1,hdR⟩ := Finset.mem_Ico.mp hd
    have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    apply le_trans _ (hx d hd1 hdR)
    exact div_le_div_of_nonneg_left hc0.le (by positivity)
      (by exact_mod_cast (show 2*d ≤ 2*R by omega))
  have hnear (d e : ℕ) : intDist (x e - x d) ≤ |y e - y d| := by
    convert round_le (x e - x d) (round (x e) - round (x d)) using 1
    congr 1
    dsimp [y]
    push_cast <;> ring_nf
  have hordered (d e : ℕ) (hd : d ∈ S) (he : e ∈ S) (hde : d < e) :
      δ ≤ |y e - y d| := by
    obtain ⟨hd1,hdR⟩ := Finset.mem_Ico.mp hd
    obtain ⟨he1,heR⟩ := Finset.mem_Ico.mp he
    have hder : (d : ℝ) < e := by exact_mod_cast hde
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have heR' : (e : ℝ) ≤ R := by exact_mod_cast heR.le
    apply le_trans _ ((hsep d e hd1 hde heR).trans (hnear d e))
    exact div_le_div_of_nonneg_left hc0.le (by positivity) (by linarith)
  have hpair (d : ℕ) (hd : d ∈ S) (e : ℕ) (he : e ∈ S) (hne : d ≠ e) :
      δ ≤ |y d-y e| := by
    rcases lt_or_gt_of_ne hne with hde | hed
    · rw [abs_sub_comm]
      exact hordered d e hd he hde
    · exact hordered e d he hd hed
  have hcard : S.card ≤ R := by simp [S] <;> omega
  have hpos : (∑ d ∈ S.filter (fun d => 0 ≤ y d), (intDist (x d))⁻¹) ≤
      δ⁻¹ * (1+Real.log R) := by
    apply agent4Spacing_positive_final _ (fun d => intDist (x d)) R
      ((Finset.card_filter_le _ _).trans hcard) δ hδ
    · intro d hd
      exact hbase d (Finset.mem_filter.mp hd).1
    · intro d hd e he hne
      obtain ⟨hd,hd0⟩ := Finset.mem_filter.mp hd
      obtain ⟨he,he0⟩ := Finset.mem_filter.mp he
      change δ ≤ abs (|y d| - |y e|)
      rw [abs_of_nonneg hd0, abs_of_nonneg he0]
      exact hpair d hd e he hne
  have hneg : (∑ d ∈ S.filter (fun d => ¬ 0 ≤ y d), (intDist (x d))⁻¹) ≤
      δ⁻¹ * (1+Real.log R) := by
    apply agent4Spacing_positive_final _ (fun d => intDist (x d)) R
      ((Finset.card_filter_le _ _).trans hcard) δ hδ
    · intro d hd
      exact hbase d (Finset.mem_filter.mp hd).1
    · intro d hd e he hne
      obtain ⟨hd,hd0⟩ := Finset.mem_filter.mp hd
      obtain ⟨he,he0⟩ := Finset.mem_filter.mp he
      change δ ≤ abs (|y d| - |y e|)
      rw [abs_of_neg (lt_of_not_ge hd0), abs_of_neg (lt_of_not_ge he0),
        neg_sub_neg, abs_sub_comm]
      exact hpair d hd e he hne
  have hh := add_le_add hpos hneg
  rw [Finset.sum_filter_add_sum_filter_not] at hh
  calc
    _ ≤ δ⁻¹ * (1+Real.log R) + δ⁻¹ * (1+Real.log R) := hh
    _ = _ := by dsimp [δ]; field_simp <;> ring
private lemma agent4WG_shift (a b : ℝ) (N : ℤ) (n : ℕ) :
    ‖∑ j ∈ Finset.range n, expTwoPiI (a*((N:ℝ)+j)^2+b*((N:ℝ)+j))‖ =
      ‖weylQuadSum a (2*a*N+b) n‖ := by
  have he (j : ℕ) : expTwoPiI (a*((N:ℝ)+j)^2+b*((N:ℝ)+j)) =
      expTwoPiI (a*(N:ℝ)^2+b*N) * expTwoPiI (a*(j:ℝ)^2+(2*a*N+b)*j) := by
    rw [← onb_exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, norm_mul, LocalizedFourierFinal.FourierMassBounds.exp_norm, one_mul]
  rfl

private lemma agent4WG_interval {E : Type*} [AddCommMonoid E] (f : ℤ → E)
    (N : ℤ) (n : ℕ) :
    (∑ h ∈ Finset.Ico N (N+(n:ℤ)), f h) =
      ∑ j ∈ Finset.range n, f (N+(j:ℤ)) := by
  classical
  symm
  apply Finset.sum_bij (fun (j : ℕ) _ => N+(j:ℤ))
  · intro j hj
    have := Finset.mem_range.mp hj
    simp only [Finset.mem_Ico]
    omega
  · intro i hi j hj he
    omega
  · intro h hh
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hh
    refine ⟨(h-N).toNat, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intros; rfl

private lemma agent4WG_log (R : ℝ) (hR : 1 ≤ R) :
    1 ≤ 2*Real.log (2*R) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  have hm := Real.log_le_log (by norm_num : (0:ℝ)<2)
    (show (2:ℝ) ≤ 2*R by linarith)
  norm_num at h
  linarith

private lemma agent4WG_local_convert (A M R u X : ℝ)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hR : 1 ≤ R) (hu : 1 ≤ u) (huR : u ≤ 2*R)
    (hX : 0 ≤ X)
    (h : X^2 ≤ u + 48*A*M^2*u*(1+Real.log u)) :
    X ≤ Real.sqrt (4+288*A*M^2) * Real.sqrt (R*Real.log (2*R)) := by
  have hl := agent4WG_log R hR
  have hlu : Real.log u ≤ Real.log (2*R) := Real.log_le_log (by linarith) huR
  have hlog : 0 ≤ Real.log (2*R) := by linarith
  have hcoef : 0 ≤ 48*A*M^2 := by positivity
  have hmul : u*(1+Real.log u) ≤ 6*(R*Real.log (2*R)) := by
    calc
      _ ≤ (2*R)*(3*Real.log (2*R)) :=
        mul_le_mul huR (by linarith) (by linarith [Real.log_nonneg hu]) (by positivity)
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_left hmul hcoef
  have hr : u ≤ 4*(R*Real.log (2*R)) := by
    nlinarith [mul_le_mul_of_nonneg_left hl (show 0≤R by linarith)]
  apply (sq_le_sq₀ hX (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  nlinarith

private lemma agent4WG_local_sq_ok (A M α : ℝ) (hA : 1 ≤ A) (hM : 1 ≤ M)
    (hα : Irrational α)
    (hbpq : ∀ i x, (GenContFract.of α).partDens.get? i = some x → x ≤ A)
    (s : ℕ) (hs : 1 ≤ s) (a q abar : ℤ)
    (hnum : (a : ℝ) = (GenContFract.of α).nums s)
    (hden : (q : ℝ) = (GenContFract.of α).dens s)
    (hq : 16*M ≤ (q : ℝ)) (habar : a*abar ≡ 1 [ZMOD q])
    (habar0 : 0 ≤ abar) (habarq : abar < q)
    (m n : ℤ) (hm : 1 ≤ |m|) (hmM : |(m : ℝ)| ≤ M)
    (hn : 1 ≤ |n|) (hnM : |(n : ℝ)| ≤ M)
    (R : ℕ) (hR : 1 ≤ R) (hRsmall : (R : ℝ) ≤ (q : ℝ)/(4*M)) (β : ℝ) :
    let α' := (m : ℝ)/(n : ℝ)*((abar : ℝ)/(4*(q : ℝ)))
    ‖weylQuadSum α' β R‖^2 ≤ (R : ℝ)+48*A*M^2*(R : ℝ)*(1+Real.log R) := by
  let α' := (m : ℝ)/(n : ℝ)*((abar : ℝ)/(4*(q : ℝ)))
  let c := 1/(12*A*M^2)
  have hAp : 0 < A := by linarith
  have hMp : 0 < M := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    apply (div_le_one (by positivity)).2
    have hMsq : 1 ≤ M^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hMsq hAp.le]
  have hdio (d : ℕ) (hd : 1 ≤ d) (hdR : d < R) :
      c/(2*(d : ℝ)) ≤ intDist (2*(d : ℝ)*α') := by
    have ht : 1 ≤ |2*(d : ℤ)| := by
      rw [abs_of_nonneg (by positivity)]
      omega
    have htq : |((2*(d : ℤ) : ℤ) : ℝ)| ≤ (q : ℝ)/(2*M) := by
      rw [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, abs_of_nonneg (by positivity)]
      apply (le_div_iff₀ (by positivity)).2
      have hbound := (le_div_iff₀ (by positivity : 0 < 4*M)).1 hRsmall
      have hdr : (d : ℝ) ≤ R := by exact_mod_cast hdR.le
      nlinarith [mul_le_mul_of_nonneg_left hdr hMp.le]
    have hh := intDist_weyl_freq_ge A M α hA hM hα hbpq s hs a q hnum hden
      hq abar habar habar0 habarq m n hm hmM hn hnM (2*(d : ℤ)) ht htq
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      abs_of_nonneg (show (0 : ℝ) ≤ 2*(d : ℝ) by positivity)] using hh
  have hnz (d : ℕ) (hd : 1 ≤ d) (hdR : d < R) : intDist (2*(d : ℝ)*α') ≠ 0 := by
    have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    exact (lt_of_lt_of_le (div_pos hc (by positivity)) (hdio d hd hdR)).ne'
  have hsep := sum_inv_intDist_le_of_separated R hR c hc hc1
    (fun d => 2*(d : ℝ)*α') hdio (by
      intro d e hd hde heR
      have hed : 1 ≤ e-d := by omega
      have hedr : e-d < R := by omega
      have hh := hdio (e-d) hed hedr
      rw [Nat.cast_sub (by omega : d ≤ e)] at hh
      convert hh using 1 <;> ring_nf)
  have hw := weyl_differencing_normSq_le α' β R hR hnz
  apply hw.trans
  apply add_le_add_right
  convert hsep using 1
  dsimp [c]
  field_simp
  <;> ring

private lemma agent4WG_blocks (f : ℕ → ℂ) (H T J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hlocal : ∀ o n : ℕ, n ≤ H → n ≤ T →
      ‖∑ j ∈ Finset.range n, f (o+j)‖ ≤ B) :
    ∀ o n : ℕ, n ≤ J*H → n ≤ T →
      ‖∑ j ∈ Finset.range n, f (o+j)‖ ≤ (J : ℝ)*B := by
  induction J with
  | zero =>
      intro o n hn hT
      have hz : n = 0 := by omega
      simp [hz]
  | succ J ih =>
      intro o n hn hT
      by_cases hsmall : n ≤ H
      · apply (hlocal o n hsmall hT).trans
        have hJB : 0 ≤ (J : ℝ)*B := mul_nonneg (Nat.cast_nonneg _) hB
        push_cast
        linarith
      · have hHn : H ≤ n := by omega
        have hrem : n-H ≤ J*H := by
          rw [Nat.succ_mul] at hn
          omega
        have he : n = H+(n-H) := by omega
        conv_lhs => rw [he, Finset.sum_range_add]
        calc
          _ ≤ ‖∑ j ∈ Finset.range H, f (o+j)‖ +
              ‖∑ j ∈ Finset.range (n-H), f (o+(H+j))‖ := norm_add_le _ _
          _ ≤ B+(J : ℝ)*B := add_le_add
            (hlocal o H le_rfl (hHn.trans hT))
            (by simpa only [Nat.add_assoc] using ih (o+H) (n-H) hrem (by omega))
          _ = _ := by push_cast; ring

private lemma agent4WG_block_sizes (M Q R : ℝ) (hM : 1 ≤ M)
    (hQ : 16*M ≤ Q) (hR : 1 ≤ R) (hRQ : R ≤ 2*Q) :
    0 < ⌊Q/(4*M)⌋₊ ∧
    (⌊Q/(4*M)⌋₊ : ℝ) ≤ Q/(4*M) ∧
    ⌈R⌉₊ ≤ (⌈32*M⌉₊+1)*⌊Q/(4*M)⌋₊ ∧
    (⌈R⌉₊ : ℝ) ≤ 2*R := by
  have hMp : 0 < M := by linarith
  have hQp : 0 < Q := by linarith
  have hratio : 1 ≤ Q/(4*M) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith
  have hf := Nat.div_two_lt_floor hratio
  have hlow : Q < (8*M)*(⌊Q/(4*M)⌋₊ : ℝ) := by
    have he : Q/(4*M)/2 = Q/(8*M) := by ring
    rw [he] at hf
    nlinarith [(div_lt_iff₀ (show 0<8*M by positivity)).1 hf]
  have hHp : 0 < ⌊Q/(4*M)⌋₊ := by
    by_contra hh
    have hz : ⌊Q/(4*M)⌋₊ = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero] at hlow
    linarith
  have hceil : (⌈R⌉₊ : ℝ) ≤ 2*R := Nat.ceil_le_two_mul (by linarith)
  refine ⟨hHp, Nat.floor_le (by positivity), ?_, hceil⟩
  have hJ := Nat.le_ceil (32*M)
  have hm := mul_le_mul_of_nonneg_right hJ
    (Nat.cast_nonneg (α := ℝ) ⌊Q/(4*M)⌋₊)
  have hh : (⌈R⌉₊ : ℝ) ≤ ((⌈32*M⌉₊+1)*⌊Q/(4*M)⌋₊ : ℕ) := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) ⌊Q/(4*M)⌋₊]
  exact_mod_cast hh

private lemma agent4WG_progression_ok (S : Finset ℤ) (q : ℕ) (hq : 0 < q)
    (v : ℤ) (f : ℤ → ℂ) (B : ℝ)
    (hB : ∀ θ : ℝ, ‖∑ h ∈ S, expTwoPiI (θ * (h : ℝ)) * f h‖ ≤ B) :
    ‖∑ h ∈ S.filter (fun h => h ≡ v [ZMOD (q : ℤ)]), f h‖ ≤ B := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  let ψ : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  have hind (h : ℤ) :
      (∑ t : ZMod q, ψ (t * ((h : ZMod q) - (v : ZMod q)))) =
        if h ≡ v [ZMOD (q : ℤ)] then (q : ℂ) else 0 := by
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
    simp only [sub_eq_zero, ZMod.card,
      ZMod.intCast_eq_intCast_iff, Nat.cast_ite, Nat.cast_zero]
  have hchar (t : ZMod q) (w : ℤ) :
      ψ (t * (w : ZMod q)) =
        expTwoPiI (((t.val : ℝ) / (q : ℝ)) * (w : ℝ)) := by
    change ZMod.stdAddChar (t * (w : ZMod q)) = _
    rw [show t * (w : ZMod q) = (((t.val : ℤ) * w : ℤ) : ZMod q) by
      push_cast
      rw [ZMod.natCast_zmod_val]]
    rw [ZMod.stdAddChar_coe]
    unfold expTwoPiI
    push_cast
    congr 1
    ring
  have hphase (t : ZMod q) (h : ℤ) :
      ψ (t * ((h : ZMod q) - (v : ZMod q))) =
        expTwoPiI (-((t.val : ℝ) / (q : ℝ)) * (v : ℝ)) *
          expTwoPiI (((t.val : ℝ) / (q : ℝ)) * (h : ℝ)) := by
    rw [← Int.cast_sub, hchar, ← onb_exp_add]
    congr 1
    push_cast
    ring
  have he :
      (q : ℂ) * (∑ h ∈ S.filter (fun h => h ≡ v [ZMOD (q : ℤ)]), f h) =
        ∑ t : ZMod q, ∑ h ∈ S,
          ψ (t * ((h : ZMod q) - (v : ZMod q))) * f h := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hind]
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    split_ifs <;> simp
  have ht (t : ZMod q) :
      ‖∑ h ∈ S, ψ (t * ((h : ZMod q) - (v : ZMod q))) * f h‖ ≤ B := by
    simp_rw [hphase, mul_assoc]
    rw [← Finset.mul_sum, norm_mul,
      LocalizedFourierFinal.FourierMassBounds.exp_norm, one_mul]
    exact hB _
  have hn :
      (q : ℝ) * ‖∑ h ∈ S.filter (fun h => h ≡ v [ZMOD (q : ℤ)]), f h‖ ≤
        (q : ℝ) * B := by
    calc
      _ = ‖(q : ℂ) *
          (∑ h ∈ S.filter (fun h => h ≡ v [ZMOD (q : ℤ)]), f h)‖ := by
        simp only [norm_mul, Complex.norm_natCast]
      _ = _ := congrArg norm he
      _ ≤ ∑ t : ZMod q,
          ‖∑ h ∈ S, ψ (t * ((h : ZMod q) - (v : ZMod q))) * f h‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _t : ZMod q, B := Finset.sum_le_sum (fun t _ => ht t)
      _ = _ := by simp [ZMod.card]
  have hp : (0 : ℝ) < q := by exact_mod_cast hq
  nlinarith

private lemma agent4WG_interval_bound_ok (A M α : ℝ) (hA : 1 ≤ A) (hM : 1 ≤ M)
    (hα : Irrational α)
    (hbpq : ∀ i x, (GenContFract.of α).partDens.get? i = some x → x ≤ A)
    (s : ℕ) (a q abar : ℤ)
    (hnum : (a : ℝ) = (GenContFract.of α).nums s)
    (hden : (q : ℝ) = (GenContFract.of α).dens s)
    (habar : a*abar ≡ 1 [ZMOD q]) (habar0 : 0 ≤ abar) (habarq : abar < q)
    (m n : ℤ) (hm : 1 ≤ |m|) (hmM : |(m : ℝ)| ≤ M)
    (hn : 1 ≤ |n|) (hnM : |(n : ℝ)| ≤ M)
    (R : ℝ) (hR : 1 ≤ R) (hRq : R ≤ 2*(q:ℝ)) (β : ℝ) (N : ℤ) :
    ‖∑ h ∈ Finset.Ico N (N+⌈R⌉),
      expTwoPiI (((m:ℝ)/(n:ℝ)*((abar:ℝ)/(4*(q:ℝ))))*(h:ℝ)^2+β*(h:ℝ))‖ ≤
    (128*M + ((⌈32*M⌉₊+1 : ℕ):ℝ)*Real.sqrt (4+288*A*M^2)+1) *
      Real.sqrt (R*Real.log (2*R)) := by
  let γ := (m:ℝ)/(n:ℝ)*((abar:ℝ)/(4*(q:ℝ)))
  let T := ⌈R⌉₊
  let J := ⌈32*M⌉₊+1
  let K := Real.sqrt (4+288*A*M^2)
  let W := Real.sqrt (R*Real.log (2*R))
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hW : 0 ≤ W := Real.sqrt_nonneg _
  have hlog := agent4WG_log R hR
  have hlog0 : 0 ≤ Real.log (2*R) := by linarith
  have hWsq : W^2 = R*Real.log (2*R) := Real.sq_sqrt (by positivity)
  have hWhalf : (1:ℝ)/2 ≤ W := by
    have hm := mul_le_mul_of_nonneg_left hlog (show 0≤R by linarith)
    nlinarith
  have hT : (T:ℝ) ≤ 2*R := Nat.ceil_le_two_mul (by linarith)
  rw [← Int.natCast_ceil_eq_ceil (show 0≤R by linarith), agent4WG_interval]
  change ‖∑ j ∈ Finset.range T,
    expTwoPiI (γ*((N+(j:ℤ):ℤ):ℝ)^2+β*((N+(j:ℤ):ℤ):ℝ))‖ ≤
      (128*M+(J:ℝ)*K+1)*W
  by_cases hq : 16*M ≤ (q:ℝ)
  · have hs : 1 ≤ s := by
      by_contra hh
      have he : s=0 := by omega
      rw [he, GenContFract.zeroth_den_eq_one] at hden
      linarith
    let H := ⌊(q:ℝ)/(4*M)⌋₊
    have hsize := agent4WG_block_sizes M q R hM hq hR hRq
    have hlocal (o u : ℕ) (huH : u ≤ H) (huT : u ≤ T) :
        ‖∑ j ∈ Finset.range u,
          expTwoPiI (γ*((N+((o+j:ℕ):ℤ):ℤ):ℝ)^2+
            β*((N+((o+j:ℕ):ℤ):ℤ):ℝ))‖ ≤ K*W := by
      by_cases hu : u=0
      · simp [hu, mul_nonneg hK hW]
      have hu1 : 1 ≤ u := by omega
      have huH' : (u:ℝ) ≤ H := by exact_mod_cast huH
      have huT' : (u:ℝ) ≤ T := by exact_mod_cast huT
      have hsmall : (u:ℝ) ≤ (q:ℝ)/(4*M) := huH'.trans hsize.2.1
      have hsquare := agent4WG_local_sq_ok A M α hA hM hα hbpq s hs a q abar
        hnum hden hq habar habar0 habarq m n hm hmM hn hnM u hu1 hsmall
        (2*γ*((N+(o:ℤ):ℤ):ℝ)+β)
      have he : (∑ j ∈ Finset.range u,
          expTwoPiI (γ*((N+((o+j:ℕ):ℤ):ℤ):ℝ)^2+β*((N+((o+j:ℕ):ℤ):ℤ):ℝ))) =
          ∑ j ∈ Finset.range u,
            expTwoPiI (γ*(((N+(o:ℤ):ℤ):ℝ)+j)^2+β*(((N+(o:ℤ):ℤ):ℝ)+j)) := by
        push_cast
        simp only [add_assoc]
      rw [he, agent4WG_shift]
      exact agent4WG_local_convert A M R u _ hA hM hR
        (by exact_mod_cast hu1) (huT'.trans hT) (norm_nonneg _) hsquare
    have hb := agent4WG_blocks
      (fun j : ℕ => expTwoPiI (γ*((N+(j:ℤ):ℤ):ℝ)^2+β*((N+(j:ℤ):ℤ):ℝ)))
      H T J (K*W) (mul_nonneg hK hW) hlocal 0 T hsize.2.2.1 le_rfl
    simp only [zero_add] at hb
    apply hb.trans
    have hz : 0 ≤ (128*M+1)*W := by positivity
    nlinarith
  · have hb : ‖∑ j ∈ Finset.range T,
        expTwoPiI (γ*((N+(j:ℤ):ℤ):ℝ)^2+β*((N+(j:ℤ):ℤ):ℝ))‖ ≤ (T:ℝ) := by
      apply (norm_sum_le _ _).trans_eq
      simp [LocalizedFourierFinal.FourierMassBounds.exp_norm]
    apply hb.trans
    have hj : 0 ≤ (J:ℝ)*K*W := by positivity
    have hh := mul_le_mul_of_nonneg_left hWhalf (show 0≤128*M by positivity)
    nlinarith

noncomputable def weylProgIco (N : ℤ) (R : ℝ) (v r : ℤ) : Finset ℤ :=
  (Finset.Ico N (N + ⌈R⌉)).filter fun h => (h : ℝ) < (N : ℝ) + R ∧ h ≡ v [ZMOD r]

/-- The quadratic exponential sum `∑_{N ≤ h < N + R, h ≡ v (mod r)} e(α' h² + β h)`
over an arithmetic progression inside an interval of length `R`. -/
noncomputable def weylProgSum (alpha' beta : ℝ) (N : ℤ) (R : ℝ) (v r : ℤ) : ℂ :=
  ∑ h ∈ weylProgIco N R v r, expTwoPiI (alpha' * (h : ℝ) ^ 2 + beta * (h : ℝ))

private lemma agent4WG_filter_exact (N : ℤ) (R : ℝ) (v r : ℤ) :
    weylProgIco N R v r =
      (Finset.Ico N (N + ⌈R⌉)).filter (fun h => h ≡ v [ZMOD r]) := by
  classical
  ext h
  simp only [weylProgIco, Finset.mem_filter, Finset.mem_Ico]
  have hh : h < N + ⌈R⌉ → (h : ℝ) < (N : ℝ) + R := by
    intro hh
    have he : h - N < ⌈R⌉ := by omega
    have he' := Int.lt_ceil.mp he
    push_cast at he'
    linarith
  tauto

/-- **Weyl differencing for the inverted convergent denominator.**
Let `A, M ≥ 1`, let `α` be irrational with all partial quotients `aᵢ ≤ A`, let `a / q` be any
convergent of `α` (including the zeroth one) and let `abar ∈ [0, q)` be the modular inverse of
`a` modulo `q`.  Then, for all `1 ≤ R ≤ 2q`, uniformly in `β ∈ ℝ`, in integers `m, n` with
`1 ≤ |m|, |n| ≤ M`, in `N ∈ ℤ` and in `v, r ≥ 1`,
`|∑_{N ≤ h < N + R, h ≡ v (mod r)} e((m/n) · (abar/(4q)) · h² + β h)| ≪_{M,A} √(R log(2R))`. -/
theorem lem_weylgauss (A M : ℝ) (hA : 1 ≤ A) (hM : 1 ≤ M) :
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
            C * Real.sqrt (R * Real.log (2 * R)) := by
  refine ⟨128*M + ((⌈32*M⌉₊+1 : ℕ):ℝ)*Real.sqrt (4+288*A*M^2)+1,
    by positivity, ?_⟩
  intro α hα hbpq s a q hnum hden abar habar habar0 habarq R hR hRq
    beta m n hm hmM hn hnM N v r hv hr
  let γ := (m:ℝ)/(n:ℝ)*((abar:ℝ)/(4*(q:ℝ)))
  have hr0 : (r.toNat:ℤ)=r := Int.toNat_of_nonneg (by omega)
  unfold weylProgSum
  rw [agent4WG_filter_exact, ← hr0]
  apply agent4WG_progression_ok _ r.toNat (by omega) v _ _
  intro θ
  have he (h : ℤ) : expTwoPiI (θ*(h:ℝ)) *
      expTwoPiI (γ*(h:ℝ)^2+beta*(h:ℝ)) =
      expTwoPiI (γ*(h:ℝ)^2+(beta+θ)*(h:ℝ)) := by
    rw [← onb_exp_add]
    congr 1
    ring
  change ‖∑ h ∈ Finset.Ico N (N+⌈R⌉),
    expTwoPiI (θ*(h:ℝ))*expTwoPiI (γ*(h:ℝ)^2+beta*(h:ℝ))‖ ≤ _
  simp_rw [he]
  exact agent4WG_interval_bound_ok A M α hA hM hα hbpq s a q abar hnum hden
    habar habar0 habarq m n hm hmM hn hnM R hR hRq (beta+θ) N
noncomputable def multiwallSTerm (α : ℝ) (c : ℕ) (U : ℝ → ℂ) (P : ℕ) (γ : ℝ)
    (h : ℤ) : ℂ :=
  U ((h : ℝ) / (P : ℝ)) * expTwoPiI (α * (c : ℝ) * (h : ℝ) ^ 2 + γ * (h : ℝ))

noncomputable def multiwallS (α : ℝ) (c : ℕ) (U : ℝ → ℂ) (P : ℕ) (γ : ℝ) : ℂ :=
  ∑' h : ℤ, multiwallSTerm α c U P γ h

noncomputable def multiwallTerm (k r : ℕ) (α : ℝ) (c : Fin k → ℕ) (β : Fin k → ℝ)
    (U : ℝ → ℂ) (P : ℕ) (w : Fin r → Fin k → ℤ) (B : Fin r → ℤ)
    (h : Fin k → ℤ) : ℂ :=
  (∏ i, ((Int.sign (2 * ((∑ s, w i s * h s) - B i) + 1) : ℤ) : ℂ)) *
    (∏ j, U ((h j : ℝ) / (P : ℝ))) *
    expTwoPiI (α * ∑ j, (c j : ℝ) * (h j : ℝ) ^ 2 + ∑ j, β j * (h j : ℝ))

noncomputable def multiwallT (k r : ℕ) (α : ℝ) (c : Fin k → ℕ) (β : Fin k → ℝ)
    (U : ℝ → ℂ) (P : ℕ) (w : Fin r → Fin k → ℤ) (B : Fin r → ℤ) : ℂ :=
  ∑' h : Fin k → ℤ, multiwallTerm k r α c β U P w B h

private lemma mw_cutoff_zero_ok (P : ℕ) (hP : 1 ≤ P) (U : ℝ → ℂ)
    (hs : Function.support U ⊆ Set.Icc (-2 : ℝ) 2) (n : ℤ)
    (hn : n ∉ Finset.Icc (-2*(P:ℤ)) (2*(P:ℤ))) : U ((n:ℝ)/P) = 0 := by
  by_contra hz
  have hh := hs hz
  have hp : (0:ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hlo := (le_div_iff₀ hp).mp hh.1
  have hhi := (div_le_iff₀ hp).mp hh.2
  apply hn
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hhi

theorem multiwall_sgn_fourier_expansion
    (k r P q : ℕ) (hk : 1 ≤ k) (hP : 1 ≤ P) (hPq : P ≤ q)
    (U : ℝ → ℂ) (hUsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U)
    (hUsupp : Function.support U ⊆ Set.Icc (-2 : ℝ) 2)
    (w : Fin r → Fin k → ℤ) (hw0 : ∀ i, w i ≠ 0) (B : Fin r → ℤ)
    (hwB : ∀ x : Fin k → ℤ, (∀ j, |x j| ≤ 2 * (P : ℤ)) →
      ∀ i, 4 * |(∑ s, w i s * x s) - B i| ≤ (q : ℤ))
    (h : Fin k → ℤ) (hsupp : (∏ j, U ((h j : ℝ) / (P : ℝ))) ≠ 0) (i : Fin r) :
    ((Int.sign (2 * ((∑ s, w i s * h s) - B i) + 1) : ℤ) : ℂ) =
      ∑ v ∈ Finset.Ioo (-(q : ℤ)) (q : ℤ),
        sgnCoeff (2 * q) v *
          expTwoPiI ((((1 - 2 * B i) * v : ℤ) : ℝ) / (2 * (q : ℝ))) *
          expTwoPiI (((v * (∑ s, w i s * h s) : ℤ) : ℝ) / (q : ℝ)) := by
  classical
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hx : ∀ j, |h j| ≤ 2 * (P : ℤ) := by
    intro j
    have hu : U ((h j : ℝ) / (P : ℝ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hsupp j (Finset.mem_univ j)
    obtain ⟨hlo, hhi⟩ := hUsupp hu
    have hab : |(h j : ℝ) / (P : ℝ)| ≤ 2 := abs_le.mpr ⟨hlo, hhi⟩
    rw [abs_div, abs_of_pos hPpos] at hab
    have hh := (div_le_iff₀ hPpos).mp hab
    exact_mod_cast hh
  have hq4 : 4 ≤ q := by
    by_contra hq4
    have hz := hwB (fun _ => 0) (by intro j; simpa using
      (show (0 : ℤ) ≤ 2 * (P : ℤ) by positivity)) i
    simp only [mul_zero, Finset.sum_const_zero, zero_sub, abs_neg] at hz
    have hB0 : B i = 0 := abs_eq_zero.mp (by have := abs_nonneg (B i); omega)
    apply hw0 i
    funext j
    have hj := hwB (fun s => if s = j then 1 else 0)
      (by intro s; split_ifs <;> norm_num <;> omega) i
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hB0, sub_zero] at hj
    exact abs_eq_zero.mp (by have := abs_nonneg (w i j); omega)
  have hh := hwB h hx i
  have hsign : 2 * |2 * ((∑ s, w i s * h s) - B i) + 1| < ((2*q : ℕ) : ℤ) := by
    have hab := abs_add_le (2 * ((∑ s, w i s * h s) - B i)) 1
    rw [abs_mul] at hab
    norm_num at hab
    push_cast
    omega
  rw [lem_sgn (2*q) (by omega) (show Even (2*q) from ⟨q, by omega⟩) _ hsign]
  have hhalf : ((2*q : ℕ) : ℤ) / 2 = (q : ℤ) := by push_cast; omega
  rw [sgnIndex, hhalf, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases ho : Odd v
  · rw [if_pos ho, mul_assoc, ← onb_exp_add]
    congr 2
    push_cast
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    field_simp
    <;> ring
  · rw [if_neg ho, sgnCoeff_of_even _ _ (Int.not_odd_iff_even.mp ho)]
    simp

private lemma mw_phase_factor_ok (k r P q : ℕ) (α : ℝ) (c : Fin k → ℕ)
    (β : Fin k → ℝ) (U : ℝ → ℂ) (w : Fin r → Fin k → ℤ)
    (B : Fin r → ℤ) (v : Fin r → ℤ) (h : Fin k → ℤ) :
    (∏ i, sgnCoeff (2*q) (v i) *
      expTwoPiI ((((1-2*B i)*v i:ℤ):ℝ)/(2*(q:ℝ))) *
      expTwoPiI (((v i*(∑ s, w i s*h s):ℤ):ℝ)/(q:ℝ))) *
      (∏ j, U ((h j:ℝ)/P)) *
      expTwoPiI (α * ∑ j, (c j:ℝ)*(h j:ℝ)^2 + ∑ j, β j*(h j:ℝ)) =
    (∏ i, sgnCoeff (2*q) (v i) *
      expTwoPiI ((((1-2*B i)*v i:ℤ):ℝ)/(2*(q:ℝ)))) *
      ∏ j, multiwallSTerm α (c j) U P
        (β j + ((∑ i, v i*w i j:ℤ):ℝ)/(q:ℝ)) (h j) := by
  simp only [Finset.prod_mul_distrib, multiwallSTerm]
  simp_rw [← onb_exp_sum]
  have he : (∑ i, ((v i * ∑ s, w i s*h s:ℤ):ℝ)/(q:ℝ)) +
      (α * ∑ j, (c j:ℝ)*(h j:ℝ)^2 + ∑ j, β j*(h j:ℝ)) =
      ∑ j, (α*(c j:ℝ)*(h j:ℝ)^2 +
        (β j + ((∑ i, v i*w i j:ℤ):ℝ)/(q:ℝ))*(h j:ℝ)) := by
    push_cast
    simp only [Finset.mul_sum, Finset.sum_div, add_mul, Finset.sum_add_distrib,
      Finset.sum_mul, mul_assoc, div_mul_eq_mul_div]
    rw [Finset.sum_comm]
    ring
  rw [show (∏ i, sgnCoeff (2*q) (v i)) *
      expTwoPiI (∑ i, (((1-2*B i)*v i:ℤ):ℝ)/(2*(q:ℝ))) *
      expTwoPiI (∑ i, ((v i * ∑ s, w i s*h s:ℤ):ℝ)/(q:ℝ)) *
      (∏ j, U ((h j:ℝ)/P)) *
      expTwoPiI (α * ∑ j, (c j:ℝ)*(h j:ℝ)^2 + ∑ j, β j*(h j:ℝ)) =
    ((∏ i, sgnCoeff (2*q) (v i)) *
      expTwoPiI (∑ i, (((1-2*B i)*v i:ℤ):ℝ)/(2*(q:ℝ)))) *
      (∏ j, U ((h j:ℝ)/P)) *
      (expTwoPiI (∑ i, ((v i * ∑ s, w i s*h s:ℤ):ℝ)/(q:ℝ)) *
      expTwoPiI (α * ∑ j, (c j:ℝ)*(h j:ℝ)^2 + ∑ j, β j*(h j:ℝ))) by ring]
  rw [← onb_exp_add, he]
  ring

theorem multiwall_T_factorization
    (k r P q : ℕ) (hk : 1 ≤ k) (hP : 1 ≤ P) (hPq : P ≤ q)
    (α : ℝ) (c : Fin k → ℕ) (hc : ∀ j, 1 ≤ c j) (β : Fin k → ℝ)
    (U : ℝ → ℂ) (hUsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U)
    (hUsupp : Function.support U ⊆ Set.Icc (-2 : ℝ) 2)
    (w : Fin r → Fin k → ℤ) (hw0 : ∀ i, w i ≠ 0) (B : Fin r → ℤ)
    (hwB : ∀ x : Fin k → ℤ, (∀ j, |x j| ≤ 2 * (P : ℤ)) →
      ∀ i, 4 * |(∑ s, w i s * x s) - B i| ≤ (q : ℤ)) :
    Summable (multiwallTerm k r α c β U P w B) ∧
      (∀ (j : Fin k) (γ : ℝ), Summable (multiwallSTerm α (c j) U P γ)) ∧
      multiwallT k r α c β U P w B =
        ∑ v ∈ Fintype.piFinset (fun _ : Fin r => Finset.Ioo (-(q : ℤ)) (q : ℤ)),
          (∏ i, sgnCoeff (2 * q) (v i) *
              expTwoPiI ((((1 - 2 * B i) * v i : ℤ) : ℝ) / (2 * (q : ℝ)))) *
            ∏ j, multiwallS α (c j) U P
              (β j + ((∑ i, v i * w i j : ℤ) : ℝ) / (q : ℝ)) := by
  have hsign := multiwall_sgn_fourier_expansion k r P q hk hP hPq
    U hUsmooth hUsupp w hw0 B hwB
  classical
  let I : Finset ℤ := Finset.Icc (-2*(P:ℤ)) (2*(P:ℤ))
  let H := Fintype.piFinset (fun _ : Fin k => I)
  let V := Fintype.piFinset (fun _ : Fin r => Finset.Ioo (-(q:ℤ)) (q:ℤ))
  let C := fun v : Fin r → ℤ => ∏ i, sgnCoeff (2*q) (v i) *
    expTwoPiI ((((1-2*B i)*v i:ℤ):ℝ)/(2*(q:ℝ)))
  let g := fun (v : Fin r → ℤ) (j : Fin k) =>
    multiwallSTerm α (c j) U P (β j + ((∑ i, v i*w i j:ℤ):ℝ)/(q:ℝ))
  have hzero (h : Fin k → ℤ) (hh : h ∉ H) : (∏ j, U ((h j:ℝ)/P)) = 0 := by
    have hex : ∃ j, h j ∉ I := by
      by_contra hn
      apply hh
      apply Fintype.mem_piFinset.mpr
      simpa using not_exists.mp hn
    obtain ⟨j,hj⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ j)
      (mw_cutoff_zero_ok P hP U hUsupp _ hj)
  have htzero (h : Fin k → ℤ) (hh : h ∉ H) :
      multiwallTerm k r α c β U P w B h = 0 := by
    simp [multiwallTerm, hzero h hh]
  have hszero (j : Fin k) (γ : ℝ) (n : ℤ) (hn : n ∉ I) :
      multiwallSTerm α (c j) U P γ n = 0 := by
    simp [multiwallSTerm, mw_cutoff_zero_ok P hP U hUsupp n hn]
  refine ⟨summable_of_ne_finset_zero htzero,
    fun j γ => summable_of_ne_finset_zero (hszero j γ), ?_⟩
  have hpoint (h : Fin k → ℤ) : multiwallTerm k r α c β U P w B h =
      ∑ v ∈ V, C v * ∏ j, g v j (h j) := by
    by_cases hz : (∏ j, U ((h j:ℝ)/P)) = 0
    · simp only [multiwallTerm, hz, mul_zero, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro v hv
      dsimp [g, multiwallSTerm]
      rw [Finset.prod_mul_distrib, hz, zero_mul, mul_zero]
    · unfold multiwallTerm
      simp_rw [hsign h hz]
      rw [Finset.prod_univ_sum, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v hv
      exact mw_phase_factor_ok k r P q α c β U w B v h
  unfold multiwallT
  rw [tsum_eq_sum htzero]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.mul_sum]
  change C v * (∑ h ∈ H, ∏ j, g v j (h j)) = C v * _
  congr 1
  rw [← Finset.prod_univ_sum]
  apply Finset.prod_congr rfl
  intro j hj
  exact (tsum_eq_sum (hszero j _)).symm
noncomputable def multiwallDelta (α : ℝ) (a : ℤ) (q : ℕ) : ℝ :=
  α - (a : ℝ) / (q : ℝ)

def multiwallG (k r : ℕ) (w : Fin r → Fin k → ℤ) (v : Fin r → ℤ) (j : Fin k) : ℤ :=
  ∑ i, v i * w i j

noncomputable def multiwallSigma (k r : ℕ) (a : ℤ) (c : Fin k → ℕ) (q : ℕ) (hq : 0 < q)
    (w : Fin r → Fin k → ℤ) (B : Fin r → ℤ) (l : Fin k → ℤ) : ℂ :=
  ∑ v ∈ Fintype.piFinset (fun _ : Fin r => Finset.Ioo (-(q : ℤ)) (q : ℤ)),
    (∏ i, sgnCoeff (2 * q) (v i) *
        expTwoPiI ((((1 - 2 * B i) * v i : ℤ) : ℝ) / (2 * (q : ℝ)))) *
      ∏ j, quadGaussSum ((c j : ℤ) * a) (l j + multiwallG k r w v j) q hq /
        (Real.sqrt (q : ℝ) : ℂ)

theorem multiwall_Sj_poisson
    (k r P q s : ℕ) (hk : 1 ≤ k) (hP : 1 ≤ P) (hq : 0 < q)
    (α : ℝ) (hα : Irrational α) (a : ℤ)
    (hnum : (a : ℝ) = (GenContFract.of α).nums s)
    (hden : (q : ℝ) = (GenContFract.of α).dens s)
    (c : Fin k → ℕ) (hc : ∀ j, 1 ≤ c j) (β : Fin k → ℝ)
    (U : ℝ → ℂ) (hU : IsSmoothCutoff U)
    (w : Fin r → Fin k → ℤ) (v : Fin r → ℤ) (j : Fin k) :
    |multiwallDelta α a q| ≤ 1 / (q : ℝ) ^ 2 ∧
      Summable (fun l : ℤ =>
        quadGaussSum ((c j : ℤ) * a) (l + multiwallG k r w v j) q hq *
          oscIntegralW U ((c j : ℝ) * multiwallDelta α a q * (P : ℝ) ^ 2)
            ((P : ℝ) * (β j - (l : ℝ) / (q : ℝ)))) ∧
      multiwallS α (c j) U P (β j + ((multiwallG k r w v j : ℤ) : ℝ) / (q : ℝ)) =
        ((P : ℂ) / (q : ℂ)) *
          ∑' l : ℤ,
            quadGaussSum ((c j : ℤ) * a) (l + multiwallG k r w v j) q hq *
              oscIntegralW U ((c j : ℝ) * multiwallDelta α a q * (P : ℝ) ^ 2)
                ((P : ℝ) * (β j - (l : ℝ) / (q : ℝ))) := by
  have hnt : ¬ (GenContFract.of α).TerminatedAt s := by
    intro ht
    obtain ⟨v, hv⟩ := GenContFract.exists_rat_eq_of_terminates ⟨s, ht⟩
    exact hα ⟨v, hv.symm⟩
  have hpq : (0 : ℝ) < q := by exact_mod_cast hq
  have herr := GenContFract.abs_sub_convs_le hnt
  rw [GenContFract.conv_eq_num_div_den, ← hnum, ← hden] at herr
  have hmono : (q : ℝ) ≤ (GenContFract.of α).dens (s+1) := by
    rw [hden]
    exact GenContFract.of_den_mono
  have hdelta : |multiwallDelta α a q| ≤ 1/(q : ℝ)^2 := by
    apply herr.trans
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hmono hpq.le]
  have hp := lem_poisson_summation U hU (P : ℝ) (by exact_mod_cast hP) q hq
    ((c j : ℝ)*multiwallDelta α a q) (β j) ((c j : ℤ)*a) (multiwallG k r w v j)
  have hcoef : (((c j : ℤ)*a : ℤ) : ℝ)/(q : ℝ) +
      (c j : ℝ)*multiwallDelta α a q = α*(c j : ℝ) := by
    unfold multiwallDelta
    push_cast
    ring
  rw [hcoef] at hp
  refine ⟨hdelta, ?_, ?_⟩
  · simpa only [add_comm] using hp.1
  · simpa only [multiwallS, multiwallSTerm, Complex.ofReal_natCast,
      add_comm, mul_comm] using hp.2

private lemma agent4MW2_pair (k : ℕ) (f : ℤ → ℂ) (g : (Fin k → ℤ) → ℂ)
    (hf : Summable f) (hg : Summable g) :
    HasSum (fun x : ℤ × (Fin k → ℤ) => f x.1 * g x.2)
      ((∑' i, f i) * (∑' j, g j)) := by
  have hnf : Summable (fun i => ‖f i‖) := hf.norm
  have hng : Summable (fun j => ‖g j‖) := hg.norm
  have hfg := summable_mul_of_summable_norm (f := f) (g := g) hnf hng
  exact hf.hasSum.mul hg.hasSum hfg

private lemma agent4MW2_pi_good (k : ℕ) (f : Fin k → ℤ → ℂ)
    (hf : ∀ j, Summable (f j)) :
    HasSum (fun l : Fin k → ℤ => ∏ j, f j (l j)) (∏ j, ∑' n, f j n) := by
  classical
  induction k with
  | zero => simpa using hasSum_fintype (fun _ : Fin 0 → ℤ => (1:ℂ))
  | succ k ih =>
    let g : (Fin k → ℤ) → ℂ := fun l => ∏ j : Fin k, f j.succ (l j)
    have ht : HasSum g (∏ j : Fin k, ∑' n : ℤ, f j.succ n) :=
      ih (fun j => f j.succ) (fun j => hf j.succ)
    have hgs : Summable g := ht.summable
    have hp := agent4MW2_pair k (f 0) g (hf 0) hgs
    rw [ht.tsum_eq] at hp
    rw [Fin.prod_univ_succ]
    apply (Fin.consEquiv (fun _ : Fin (k+1) => ℤ)).hasSum_iff.mp
    apply hp.congr_fun
    intro l
    change (∏ j, f j (Fin.cons (α := fun _ : Fin (k+1) => ℤ) l.1 l.2 j)) = _
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, g]

set_option maxHeartbeats 2000000 in
theorem multiwall_T_exact_formula
    (k r P q s : ℕ) (hk : 1 ≤ k) (hP : 1 ≤ P) (hPq : P ≤ q) (hq : 0 < q)
    (α : ℝ) (hα : Irrational α) (a : ℤ)
    (hnum : (a : ℝ) = (GenContFract.of α).nums s)
    (hden : (q : ℝ) = (GenContFract.of α).dens s)
    (c : Fin k → ℕ) (hc : ∀ j, 1 ≤ c j) (β : Fin k → ℝ)
    (U : ℝ → ℂ) (hU : IsSmoothCutoff U)
    (w : Fin r → Fin k → ℤ) (hw0 : ∀ i, w i ≠ 0) (B : Fin r → ℤ)
    (hwB : ∀ x : Fin k → ℤ, (∀ j, |x j| ≤ 2 * (P : ℤ)) →
      ∀ i, 4 * |(∑ t, w i t * x t) - B i| ≤ (q : ℤ)) :
    Summable (fun l : Fin k → ℤ =>
        (∏ j, oscIntegralW U ((c j : ℝ) * multiwallDelta α a q * (P : ℝ) ^ 2)
            ((P : ℝ) * (β j - (l j : ℝ) / (q : ℝ)))) *
          multiwallSigma k r a c q hq w B l) ∧
      multiwallT k r α c β U P w B =
        ((P : ℂ) / (Real.sqrt (q : ℝ) : ℂ)) ^ k *
          ∑' l : Fin k → ℤ,
            (∏ j, oscIntegralW U ((c j : ℝ) * multiwallDelta α a q * (P : ℝ) ^ 2)
                ((P : ℝ) * (β j - (l j : ℝ) / (q : ℝ)))) *
              multiwallSigma k r a c q hq w B l := by
  classical
  let V := Fintype.piFinset (fun _ : Fin r => Finset.Ioo (-(q : ℤ)) (q : ℤ))
  let C := fun v : Fin r → ℤ => ∏ i, sgnCoeff (2*q) (v i) *
    expTwoPiI ((((1-2*B i)*v i : ℤ) : ℝ)/(2*(q : ℝ)))
  let W := fun (j : Fin k) (l : ℤ) => oscIntegralW U
    ((c j : ℝ)*multiwallDelta α a q*(P : ℝ)^2)
    ((P : ℝ)*(β j-(l : ℝ)/(q : ℝ)))
  let G := fun (v : Fin r → ℤ) (j : Fin k) (l : ℤ) =>
    quadGaussSum ((c j : ℤ)*a) (l+multiwallG k r w v j) q hq
  let Q : ℂ := Real.sqrt (q : ℝ)
  let f := fun (v : Fin r → ℤ) (j : Fin k) (l : ℤ) => G v j l * W j l / Q
  have hQ : Q ≠ 0 := by
    dsimp [Q]
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < q by exact_mod_cast hq)).ne'
  have hQsq : Q*Q = (q : ℂ) := by
    dsimp [Q]
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hSj (v : Fin r → ℤ) (j : Fin k) :=
    multiwall_Sj_poisson k r P q s hk hP hq α hα a hnum hden c hc β U hU w v j
  have hf (v : Fin r → ℤ) (j : Fin k) : Summable (f v j) := by
    simpa only [f, G, W, div_eq_mul_inv] using (hSj v j).2.1.mul_right Q⁻¹
  have hprod (v : Fin r → ℤ) := agent4MW2_pi_good k (f v) (hf v)
  have hsum := hasSum_sum (s := V) (fun v _ => (hprod v).mul_left (C v))
  have hpoint (l : Fin k → ℤ) :
      (∑ v ∈ V, C v * ∏ j, f v j (l j)) =
        (∏ j, W j (l j)) * multiwallSigma k r a c q hq w B l := by
    unfold multiwallSigma
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    change C v * (∏ j, G v j (l j) * W j (l j) / Q) =
      (∏ j, W j (l j)) * (C v * ∏ j, G v j (l j) / Q)
    simp only [div_eq_mul_inv, Finset.prod_mul_distrib]
    ring
  simp_rw [hpoint] at hsum
  refine ⟨hsum.summable, ?_⟩
  have hfactor (v : Fin r → ℤ) (j : Fin k) :
      multiwallS α (c j) U P (β j+(multiwallG k r w v j : ℝ)/(q : ℝ)) =
        ((P : ℂ)/Q) * ∑' l : ℤ, f v j l := by
    rw [(hSj v j).2.2]
    change ((P : ℂ)/(q : ℂ)) * (∑' l : ℤ, G v j l * W j l) =
      ((P : ℂ)/Q) * ∑' l : ℤ, (G v j l * W j l)/Q
    simp only [div_eq_mul_inv, tsum_mul_right]
    rw [← hQsq]
    ring
  have ht := (multiwall_T_factorization k r P q hk hP hPq α c hc β U hU.1 hU.2
    w hw0 B hwB).2.2
  rw [ht]
  change (∑ v ∈ V, C v * ∏ j,
    multiwallS α (c j) U P (β j+(multiwallG k r w v j : ℝ)/(q : ℝ))) = _
  simp_rw [hfactor]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  change _ = ((P : ℂ)/Q)^k * ∑' l : Fin k → ℤ,
    (∏ j, W j (l j)) * multiwallSigma k r a c q hq w B l
  rw [hsum.tsum_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring
def multiwallQ (k : ℕ) (c : Fin k → ℕ) : ℕ := 2 * ∏ j, c j

def multiwallM (k r : ℕ) (c : Fin k → ℕ) (w : Fin r → Fin k → ℤ) (i : Fin r) : ℤ :=
  ∑ j, (w i j) ^ 2 * ∏ t ∈ Finset.univ.erase j, (c t : ℤ)

noncomputable def multiwallSigmaWeight (r q : ℕ) (B : Fin r → ℤ) (v : Fin r → ℤ) : ℂ :=
  ∏ i, sgnCoeff (2 * q) (v i) *
    expTwoPiI ((((1 - 2 * B i) * v i : ℤ) : ℝ) / (2 * (q : ℝ)))

noncomputable def multiwallQuadPhase (k r : ℕ) (abar : ℤ) (c : Fin k → ℕ) (q : ℕ)
    (w : Fin r → Fin k → ℤ) (l : Fin k → ℤ) (v : Fin r → ℤ) : ℝ :=
  -(abar : ℝ) / (4 * (q : ℝ)) *
    ∑ j, ((l j + multiwallG k r w v j : ℤ) : ℝ) ^ 2 / (c j : ℝ)

noncomputable def multiwallSigmaClass (k r : ℕ) (abar : ℤ) (c : Fin k → ℕ) (q Q : ℕ)
    (w : Fin r → Fin k → ℤ) (B : Fin r → ℤ) (l : Fin k → ℤ) (ρ : Fin r → ℤ) : ℂ := by
  classical
  exact ∑ v ∈ (Fintype.piFinset fun _ : Fin r => Finset.Ioo (-(q : ℤ)) (q : ℤ)).filter
      (fun v => ∀ i, v i ≡ ρ i [ZMOD (Q : ℤ)]),
    multiwallSigmaWeight r q B v * expTwoPiI (multiwallQuadPhase k r abar c q w l v)

theorem multiwall_Sigma_gaussphase_form
    (k r q : ℕ) (hk : 1 ≤ k) (hq : 0 < q) (a abar : ℤ) (c : Fin k → ℕ)
    (hc : ∀ j, 1 ≤ c j)
    (ha : Int.gcd a q = 1) (habar : a * abar ≡ 1 [ZMOD (q : ℤ)])
    (habar0 : 0 ≤ abar) (habarq : abar < (q : ℤ))
    (w : Fin r → Fin k → ℤ) (B : Fin r → ℤ) (l : Fin k → ℤ) :
    multiwallSigma k r a c q hq w B l =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin r => Finset.Ioo (-(q : ℤ)) (q : ℤ)),
        multiwallSigmaWeight r q B v *
          ∏ j, gaussPhasePhi a abar (c j) q hq (l j + multiwallG k r w v j) *
            expTwoPiI (-((abar : ℝ) * ((l j + multiwallG k r w v j : ℤ) : ℝ) ^ 2) /
              (4 * (c j : ℝ) * (q : ℝ))) := by
  classical
  have hs : (Real.sqrt (q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < q by exact_mod_cast hq)).ne'
  unfold multiwallSigma multiwallSigmaWeight
  apply Finset.sum_congr rfl
  intro v hv
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [(lem_gaussphase a abar (c j) q (hc j) hq ha habar).1]
  field_simp

theorem multiwall_gaussphase_prod_const_on_class
    (k r q : ℕ) (hk : 1 ≤ k) (hq : 0 < q) (a abar : ℤ) (c : Fin k → ℕ)
    (hc : ∀ j, 1 ≤ c j)
    (ha : Int.gcd a q = 1) (habar : a * abar ≡ 1 [ZMOD (q : ℤ)])
    (habar0 : 0 ≤ abar) (habarq : abar < (q : ℤ))
    (w : Fin r → Fin k → ℤ) (l : Fin k → ℤ) (v v' : Fin r → ℤ)
    (hvv : ∀ i, v i ≡ v' i [ZMOD ((multiwallQ k c : ℕ) : ℤ)]) :
    (∏ j, gaussPhasePhi a abar (c j) q hq (l j + multiwallG k r w v j)) =
      ∏ j, gaussPhasePhi a abar (c j) q hq (l j + multiwallG k r w v' j) := by
  classical
  apply Finset.prod_congr rfl
  intro j hj
  have hp : Function.Periodic (gaussPhasePhi a abar (c j) q hq)
      (2 * (c j : ℤ)) :=
    (lem_gaussphase a abar (c j) q (hc j) hq ha habar).2.1
  have hdiv : 2 * (c j : ℤ) ∣ (multiwallQ k c : ℤ) := by
    have he := Finset.prod_erase_mul (Finset.univ : Finset (Fin k))
      (fun t => (c t : ℤ)) (Finset.mem_univ j)
    refine ⟨∏ t ∈ Finset.univ.erase j, (c t : ℤ), ?_⟩
    unfold multiwallQ
    push_cast
    rw [← he]
    ring
  have hvdiv (i : Fin r) : 2 * (c j : ℤ) ∣ v' i - v i :=
    dvd_trans hdiv (Int.modEq_iff_dvd.mp (hvv i))
  have hG : 2 * (c j : ℤ) ∣
      multiwallG k r w v' j - multiwallG k r w v j := by
    unfold multiwallG
    rw [← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro i hi
    rw [← sub_mul]
    exact dvd_mul_of_dvd_left (hvdiv i) (w i j)
  obtain ⟨n, hn⟩ := hG
  have he : l j + multiwallG k r w v' j =
      (l j + multiwallG k r w v j) + n * (2 * (c j : ℤ)) := by
    linear_combination hn
  rw [he]
  exact ((hp.int_mul n) (l j + multiwallG k r w v j)).symm

private lemma mw3_fiber_bound_ok {ι κ : Type*} [Fintype κ] [Nonempty κ] [DecidableEq κ]
    (S : Finset ι) (p : ι → κ) (F : ι → ℂ) (g : κ → ℂ)
    (D : ℝ) (hD : 0 ≤ D) (hg : ∀ t, ‖g t‖ ≤ D) :
    ∃ t : κ, ‖∑ v ∈ S, g (p v) * F v‖ ≤
      (Fintype.card κ : ℝ) * D * ‖∑ v ∈ S.filter (fun v => p v = t), F v‖ := by
  classical
  let f (t : κ) := ∑ v ∈ S.filter (fun v => p v = t), F v
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image Finset.univ (fun t => ‖f t‖)
    Finset.univ_nonempty
  refine ⟨t, ?_⟩
  have he : (∑ v ∈ S, g (p v) * F v) = ∑ t : κ, g t * f t := by
    simp only [f, Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    simp [mul_ite]
  rw [he]
  calc
    _ ≤ ∑ t : κ, ‖g t * f t‖ := norm_sum_le _ _
    _ ≤ ∑ _t : κ, D * ‖f t‖ := by
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul]
      exact mul_le_mul (hg u) (hmax u hu) (norm_nonneg _) hD
    _ = _ := by simp [f]; ring

private lemma mw3_combine_phase (k r q : ℕ) (abar : ℤ) (c : Fin k → ℕ)
    (w : Fin r → Fin k → ℤ) (l : Fin k → ℤ) (v : Fin r → ℤ) :
    (∏ j, expTwoPiI (-((abar : ℝ) * ((l j + multiwallG k r w v j : ℤ) : ℝ)^2) /
      (4*(c j : ℝ)*(q : ℝ)))) =
      expTwoPiI (multiwallQuadPhase k r abar c q w l v) := by
  rw [← onb_exp_sum]
  congr 1
  unfold multiwallQuadPhase
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem multiwall_Sigma_residue_class_bound
    (k r h : ℕ) (hk : 1 ≤ k) (hh : 1 ≤ h) :
    ∃ C > 0, ∀ (q : ℕ) (hq : 0 < q) (a abar : ℤ) (c : Fin k → ℕ),
      (∀ j, 1 ≤ c j) → (∀ j, c j ≤ h) →
      Int.gcd a q = 1 → a * abar ≡ 1 [ZMOD (q : ℤ)] → 0 ≤ abar → abar < (q : ℤ) →
      ∀ (w : Fin r → Fin k → ℤ) (B : Fin r → ℤ) (l : Fin k → ℤ),
        ∃ ρ : Fin r → ℤ, (∀ i, 0 ≤ ρ i ∧ ρ i < (multiwallQ k c : ℤ)) ∧
          ‖multiwallSigma k r a c q hq w B l‖ ≤
            C * ‖multiwallSigmaClass k r abar c q (multiwallQ k c) w B l ρ‖ := by
  classical
  refine ⟨((2 * h^k : ℕ) : ℝ)^r * (Real.sqrt (2*(h : ℝ)))^k, by positivity, ?_⟩
  intro q hq a abar c hc hch ha habar habar0 habarq w B l
  let Q := multiwallQ k c
  have hQ : 0 < Q := by
    apply Nat.mul_pos (by norm_num)
    exact Finset.prod_pos (fun j _ => by have := hc j; omega)
  letI : NeZero Q := ⟨hQ.ne'⟩
  let ρ (t : Fin r → Fin Q) : Fin r → ℤ := fun i => ((t i).val : ℤ)
  let p (v : Fin r → ℤ) : Fin r → Fin Q := fun i =>
    ⟨(v i % (Q : ℤ)).toNat, by
      have ht := Int.emod_lt_of_pos (v i) (show (0 : ℤ) < Q by exact_mod_cast hQ)
      have hn := Int.emod_nonneg (v i) (show (Q : ℤ) ≠ 0 by exact_mod_cast hQ.ne')
      omega⟩
  have hp (v : Fin r → ℤ) (i : Fin r) : v i ≡ ρ (p v) i [ZMOD (Q : ℤ)] := by
    dsimp [ρ, p]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hQ.ne'))]
    exact (Int.mod_modEq _ _).symm
  have hpiff (v : Fin r → ℤ) (t : Fin r → Fin Q) :
      p v = t ↔ ∀ i, v i ≡ ρ t i [ZMOD (Q : ℤ)] := by
    constructor
    · rintro rfl
      exact hp v
    · intro hv
      funext i
      apply Fin.ext
      have he : v i % (Q : ℤ) = ρ t i % (Q : ℤ) := hv i
      have ht0 : 0 ≤ ρ t i := by dsimp [ρ]; positivity
      have htQ : ρ t i < (Q : ℤ) := by
        dsimp [ρ]
        exact_mod_cast (t i).isLt
      rw [Int.emod_eq_of_lt ht0 htQ] at he
      change (v i % (Q : ℤ)).toNat = (t i).val
      rw [he]
      simp [ρ]
  let S := Fintype.piFinset (fun _ : Fin r => Finset.Ioo (-(q : ℤ)) (q : ℤ))
  let F (v : Fin r → ℤ) := multiwallSigmaWeight r q B v *
    expTwoPiI (multiwallQuadPhase k r abar c q w l v)
  let g (t : Fin r → Fin Q) :=
    ∏ j, gaussPhasePhi a abar (c j) q hq (l j + multiwallG k r w (ρ t) j)
  have hg (t : Fin r → Fin Q) : ‖g t‖ ≤ (Real.sqrt (2*(h : ℝ)))^k := by
    dsimp [g]
    rw [norm_prod]
    calc
      _ ≤ ∏ _j : Fin k, Real.sqrt (2*(h : ℝ)) := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro j hj
        apply ((lem_gaussphase a abar (c j) q (hc j) hq ha habar).2.2 _).trans
        apply Real.sqrt_le_sqrt
        have ht : (c j : ℝ) ≤ h := by exact_mod_cast hch j
        linarith
      _ = _ := by simp
  have he : multiwallSigma k r a c q hq w B l = ∑ v ∈ S, g (p v) * F v := by
    rw [multiwall_Sigma_gaussphase_form k r q hk hq a abar c hc ha habar habar0 habarq]
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.prod_mul_distrib, mw3_combine_phase]
    have hconst := multiwall_gaussphase_prod_const_on_class k r q hk hq a abar c hc
      ha habar habar0 habarq w l v (ρ (p v)) (hp v)
    rw [hconst]
    dsimp [g, F]
    ring
  obtain ⟨t, ht⟩ := mw3_fiber_bound_ok S p F g ((Real.sqrt (2*(h : ℝ)))^k)
    (by positivity) hg
  refine ⟨ρ t, ?_, ?_⟩
  · intro i
    exact ⟨by dsimp [ρ]; positivity, by dsimp [ρ]; exact_mod_cast (t i).isLt⟩
  have hclass : (∑ v ∈ S.filter (fun v => p v = t), F v) =
      multiwallSigmaClass k r abar c q Q w B l (ρ t) := by
    unfold multiwallSigmaClass
    simp only [hpiff]
    rfl
  rw [← he, hclass] at ht
  apply ht.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hQle : Q ≤ 2*h^k := by
    apply Nat.mul_le_mul_left
    calc
      _ ≤ ∏ _j : Fin k, h := Finset.prod_le_prod (fun j _ => hch j)
      _ = _ := by simp
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  gcongr

theorem multiwall_phase_quadratic_in_coord
    (k r q : ℕ) (hk : 1 ≤ k) (hq : 0 < q) (abar : ℤ) (c : Fin k → ℕ)
    (hc : ∀ j, 1 ≤ c j)
    (w : Fin r → Fin k → ℤ) (l : Fin k → ℤ) (u : Fin r → ℤ) (i : Fin r) :
    ∃ γ θ : ℝ, ∀ t : ℤ,
      multiwallQuadPhase k r abar c q w l (Function.update u i t) =
        -((multiwallM k r c w i : ℝ) / ∏ j, (c j : ℝ)) *
            ((abar : ℝ) / (4 * (q : ℝ))) * (t : ℝ) ^ 2 +
          γ * (t : ℝ) + θ := by
  classical
  let d : Fin k → ℝ := fun j =>
    ((l j + ∑ s ∈ Finset.univ.erase i, u s * w s j : ℤ) : ℝ)
  have hG (t : ℤ) (j : Fin k) :
      multiwallG k r w (Function.update u i t) j =
        (∑ s ∈ Finset.univ.erase i, u s * w s j) + t * w i j := by
    unfold multiwallG
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
  have he (t : ℤ) (j : Fin k) :
      ((l j + multiwallG k r w (Function.update u i t) j : ℤ) : ℝ) =
        (w i j : ℝ) * (t : ℝ) + d j := by
    rw [hG]
    dsimp [d]
    push_cast
    ring
  have hc0 (j : Fin k) : (c j : ℝ) ≠ 0 := by
    exact_mod_cast (show c j ≠ 0 by have := hc j; omega)
  have hp0 : (∏ j, (c j : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hc0 j)
  have hcoef : (multiwallM k r c w i : ℝ) / (∏ j, (c j : ℝ)) =
      ∑ j, (w i j : ℝ)^2 / (c j : ℝ) := by
    simp only [multiwallM, Int.cast_sum, Int.cast_mul, Int.cast_pow,
      Int.cast_prod, Int.cast_natCast, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    apply (div_eq_div_iff hp0 (hc0 j)).2
    rw [mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  have hexpand (t : ℤ) :
      (∑ j, ((w i j : ℝ) * (t : ℝ) + d j)^2 / (c j : ℝ)) =
        (∑ j, (w i j : ℝ)^2 / (c j : ℝ)) * (t : ℝ)^2 +
        (∑ j, 2 * d j * (w i j : ℝ) / (c j : ℝ)) * (t : ℝ) +
        ∑ j, (d j)^2 / (c j : ℝ) := by
    simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  refine ⟨-(abar : ℝ) / (4 * (q : ℝ)) *
      (∑ j, 2 * d j * (w i j : ℝ) / (c j : ℝ)),
    -(abar : ℝ) / (4 * (q : ℝ)) * (∑ j, (d j)^2 / (c j : ℝ)), ?_⟩
  intro t
  unfold multiwallQuadPhase
  simp_rw [he]
  rw [hexpand, hcoef]
  ring

theorem multiwall_M_bounds (k r V h : ℕ) (hk : 1 ≤ k) (hV : 1 ≤ V) (hh : 1 ≤ h)
    (c : Fin k → ℕ) (hc : ∀ j, 1 ≤ c j) (hch : ∀ j, c j ≤ h)
    (w : Fin r → Fin k → ℤ) (i : Fin r) (hw : w i ≠ 0)
    (hVw : ∑ j, |w i j| ≤ (V : ℤ)) :
    1 ≤ multiwallM k r c w i ∧
      multiwallM k r c w i ≤ (V : ℤ) ^ 2 * (h : ℤ) ^ k := by
  classical
  have hcpos (j : Fin k) : (0 : ℤ) < c j := by
    exact_mod_cast (show 0 < c j by have := hc j; omega)
  have hp (j : Fin k) : 0 < ∏ t ∈ Finset.univ.erase j, (c t : ℤ) :=
    Finset.prod_pos (fun t _ => hcpos t)
  have hall : (∏ t : Fin k, (c t : ℤ)) ≤ (h : ℤ)^k := by
    calc
      _ ≤ ∏ _t : Fin k, (h : ℤ) := Finset.prod_le_prod₀
        (fun t _ => (hcpos t).le) (fun t _ => by exact_mod_cast hch t)
      _ = _ := by simp
  have hpup (j : Fin k) : (∏ t ∈ Finset.univ.erase j, (c t : ℤ)) ≤ (h : ℤ)^k := by
    apply le_trans _ hall
    rw [← Finset.prod_erase_mul Finset.univ (fun t : Fin k => (c t : ℤ)) (Finset.mem_univ j)]
    have hj : (1 : ℤ) ≤ c j := by exact_mod_cast hc j
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hj (hp j).le
  have hterm (j : Fin k) : 0 ≤ (w i j)^2 * ∏ t ∈ Finset.univ.erase j, (c t : ℤ) :=
    mul_nonneg (sq_nonneg _) (hp j).le
  constructor
  · obtain ⟨j, hj⟩ : ∃ j, w i j ≠ 0 := by
      by_contra hn
      apply hw
      funext j
      simpa using not_exists.mp hn j
    have hab : 1 ≤ |w i j| := by have := abs_pos.mpr hj; omega
    have hsq : 1 ≤ (w i j)^2 := by nlinarith [sq_abs (w i j)]
    have hh : 1 ≤ (w i j)^2 * ∏ t ∈ Finset.univ.erase j, (c t : ℤ) := by
      have hh : 1 ≤ ∏ t ∈ Finset.univ.erase j, (c t : ℤ) := by have := hp j; omega
      simpa only [one_mul] using
        mul_le_mul hsq hh (by norm_num : (0 : ℤ) ≤ 1) (sq_nonneg (w i j))
    exact hh.trans (Finset.single_le_sum (fun t _ => hterm t) (Finset.mem_univ j))
  · have hW (j : Fin k) : |w i j| ≤ (V : ℤ) :=
      (Finset.single_le_sum (fun t _ => abs_nonneg (w i t)) (Finset.mem_univ j)).trans hVw
    have hs : (∑ j, (w i j)^2) ≤ (V : ℤ)^2 := by
      calc
        _ ≤ ∑ j, (V : ℤ) * |w i j| := by
          apply Finset.sum_le_sum
          intro j hj
          nlinarith [sq_abs (w i j),
            mul_le_mul_of_nonneg_right (hW j) (abs_nonneg (w i j))]
        _ = (V : ℤ) * ∑ j, |w i j| := (Finset.mul_sum _ _ _).symm
        _ ≤ (V : ℤ) * V := mul_le_mul_of_nonneg_left hVw (by positivity)
        _ = _ := by ring
    unfold multiwallM
    calc
      _ ≤ ∑ j, (w i j)^2 * (h : ℤ)^k := Finset.sum_le_sum
        (fun j _ => mul_le_mul_of_nonneg_left (hpup j) (sq_nonneg _))
      _ = (∑ j, (w i j)^2) * (h : ℤ)^k := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hs (by positivity)
def multiwallDyadicIndex (r q Q : ℕ) (ρ ε : Fin r → ℤ) (J : Fin r → ℕ) :
    Finset (Fin r → ℤ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin r => Finset.Ioo (-(q : ℤ)) (q : ℤ)).filter
    fun v => (∀ i, v i ≡ ρ i [ZMOD (Q : ℤ)]) ∧
      ∀ i, 2 ^ (J i) ≤ ε i * v i ∧ ε i * v i < 2 ^ (J i + 1)

noncomputable def multiwallDyadicPiece (k r : ℕ) (abar : ℤ) (c : Fin k → ℕ) (q Q : ℕ)
    (w : Fin r → Fin k → ℤ) (B : Fin r → ℤ) (l : Fin k → ℤ)
    (ρ ε : Fin r → ℤ) (J : Fin r → ℕ) : ℂ :=
  ∑ v ∈ multiwallDyadicIndex r q Q ρ ε J,
    multiwallSigmaWeight r q B v * expTwoPiI (multiwallQuadPhase k r abar c q w l v)

private lemma agent4Dyadic_abel_identity_ok (a : ℕ → ℝ) (f : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), (a j : ℂ) * f j) =
      (a n : ℂ) * (∑ j ∈ Finset.range (n+1), f j) +
        ∑ j ∈ Finset.range n, ((a j-a (j+1) : ℝ) : ℂ) *
          (∑ t ∈ Finset.range (j+1), f t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ (fun j => (a j : ℂ) * f j) (n+1), ih,
      Finset.sum_range_succ (fun j => f j) (n+1),
      Finset.sum_range_succ (fun j => ((a j-a (j+1) : ℝ) : ℂ) *
        (∑ t ∈ Finset.range (j+1), f t)) n]
    push_cast
    ring

private lemma agent4Dyadic_abel_bound_ok (a : ℕ → ℝ) (f : ℕ → ℂ)
    (n : ℕ) (D B : ℝ) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (ha : ∀ j, j ≤ n → |a j| ≤ D)
    (hmono : ∀ j, j < n → a (j+1) ≤ a j)
    (hf : ∀ j, j ≤ n → ‖∑ t ∈ Finset.range (j+1), f t‖ ≤ B) :
    ‖∑ j ∈ Finset.range (n+1), (a j : ℂ) * f j‖ ≤ 3*D*B := by
  rw [agent4Dyadic_abel_identity_ok]
  have hdiff (j : ℕ) (hj : j ∈ Finset.range n) : 0 ≤ a j-a (j+1) :=
    sub_nonneg.mpr (hmono j (Finset.mem_range.mp hj))
  have htel : (∑ j ∈ Finset.range n, (a j-a (j+1))) = a 0-a n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have ht := ih (fun j hj => ha j (by omega))
        (fun j hj => hmono j (by omega)) (fun j hj => hf j (by omega))
        (fun j hj => sub_nonneg.mpr
          (hmono j (by have := Finset.mem_range.mp hj; omega)))
      linarith
  calc
    _ ≤ ‖(a n : ℂ) * (∑ j ∈ Finset.range (n+1), f j)‖ +
        ∑ j ∈ Finset.range n, ‖((a j-a (j+1) : ℝ) : ℂ) *
          (∑ t ∈ Finset.range (j+1), f t)‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ D*B + ∑ j ∈ Finset.range n, (a j-a (j+1))*B := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (ha n le_rfl) (hf n le_rfl) (norm_nonneg _) hD
      · apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hdiff j hj)]
        exact mul_le_mul_of_nonneg_left
          (hf j (Finset.mem_range.mp hj).le) (hdiff j hj)
    _ = D*B + (a 0-a n)*B := by rw [← Finset.sum_mul, htel]
    _ ≤ _ := by
      have h0 := (abs_le.mp (ha 0 (Nat.zero_le n))).2
      have hn := (abs_le.mp (ha n le_rfl)).1
      nlinarith [mul_le_mul_of_nonneg_right
        (show a 0-a n ≤ 2*D by linarith) hB]

private lemma agent4Dyadic2026_numeric (J : ℕ) :
    ((2 : ℝ)^J)⁻¹ * Real.sqrt ((2 : ℝ)^J * Real.log (2 * (2 : ℝ)^J)) =
      Real.sqrt (Real.log 2) * Real.sqrt (1 + (J : ℝ)) *
        (2 : ℝ)^(-(J : ℝ)/2) := by
  have hlog : Real.log (2 * (2 : ℝ)^J) = (1+(J : ℝ))*Real.log 2 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    ring
  have hscale : ((2 : ℝ)^J)⁻¹ * Real.sqrt ((2 : ℝ)^J) =
      (2 : ℝ)^(-(J : ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_neg_one, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  rw [hlog, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  calc
    _ = (((2 : ℝ)^J)⁻¹ * Real.sqrt ((2 : ℝ)^J)) *
        Real.sqrt (1+(J : ℝ)) * Real.sqrt (Real.log 2) := by ring
    _ = _ := by rw [hscale]; ring

private lemma agent4Dyadic2026_l1 (q J : ℕ) (hq : 2 ≤ q) (S : Finset ℤ)
    (hcard : S.card ≤ 2^J)
    (hmem : ∀ t ∈ S, (2:ℤ)^J ≤ |t| ∧ |t| < (q:ℤ)) :
    (∑ t ∈ S, ‖sgnCoeff (2*q) t‖) ≤ 2 := by
  have hp : (0:ℝ) < (2:ℝ)^J := by positivity
  calc
    _ ≤ ∑ _t ∈ S, (2:ℝ)/(2:ℝ)^J := by
      apply Finset.sum_le_sum
      intro t ht
      exact norm_sgnCoeff_le_dyadic (2*q) (by omega) t J (hmem t ht).1
        (by have := (hmem t ht).2; push_cast; omega)
    _ = (S.card:ℝ) * (2/(2:ℝ)^J) := by simp
    _ ≤ (2:ℝ)^J * (2/(2:ℝ)^J) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard
    _ = 2 := by field_simp

private lemma agent4Dyadic2026_card (q Q J : ℕ) (ρ ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) :
    ((Finset.Ioo (-(q:ℤ)) (q:ℤ)).filter fun t =>
      t ≡ ρ [ZMOD (Q:ℤ)] ∧ (2:ℤ)^J ≤ ε*t ∧ ε*t < 2^(J+1)).card ≤ 2^J := by
  classical
  rcases hε with rfl | rfl
  · have hs : ((Finset.Ioo (-(q:ℤ)) (q:ℤ)).filter fun t =>
        t ≡ ρ [ZMOD (Q:ℤ)] ∧ (2:ℤ)^J ≤ 1*t ∧ 1*t < 2^(J+1)) ⊆
        Finset.Ico ((2:ℤ)^J) (2^(J+1)) := by
      intro t ht
      have ht := (Finset.mem_filter.mp ht).2
      simpa using ht.2
    apply (Finset.card_le_card hs).trans
    rw [Int.card_Ico, pow_succ]
    have he : (2:ℤ)^J*2-2^J = 2^J := by ring
    rw [he]
    simp
  · have hs : ((Finset.Ioo (-(q:ℤ)) (q:ℤ)).filter fun t =>
        t ≡ ρ [ZMOD (Q:ℤ)] ∧ (2:ℤ)^J ≤ -1*t ∧ -1*t < 2^(J+1)) ⊆
        Finset.Ioc (-(2:ℤ)^(J+1)) (-(2:ℤ)^J) := by
      intro t ht
      have ht := (Finset.mem_filter.mp ht).2
      simp only [neg_one_mul] at ht
      exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
    apply (Finset.card_le_card hs).trans
    rw [Int.card_Ioc, pow_succ]
    have he : -(2:ℤ)^J - -(2^J*2) = 2^J := by ring
    rw [he]
    simp

private lemma agent4Dyadic2026_assemble {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → Type*) [∀ j, Fintype (β j)] (i : ι)
    (F : (∀ j, β j) → ℂ) (g : ∀ j, β j → ℝ) (K : ℝ)
    (hf : ∀ u : (j : {j // j ≠ i}) → β j.val,
      ‖∑ t : β i, F ((Equiv.piSplitAt i β).symm (t,u))‖ ≤
        K * ∏ j : {j // j ≠ i}, g j.val (u j)) :
    ‖∑ v, F v‖ ≤ K * ∏ j : {j // j ≠ i}, ∑ t, g j.val t := by
  classical
  rw [← (Equiv.piSplitAt i β).symm.sum_comp F, Fintype.sum_prod_type,
    Finset.sum_comm]
  calc
    _ ≤ ∑ u, ‖∑ t : β i, F ((Equiv.piSplitAt i β).symm (t,u))‖ := norm_sum_le _ _
    _ ≤ ∑ u, K * ∏ j : {j // j ≠ i}, g j.val (u j) :=
      Finset.sum_le_sum (fun u _ => hf u)
    _ = _ := by rw [← Finset.mul_sum, ← Fintype.prod_sum]

private lemma agent4Dyadic2026_pi_sum_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → Finset ℤ) (F : (ι → ℤ) → ℂ) :
    (∑ v : (j : ι) → ↥(D j), F (fun j => (v j).val)) =
      ∑ v ∈ Fintype.piFinset D, F v := by
  classical
  apply Finset.sum_bij (fun (v : (j : ι) → ↥(D j)) _ => fun j => (v j).val)
  · intro v hv
    exact Fintype.mem_piFinset.mpr (fun j => (v j).property)
  · intro v hv u hu he
    funext j
    exact Subtype.ext (congrFun he j)
  · intro v hv
    exact ⟨(fun j => ⟨v j, (Fintype.mem_piFinset.mp hv) j⟩), Finset.mem_univ _, rfl⟩
  · intros
    rfl

private lemma agent4Dyadic2026_restrict_checked
    (S : Finset ℤ) (L Q : ℕ) (hQ : 0 < Q) (ρ : ℤ)
    (γ D : ℝ)
    (hfull : ∀ β : ℝ,
      ‖∑ t ∈ S, (sgnCotWeight L (t : ℝ) : ℂ) *
        expTwoPiI (γ * (t : ℝ)^2 + β * (t : ℝ))‖ ≤ D) :
    ∀ β : ℝ,
      ‖∑ t ∈ S.filter (fun t => t ≡ ρ [ZMOD (Q : ℤ)]),
        sgnCoeff L t * expTwoPiI (γ * (t : ℝ)^2 + β * (t : ℝ))‖ ≤ D := by
  classical
  have hodd (β : ℝ) :
      ‖∑ t ∈ S.filter Odd, (sgnCotWeight L (t : ℝ) : ℂ) *
        expTwoPiI (γ * (t : ℝ)^2 + β * (t : ℝ))‖ ≤ D := by
    have hfilter : S.filter Odd =
        S.filter (fun t => t ≡ (1 : ℤ) [ZMOD ((2 : ℕ) : ℤ)]) := by
      ext t
      simp only [Finset.mem_filter, Int.odd_iff]
      change (t ∈ S ∧ t % 2 = 1) ↔ (t ∈ S ∧ t % 2 = 1 % 2)
      norm_num
    rw [hfilter]
    apply agent4WG_progression_ok S 2 (by norm_num) 1 _ D
    intro θ
    have he (t : ℤ) :
        expTwoPiI (θ * (t : ℝ)) *
          ((sgnCotWeight L (t : ℝ) : ℂ) *
            expTwoPiI (γ * (t : ℝ)^2 + β * (t : ℝ))) =
        (sgnCotWeight L (t : ℝ) : ℂ) *
          expTwoPiI (γ * (t : ℝ)^2 + (β + θ) * (t : ℝ)) := by
      rw [mul_left_comm, ← onb_exp_add]
      congr 2
      ring
    simp_rw [he]
    exact hfull (β + θ)
  have hsgn (β : ℝ) :
      ‖∑ t ∈ S, sgnCoeff L t *
        expTwoPiI (γ * (t : ℝ)^2 + β * (t : ℝ))‖ ≤ D := by
    have he : (∑ t ∈ S, sgnCoeff L t *
        expTwoPiI (γ * (t : ℝ)^2 + β * (t : ℝ))) =
        -Complex.I * ∑ t ∈ S.filter Odd,
          (sgnCotWeight L (t : ℝ) : ℂ) *
            expTwoPiI (γ * (t : ℝ)^2 + β * (t : ℝ)) := by
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro t ht
      by_cases ho : Odd t <;> simp [sgnCoeff, ho, mul_assoc]
    rw [he, norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact hodd β
  intro β
  apply agent4WG_progression_ok S Q hQ ρ _ D
  intro θ
  have he (t : ℤ) :
      expTwoPiI (θ * (t : ℝ)) *
        (sgnCoeff L t * expTwoPiI (γ * (t : ℝ)^2 + β * (t : ℝ))) =
      sgnCoeff L t * expTwoPiI (γ * (t : ℝ)^2 + (β + θ) * (t : ℝ)) := by
    rw [mul_left_comm, ← onb_exp_add]
    congr 2
    ring
  simp_rw [he]
  exact hsgn (β + θ)

private lemma agent4Dyadic2026_interval_abel
    (N : ℤ) (n : ℕ) (a : ℤ → ℝ) (γ D H : ℝ)
    (hD : 0 ≤ D) (hH : 0 ≤ H)
    (ha : ∀ t ∈ Finset.Ico N (N + (n : ℤ)), |a t| ≤ D)
    (hmono : ∀ t ∈ Finset.Ico N (N + (n : ℤ)),
      ∀ u ∈ Finset.Ico N (N + (n : ℤ)), t ≤ u → a u ≤ a t)
    (hpref : ∀ (β : ℝ) (m : ℕ), m ≤ n →
      ‖∑ t ∈ Finset.Ico N (N + (m : ℤ)),
        expTwoPiI (γ * (t : ℝ)^2 + β * (t : ℝ))‖ ≤ H) :
    ∀ β : ℝ,
      ‖∑ t ∈ Finset.Ico N (N + (n : ℤ)),
        (a t : ℂ) * expTwoPiI (γ * (t : ℝ)^2 + β * (t : ℝ))‖ ≤ 3*D*H := by
  intro β
  rw [agent4WG_interval]
  cases n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, norm_zero]; positivity
  | succ n =>
    apply agent4Dyadic_abel_bound_ok
      (fun j => a (N + (j : ℤ)))
      (fun j => expTwoPiI (γ * ((N + (j : ℤ) : ℤ) : ℝ)^2 +
        β * ((N + (j : ℤ) : ℤ) : ℝ))) n D H hD hH
    · intro j hj
      apply ha
      simp only [Finset.mem_Ico]
      constructor <;> omega
    · intro j hj
      apply hmono (N + (j : ℤ))
      · simp only [Finset.mem_Ico]; constructor <;> omega
      · simp only [Finset.mem_Ico]; constructor <;> omega
      · omega
    · intro j hj
      simpa only [agent4WG_interval] using hpref β (j+1) (by omega)

private lemma agent4Dyadic2026_cot_bound_checked
    (q Q d n : ℕ) (hq : 2 ≤ q) (hQ : 0 < Q) (hd : 0 < d)
    (N ρ : ℤ) (γ H : ℝ) (hH : 0 ≤ H)
    (hsize : ∀ t ∈ Finset.Ico N (N + (n : ℤ)),
      (d : ℤ) ≤ |t| ∧ |t| < (q : ℤ))
    (hside : (∀ t ∈ Finset.Ico N (N + (n : ℤ)), 0 < t) ∨
      (∀ t ∈ Finset.Ico N (N + (n : ℤ)), t < 0))
    (hpref : ∀ (β : ℝ) (m : ℕ), m ≤ n →
      ‖∑ t ∈ Finset.Ico N (N + (m : ℤ)),
        expTwoPiI (γ * (t : ℝ)^2 + β * (t : ℝ))‖ ≤ H) :
    ∀ β : ℝ,
      ‖∑ t ∈ (Finset.Ico N (N + (n : ℤ))).filter
          (fun t => t ≡ ρ [ZMOD (Q : ℤ)]),
        sgnCoeff (2*q) t * expTwoPiI (γ * (t : ℝ)^2 + β * (t : ℝ))‖ ≤
        3 * (2 / (d : ℝ)) * H := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  apply agent4Dyadic2026_restrict_checked
    (Finset.Ico N (N + (n : ℤ))) (2*q) Q hQ ρ γ (3 * (2 / (d : ℝ)) * H)
  apply agent4Dyadic2026_interval_abel N n
    (fun t => sgnCotWeight (2*q) (t : ℝ)) γ
    (2 / (d : ℝ)) H (by positivity) hH
  · intro t ht
    have hts := hsize t ht
    have ht0 : t ≠ 0 := by intro he; simp only [he, abs_zero] at hts; omega
    apply (abs_sgnCotWeight_le (2*q) (by omega) t ht0 (by push_cast; omega)).trans
    apply div_le_div_of_nonneg_left (by norm_num) hdR
    have hdr : (d : ℝ) ≤ |(t : ℝ)| := by exact_mod_cast hts.1
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    nlinarith [mul_nonneg (sub_nonneg.mpr hpi) (abs_nonneg (t : ℝ))]
  · intro t ht u hu htu
    rcases hside with hpos | hneg
    · apply sgnCotWeight_anti_int_pos (2*q) (by omega) t u (hpos t ht) htu
      have huq := (abs_lt.mp (hsize u hu).2).2
      push_cast
      omega
    · apply sgnCotWeight_anti_int_neg (2*q) (by omega) t u (hneg u hu) htu
      have htq := (abs_lt.mp (hsize t ht).2).1
      push_cast
      omega
  · exact hpref

private lemma agent4Dyadic2026_geometry (q d : ℕ) (hd : 0 < d) (hdq : d < q)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ (N : ℤ) (n : ℕ), n ≤ d ∧
      ((Finset.Ioo (-(q:ℤ)) (q:ℤ)).filter fun t =>
        (d:ℤ) ≤ ε*t ∧ ε*t < 2*(d:ℤ)) = Finset.Ico N (N+(n:ℤ)) ∧
      (∀ t ∈ Finset.Ico N (N+(n:ℤ)), (d:ℤ) ≤ |t| ∧ |t| < (q:ℤ)) ∧
      ((∀ t ∈ Finset.Ico N (N+(n:ℤ)), 0 < t) ∨
       (∀ t ∈ Finset.Ico N (N+(n:ℤ)), t < 0)) := by
  let u := min (2*d) q
  have hdu : d ≤ u := by dsimp [u]; omega
  have huq : u ≤ q := min_le_right _ _
  have hud : u ≤ 2*d := min_le_left _ _
  have huc : (u:ℤ) = min (2*(d:ℤ)) (q:ℤ) := by dsimp [u]; omega
  have hn : ((u-d:ℕ):ℤ) = (u:ℤ)-d := by omega
  rcases hε with rfl | rfl
  · refine ⟨(d:ℤ), u-d, by omega, ?_, ?_, Or.inl ?_⟩
    · ext t
      simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Ico, one_mul, hn]
      omega
    · intro t ht
      obtain ⟨ht0,ht1⟩ := Finset.mem_Ico.mp ht
      have htp : 0 ≤ t := by omega
      rw [abs_of_nonneg htp]
      constructor <;> omega
    · intro t ht
      have := (Finset.mem_Ico.mp ht).1
      omega
  · refine ⟨1-(u:ℤ), u-d, by omega, ?_, ?_, Or.inr ?_⟩
    · ext t
      simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Ico, neg_one_mul, hn]
      omega
    · intro t ht
      obtain ⟨ht0,ht1⟩ := Finset.mem_Ico.mp ht
      have htp : t ≤ 0 := by omega
      rw [abs_of_nonpos htp]
      constructor <;> omega
    · intro t ht
      have := (Finset.mem_Ico.mp ht).2
      omega

private lemma agent4Dyadic2026_one_dim (q Q J : ℕ) (hQ : 0 < Q)
    (ρ ε : ℤ) (hε : ε=1 ∨ ε= -1) (γ H : ℝ) (hH : 0 ≤ H)
    (hweyl : ∀ (N : ℤ) (n : ℕ), n ≤ 2^J → ∀ β : ℝ,
      ‖∑ t ∈ Finset.Ico N (N+(n:ℤ)),
        expTwoPiI (γ*(t:ℝ)^2+β*(t:ℝ))‖ ≤ H) :
    ∀ β : ℝ,
    ‖∑ t ∈ (Finset.Ioo (-(q:ℤ)) (q:ℤ)).filter (fun t =>
      t ≡ ρ [ZMOD (Q:ℤ)] ∧ (2:ℤ)^J ≤ ε*t ∧ ε*t < 2^(J+1)),
      sgnCoeff (2*q) t * expTwoPiI (γ*(t:ℝ)^2+β*(t:ℝ))‖ ≤
      3*(2/(2:ℝ)^J)*H := by
  classical
  have hd : 0 < (2:ℕ)^J := by positivity
  by_cases hdq : 2^J < q
  · obtain ⟨N,n,hn,he,hsize,hside⟩ :=
      agent4Dyadic2026_geometry q (2^J) hd hdq ε hε
    have he' : ((Finset.Ioo (-(q:ℤ)) (q:ℤ)).filter (fun t =>
        t ≡ ρ [ZMOD (Q:ℤ)] ∧ (2:ℤ)^J ≤ ε*t ∧ ε*t < 2^(J+1))) =
        (Finset.Ico N (N+(n:ℤ))).filter (fun t => t ≡ ρ [ZMOD (Q:ℤ)]) := by
      rw [← he]
      ext t
      simp only [Finset.mem_filter, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      constructor <;> intro ht <;> rcases ht with ⟨h₁,h₂⟩
      · exact ⟨⟨h₁,h₂.2.1, by nlinarith [h₂.2.2]⟩,h₂.1⟩
      · exact ⟨h₁.1,h₂,h₁.2.1,by nlinarith [h₁.2.2]⟩
    intro β
    rw [he']
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      agent4Dyadic2026_cot_bound_checked q Q (2^J) n (by omega) hQ hd
        N ρ γ H hH hsize hside (fun β m hm => hweyl N m (hm.trans hn) β) β
  · have he : ((Finset.Ioo (-(q:ℤ)) (q:ℤ)).filter (fun t =>
        t ≡ ρ [ZMOD (Q:ℤ)] ∧ (2:ℤ)^J ≤ ε*t ∧ ε*t < 2^(J+1))) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨ht,hmod,hlo,hhi⟩ := Finset.mem_filter.mp ht
      obtain ⟨ht0,ht1⟩ := Finset.mem_Ioo.mp ht
      have hp : (q:ℤ) ≤ (2:ℤ)^J := by
        exact_mod_cast (show q ≤ 2^J by omega)
      rcases hε with rfl | rfl <;>
        simp only [one_mul,neg_one_mul] at hlo <;> omega
    intro β
    rw [he,Finset.sum_empty,norm_zero]
    positivity

private lemma agent4Dyadic2026_pi_bound_checked (r : ℕ) (D : Fin r → Finset ℤ)
    (F : (Fin r → ℤ) → ℂ) (g : Fin r → ℤ → ℝ) (i : Fin r) (K : ℝ)
    (hK : 0 ≤ K) (hg : ∀ j t, 0 ≤ g j t)
    (hL : ∀ j, ∑ t ∈ D j, g j t ≤ 2)
    (hf : ∀ u : Fin r → ℤ,
      ‖∑ t ∈ D i, F (Function.update u i t)‖ ≤
        K * ∏ j ∈ Finset.univ.erase i, g j (u j)) :
    ‖∑ v ∈ Fintype.piFinset D, F v‖ ≤ K * 2^r := by
  classical
  rw [← agent4Dyadic2026_pi_sum_fixed D F]
  have hf' (v : (j : {j : Fin r // j ≠ i}) → ↥(D j.val)) :
      ‖∑ t : ↥(D i), (fun z : (j : Fin r) → ↥(D j) => F (fun j => (z j).val))
        ((Equiv.piSplitAt i (fun j => ↥(D j))).symm (t,v))‖ ≤
        K * ∏ j : {j : Fin r // j ≠ i}, g j.val (v j).val := by
    let u : Fin r → ℤ := fun j => if h : j=i then 0 else (v ⟨j,h⟩).val
    have he (t : ↥(D i)) :
        (fun j => (((Equiv.piSplitAt i (fun j => ↥(D j))).symm (t,v)) j).val) =
          Function.update u i t.val := by
      funext j
      by_cases hj : j=i
      · subst j
        simp [Equiv.piSplitAt_symm_apply]
      · simp [Equiv.piSplitAt_symm_apply, hj, Function.update_of_ne hj, u]
    simp only [he]
    rw [Finset.sum_coe_sort (D i) (fun t => F (Function.update u i t))]
    have hh := hf u
    apply hh.trans_eq
    congr 1
    apply Finset.prod_bij
      (fun (j : Fin r) hj => (⟨j,Finset.ne_of_mem_erase hj⟩ : {j : Fin r // j ≠ i}))
    · intros; exact Finset.mem_univ _
    · intros a ha b hb he; exact congrArg Subtype.val he
    · intro j hj
      exact ⟨j.val, Finset.mem_erase.mpr ⟨j.property,Finset.mem_univ _⟩,rfl⟩
    · intro j hj
      simp [u, Finset.ne_of_mem_erase hj]
  apply (agent4Dyadic2026_assemble (fun j => ↥(D j)) i
    (fun z => F (fun j => (z j).val)) (fun j t => g j t.val) K hf').trans
  apply mul_le_mul_of_nonneg_left _ hK
  calc
    _ ≤ ∏ _j : {j : Fin r // j ≠ i}, (2:ℝ) := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact Finset.sum_nonneg (fun t _ => hg j.val t.val)
      · intro j hj
        simpa only [Finset.sum_coe_sort] using hL j.val
    _ = (2:ℝ)^Fintype.card {j : Fin r // j ≠ i} := by simp
    _ ≤ 2^r := by
      have hc : Fintype.card {j : Fin r // j ≠ i} ≤ r := by
        simpa using Fintype.card_subtype_le (fun j : Fin r => j ≠ i)
      gcongr <;> norm_num

private lemma agent4Dyadic2026_fiber_checked (k r q : ℕ) (abar : ℤ) (c : Fin k → ℕ)
    (w : Fin r → Fin k → ℤ) (B : Fin r → ℤ) (l : Fin k → ℤ)
    (i : Fin r) (S : Finset ℤ) (u : Fin r → ℤ) (γ K : ℝ)
    (hphase : ∃ β θ : ℝ, ∀ t : ℤ,
      multiwallQuadPhase k r abar c q w l (Function.update u i t) =
        γ*(t:ℝ)^2+β*(t:ℝ)+θ)
    (hbound : ∀ β : ℝ,
      ‖∑ t ∈ S, sgnCoeff (2*q) t * expTwoPiI (γ*(t:ℝ)^2+β*(t:ℝ))‖ ≤ K) :
    ‖∑ t ∈ S, multiwallSigmaWeight r q B (Function.update u i t) *
      expTwoPiI (multiwallQuadPhase k r abar c q w l (Function.update u i t))‖ ≤
      K * ∏ j ∈ Finset.univ.erase i, ‖sgnCoeff (2*q) (u j)‖ := by
  classical
  obtain ⟨β,θ,hphase⟩ := hphase
  let P : ℂ := ∏ j ∈ Finset.univ.erase i,
    sgnCoeff (2*q) (u j) * expTwoPiI ((((1-2*B j)*u j:ℤ):ℝ)/(2*(q:ℝ)))
  have hweight (t : ℤ) : multiwallSigmaWeight r q B (Function.update u i t) =
      P * (sgnCoeff (2*q) t * expTwoPiI ((((1-2*B i)*t:ℤ):ℝ)/(2*(q:ℝ)))) := by
    unfold multiwallSigmaWeight
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have he (t : ℤ) :
      multiwallSigmaWeight r q B (Function.update u i t) *
      expTwoPiI (multiwallQuadPhase k r abar c q w l (Function.update u i t)) =
      (P * expTwoPiI θ) * (sgnCoeff (2*q) t *
        expTwoPiI (γ*(t:ℝ)^2+(β+(1-2*(B i:ℝ))/(2*(q:ℝ)))*(t:ℝ))) := by
    rw [hweight,hphase]
    have hp : (((1-2*B i)*t:ℤ):ℝ)/(2*(q:ℝ)) + (γ*(t:ℝ)^2+β*(t:ℝ)+θ) =
        θ + (γ*(t:ℝ)^2+(β+(1-2*(B i:ℝ))/(2*(q:ℝ)))*(t:ℝ)) := by
      push_cast
      ring
    calc
      _ = (P * sgnCoeff (2*q) t) *
          (expTwoPiI ((((1-2*B i)*t:ℤ):ℝ)/(2*(q:ℝ))) *
            expTwoPiI (γ*(t:ℝ)^2+β*(t:ℝ)+θ)) := by ring
      _ = _ := by rw [← onb_exp_add,hp,onb_exp_add]; ring
  simp_rw [he]
  rw [← Finset.mul_sum,norm_mul,norm_mul,
    LocalizedFourierFinal.FourierMassBounds.exp_norm,mul_one]
  have hP : ‖P‖ = ∏ j ∈ Finset.univ.erase i, ‖sgnCoeff (2*q) (u j)‖ := by
    simp [P,norm_prod,norm_mul,LocalizedFourierFinal.FourierMassBounds.exp_norm]
  rw [hP]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (hbound (β+(1-2*(B i:ℝ))/(2*(q:ℝ))))
      (Finset.prod_nonneg (fun j (_ : j ∈ Finset.univ.erase i) =>
        norm_nonneg (sgnCoeff (2*q) (u j))))

private lemma agent4Dyadic2026_weyl_prefix
    (k r V h q d n : ℕ) (hk : 1 ≤ k) (hV : 1 ≤ V) (hh : 1 ≤ h)
    (hd : 1 ≤ d) (hdq : d < q) (hnd : n ≤ d)
    (abar : ℤ) (c : Fin k → ℕ) (hc : ∀ j, 1 ≤ c j)
    (hch : ∀ j, c j ≤ h) (w : Fin r → Fin k → ℤ) (i : Fin r)
    (hw : w i ≠ 0) (hwV : ∑ j, |w i j| ≤ (V : ℤ))
    (C : ℝ) (hC : 0 < C)
    (hWG : ∀ R : ℝ, 1 ≤ R → R ≤ 2 * (q : ℝ) →
      ∀ (β : ℝ) (m p : ℤ), 1 ≤ |m| →
        |(m : ℝ)| ≤ ((V^2*h^k : ℕ) : ℝ) → 1 ≤ |p| →
        |(p : ℝ)| ≤ ((V^2*h^k : ℕ) : ℝ) →
        ∀ N v z : ℤ, 1 ≤ v → 1 ≤ z →
          ‖weylProgSum ((m : ℝ)/(p : ℝ) * ((abar : ℝ)/(4*(q : ℝ))))
            β N R v z‖ ≤ C * Real.sqrt (R * Real.log (2*R)))
    (N : ℤ) (β : ℝ) :
    ‖∑ t ∈ Finset.Ico N (N + (n : ℤ)),
      expTwoPiI (-((multiwallM k r c w i : ℝ) / ∏ j, (c j : ℝ)) *
        ((abar : ℝ)/(4*(q : ℝ))) * (t : ℝ)^2 + β * (t : ℝ))‖ ≤
      C * Real.sqrt ((d : ℝ) * Real.log (2*(d : ℝ))) := by
  classical
  by_cases hn0 : n = 0
  · subst n
    simp only [Nat.cast_zero, add_zero, Finset.Ico_self, Finset.sum_empty, norm_zero]
    positivity
  have hn1 : 1 ≤ n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hm := multiwall_M_bounds k r V h hk hV hh c hc hch w i hw hwV
  have hpPos : (0 : ℤ) < ∏ j, (c j : ℤ) := by
    apply Finset.prod_pos
    intro j hj
    exact_mod_cast (show 0 < c j by have := hc j; omega)
  have hpH : (∏ j, (c j : ℤ)) ≤ (h : ℤ)^k := by
    calc
      _ ≤ ∏ _j : Fin k, (h : ℤ) := Finset.prod_le_prod₀
        (fun j _ => by positivity) (fun j _ => by exact_mod_cast hch j)
      _ = _ := by simp
  have hV1 : (1 : ℤ) ≤ V := by exact_mod_cast hV
  have hpM : (∏ j, (c j : ℤ)) ≤ (V : ℤ)^2 * (h : ℤ)^k := by
    apply hpH.trans
    have ht := mul_nonneg (show (0 : ℤ) ≤ (V : ℤ)^2 - 1 by nlinarith)
      (show (0 : ℤ) ≤ (h : ℤ)^k by positivity)
    nlinarith
  have hm0 : (0 : ℤ) ≤ multiwallM k r c w i := by omega
  have hm1 : 1 ≤ |-(multiwallM k r c w i)| := by
    rw [abs_neg, abs_of_nonneg hm0]
    exact hm.1
  have hmR : |((-(multiwallM k r c w i) : ℤ) : ℝ)| ≤
      ((V^2*h^k : ℕ) : ℝ) := by
    rw [Int.cast_neg, abs_neg,
      abs_of_nonneg (show (0 : ℝ) ≤ multiwallM k r c w i by exact_mod_cast hm0)]
    exact_mod_cast hm.2
  have hp1 : 1 ≤ |∏ j, (c j : ℤ)| := by
    rw [abs_of_pos hpPos]
    omega
  have hpR : |((∏ j, (c j : ℤ) : ℤ) : ℝ)| ≤ ((V^2*h^k : ℕ) : ℝ) := by
    rw [abs_of_nonneg
      (show (0 : ℝ) ≤ (∏ j, (c j : ℤ) : ℤ) by exact_mod_cast hpPos.le)]
    exact_mod_cast hpM
  have ht := hWG (n : ℝ) (by exact_mod_cast hn1)
    (by exact_mod_cast (show n ≤ 2*q by omega)) β
    (-multiwallM k r c w i) (∏ j, (c j : ℤ)) hm1 hmR hp1 hpR
    N 1 1 (by norm_num) (by norm_num)
  calc
    _ ≤ C * Real.sqrt ((n : ℝ) * Real.log (2*(n : ℝ))) := by
      simpa [weylProgSum, agent4WG_filter_exact, Int.ModEq, Int.cast_prod,
        Int.cast_neg, neg_div] using ht
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.sqrt_le_sqrt
      apply mul_le_mul
      · exact_mod_cast hnd
      · apply Real.log_le_log (by positivity : (0 : ℝ) < 2*(n : ℝ))
        exact_mod_cast (show 2*n ≤ 2*d by omega)
      · apply Real.log_nonneg
        exact_mod_cast (show 1 ≤ 2*n by omega)
      · exact Nat.cast_nonneg d

private lemma agent4Dyadic2026_mem_abs (q Q J : ℕ) (ρ ε t : ℤ)
    (hε : ε=1 ∨ ε= -1)
    (ht : t ∈ (Finset.Ioo (-(q:ℤ)) (q:ℤ)).filter (fun t =>
      t ≡ ρ [ZMOD (Q:ℤ)] ∧ (2:ℤ)^J ≤ ε*t ∧ ε*t < 2^(J+1))) :
    (2:ℤ)^J ≤ |t| ∧ |t| < (q:ℤ) := by
  obtain ⟨ht,hm,hl,hu⟩ := Finset.mem_filter.mp ht
  have hp : (0:ℤ) < 2^J := by positivity
  refine ⟨?_,abs_lt.mpr (Finset.mem_Ioo.mp ht)⟩
  rcases hε with rfl | rfl
  · simp only [one_mul] at hl
    rw [abs_of_nonneg (by omega)]
    exact hl
  · simp only [neg_one_mul] at hl
    rw [abs_of_nonpos (by omega)]
    exact hl

theorem multiwall_dyadic_piece_bound (A : ℝ) (k r V h : ℕ) (hA : 1 ≤ A) (hk : 1 ≤ k)
    (hV : 1 ≤ V) (hh : 1 ≤ h) :
    ∃ C > 0, ∀ α : ℝ, Irrational α →
      (∀ (i : ℕ) (x : ℝ), (GenContFract.of α).partDens.get? i = some x → x ≤ A) →
      ∀ (s : ℕ) (a : ℤ) (q : ℕ), 0 < q →
        (a : ℝ) = (GenContFract.of α).nums s →
        ((q : ℕ) : ℝ) = (GenContFract.of α).dens s →
        ∀ abar : ℤ, a * abar ≡ 1 [ZMOD (q : ℤ)] → 0 ≤ abar → abar < (q : ℤ) →
        ∀ c : Fin k → ℕ, (∀ j, 1 ≤ c j) → (∀ j, c j ≤ h) →
        ∀ w : Fin r → Fin k → ℤ, (∀ i, w i ≠ 0) →
          (∀ i, ∑ j, |w i j| ≤ (V : ℤ)) →
        ∀ (B : Fin r → ℤ) (l : Fin k → ℤ) (Q : ℕ), 1 ≤ Q →
        ∀ ρ ε : Fin r → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) →
        ∀ (J : Fin r → ℕ) (i : Fin r),
          ‖multiwallDyadicPiece k r abar c q Q w B l ρ ε J‖ ≤
            C * Real.sqrt (1 + (J i : ℝ)) * (2 : ℝ) ^ (-(J i : ℝ) / 2) := by
  classical
  let M : ℝ := ((V^2*h^k:ℕ):ℝ)
  have hM : 1 ≤ M := by
    dsimp [M]
    exact_mod_cast (show 1 ≤ V^2*h^k by
      have hv : 0 < V := by omega
      have hh' : 0 < h := by omega
      have : 0 < V^2*h^k := by positivity
      omega)
  obtain ⟨C,hC,hWG⟩ := lem_weylgauss A M hA hM
  refine ⟨6*C*Real.sqrt (Real.log 2)*2^r, ?_, ?_⟩
  · have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  intro α hα hαA s a q hq hnum hden abar hab hbar0 hbarq
    c hc hch w hw hwV B l Q hQ ρ ε hε J i
  let D : Fin r → Finset ℤ := fun j =>
    (Finset.Ioo (-(q:ℤ)) (q:ℤ)).filter (fun t =>
      t ≡ ρ j [ZMOD (Q:ℤ)] ∧ (2:ℤ)^(J j) ≤ ε j*t ∧ ε j*t < 2^(J j+1))
  have he : multiwallDyadicIndex r q Q ρ ε J = Fintype.piFinset D := by
    ext v
    simp only [multiwallDyadicIndex,D,Finset.mem_filter,Fintype.mem_piFinset]
    constructor
    · rintro ⟨hv,hm,hd⟩ j
      exact ⟨hv j,hm j,hd j⟩
    · intro hv
      exact ⟨fun j => (hv j).1,fun j => (hv j).2.1,fun j => (hv j).2.2⟩
  unfold multiwallDyadicPiece
  rw [he]
  by_cases hne : (Fintype.piFinset D).Nonempty
  · obtain ⟨v,hv⟩ := hne
    have ht := agent4Dyadic2026_mem_abs q Q (J i) (ρ i) (ε i) (v i) (hε i)
      (Fintype.mem_piFinset.mp hv i)
    have hdq : 2^(J i) < q := by exact_mod_cast (ht.1.trans_lt ht.2)
    have hd : 1 ≤ (2:ℕ)^(J i) := Nat.one_le_two_pow
    have hq2 : 2 ≤ q := by omega
    let γ : ℝ := -((multiwallM k r c w i : ℝ) / ∏ j, (c j : ℝ)) *
      ((abar:ℝ)/(4*(q:ℝ)))
    let H : ℝ := C * Real.sqrt ((2:ℝ)^(J i)*Real.log (2*(2:ℝ)^(J i)))
    let K : ℝ := 3*(2/(2:ℝ)^(J i))*H
    have hH : 0 ≤ H := by dsimp [H]; positivity
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hspec := hWG α hα hαA s a (q:ℤ) hnum (by simpa using hden)
      abar hab hbar0 hbarq
    have hpref (N : ℤ) (n : ℕ) (hn : n ≤ 2^(J i)) (β : ℝ) :
        ‖∑ t ∈ Finset.Ico N (N+(n:ℤ)), expTwoPiI (γ*(t:ℝ)^2+β*(t:ℝ))‖ ≤ H := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using
        agent4Dyadic2026_weyl_prefix k r V h q (2^(J i)) n hk hV hh hd hdq hn
          abar c hc hch w i (hw i) (hwV i) C hC
          (by simpa only [Int.cast_natCast] using hspec) N β
    have hone (β : ℝ) :
        ‖∑ t ∈ D i, sgnCoeff (2*q) t * expTwoPiI (γ*(t:ℝ)^2+β*(t:ℝ))‖ ≤ K :=
      agent4Dyadic2026_one_dim q Q (J i) (by omega) (ρ i) (ε i) (hε i)
        γ H hH hpref β
    have hbound :
        ‖∑ v ∈ Fintype.piFinset D, multiwallSigmaWeight r q B v *
          expTwoPiI (multiwallQuadPhase k r abar c q w l v)‖ ≤ K*2^r := by
      apply agent4Dyadic2026_pi_bound_checked r D _
        (fun _ t => ‖sgnCoeff (2*q) t‖) i K hK (fun _ _ => norm_nonneg _) ?_ ?_
      · intro j
        apply agent4Dyadic2026_l1 q (J j) hq2 (D j)
        · exact agent4Dyadic2026_card q Q (J j) (ρ j) (ε j) (hε j)
        · intro t ht
          exact agent4Dyadic2026_mem_abs q Q (J j) (ρ j) (ε j) t (hε j) ht
      · intro u
        exact agent4Dyadic2026_fiber_checked k r q abar c w B l i (D i) u γ K
          (multiwall_phase_quadratic_in_coord k r q hk hq abar c hc w l u i) hone
    apply hbound.trans_eq
    have hscale := agent4Dyadic2026_numeric (J i)
    dsimp [K,H]
    calc
      _ = (6*C*2^r) * (((2:ℝ)^(J i))⁻¹ *
          Real.sqrt ((2:ℝ)^(J i)*Real.log (2*(2:ℝ)^(J i)))) := by ring
      _ = _ := by rw [hscale]; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty,norm_zero]
    positivity
private lemma sigma5_inverse (a : ℤ) (q : ℕ) (hq : 0 < q)
    (ha : Int.gcd a q = 1) :
    ∃ abar : ℤ, a * abar ≡ 1 [ZMOD (q : ℤ)] ∧ 0 ≤ abar ∧ abar < (q : ℤ) := by
  let b := Int.gcdA a (q : ℤ)
  have hz := Int.gcd_eq_gcd_ab a (q : ℤ)
  rw [ha] at hz
  have hb : a*b ≡ 1 [ZMOD (q : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨Int.gcdB a (q : ℤ), ?_⟩
    dsimp [b]
    linear_combination hz
  refine ⟨b % (q : ℤ), ?_, Int.emod_nonneg _ (by exact_mod_cast hq.ne'),
    Int.emod_lt_of_pos _ (by exact_mod_cast hq)⟩
  exact ((Int.ModEq.refl a).mul (Int.mod_modEq b (q : ℤ))).trans hb

private lemma sigma5_zero_final (k h : ℕ) (hh : 1 ≤ h) (q : ℕ) (hq : 0 < q)
    (a : ℤ) (ha : Int.gcd a q = 1) (c : Fin k → ℕ)
    (hc : ∀ j, 1 ≤ c j) (hch : ∀ j, c j ≤ h)
    (w : Fin 0 → Fin k → ℤ) (B : Fin 0 → ℤ) (l : Fin k → ℤ) :
    ‖multiwallSigma k 0 a c q hq w B l‖ ≤ (Real.sqrt (2*(h:ℝ)))^k := by
  classical
  obtain ⟨abar, hi, hi0, hiq⟩ := sigma5_inverse a q hq ha
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : (Real.sqrt (q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hqpos).ne'
  have hg (j : Fin k) : ‖quadGaussSum ((c j : ℤ)*a) (l j) q hq‖ ≤
      Real.sqrt (q : ℝ) * Real.sqrt (2*(h:ℝ)) := by
    have hb := quadGaussSum_normSq_le_gcd a (l j) (c j) q (hc j) hq ha
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hqpos.le, Real.sq_sqrt (by positivity)]
    have hj : (c j : ℝ) ≤ h := by exact_mod_cast hch j
    nlinarith [hb.1.trans hb.2]
  have hprod := Finset.prod_le_prod₀ (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) =>
    norm_nonneg (quadGaussSum ((c j : ℤ)*a) (l j) q hq)) (fun j _ => hg j)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow] at hprod
  have hd : (∏ j, ‖quadGaussSum ((c j : ℤ)*a) (l j) q hq‖) /
      Real.sqrt (q : ℝ)^k ≤ Real.sqrt (2*(h:ℝ))^k :=
    (div_le_iff₀ (pow_pos (Real.sqrt_pos.mpr hqpos) k)).2 (by
      simpa only [mul_comm] using hprod)
  simpa [multiwallSigma, multiwallG, norm_prod, norm_div,
    abs_of_nonneg (Real.sqrt_nonneg _)] using hd

private lemma sigma5_bin_unique (v ε : ℤ) (J : ℕ) (hε : ε = 1 ∨ ε = -1)
    (hv : v ≠ 0) :
    ((2:ℤ)^J ≤ ε*v ∧ ε*v < 2^(J+1)) ↔
      ε = Int.sign v ∧ J = Nat.log 2 v.natAbs := by
  constructor
  · intro h
    have hp : (0 : ℤ) < 2^J := by positivity
    have he : ε = Int.sign v := by
      rcases hε with rfl | rfl
      · rw [Int.sign_eq_one_of_pos (by simpa using hp.trans_le h.1)]
      · rw [Int.sign_eq_neg_one_of_neg (by nlinarith [h.1])]
    refine ⟨he, ?_⟩
    rw [he, Int.sign_mul_self] at h
    have h1 : (2:ℕ)^J ≤ v.natAbs := by exact_mod_cast h.1
    have h2 : v.natAbs < (2:ℕ)^(J+1) := by exact_mod_cast h.2
    exact (Nat.log_eq_of_pow_le_of_lt_pow h1 h2).symm
  · rintro ⟨rfl,rfl⟩
    rw [Int.sign_mul_self]
    constructor
    · exact_mod_cast Nat.pow_log_le_self 2 (Int.natAbs_ne_zero.mpr hv)
    · exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) v.natAbs

set_option maxHeartbeats 1000000 in
private lemma sigma5_shell_summable (r : ℕ) :
    Summable (fun n : ℕ => ((n:ℝ)+1)^(r+1) * ((Real.sqrt 2)⁻¹)^n) := by
  have hp : 0 < Real.sqrt (2:ℝ) := by positivity
  have ha0 : (Real.sqrt (2:ℝ))⁻¹ ≠ 0 := by positivity
  have ha : ‖(Real.sqrt (2:ℝ))⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
    apply (inv_lt_one₀ hp).2
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  have hs : Summable (fun n : ℕ => ((n+1 : ℕ):ℝ)^(r+1) * ((Real.sqrt 2)⁻¹)^(n+1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n:ℝ)^(r+1)*((Real.sqrt 2)⁻¹)^n) 1).2
      (summable_pow_mul_geometric_of_norm_lt_one (r+1) ha)
  apply (hs.mul_right (((Real.sqrt (2:ℝ))⁻¹)⁻¹)).congr
  intro n
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

private lemma sigma5_decompose_ok (k r q Q : ℕ) (abar : ℤ) (c : Fin k → ℕ)
    (w : Fin r → Fin k → ℤ) (B : Fin r → ℤ) (l : Fin k → ℤ) (ρ : Fin r → ℤ) :
    multiwallSigmaClass k r abar c q Q w B l ρ =
      ∑ ε ∈ Fintype.piFinset (fun _ : Fin r => ({1,-1} : Finset ℤ)),
        ∑ J ∈ Fintype.piFinset (fun _ : Fin r => Finset.range q),
          multiwallDyadicPiece k r abar c q Q w B l ρ ε J := by
  classical
  let S := Fintype.piFinset (fun _ : Fin r => Finset.Ioo (-(q:ℤ)) (q:ℤ))
  let E := Fintype.piFinset (fun _ : Fin r => ({1,-1} : Finset ℤ))
  let D := Fintype.piFinset (fun _ : Fin r => Finset.range q)
  let F := fun v => multiwallSigmaWeight r q B v *
    expTwoPiI (multiwallQuadPhase k r abar c q w l v)
  let H := fun v : Fin r → ℤ => ∀ i, v i ≡ ρ i [ZMOD (Q:ℤ)]
  let T := fun (v ε : Fin r → ℤ) (J : Fin r → ℕ) =>
    ∀ i, 2^(J i) ≤ ε i*v i ∧ ε i*v i < 2^(J i+1)
  have hpoint (v : Fin r → ℤ) (hv : v ∈ S) :
      (if H v then F v else 0) =
        ∑ ε ∈ E, ∑ J ∈ D, if H v ∧ T v ε J then F v else 0 := by
    by_cases hz : ∃ i, v i = 0
    · obtain ⟨i,hi⟩ := hz
      have hF : F v = 0 := by
        dsimp [F, multiwallSigmaWeight]
        have hp : (∏ j, sgnCoeff (2*q) (v j) *
          expTwoPiI ((((1-2*B j)*v j:ℤ):ℝ)/(2*(q:ℝ)))) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          rw [hi]
          simp [sgnCoeff]
        rw [hp, zero_mul]
      simp [hF]
    · have hv0 (i) : v i ≠ 0 := by intro hi; exact hz ⟨i,hi⟩
      let ε₀ := fun i => Int.sign (v i)
      let J₀ := fun i => Nat.log 2 (v i).natAbs
      have hε₀ : ε₀ ∈ E := by
        apply Fintype.mem_piFinset.mpr
        intro i
        rcases lt_or_gt_of_ne (hv0 i) with hi | hi
        · simp [ε₀, Int.sign_eq_neg_one_of_neg hi]
        · simp [ε₀, Int.sign_eq_one_of_pos hi]
      have hJ₀ : J₀ ∈ D := by
        apply Fintype.mem_piFinset.mpr
        intro i
        apply Finset.mem_range.mpr
        have hi := Finset.mem_Ioo.mp (Fintype.mem_piFinset.mp hv i)
        have ha : |v i| < (q:ℤ) := abs_lt.mpr hi
        have han : (v i).natAbs < q := by
          have ha' : ((v i).natAbs : ℤ) < (q : ℤ) := by simpa using ha
          exact_mod_cast ha'
        exact (Nat.log_le_self 2 _).trans_lt han
      have hiff (ε : Fin r → ℤ) (hε : ε ∈ E) (J : Fin r → ℕ) :
          T v ε J ↔ ε = ε₀ ∧ J = J₀ := by
        have he (i) : ε i = 1 ∨ ε i = -1 := by
          simpa using Fintype.mem_piFinset.mp hε i
        constructor
        · intro ht
          exact ⟨funext (fun i => ((sigma5_bin_unique (v i) (ε i) (J i) (he i) (hv0 i)).1 (ht i)).1),
            funext (fun i => ((sigma5_bin_unique (v i) (ε i) (J i) (he i) (hv0 i)).1 (ht i)).2)⟩
        · rintro ⟨rfl,rfl⟩
          intro i
          exact (sigma5_bin_unique (v i) (ε₀ i) (J₀ i) (he i) (hv0 i)).2 ⟨rfl,rfl⟩
      have heq : (∑ ε ∈ E, ∑ J ∈ D, if H v ∧ T v ε J then F v else 0) =
          ∑ ε ∈ E, ∑ J ∈ D, if H v ∧ (ε = ε₀ ∧ J = J₀) then F v else 0 := by
        apply Finset.sum_congr rfl
        intro ε hε
        simp_rw [hiff ε hε]
      rw [heq]
      by_cases hh : H v <;> simp [hh, ite_and, hε₀, hJ₀]
  unfold multiwallSigmaClass multiwallDyadicPiece multiwallDyadicIndex
  simp only [Finset.sum_filter]
  change (∑ v ∈ S, if H v then F v else 0) =
    ∑ ε ∈ E, ∑ J ∈ D, ∑ v ∈ S, if H v ∧ T v ε J then F v else 0
  calc
    _ = ∑ v ∈ S, ∑ ε ∈ E, ∑ J ∈ D, if H v ∧ T v ε J then F v else 0 :=
      Finset.sum_congr rfl hpoint
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ε hε
      rw [Finset.sum_comm]

private lemma sigma5_shell_bound (r : ℕ) (hr : 0 < r) :
    ∃ D > 0, ∀ C : ℝ, 0 ≤ C →
      ∀ f : (Fin r → ℕ) → ℂ,
      (∀ J i, ‖f J‖ ≤ C * Real.sqrt (1+(J i:ℝ)) * (2:ℝ)^(-(J i:ℝ)/2)) →
      ∀ T : ℕ,
      (∑ J ∈ Fintype.piFinset (fun _ : Fin r => Finset.range T), ‖f J‖) ≤ C*D := by
  classical
  let a : ℝ := (Real.sqrt 2)⁻¹
  let H : ℕ → ℝ := fun n => ((n:ℝ)+1)^(r+1)*a^n
  have hHs : Summable H := sigma5_shell_summable r
  have hH0 (n) : 0 ≤ H n := by dsimp [H,a]; positivity
  let D : ℝ := (∑' n, H n)+1
  have hsum0 : 0 ≤ ∑' n, H n := tsum_nonneg hH0
  refine ⟨D, by dsimp [D]; linarith, ?_⟩
  intro C hC f hf T
  let S := Fintype.piFinset (fun _ : Fin r => Finset.range T)
  let u : (Fin r → ℕ) → ℕ := fun J => Finset.univ.sup J
  let g : ℕ → ℝ := fun n => Real.sqrt (1+(n:ℝ))*a^n
  have hg0 (n) : 0 ≤ g n := by dsimp [g,a]; positivity
  have hscale (n : ℕ) : (2:ℝ)^(-(n:ℝ)/2)=a^n := by
    simpa only [a, inv_pow] using haarRow_nat_scale n
  have hpoint (J : Fin r → ℕ) : ‖f J‖ ≤ C*g (u J) := by
    obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin r)) J
      ⟨⟨0,hr⟩, Finset.mem_univ _⟩
    have he : u J = J i := le_antisymm
      (Finset.sup_le (fun j hj => hmax j hj)) (Finset.le_sup hi)
    rw [he]
    simpa only [g, hscale, mul_assoc] using hf J i
  have hcard (n : ℕ) : (S.filter (fun J => u J=n)).card ≤ (n+1)^r := by
    have hsub : S.filter (fun J => u J=n) ⊆
        Fintype.piFinset (fun _ : Fin r => Finset.range (n+1)) := by
      intro J hJ
      have he := (Finset.mem_filter.mp hJ).2
      apply Fintype.mem_piFinset.mpr
      intro i
      apply Finset.mem_range.mpr
      have hi : J i ≤ u J := Finset.le_sup (Finset.mem_univ i)
      omega
    simpa [Fintype.card_piFinset] using Finset.card_le_card hsub
  have hroot (n : ℕ) : Real.sqrt (1+(n:ℝ)) ≤ (n:ℝ)+1 := by
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ 1+(n:ℝ) by positivity)
    have hp := Real.sqrt_nonneg (1+(n:ℝ))
    nlinarith
  have hmajor (n : ℕ) : ((S.filter (fun J => u J=n)).card:ℝ)*g n ≤ H n := by
    calc
      _ ≤ (((n+1)^r:ℕ):ℝ)*g n := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard n) (hg0 n)
      _ ≤ ((n:ℝ)+1)^r * (((n:ℝ)+1)*a^n) := by
        push_cast
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hroot n) (by dsimp [a]; positivity)) (by positivity)
      _ = H n := by dsimp [H]; rw [pow_succ]; ring
  calc
    _ ≤ ∑ J ∈ S, C*g (u J) := Finset.sum_le_sum (fun J _ => hpoint J)
    _ = C * ∑ J ∈ S, g (u J) := (Finset.mul_sum _ _ _).symm
    _ = C * ∑ n ∈ S.image u, ((S.filter (fun J => u J=n)).card:ℝ)*g n := by
      rw [Finset.sum_comp]
      simp only [nsmul_eq_mul]
    _ ≤ C * ∑ n ∈ S.image u, H n := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun n _ => hmajor n)) hC
    _ ≤ C * ∑' n, H n := mul_le_mul_of_nonneg_left
      (Summable.sum_le_tsum (S.image u) (fun n _ => hH0 n) hHs) hC
    _ ≤ C*D := mul_le_mul_of_nonneg_left (by dsimp [D]; linarith) hC

theorem multiwall_Sigma_bound (A : ℝ) (k r V h : ℕ) (hA : 1 ≤ A) (hk : 1 ≤ k)
    (hV : 1 ≤ V) (hh : 1 ≤ h) :
    ∃ C > 0, ∀ α : ℝ, Irrational α →
      (∀ (i : ℕ) (x : ℝ), (GenContFract.of α).partDens.get? i = some x → x ≤ A) →
      ∀ (s : ℕ) (a : ℤ) (q : ℕ) (hq : 0 < q),
        (a : ℝ) = (GenContFract.of α).nums s →
        (q : ℝ) = (GenContFract.of α).dens s →
        Int.gcd a q = 1 →
        ∀ c : Fin k → ℕ, (∀ j, 1 ≤ c j) → (∀ j, c j ≤ h) →
        ∀ w : Fin r → Fin k → ℤ, (∀ i, w i ≠ 0) →
          (∀ i, ∑ j, |w i j| ≤ (V : ℤ)) →
        ∀ (B : Fin r → ℤ) (l : Fin k → ℤ),
          ‖multiwallSigma k r a c q hq w B l‖ ≤ C := by
  classical
  by_cases hr : r = 0
  · subst r
    refine ⟨(Real.sqrt (2*(h:ℝ)))^k, by positivity, ?_⟩
    intro α hα hbpq s a q hq hnum hden ha c hc hch w hw hwV B l
    exact sigma5_zero_final k h hh q hq a ha c hc hch w B l
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  obtain ⟨D, hD, hsum⟩ := sigma5_shell_bound r hrpos
  obtain ⟨E, hE, hdyad⟩ := multiwall_dyadic_piece_bound A k r V h hA hk hV hh
  obtain ⟨F, hF, hclass⟩ := multiwall_Sigma_residue_class_bound k r h hk hh
  refine ⟨F * ((2:ℝ)^r * (E*D)), by positivity, ?_⟩
  intro α hα hbpq s a q hq hnum hden ha c hc hch w hw hwV B l
  obtain ⟨abar, habar, habar0, habarq⟩ := sigma5_inverse a q hq ha
  obtain ⟨ρ, hρ, hb⟩ := hclass q hq a abar c hc hch ha habar habar0 habarq w B l
  have hQ : 1 ≤ multiwallQ k c := by
    unfold multiwallQ
    have hp : 0 < ∏ j, c j := Finset.prod_pos (fun j _ => by have := hc j; omega)
    omega
  have hp (ε : Fin r → ℤ)
      (hε : ε ∈ Fintype.piFinset (fun _ : Fin r => ({1,-1} : Finset ℤ))) :
      ‖∑ J ∈ Fintype.piFinset (fun _ : Fin r => Finset.range q),
        multiwallDyadicPiece k r abar c q (multiwallQ k c) w B l ρ ε J‖ ≤ E*D := by
    apply (norm_sum_le _ _).trans
    apply hsum E hE.le
    intro J i
    exact hdyad α hα hbpq s a q hq hnum hden abar habar habar0 habarq
      c hc hch w hw hwV B l (multiwallQ k c) hQ ρ ε
      (fun i => by simpa using Fintype.mem_piFinset.mp hε i) J i
  have hcb : ‖multiwallSigmaClass k r abar c q (multiwallQ k c) w B l ρ‖ ≤
      (2:ℝ)^r * (E*D) := by
    rw [sigma5_decompose_ok]
    calc
      _ ≤ ∑ ε ∈ Fintype.piFinset (fun _ : Fin r => ({1,-1} : Finset ℤ)),
          ‖∑ J ∈ Fintype.piFinset (fun _ : Fin r => Finset.range q),
            multiwallDyadicPiece k r abar c q (multiwallQ k c) w B l ρ ε J‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _ε ∈ Fintype.piFinset (fun _ : Fin r => ({1,-1} : Finset ℤ)), E*D :=
        Finset.sum_le_sum hp
      _ = _ := by simp [Fintype.card_piFinset]
  exact hb.trans (mul_le_mul_of_nonneg_left hcb hF.le)
private lemma agent4MW_real_product (k : ℕ) (f : Fin k → ℤ → ℝ)
    (hf : ∀ j, Summable (f j)) :
    HasSum (fun l : Fin k → ℤ => ∏ j, f j (l j))
      (∏ j, ∑' n, f j n) := by
  apply Complex.hasSum_ofReal.mp
  simpa only [Complex.ofReal_prod, Complex.ofReal_tsum] using
    agent4MW2_pi_good k (fun j n => (f j n : ℂ))
      (fun j => Complex.summable_ofReal.mpr (hf j))

private lemma agent4MW_sum_bound (k : ℕ) (W : Fin k → ℤ → ℂ)
    (S : (Fin k → ℤ) → ℂ) (D C : ℝ) (hC : 0 ≤ C)
    (hS : ∀ l, ‖S l‖ ≤ C)
    (hW : ∀ j, Summable (fun n => ‖W j n‖))
    (hD : ∀ j, (∑' n, ‖W j n‖) ≤ D) :
    ‖∑' l : Fin k → ℤ, (∏ j, W j (l j)) * S l‖ ≤ C * D^k := by
  have hp := agent4MW_real_product k (fun j n => ‖W j n‖) hW
  have hb : ‖∑' l : Fin k → ℤ, (∏ j, W j (l j)) * S l‖ ≤
      (∏ j, ∑' n, ‖W j n‖) * C := by
    apply tsum_of_norm_bounded (hp.mul_right C)
    intro l
    rw [norm_mul, norm_prod]
    exact mul_le_mul_of_nonneg_left (hS l)
      (Finset.prod_nonneg (fun j _ => norm_nonneg _))
  apply hb.trans
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_left _ hC
  calc
    _ ≤ ∏ _j : Fin k, D := Finset.prod_le_prod₀
      (fun j _ => tsum_nonneg (fun n => norm_nonneg _)) (fun j _ => hD j)
    _ = _ := by simp

private lemma agent4MW_delta (α : ℝ) (hα : Irrational α) (s q : ℕ) (hq : 0 < q)
    (a : ℤ) (hnum : (a : ℝ) = (GenContFract.of α).nums s)
    (hden : (q : ℝ) = (GenContFract.of α).dens s) :
    |multiwallDelta α a q| ≤ 1 / (q : ℝ)^2 := by
  have hnt : ¬ (GenContFract.of α).TerminatedAt s := by
    intro ht
    obtain ⟨v, hv⟩ := GenContFract.exists_rat_eq_of_terminates ⟨s, ht⟩
    exact hα ⟨v, hv.symm⟩
  have hpq : (0 : ℝ) < q := by exact_mod_cast hq
  have herr := GenContFract.abs_sub_convs_le hnt
  rw [GenContFract.conv_eq_num_div_den, ← hnum, ← hden] at herr
  have hmono : (q : ℝ) ≤ (GenContFract.of α).dens (s+1) := by
    rw [hden]
    exact GenContFract.of_den_mono
  apply herr.trans
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hmono hpq.le]

private lemma agent4MW_lam_bound_checked (c h P q : ℕ) (hch : c ≤ h)
    (hq : 0 < q) (hPq : P ≤ q) (δ : ℝ) (hδ : |δ| ≤ 1/(q : ℝ)^2) :
    |(c : ℝ)*δ*(P : ℝ)^2| ≤ (h : ℝ) := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hPq' : (P : ℝ) ≤ q := by exact_mod_cast hPq
  have hch' : (c : ℝ) ≤ h := by exact_mod_cast hch
  have hd : |δ| * (q : ℝ)^2 ≤ 1 := (le_div_iff₀ (by positivity)).1 hδ
  have hsq : (P : ℝ)^2 ≤ (q : ℝ)^2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) P]
  have he : |δ| * (P : ℝ)^2 ≤ 1 :=
    (mul_le_mul_of_nonneg_left hsq (abs_nonneg _)).trans hd
  simp only [abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) c),
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) P)]
  nlinarith [mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (α := ℝ) c)]

private lemma mw_lattice_nat_ok (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) :
    Summable (fun n : ℕ => (1 + (d * n)^2)⁻¹) ∧
      (∑' n : ℕ, (1 + (d * n)^2)⁻¹) ≤ 4 / d := by
  have hpoint (n : ℕ) :
      (1 + (d * n)^2)⁻¹ ≤ (4/d) *
        ((1 + d*n)⁻¹ - (1 + d*(n+1))⁻¹) := by
    have hu : 0 ≤ d * (n : ℝ) := by positivity
    have hp : (1 + d*n) * (1 + d*(n+1)) ≤ 4 * (1 + (d*n)^2) := by
      nlinarith [sq_nonneg (d*(n : ℝ)-1), sq_nonneg (d*(n : ℝ)),
        mul_nonneg (sub_nonneg.mpr hd1) (show 0 ≤ 1+d*(n : ℝ) by positivity)]
    calc
      _ ≤ 4 / ((1 + d*n) * (1 + d*(n+1))) := by
        rw [inv_eq_one_div]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith
      _ = _ := by field_simp; ring
  have hfinite (N : ℕ) :
      (∑ n ∈ Finset.range N, (1 + (d * n)^2)⁻¹) ≤ 4/d := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, (4/d) *
          ((1 + d*n)⁻¹ - (1 + d*(n+1))⁻¹) :=
        Finset.sum_le_sum (fun n _ => hpoint n)
      _ = (4/d) * (1 - (1 + d*N)⁻¹) := by
        rw [← Finset.mul_sum]
        have ht := Finset.sum_range_sub' (fun n : ℕ => (1+d*(n : ℝ))⁻¹) N
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero,
          mul_zero, add_zero, inv_one] using congrArg (fun x : ℝ => (4/d)*x) ht
      _ ≤ 4/d := by
        have hp : 0 ≤ (4/d) * (1 + d*N)⁻¹ := by positivity
        nlinarith
  have hs : Summable (fun n : ℕ => (1 + (d * n)^2)⁻¹) :=
    summable_of_sum_range_le (fun n => by positivity) hfinite
  exact ⟨hs, hs.tsum_le_of_sum_range_le hfinite⟩

private lemma mw_lattice_base_final (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) :
    Summable (fun n : ℤ => (1 + (d * n)^2)⁻¹) ∧
      (∑' n : ℤ, (1 + (d * n)^2)⁻¹) ≤ 8 / d := by
  have hn := mw_lattice_nat_ok d hd hd1
  have hp : Summable (fun n : ℕ => (1 + (d * (n : ℤ))^2)⁻¹) := by
    simpa only [Int.cast_natCast] using hn.1
  have hm : Summable (fun n : ℕ => (1 + (d * ((-(n : ℤ) : ℤ) : ℝ))^2)⁻¹) := by
    simpa only [Int.cast_neg, Int.cast_natCast, mul_neg, neg_sq] using hn.1
  refine ⟨Summable.of_nat_of_neg hp hm, ?_⟩
  rw [Summable.tsum_of_nat_of_neg
    (f := fun n : ℤ => (1 + (d * (n : ℝ))^2)⁻¹) hp hm]
  simp only [Int.cast_neg, Int.cast_natCast, mul_neg, neg_sq,
    Int.cast_zero, mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero, inv_one]
  rw [show (8:ℝ)/d = 2*(4/d) by ring]
  linarith [hn.2]

private lemma mw_lattice_shifted (d x : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) :
    Summable (fun n : ℤ => (1 + (d * ((n : ℝ)-x))^2)⁻¹) ∧
      (∑' n : ℤ, (1 + (d * ((n : ℝ)-x))^2)⁻¹) ≤ 24 / d := by
  let a : ℤ := ⌊x⌋
  have ha : (a : ℝ) ≤ x := Int.floor_le x
  have ha' : x < (a : ℝ)+1 := Int.lt_floor_add_one x
  have hb : 0 ≤ d*(x-(a : ℝ)) := by positivity
  have hb1 : d*(x-(a : ℝ)) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (show x-(a : ℝ) ≤ 1 by linarith) hd.le
    nlinarith
  have hbase := mw_lattice_base_final d hd hd1
  have hs : Summable (fun n : ℤ => (1 + (d*((n : ℝ)-(a : ℝ)))^2)⁻¹) := by
    simpa only [Function.comp_def, Equiv.subRight_apply, Int.cast_sub] using
      (Equiv.subRight a).summable_iff.mpr hbase.1
  have he : (∑' n : ℤ, (1 + (d*((n : ℝ)-(a : ℝ)))^2)⁻¹) =
      ∑' n : ℤ, (1 + (d*(n : ℝ))^2)⁻¹ := by
    simpa only [Equiv.subRight_apply, Int.cast_sub] using
      (Equiv.subRight a).tsum_eq (fun n : ℤ => (1+(d*(n : ℝ))^2)⁻¹)
  have hpoint (n : ℤ) :
      (1 + (d*((n : ℝ)-x))^2)⁻¹ ≤
        3 * (1 + (d*((n : ℝ)-(a : ℝ)))^2)⁻¹ := by
    have hbsq : (d*(x-(a : ℝ)))^2 ≤ 1 := by nlinarith
    have halg : d*((n : ℝ)-(a : ℝ)) =
        d*((n : ℝ)-x) + d*(x-(a : ℝ)) := by ring
    have hden : 1 + (d*((n : ℝ)-(a : ℝ)))^2 ≤
        3*(1 + (d*((n : ℝ)-x))^2) := by
      rw [halg]
      nlinarith [sq_nonneg (d*((n : ℝ)-x)-d*(x-(a : ℝ))),
        sq_nonneg (d*((n : ℝ)-x))]
    simp only [inv_eq_one_div, mul_one_div]
    exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by nlinarith)
  have ht : Summable (fun n : ℤ => (1 + (d*((n : ℝ)-x))^2)⁻¹) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hpoint (hs.mul_left 3)
  refine ⟨ht, ?_⟩
  calc
    _ ≤ ∑' n : ℤ, 3 * (1 + (d*((n : ℝ)-(a : ℝ)))^2)⁻¹ :=
      Summable.tsum_le_tsum hpoint ht (hs.mul_left 3)
    _ = 3 * ∑' n : ℤ, (1+(d*(n : ℝ))^2)⁻¹ := by rw [tsum_mul_left, he]
    _ ≤ 3*(8/d) := mul_le_mul_of_nonneg_left hbase.2 (by norm_num)
    _ = 24/d := by ring

private lemma agent4MW_kernel (P q : ℝ) (hP : 0 < P) (hq : 0 < q)
    (hPq : P ≤ q) (β : ℝ) :
    Summable (fun n : ℤ => (1 + |P*(β-(n : ℝ)/q)|^2)⁻¹) ∧
      (∑' n : ℤ, (1 + |P*(β-(n : ℝ)/q)|^2)⁻¹) ≤ 24*q/P := by
  have hh := mw_lattice_shifted (P/q) (q*β) (div_pos hP hq)
    ((div_le_one hq).2 hPq)
  have he (n : ℤ) : (1 + |P*(β-(n : ℝ)/q)|^2)⁻¹ =
      (1 + (P/q*((n : ℝ)-q*β))^2)⁻¹ := by
    rw [sq_abs]
    have hh : P*(β-(n : ℝ)/q) = -(P/q*((n : ℝ)-q*β)) := by
      field_simp
      <;> ring
    rw [hh, neg_sq]
  simp_rw [he]
  refine ⟨hh.1, ?_⟩
  convert hh.2 using 1 <;> field_simp <;> ring

private lemma agent4MW_W_mass (U : ℝ → ℂ) (hU : IsSmoothCutoff U)
    (P q Lam D H : ℝ) (hP : 0 < P) (hq : 0 < q) (hPq : P ≤ q)
    (hD : 0 < D) (hLam : 1 ≤ Lam)
    (hU1 : (∫ t : ℝ, ‖deriv U t‖) ≤ Lam)
    (hU2 : (∫ t : ℝ, ‖deriv (deriv U) t‖) ≤ Lam)
    (hdec : ∀ lam : ℝ, |lam| ≤ H → ∀ xi : ℝ,
      ‖oscIntegralW U lam xi‖ ≤
        D*(1+(∫ t : ℝ, ‖deriv U t‖)+(∫ t : ℝ, ‖deriv (deriv U) t‖))/(1+|xi|^2))
    (lam β : ℝ) (hlam : |lam| ≤ H) :
    Summable (fun n : ℤ => ‖oscIntegralW U lam (P*(β-(n : ℝ)/q))‖) ∧
      (∑' n : ℤ, ‖oscIntegralW U lam (P*(β-(n : ℝ)/q))‖) ≤
        (D*(1+2*Lam)*24)*q/P := by
  have hk := agent4MW_kernel P q hP hq hPq β
  have hb (n : ℤ) : ‖oscIntegralW U lam (P*(β-(n : ℝ)/q))‖ ≤
      (D*(1+2*Lam))*(1+|P*(β-(n : ℝ)/q)|^2)⁻¹ := by
    apply (hdec lam hlam _).trans
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) hD.le) (by positivity)
  have hs := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb
    (hk.1.mul_left (D*(1+2*Lam)))
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n : ℤ, (D*(1+2*Lam))*(1+|P*(β-(n : ℝ)/q)|^2)⁻¹ :=
      Summable.tsum_le_tsum hb hs (hk.1.mul_left _)
    _ = (D*(1+2*Lam)) * ∑' n : ℤ, (1+|P*(β-(n : ℝ)/q)|^2)⁻¹ := tsum_mul_left
    _ ≤ (D*(1+2*Lam)) * (24*q/P) :=
      mul_le_mul_of_nonneg_left hk.2 (by positivity)
    _ = _ := by ring

theorem prop_multiwall (A : ℝ) (k r V h : ℕ) (Lam : ℝ) (hA : 1 ≤ A) (hk : 1 ≤ k)
    (hV : 1 ≤ V) (hh : 1 ≤ h) (hLam : 1 ≤ Lam) :
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
            ‖multiwallT k r α c β U P w B‖ ≤ C * Real.sqrt (q : ℝ) ^ k := by
  classical
  obtain ⟨E, hE, hSigma⟩ := multiwall_Sigma_bound A k r V h hA hk hV hh
  obtain ⟨D, hD, hdec⟩ := lem_poisson_decay (h : ℝ) (by exact_mod_cast hh)
  let K : ℝ := D*(1+2*Lam)*24
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨E*K^k, by positivity, ?_⟩
  intro α hα hbpq s a q hq hnum hden hagcd c hc hch P hP hPq w hw hVw B hwB
    U hU hU0 hU1 hU2 β
  refine ⟨(multiwall_T_factorization k r P q hk hP hPq α c hc β U hU.1 hU.2
    w hw B hwB).1, ?_⟩
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hPq' : (P : ℝ) ≤ q := by exact_mod_cast hPq
  have hdelta := agent4MW_delta α hα s q hq a hnum hden
  let W : Fin k → ℤ → ℂ := fun j n =>
    oscIntegralW U ((c j : ℝ)*multiwallDelta α a q*(P : ℝ)^2)
      ((P : ℝ)*(β j-(n : ℝ)/(q : ℝ)))
  have hmass (j : Fin k) : Summable (fun n : ℤ => ‖W j n‖) ∧
      (∑' n : ℤ, ‖W j n‖) ≤ K*(q : ℝ)/(P : ℝ) :=
    agent4MW_W_mass U hU P q Lam D h hPpos hqpos hPq' hD hLam hU1 hU2
      (hdec U hU) _ (β j) (agent4MW_lam_bound_checked (c j) h P q (hch j) hq hPq _ hdelta)
  have hsum := agent4MW_sum_bound k W (multiwallSigma k r a c q hq w B)
    (K*(q : ℝ)/(P : ℝ)) E hE.le
    (hSigma α hα hbpq s a q hq hnum hden hagcd c hc hch w hw hVw B)
    (fun j => (hmass j).1) (fun j => (hmass j).2)
  rw [(multiwall_T_exact_formula k r P q s hk hP hPq hq α hα a hnum hden
    c hc β U hU w hw B hwB).2, norm_mul, norm_pow, norm_div,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqpos
  have hs2 : Real.sqrt (q : ℝ)^2 = (q : ℝ) := Real.sq_sqrt hqpos.le
  have halg : ((P : ℝ)/Real.sqrt (q : ℝ)) * (K*(q : ℝ)/(P : ℝ)) =
      K*Real.sqrt (q : ℝ) := by
    field_simp
    nlinarith [hs2]
  calc
    _ = E * (((P : ℝ)/Real.sqrt (q : ℝ)) * (K*(q : ℝ)/(P : ℝ)))^k := by
      rw [mul_pow]
      ring
    _ = _ := by rw [halg, mul_pow]; ring
open scoped ContDiff

private lemma agent4GeneralOct12Final_cutoff_ok : ∃ U : ℝ → ℂ, IsSmoothCutoff U ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, U x = 1) := by
  obtain ⟨f,hf,hrange,hsupp,hone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) (s := Set.Ioo (-2 : ℝ) 2) (t := Set.Icc (0 : ℝ) 1)
    isOpen_Ioo isClosed_Icc (by intro x hx; constructor <;> linarith [hx.1,hx.2])
  have hsmooth : ContDiff ℝ ∞ f := hf
  let U : ℝ → ℂ := fun x => (f x : ℂ)
  have hU : IsSmoothCutoff U := by
    refine ⟨Complex.ofRealCLM.contDiff.comp hsmooth, ?_⟩
    intro x hx
    have hfx : f x ≠ 0 := by intro h; exact hx (by simp [U,h])
    have hxs : x ∈ Set.Ioo (-2 : ℝ) 2 := by rw [← hsupp]; exact hfx
    exact ⟨hxs.1.le,hxs.2.le⟩
  exact ⟨U, hU, fun x hx => by simp [U, (hone x).mp hx]⟩

private lemma agent4GeneralOct12Final_dot_bound_ok (k R P : ℕ) (w x : Fin k → ℤ)
    (hw : ∑ j, |w j| ≤ (R : ℤ)) (hx : ∀ j, |x j| ≤ (P : ℤ)) :
    |∑ j, w j*x j| ≤ (R : ℤ)*P := by
  calc
    _ ≤ ∑ j, |w j*x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |w j| * (P : ℤ) := Finset.sum_le_sum (fun j _ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _))
    _ = (∑ j, |w j|) *(P : ℤ) := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hw (by positivity)

private lemma agent4GeneralOct12Final_box_size (k R : ℕ) (hk : 1 ≤ k)
    (lo hi : Fin k → ℤ) (hlo : ∀ j, lo j ≤ hi j)
    (hbal : ∀ i j, boxSide k lo hi i ≤ R * boxSide k lo hi j) :
    ∃ H : ℕ, 1 ≤ H ∧ (∀ j, hi j-lo j ≤ (R*H : ℕ)) ∧
      H^k ≤ boxVol k lo hi := by
  classical
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image Finset.univ (boxSide k lo hi)
    (show (Finset.univ : Finset (Fin k)).Nonempty from ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
  let H := boxSide k lo hi j
  have hH : 1 ≤ H := by
    apply Finset.card_pos.mpr
    exact ⟨lo j, Finset.mem_Icc.mpr ⟨le_rfl, hlo j⟩⟩
  refine ⟨H,hH,?_,?_⟩
  · intro i
    have hside : (boxSide k lo hi i : ℤ) = hi i+1-lo i := by
      unfold boxSide
      rw [Int.card_Icc, Int.toNat_of_nonneg (by have := hlo i; omega)]
    have hb : (boxSide k lo hi i : ℤ) ≤ (R*H : ℕ) := by exact_mod_cast hbal i j
    omega
  · calc
      _ = ∏ _i : Fin k, H := by simp
      _ ≤ ∏ i : Fin k, boxSide k lo hi i := Finset.prod_le_prod (fun i hi => hmin i hi)
      _ = _ := rfl

private lemma agent4GeneralOct12Final_constraints_final (k R P : ℕ) (hR : 1 ≤ R)
    (lo hi : Fin k → ℤ) (hlo : ∀ j, lo j ≤ hi j)
    (hwidth : ∀ j, hi j-lo j ≤ (P : ℤ))
    (L : Finset ((Fin k → ℤ) × ℤ)) (hL : IsBalancedPair k R L lo hi)
    (hne : (polyBoxZ k L lo hi).Nonempty) :
    ∃ D : Finset ((Fin k → ℤ) × ℤ), D.card ≤ R+2*k ∧
      (∀ p ∈ D, p.1 ≠ 0 ∧ (∑ j, |p.1 j|) ≤ (R : ℤ) ∧ |p.2| ≤ (R : ℤ)*P) ∧
      ∀ x : Fin k → ℤ,
        (∀ p ∈ D, p.2 ≤ ∑ j, p.1 j*x j) ↔
          (fun j => lo j+x j) ∈ polyBoxZ k L lo hi := by
  classical
  let e (j : Fin k) : Fin k → ℤ := fun t => if t=j then 1 else 0
  let b (p : (Fin k → ℤ) × ℤ) := -(∑ j, p.1 j*lo j)-p.2
  let D₀ := L.image (fun p => (p.1, max (-(R : ℤ)*P) (b p)))
  let D₁ := Finset.univ.image (fun j : Fin k => (e j, (0 : ℤ)))
  let D₂ := Finset.univ.image (fun j : Fin k => (-e j, lo j-hi j))
  let D := D₀ ∪ (D₁ ∪ D₂)
  have he (j : Fin k) : e j ≠ 0 := by
    intro hz
    have hh := congrFun hz j
    simp [e] at hh
  have heabs (j : Fin k) : ∑ t, |e j t| = 1 := by simp [e, apply_ite abs]
  have hedot (j : Fin k) (x : Fin k → ℤ) : ∑ t, e j t*x t = x j := by
    simp [e, ite_mul]
  have hnegdot (j : Fin k) (x : Fin k → ℤ) : ∑ t, (-e j) t*x t = -x j := by
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, hedot]
  have htranslate (p : (Fin k → ℤ) × ℤ) (x : Fin k → ℤ) :
      b p ≤ ∑ j, p.1 j*x j ↔ 0 ≤ (∑ j, p.1 j*(lo j+x j))+p.2 := by
    simp only [b, mul_add, Finset.sum_add_distrib]
    omega
  obtain ⟨n, hn⟩ := hne
  obtain ⟨hnbox, hnL⟩ := Finset.mem_filter.mp hn
  have hncoord (j : Fin k) : lo j ≤ n j ∧ n j ≤ hi j :=
    Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hnbox j)
  have hb (p) (hp : p ∈ L) : b p ≤ (R : ℤ)*P := by
    have hx (j) : |n j-lo j| ≤ (P : ℤ) := by
      rw [abs_of_nonneg (sub_nonneg.mpr (hncoord j).1)]
      have := hwidth j
      have := (hncoord j).2
      omega
    have ht := agent4GeneralOct12Final_dot_bound_ok k R P p.1 (fun j => n j-lo j)
      (hL.2.1 p hp).2 hx
    have hb' : b p ≤ ∑ j, p.1 j*(n j-lo j) := by
      apply (htranslate p _).2
      simpa only [add_sub_cancel] using hnL p hp
    exact hb'.trans ((le_abs_self _).trans ht)
  refine ⟨D, ?_, ?_, ?_⟩
  · have h₀ : D₀.card ≤ R := Finset.card_image_le.trans hL.1
    have h₁ : D₁.card ≤ k := Finset.card_image_le.trans (by simp)
    have h₂ : D₂.card ≤ k := Finset.card_image_le.trans (by simp)
    have hh := Finset.card_union_le D₀ (D₁ ∪ D₂)
    have hh' := Finset.card_union_le D₁ D₂
    change (D₀ ∪ (D₁ ∪ D₂)).card ≤ _
    omega
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
      change z.1 ≠ 0 ∧ (∑ j, |z.1 j|) ≤ (R : ℤ) ∧
        |max (-(R : ℤ)*P) (b z)| ≤ (R : ℤ)*P
      refine ⟨?_, (hL.2.1 z hz).2, ?_⟩
      · intro hez
        have hh := (hL.2.1 z hz).1
        simp [hez] at hh
      · apply abs_le.mpr
        constructor
        · simpa only [neg_mul] using le_max_left (-(R : ℤ)*P) (b z)
        · exact max_le
            (by nlinarith [mul_nonneg (Int.natCast_nonneg R) (Int.natCast_nonneg P)])
            (hb z hz)
    · rcases Finset.mem_union.mp hp with hp | hp
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
        exact ⟨he j,
          by simpa [heabs] using (show (1 : ℤ) ≤ R by exact_mod_cast hR),
          by simpa using (show (0 : ℤ) ≤ (R : ℤ)*P by positivity)⟩
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
        refine ⟨neg_ne_zero.mpr (he j), ?_, ?_⟩
        · simpa only [Pi.neg_apply, abs_neg, heabs] using
            (show (1 : ℤ) ≤ R by exact_mod_cast hR)
        · rw [abs_of_nonpos (sub_nonpos.mpr (hlo j))]
          have hh := hwidth j
          have hRP : (P : ℤ) ≤ (R : ℤ)*P := by
            have hr : (1 : ℤ) ≤ R := by exact_mod_cast hR
            simpa using mul_le_mul_of_nonneg_right hr
              (show (0 : ℤ) ≤ P by positivity)
          omega
  · intro x
    have hd : (∀ p ∈ D, p.2 ≤ ∑ j, p.1 j*x j) ↔
        (∀ p ∈ L, max (-(R : ℤ)*P) (b p) ≤ ∑ j, p.1 j*x j) ∧
        (∀ j, 0 ≤ x j) ∧ (∀ j, lo j-hi j ≤ -x j) := by
      simp only [D, D₀, D₁, D₂, Finset.forall_mem_union, Finset.forall_mem_image,
        Finset.mem_univ, forall_const, hedot, hnegdot]
    rw [hd]
    constructor
    · rintro ⟨hL', hx0, hxhi⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Fintype.mem_piFinset.mpr
        intro j
        exact Finset.mem_Icc.mpr
          ⟨by have := hx0 j; omega, by have := hxhi j; omega⟩
      · intro p hp
        exact (htranslate p x).1 ((le_max_right _ _).trans (hL' p hp))
    · intro hx
      obtain ⟨hxbox,hxL⟩ := Finset.mem_filter.mp hx
      have hxcoord (j) := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hxbox j)
      have hxab (j) : |x j| ≤ (P : ℤ) := by
        have := hxcoord j
        have := hwidth j
        rw [abs_of_nonneg (by omega)]
        omega
      refine ⟨?_, fun j => by have := hxcoord j; omega,
        fun j => by have := hxcoord j; omega⟩
      intro p hp
      apply max_le
      · have hh := agent4GeneralOct12Final_dot_bound_ok k R P p.1 x
          (hL.2.1 p hp).2 hxab
        have := (abs_le.mp hh).1
        linarith
      · exact (htranslate p x).2 (hxL p hp)

private lemma agent4GeneralOct12Final_indicator_bound_final
    (k r P : ℕ) (hP : 1 ≤ P) (α : ℝ) (c : Fin k → ℕ) (β : Fin k → ℝ)
    (U : ℝ → ℂ) (hUs : Function.support U ⊆ Set.Icc (-2 : ℝ) 2)
    (w : Fin r → Fin k → ℤ) (B : Fin r → ℤ) (D : ℝ) (hD : 0 ≤ D)
    (hsub : ∀ t : Finset (Fin r),
      ‖∑' x : Fin k → ℤ, (∏ i ∈ t,
        (Int.sign (2*((∑ j, w i j*x j)-B i)+1) : ℂ)) *
        (∏ j, U ((x j : ℝ)/P)) *
        expTwoPiI (α * ∑ j, (c j : ℝ)*(x j : ℝ)^2 + ∑ j, β j*(x j : ℝ))‖ ≤ D) :
    ‖∑' x : Fin k → ℤ,
      (if ∀ i, 0 ≤ (∑ j, w i j*x j)-B i then (1 : ℂ) else 0) *
      (∏ j, U ((x j : ℝ)/P)) *
      expTwoPiI (α * ∑ j, (c j : ℝ)*(x j : ℝ)^2 + ∑ j, β j*(x j : ℝ))‖ ≤ D := by
  classical
  let H := Fintype.piFinset
    (fun _ : Fin k => Finset.Icc (-2*(P:ℤ)) (2*(P:ℤ)))
  let f (x : Fin k → ℤ) := (∏ j, U ((x j : ℝ)/P)) *
    expTwoPiI (α * ∑ j, (c j : ℝ)*(x j : ℝ)^2 + ∑ j, β j*(x j : ℝ))
  have hf (x : Fin k → ℤ) (hx : x ∉ H) : f x = 0 := by
    have hex : ∃ j, x j ∉ Finset.Icc (-2*(P:ℤ)) (2*(P:ℤ)) := by
      by_contra hn
      apply hx
      exact Fintype.mem_piFinset.mpr (by simpa using not_exists.mp hn)
    obtain ⟨j,hj⟩ := hex
    have hz : (∏ j, U ((x j : ℝ)/P)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (mw_cutoff_zero_ok P hP U hUs _ hj)
    exact mul_eq_zero_of_left hz _
  have he (x : Fin k → ℤ) :
      (if ∀ i, 0 ≤ (∑ j, w i j*x j)-B i then (1 : ℂ) else 0) =
      (2 : ℂ)⁻¹^r * ∑ t ∈ (Finset.univ : Finset (Fin r)).powerset,
        ∏ i ∈ t, (Int.sign (2*((∑ j, w i j*x j)-B i)+1) : ℂ) := by
    have ht := indicator_forall_nonneg_eq_prod w B x
    have ht' := congrArg Complex.ofReal ht
    simpa only [Complex.ofReal_inv, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat,
      Complex.ofReal_one, Complex.ofReal_prod, Complex.ofReal_add,
      Complex.ofReal_intCast, apply_ite Complex.ofReal,
      Complex.ofReal_zero, one_div, inv_pow, Finset.prod_one_add] using ht'
  simp only [mul_assoc]
  change ‖∑' x, (if ∀ i, 0 ≤ (∑ j, w i j*x j)-B i then (1 : ℂ) else 0) * f x‖ ≤ D
  rw [tsum_eq_sum (s := H) (fun x hx => by rw [hf x hx, mul_zero])]
  simp_rw [he, mul_assoc]
  rw [← Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, norm_mul, norm_pow]
  have ht (t : Finset (Fin r)) :
      ‖∑ x ∈ H, (∏ i ∈ t,
        (Int.sign (2*((∑ j, w i j*x j)-B i)+1) : ℂ)) * f x‖ ≤ D := by
    have heq : (∑' x : Fin k → ℤ, (∏ i ∈ t,
        (Int.sign (2*((∑ j, w i j*x j)-B i)+1) : ℂ)) * f x) =
        ∑ x ∈ H, (∏ i ∈ t,
          (Int.sign (2*((∑ j, w i j*x j)-B i)+1) : ℂ)) * f x :=
      tsum_eq_sum (fun x hx => by rw [hf x hx, mul_zero])
    rw [← heq]
    simpa only [f, mul_assoc] using hsub t
  calc
    _ ≤ ‖(2 : ℂ)⁻¹‖^r * ∑ t ∈ (Finset.univ : Finset (Fin r)).powerset, D :=
      mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun t _ => ht t))) (by positivity)
    _ = D := by simp [Finset.card_powerset, norm_inv, mul_assoc]

private lemma agent4GeneralOct12Final_multi_bound_ok (k R T : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (U : ℝ → ℂ) (hU : IsSmoothCutoff U) :
    ∃ C > 0, ∀ α : ℝ, Irrational α →
    (∀ i x, (GenContFract.of α).partDens.get? i = some x → x ≤ (R : ℝ)) →
    ∀ (s : ℕ) (a : ℤ) (q : ℕ), ∀ hq : 0 < q,
    (a : ℝ) = (GenContFract.of α).nums s →
    (q : ℝ) = (GenContFract.of α).dens s → Int.gcd a q = 1 →
    ∀ c : Fin k → ℕ, (∀ j, 1 ≤ c j) → (∀ j, c j ≤ R) →
    ∀ P : ℕ, 1 ≤ P → P ≤ q → ∀ r : ℕ, r ≤ T →
    ∀ w : Fin r → Fin k → ℤ, (∀ i, w i ≠ 0) →
    (∀ i, ∑ j, |w i j| ≤ (R : ℤ)) → ∀ B : Fin r → ℤ,
    (∀ x : Fin k → ℤ, (∀ j, |x j| ≤ 2*(P : ℤ)) →
      ∀ i, 4*|(∑ j, w i j*x j)-B i| ≤ (q : ℤ)) →
    ∀ β : Fin k → ℝ,
    ‖∑' x : Fin k → ℤ,
      (if ∀ i, 0 ≤ (∑ j, w i j*x j)-B i then (1 : ℂ) else 0) *
      (∏ j, U ((x j : ℝ)/P)) *
      expTwoPiI (α * ∑ j, (c j : ℝ)*(x j : ℝ)^2 + ∑ j, β j*(x j : ℝ))‖ ≤
      C * Real.sqrt (q : ℝ)^k := by
  classical
  let Lam := 1 + (∫ t : ℝ, ‖U t‖) + (∫ t : ℝ, ‖deriv U t‖) +
    (∫ t : ℝ, ‖deriv (deriv U) t‖)
  have h0 : 0 ≤ ∫ t : ℝ, ‖U t‖ := MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  have h1 : 0 ≤ ∫ t : ℝ, ‖deriv U t‖ :=
    MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  have h2 : 0 ≤ ∫ t : ℝ, ‖deriv (deriv U) t‖ :=
    MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  have hLam : 1 ≤ Lam := by dsimp [Lam]; linarith
  have hex (r : ℕ) :=
    prop_multiwall (R : ℝ) k r R R Lam (by exact_mod_cast hR) hk hR hR hLam
  choose D hD hbound using hex
  let C := (∑ t ∈ Finset.range (T+1), D t)+1
  have hC : 0 < C := by
    have hn : 0 ≤ ∑ t ∈ Finset.range (T+1), D t :=
      Finset.sum_nonneg (fun t _ => (hD t).le)
    dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro α hα hbp s a q hq hnum hden hagcd c hc hch P hP hPq r hr w hw hwR B hwB β
  apply agent4GeneralOct12Final_indicator_bound_final k r P hP α c β U hU.2 w B
    (C * Real.sqrt (q : ℝ)^k) (by positivity)
  intro t
  let e : Fin t.card ≃ ↥t := (Fintype.equivFinOfCardEq (Fintype.card_coe t)).symm
  have ht := (hbound t.card α hα hbp s a q hq hnum hden hagcd c hc hch P hP hPq
    (fun i => w (e i).val) (fun i => hw _) (fun i => hwR _) (fun i => B (e i).val)
    (fun x hx i => hwB x hx _) U hU (by dsimp [Lam]; linarith)
    (by dsimp [Lam]; linarith) (by dsimp [Lam]; linarith) β).2
  have he (x : Fin k → ℤ) : (∏ i ∈ t,
      (Int.sign (2*((∑ j, w i j*x j)-B i)+1) : ℂ)) =
      ∏ i : Fin t.card,
        (Int.sign (2*((∑ j, w (e i).val j*x j)-B (e i).val)+1) : ℂ) := by
    rw [← Finset.prod_coe_sort t]
    exact (e.prod_comp _).symm
  simp_rw [he]
  apply ht.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have htcard : t.card ≤ T := (Finset.card_le_univ t).trans (by simpa using hr)
  have hdle : D t.card ≤ ∑ n ∈ Finset.range (T+1), D n :=
    Finset.single_le_sum (fun n _ => (hD n).le) (Finset.mem_range.mpr (by omega))
  dsimp [C]
  linarith

private lemma agent4GeneralOct12Final_shift_cutoff (k P : ℕ) (hP : 1 ≤ P)
    (α : ℝ) (c : Fin k → ℕ) (θ : Fin k → ℝ)
    (lo hi : Fin k → ℤ) (L : Finset ((Fin k → ℤ) × ℤ))
    (hwidth : ∀ j, hi j-lo j ≤ (P : ℤ))
    (U : ℝ → ℂ) (hUone : ∀ x ∈ Set.Icc (0 : ℝ) 1, U x = 1)
    (r : ℕ) (w : Fin r → Fin k → ℤ) (B : Fin r → ℤ)
    (hD : ∀ x : Fin k → ℤ,
      (∀ i, 0 ≤ (∑ j, w i j*x j)-B i) ↔
        (fun j => lo j+x j) ∈ polyBoxZ k L lo hi) :
    ‖quadExpSum k α c θ (polyBoxZ k L lo hi)‖ =
    ‖∑' x : Fin k → ℤ,
      (if ∀ i, 0 ≤ (∑ j, w i j*x j)-B i then (1 : ℂ) else 0) *
      (∏ j, U ((x j : ℝ)/P)) *
      expTwoPiI (α * ∑ j, (c j : ℝ)*(x j : ℝ)^2 +
        ∑ j, (θ j+2*α*(c j : ℝ)*(lo j : ℝ))*(x j : ℝ))‖ := by
  classical
  let S := polyBoxZ k L lo hi
  let f (n : Fin k → ℤ) := expTwoPiI (α * ∑ j, (c j : ℝ)*(n j : ℝ)^2 +
    ∑ j, θ j*(n j : ℝ))
  let g (x : Fin k → ℤ) := expTwoPiI (α * ∑ j, (c j : ℝ)*(x j : ℝ)^2 +
    ∑ j, (θ j+2*α*(c j : ℝ)*(lo j : ℝ))*(x j : ℝ))
  have hphase (x : Fin k → ℤ) : f (lo+x) = f lo * g x := by
    rw [← onb_exp_add]
    congr 1
    dsimp [f, g]
    simp only [Pi.add_apply, Int.cast_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hu (x : Fin k → ℤ) (hx : lo+x ∈ S) : (∏ j, U ((x j : ℝ)/P)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    have hh := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx).1 j)
    have hw := hwidth j
    have hx0 : (0 : ℝ) ≤ x j := by
      exact_mod_cast (show (0 : ℤ) ≤ x j by
        change lo j ≤ lo j+x j ∧ _ at hh; omega)
    have hxP : (x j : ℝ) ≤ P := by
      exact_mod_cast (show x j ≤ (P : ℤ) by
        change _ ∧ lo j+x j ≤ hi j at hh; omega)
    apply hUone
    have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
    exact ⟨div_nonneg hx0 hPr.le, (div_le_one hPr).2 hxP⟩
  have ht : quadExpSum k α c θ S = ∑' n : Fin k → ℤ, if n ∈ S then f n else 0 := by
    rw [tsum_eq_sum (s := S) (fun n hn => if_neg hn)]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [if_pos hn]
    rfl
  rw [ht, ← (Equiv.addLeft lo).tsum_eq
    (fun n : Fin k → ℤ => if n ∈ S then f n else 0)]
  have he (x : Fin k → ℤ) : (if lo+x ∈ S then f (lo+x) else 0) =
      f lo * ((if ∀ i, 0 ≤ (∑ j, w i j*x j)-B i then (1 : ℂ) else 0) *
        (∏ j, U ((x j : ℝ)/P)) * g x) := by
    by_cases hx : lo+x ∈ S
    · rw [if_pos hx, if_pos ((hD x).2 hx), hu x hx, one_mul, one_mul, hphase]
    · rw [if_neg hx, if_neg (fun hn => hx ((hD x).1 hn))]
      simp
  change ‖∑' x, (if lo+x ∈ S then f (lo+x) else 0)‖ = _
  simp_rw [he]
  rw [tsum_mul_left, norm_mul]
  simp only [f, LocalizedFourierFinal.FourierMassBounds.exp_norm, one_mul]
  rfl

theorem thm_general (k R : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R) :
    ∃ C > 0, ∀ α : ℝ, Irrational α →
      (∀ (i : ℕ) (x : ℝ),
        (GenContFract.of α).partDens.get? i = some x → x ≤ (R : ℝ)) →
      ∀ c : Fin k → ℕ, (∀ j, 1 ≤ c j) → (∀ j, c j ≤ R) →
      ∀ lo hi : Fin k → ℤ, (∀ s, lo s ≤ hi s) →
      ∀ L : Finset ((Fin k → ℤ) × ℤ), IsBalancedPair k R L lo hi →
      ∀ θ : Fin k → ℝ,
        ‖quadExpSum k α c θ (polyBoxZ k L lo hi)‖ ≤
          C * Real.sqrt (boxVol k lo hi) := by
  classical
  obtain ⟨U,hU,hUone⟩ := agent4GeneralOct12Final_cutoff_ok
  obtain ⟨C,hC,hbound⟩ :=
    agent4GeneralOct12Final_multi_bound_ok k R (R+2*k) hk hR U hU
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  refine ⟨C * Real.sqrt (100*(R : ℝ)^3)^k, by positivity, ?_⟩
  intro α hα hbp c hc hch lo hi hlo L hL θ
  by_cases hne : (polyBoxZ k L lo hi).Nonempty
  swap
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hz, quadExpSum, Finset.sum_empty, norm_zero]
    positivity
  obtain ⟨H,hH,hwidth,hvol⟩ :=
    agent4GeneralOct12Final_box_size k R hk lo hi hlo hL.2.2
  let P := R*H
  have hP : 1 ≤ P := by dsimp [P]; nlinarith
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  obtain ⟨s,a,qz,hnum,hden,hgcd,hqlow,hqmin,hqhigh⟩ :=
    convergent_smallest_den_le R H α hRr hHr hα hbp
  have hqz : 0 < qz := by
    have hp : (0 : ℝ) < 12*(R : ℝ)^2*H := by positivity
    exact_mod_cast hp.trans_le hqlow
  let q := qz.toNat
  have hqcast : (q : ℤ) = qz := Int.toNat_of_nonneg hqz.le
  have hqr : (q : ℝ) = (qz : ℝ) := by exact_mod_cast hqcast
  have hq : 0 < q := by omega
  have hqnum : (q : ℝ) = (GenContFract.of α).dens s := hqr.trans hden
  have hqgcd : Int.gcd a q = 1 := by rwa [hqcast]
  have hPq : P ≤ q := by
    have hp : (P : ℝ) = (R : ℝ)*H := by simp [P]
    have hlarge : (R : ℝ)*H ≤ 12*(R : ℝ)^2*H := by
      have hh : (R : ℝ) ≤ 12*(R : ℝ)^2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg H)
    have he : (P : ℝ) ≤ q := by rw [hp,hqr]; exact hlarge.trans hqlow
    exact_mod_cast he
  obtain ⟨D,hDcard,hDsize,hDmem⟩ :=
    agent4GeneralOct12Final_constraints_final k R P hR lo hi hlo hwidth L hL hne
  let e : Fin D.card ≃ ↥D := (Fintype.equivFinOfCardEq (Fintype.card_coe D)).symm
  let w : Fin D.card → Fin k → ℤ := fun i => (e i).val.1
  let B : Fin D.card → ℤ := fun i => (e i).val.2
  have hw (i) : w i ≠ 0 := (hDsize _ (e i).property).1
  have hwR (i) : ∑ j, |w i j| ≤ (R : ℤ) := (hDsize _ (e i).property).2.1
  have hBR (i) : |B i| ≤ (R : ℤ)*P := (hDsize _ (e i).property).2.2
  have hwB (x : Fin k → ℤ) (hx : ∀ j, |x j| ≤ 2*(P : ℤ)) (i : Fin D.card) :
      4*|(∑ j, w i j*x j)-B i| ≤ (q : ℤ) := by
    have hd := agent4GeneralOct12Final_dot_bound_ok k R (2*P) (w i) x
      (hwR i) (by simpa using hx)
    have ht := abs_add_le (∑ j, w i j*x j) (-(B i))
    rw [abs_neg, ← sub_eq_add_neg] at ht
    have hb := hBR i
    have hlow : 12*(R : ℤ)^2*H ≤ (q : ℤ) := by
      exact_mod_cast (show 12*(R : ℝ)^2*H ≤ (q : ℝ) by rw [hqr]; exact hqlow)
    dsimp [P] at *
    push_cast at hd hb
    nlinarith
  have hmem (x : Fin k → ℤ) :
      (∀ i, 0 ≤ (∑ j, w i j*x j)-B i) ↔
        (fun j => lo j+x j) ∈ polyBoxZ k L lo hi := by
    rw [← hDmem]
    constructor
    · intro ht p hp
      obtain ⟨i,hi⟩ := e.surjective ⟨p,hp⟩
      have hh := ht i
      dsimp [w,B] at hh
      rw [hi] at hh
      change 0 ≤ (∑ j, p.1 j*x j)-p.2 at hh
      omega
    · intro ht i
      have hh := ht (e i).val (e i).property
      change 0 ≤ (∑ j, (e i).val.1 j*x j)-(e i).val.2
      omega
  rw [agent4GeneralOct12Final_shift_cutoff k P hP α c θ lo hi L hwidth U
    hUone D.card w B hmem]
  apply (hbound α hα hbp s a q hq hnum hqnum hqgcd c hc hch P hP hPq
    D.card hDcard w hw hwR B hwB _).trans
  have hv : Real.sqrt (H : ℝ)^k ≤ Real.sqrt (boxVol k lo hi : ℝ) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).2
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, Real.sq_sqrt (Nat.cast_nonneg H)]
    exact_mod_cast hvol
  have hqs : Real.sqrt (q : ℝ) ≤
      Real.sqrt (100*(R : ℝ)^3) * Real.sqrt (H : ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [hqr]
    exact hqhigh
  calc
    C * Real.sqrt (q : ℝ)^k ≤
        C * (Real.sqrt (100*(R : ℝ)^3)*Real.sqrt (H : ℝ))^k := by
      gcongr
    _ = (C * Real.sqrt (100*(R : ℝ)^3)^k) * Real.sqrt (H : ℝ)^k := by
      rw [mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
def constraintRho (k : ℕ) (W : Finset ((Fin k → ℤ) × ℤ)) : ℕ :=
  max W.card (W.sup fun p => (∑ s, |p.1 s|).toNat)

def constraintGraph (k : ℕ) (W : Finset ((Fin k → ℤ) × ℤ)) : SimpleGraph (Fin k) :=
  SimpleGraph.fromRel fun i j => ∃ p ∈ W, p.1 i * p.1 j ≠ 0

theorem card_le_constraintRho (k : ℕ) (W : Finset ((Fin k → ℤ) × ℤ)) :
    W.card ≤ constraintRho k W := by
  exact le_max_left _ _

theorem l1_le_constraintRho (k : ℕ) (W : Finset ((Fin k → ℤ) × ℤ)) :
    ∀ p ∈ W, ∑ s, |p.1 s| ≤ (constraintRho k W : ℤ) := by
  intro p hp
  have h := (Finset.le_sup (f := fun p : (Fin k → ℤ) × ℤ =>
    (∑ s, |p.1 s|).toNat) hp).trans (le_max_right W.card _)
  change (∑ s, |p.1 s|).toNat ≤ constraintRho k W at h
  omega

theorem constraintRho_le_iff (k : ℕ) (W : Finset ((Fin k → ℤ) × ℤ)) (R : ℕ) :
    constraintRho k W ≤ R ↔
      W.card ≤ R ∧ ∀ p ∈ W, ∑ s, |p.1 s| ≤ (R : ℤ) := by
  simp only [constraintRho, max_le_iff, Finset.sup_le_iff]
  constructor
  · rintro ⟨hc, hp⟩
    refine ⟨hc, ?_⟩
    intro p hmem
    have := hp p hmem
    omega
  · rintro ⟨hc, hp⟩
    refine ⟨hc, ?_⟩
    intro p hmem
    have := hp p hmem
    omega

theorem constraintGraph_adj_iff (k : ℕ) (W : Finset ((Fin k → ℤ) × ℤ)) (i j : Fin k) :
    (constraintGraph k W).Adj i j ↔ i ≠ j ∧ ∃ p ∈ W, p.1 i * p.1 j ≠ 0 := by
  simp only [constraintGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · obtain ⟨p, hp, hmul⟩ := h
      exact ⟨hne, p, hp, by simpa only [mul_comm] using hmul⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩
def IsBalancedWrt (k R : ℕ) (W : Finset ((Fin k → ℤ) × ℤ)) (lo hi : Fin k → ℤ) : Prop :=
  1 ≤ k ∧ 1 ≤ R ∧ (∀ p ∈ W, p.1 ≠ 0) ∧
    ∀ i j : Fin k,
      (constraintGraph k W).connectedComponentMk i =
          (constraintGraph k W).connectedComponentMk j →
        boxSide k lo hi i ≤ R * boxSide k lo hi j

theorem isBalancedWrt_iff_reachable (k R : ℕ) (W : Finset ((Fin k → ℤ) × ℤ))
    (lo hi : Fin k → ℤ) :
    IsBalancedWrt k R W lo hi ↔
      1 ≤ k ∧ 1 ≤ R ∧ (∀ p ∈ W, p.1 ≠ 0) ∧
        ∀ i j : Fin k, (constraintGraph k W).Reachable i j →
          boxSide k lo hi i ≤ R * boxSide k lo hi j := by
  simp only [IsBalancedWrt, SimpleGraph.ConnectedComponent.eq]
def vecSupport {d : ℕ} (w : Fin d → ℤ) : Finset (Fin d) :=
  Finset.univ.filter fun j => w j ≠ 0

def polyPZ (d : ℕ) (W : Finset ((Fin d → ℤ) × ℤ)) : Set (Fin d → ℤ) :=
  {x | ∀ p ∈ W, 0 ≤ (∑ s, p.1 s * x s) + p.2}

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

def Piece.quad {d : ℕ} (p : Piece d) (x : Fin d → ℤ) : ℤ :=
  ∑ j, (p.gamma j : ℤ) * x j ^ 2

def Piece.side {d : ℕ} (p : Piece d) (j : Fin d) : ℕ := boxSide d p.lo p.hi j

def Piece.minSide {d : ℕ} (p : Piece d) : ℕ :=
  Finset.univ.inf'
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp p.one_le_dim)) p.side

def Piece.IsShort {d : ℕ} (p : Piece d) (j : Fin d) : Prop :=
  p.side j ≤ p.A * p.minSide

def Piece.IsLong {d : ℕ} (p : Piece d) (j : Fin d) : Prop := ¬ p.IsShort j

def Piece.shortCoords {d : ℕ} (p : Piece d) : Finset (Fin d) :=
  Finset.univ.filter fun j => p.side j ≤ p.A * p.minSide

def Piece.longCoords {d : ℕ} (p : Piece d) : Finset (Fin d) :=
  Finset.univ.filter fun j => ¬ p.side j ≤ p.A * p.minSide

def Piece.IsMixed {d : ℕ} (p : Piece d) (q : (Fin d → ℤ) × ℤ) : Prop :=
  (vecSupport q.1 ∩ p.shortCoords).Nonempty ∧
    (vecSupport q.1 ∩ p.longCoords).Nonempty

noncomputable def Piece.mixedIneqs {d : ℕ} (p : Piece d) :
    Finset ((Fin d → ℤ) × ℤ) := by
  classical
  exact p.W.filter fun q => p.IsMixed q

def Piece.nLong {d : ℕ} (p : Piece d) : ℕ := p.longCoords.card

noncomputable def Piece.nMix {d : ℕ} (p : Piece d) : ℕ := p.mixedIneqs.card

noncomputable def Piece.index {d : ℕ} (p : Piece d) : ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (d, toLex (p.nLong, p.nMix))

theorem Piece.index_lt_iff {d d' : ℕ} (p : Piece d) (p' : Piece d') :
    p.index < p'.index ↔
      d < d' ∨
        (d = d' ∧ (p.nLong < p'.nLong ∨
          (p.nLong = p'.nLong ∧ p.nMix < p'.nMix))) := by
  simp only [Piece.index, Prod.Lex.toLex_lt_toLex]

theorem Piece.mixedIneqs_subset {d : ℕ} (p : Piece d) :
    p.mixedIneqs ⊆ p.W := by
  classical
  exact Finset.filter_subset _ _

theorem Piece.nMix_le_card_W {d : ℕ} (p : Piece d) :
    p.nMix ≤ p.W.card := by
  exact Finset.card_le_card p.mixedIneqs_subset

theorem Piece.card_W_le_A {d : ℕ} (p : Piece d) :
    p.W.card ≤ p.A := by
  exact (card_le_constraintRho d p.W).trans p.rho_le_A

theorem Piece.nMix_le_A {d : ℕ} (p : Piece d) :
    p.nMix ≤ p.A := by
  exact p.nMix_le_card_W.trans p.card_W_le_A

theorem Piece.shortCoords_nonempty {d : ℕ} (p : Piece d) :
    p.shortCoords.Nonempty := by
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp p.one_le_dim)) p.side
  refine ⟨j, Finset.mem_filter.mpr ⟨hj, ?_⟩⟩
  change p.minSide = p.side j at he
  rw [← he]
  simpa only [one_mul] using Nat.mul_le_mul_right p.minSide p.one_le_A

theorem Piece.nLong_lt_dim {d : ℕ} (p : Piece d) :
    p.nLong < d := by
  obtain ⟨j, hj⟩ := p.shortCoords_nonempty
  have hn : j ∉ p.longCoords := by
    intro h
    exact (Finset.mem_filter.mp h).2 (Finset.mem_filter.mp hj).2
  simpa only [Piece.nLong, Fintype.card_fin] using
    Finset.card_lt_univ_of_notMem hn
/-- `|Φ|_∞`, the largest absolute value of an entry of an integer matrix. -/
def matInftyNorm {d : ℕ} (Φ : Matrix (Fin d) (Fin d) ℤ) : ℕ :=
  Finset.univ.sup fun ij : Fin d × Fin d => (Φ ij.1 ij.2).natAbs

theorem matInftyNorm_le_iff {d : ℕ} (Φ : Matrix (Fin d) (Fin d) ℤ) (R : ℕ) :
    matInftyNorm Φ ≤ R ↔ ∀ i j, |Φ i j| ≤ (R : ℤ) := by
  simp only [matInftyNorm, Finset.sup_le_iff, Finset.mem_univ, forall_true_left,
    Prod.forall, Int.abs_eq_natAbs]
  constructor
  · intro h i j
    exact_mod_cast h i j
  · intro h i j
    exact_mod_cast h i j

/-- The image `u + Φ S` of a set of lattice points under the substitution `x = u + Φ y`. -/
def pieceAffineImage {d : ℕ} (u : Fin d → ℤ) (Φ : Matrix (Fin d) (Fin d) ℤ)
    (S : Set (Fin d → ℤ)) : Set (Fin d → ℤ) :=
  (fun y => u + Φ *ᵥ y) '' S

theorem mem_pieceAffineImage_iff {d : ℕ} (u : Fin d → ℤ)
    (Φ : Matrix (Fin d) (Fin d) ℤ) (S : Set (Fin d → ℤ)) (x : Fin d → ℤ) :
    x ∈ pieceAffineImage u Φ S ↔ ∃ y ∈ S, u + Φ *ᵥ y = x := by
  rfl

/-- A transition between pieces of the same dimension. -/
structure IsTransition {d : ℕ} (p p' : Piece d) (u : Fin d → ℤ)
    (Φ : Matrix (Fin d) (Fin d) ℤ) : Prop where
  det_ne_zero : Φ.det ≠ 0
  image_subset : pieceAffineImage u Φ (polyPZ d p'.W) ⊆ polyPZ d p.W
  quad_eq : ∀ y : Fin d → ℤ, p'.quad y = p.quad (Φ *ᵥ y)

/-- The size of a transition is `|Φ|_∞`. -/
def transitionSize {d : ℕ} (Φ : Matrix (Fin d) (Fin d) ℤ) : ℕ := matInftyNorm Φ

/-- A decomposition is a finite family of transitions whose images form a disjoint union. -/
structure IsDecomposition {d M : ℕ} (p : Piece d) (q : Fin M → Piece d)
    (u : Fin M → Fin d → ℤ) (Φ : Fin M → Matrix (Fin d) (Fin d) ℤ) : Prop where
  transitions : ∀ m, IsTransition p (q m) (u m) (Φ m)
  pieces_disjoint : ∀ m m' : Fin M, m ≠ m' →
    Disjoint (pieceAffineImage (u m) (Φ m) (polyPZ d (q m).W))
      (pieceAffineImage (u m') (Φ m') (polyPZ d (q m').W))
  iUnion_eq : polyPZ d p.W =
    ⋃ m : Fin M, pieceAffineImage (u m) (Φ m) (polyPZ d (q m).W)

theorem isDecomposition_iff {d M : ℕ} (p : Piece d) (q : Fin M → Piece d)
    (u : Fin M → Fin d → ℤ) (Φ : Fin M → Matrix (Fin d) (Fin d) ℤ) :
    IsDecomposition p q u Φ ↔
      (∀ m, IsTransition p (q m) (u m) (Φ m)) ∧
        ∀ x : Fin d → ℤ, x ∈ polyPZ d p.W ↔
          ∃! m : Fin M, x ∈ pieceAffineImage (u m) (Φ m) (polyPZ d (q m).W) := by
  classical
  constructor
  · intro h
    refine ⟨h.transitions, fun x => ⟨?_, ?_⟩⟩
    · intro hx
      rw [h.iUnion_eq] at hx
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
      refine ⟨m, hm, ?_⟩
      intro m' hm'
      by_contra hne
      exact Set.disjoint_left.mp (h.pieces_disjoint m' m hne) hm' hm
    · rintro ⟨m, hm, _⟩
      exact (h.transitions m).image_subset hm
  · rintro ⟨ht, hx⟩
    refine ⟨ht, ?_, ?_⟩
    · intro m m' hne
      apply Set.disjoint_left.mpr
      intro x hm hm'
      obtain ⟨j, hj, hu⟩ := (hx x).mp ((ht m).image_subset hm)
      exact hne ((hu m hm).trans (hu m' hm').symm)
    · ext x
      constructor
      · intro hp
        obtain ⟨m, hm, _⟩ := (hx x).mp hp
        exact Set.mem_iUnion.mpr ⟨m, hm⟩
      · intro hp
        obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hp
        exact (ht m).image_subset hm
open scoped Matrix

theorem sum_mul_sq_eq_dotProduct_diagonal_mulVec {d : ℕ} (γ : Fin d → ℤ) (x : Fin d → ℤ) :
    (∑ j, γ j * x j ^ 2) = x ⬝ᵥ (Matrix.diagonal γ *ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem sum_mul_sq_affine_substitution {d : ℕ} (γ : Fin d → ℤ) (u : Fin d → ℤ)
    (Φ : Matrix (Fin d) (Fin d) ℤ) (y : Fin d → ℤ) :
    (∑ j, γ j * (u + Φ *ᵥ y) j ^ 2) =
      (∑ j, γ j * (Φ *ᵥ y) j ^ 2) +
        2 * ((Φᵀ *ᵥ (Matrix.diagonal γ *ᵥ u)) ⬝ᵥ y) +
        ∑ j, γ j * u j ^ 2 := by
  rw [dotProduct_comm (Φᵀ *ᵥ (Matrix.diagonal γ *ᵥ u)) y,
    Matrix.dotProduct_transpose_mulVec]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.add_apply,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem Piece.quad_eq_dotProduct_diagonal_mulVec {d : ℕ} (p : Piece d) (x : Fin d → ℤ) :
    p.quad x = x ⬝ᵥ (Matrix.diagonal (fun j => (p.gamma j : ℤ)) *ᵥ x) := by
  exact sum_mul_sq_eq_dotProduct_diagonal_mulVec _ _

theorem Piece.quad_affine_substitution {d : ℕ} (p : Piece d) (u : Fin d → ℤ)
    (Φ : Matrix (Fin d) (Fin d) ℤ) (y : Fin d → ℤ) :
    p.quad (u + Φ *ᵥ y) =
      p.quad (Φ *ᵥ y) +
        2 * ((Φᵀ *ᵥ (Matrix.diagonal (fun j => (p.gamma j : ℤ)) *ᵥ u)) ⬝ᵥ y) +
        p.quad u := by
  exact sum_mul_sq_affine_substitution _ _ _ _

theorem IsTransition.quad_affine_substitution {d : ℕ} {p p' : Piece d} {u : Fin d → ℤ}
    {Φ : Matrix (Fin d) (Fin d) ℤ} (h : IsTransition p p' u Φ) (y : Fin d → ℤ) :
    p.quad (u + Φ *ᵥ y) =
      p'.quad y +
        2 * ((Φᵀ *ᵥ (Matrix.diagonal (fun j => (p.gamma j : ℤ)) *ᵥ u)) ⬝ᵥ y) +
        p.quad u := by
  rw [p.quad_affine_substitution, h.quad_eq]

theorem IsTransition.exists_affine_correction {d : ℕ} {p p' : Piece d} {u : Fin d → ℤ}
    {Φ : Matrix (Fin d) (Fin d) ℤ} (h : IsTransition p p' u Φ) :
    ∃ (θ : Fin d → ℤ) (κ : ℤ), ∀ y : Fin d → ℤ,
      p.quad (u + Φ *ᵥ y) = p'.quad y + θ ⬝ᵥ y + κ := by
  refine ⟨fun j => 2 * (Φᵀ *ᵥ (Matrix.diagonal (fun j => (p.gamma j : ℤ)) *ᵥ u)) j,
    p.quad u, ?_⟩
  intro y
  rw [h.quad_affine_substitution]
  simp only [dotProduct, Finset.mul_sum, mul_assoc]
def sigmaPieceIndexEquiv {M : ℕ} (N : Fin M → ℕ) :
    ((m : Fin M) × Fin (N m)) ≃ Fin (∑ m, N m) :=
  finSigmaFinEquiv

theorem pieceAffineImage_comp {d : ℕ} (u v : Fin d → ℤ)
    (Φ Ψ : Matrix (Fin d) (Fin d) ℤ) (S : Set (Fin d → ℤ)) :
    pieceAffineImage (u + Φ *ᵥ v) (Φ * Ψ) S =
      pieceAffineImage u Φ (pieceAffineImage v Ψ S) := by
  unfold pieceAffineImage
  rw [Set.image_image]
  congr 1
  funext z
  simp [Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]

theorem transitionSize_mul_le {d : ℕ} (Φ Ψ : Matrix (Fin d) (Fin d) ℤ) :
    transitionSize (Φ * Ψ) ≤ d * transitionSize Φ * transitionSize Ψ := by
  apply (matInftyNorm_le_iff _ _).2
  intro i j
  have hΦ := (matInftyNorm_le_iff Φ (transitionSize Φ)).1 le_rfl
  have hΨ := (matInftyNorm_le_iff Ψ (transitionSize Ψ)).1 le_rfl
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ t : Fin d, |Φ i t * Ψ t j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin d, (transitionSize Φ : ℤ) * (transitionSize Ψ : ℤ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [abs_mul]
      exact mul_le_mul (hΦ i t) (hΨ t j) (abs_nonneg _) (by positivity)
    _ = _ := by simp [Nat.cast_mul, mul_assoc]

theorem IsTransition.comp {d : ℕ} {p p' p'' : Piece d} {u v : Fin d → ℤ}
    {Φ Ψ : Matrix (Fin d) (Fin d) ℤ}
    (h : IsTransition p p' u Φ) (h' : IsTransition p' p'' v Ψ) :
    IsTransition p p'' (u + Φ *ᵥ v) (Φ * Ψ) ∧
      transitionSize (Φ * Ψ) ≤ d * transitionSize Φ * transitionSize Ψ := by
  refine ⟨⟨?_, ?_, ?_⟩, transitionSize_mul_le Φ Ψ⟩
  · rw [Matrix.det_mul]
    exact mul_ne_zero h.det_ne_zero h'.det_ne_zero
  · rw [pieceAffineImage_comp]
    exact (Set.image_mono h'.image_subset).trans h.image_subset
  · intro z
    rw [h'.quad_eq, h.quad_eq, Matrix.mulVec_mulVec]

theorem IsDecomposition.comp {d M : ℕ} {p : Piece d} {q : Fin M → Piece d}
    {u : Fin M → Fin d → ℤ} {Φ : Fin M → Matrix (Fin d) (Fin d) ℤ}
    (h : IsDecomposition p q u Φ)
    (N : Fin M → ℕ) (q' : (m : Fin M) → Fin (N m) → Piece d)
    (v : (m : Fin M) → Fin (N m) → Fin d → ℤ)
    (Ψ : (m : Fin M) → Fin (N m) → Matrix (Fin d) (Fin d) ℤ)
    (h' : ∀ m, IsDecomposition (q m) (q' m) (v m) (Ψ m)) :
    IsDecomposition (M := ∑ m, N m) p
      (fun t =>
        q' ((sigmaPieceIndexEquiv N).symm t).1 ((sigmaPieceIndexEquiv N).symm t).2)
      (fun t =>
        u ((sigmaPieceIndexEquiv N).symm t).1 +
          Φ ((sigmaPieceIndexEquiv N).symm t).1 *ᵥ
            v ((sigmaPieceIndexEquiv N).symm t).1 ((sigmaPieceIndexEquiv N).symm t).2)
      (fun t =>
        Φ ((sigmaPieceIndexEquiv N).symm t).1 *
          Ψ ((sigmaPieceIndexEquiv N).symm t).1 ((sigmaPieceIndexEquiv N).symm t).2) := by
  classical
  let e := sigmaPieceIndexEquiv N
  have ht (t : Fin (∑ m, N m)) :=
    ((h.transitions (e.symm t).1).comp
      ((h' (e.symm t).1).transitions (e.symm t).2)).1
  refine ⟨ht, ?_, ?_⟩
  · intro t t' hne
    obtain ⟨⟨m, n⟩, rfl⟩ := e.surjective t
    obtain ⟨⟨m', n'⟩, rfl⟩ := e.surjective t'
    dsimp only [e]
    repeat rw [Equiv.symm_apply_apply]
    rw [pieceAffineImage_comp, pieceAffineImage_comp]
    by_cases hmm : m = m'
    · subst m'
      have hnn : n ≠ n' := by
        intro he
        subst n'
        exact hne rfl
      apply Set.disjoint_image_of_injective
        (fun x y he => Matrix.mulVec_injective_of_det_ne_zero
          (h.transitions m).det_ne_zero (add_left_cancel he))
      exact (h' m).pieces_disjoint n n' hnn
    · exact (h.pieces_disjoint m m' hmm).mono
        (Set.image_mono ((h' m).transitions n).image_subset)
        (Set.image_mono ((h' m').transitions n').image_subset)
  · ext x
    constructor
    · intro hx
      rw [h.iUnion_eq] at hx
      obtain ⟨m, y, hy, hxy⟩ := Set.mem_iUnion.mp hx
      rw [(h' m).iUnion_eq] at hy
      obtain ⟨n, z, hz, hyz⟩ := Set.mem_iUnion.mp hy
      apply Set.mem_iUnion.mpr
      refine ⟨e ⟨m, n⟩, ?_⟩
      dsimp only [e]
      repeat rw [Equiv.symm_apply_apply]
      rw [pieceAffineImage_comp]
      exact ⟨y, ⟨z, hz, hyz⟩, hxy⟩
    · intro hx
      obtain ⟨t, ht'⟩ := Set.mem_iUnion.mp hx
      exact (ht t).image_subset ht'
def padLeftVec (d₁ d₂ : ℕ) (w : Fin d₁ → ℤ) : Fin (d₁ + d₂) → ℤ :=
  Fin.append w 0

def padRightVec (d₁ d₂ : ℕ) (w : Fin d₂ → ℤ) : Fin (d₁ + d₂) → ℤ :=
  Fin.append 0 w

noncomputable def oplusConstraints (d₁ d₂ : ℕ)
    (W₁ : Finset ((Fin d₁ → ℤ) × ℤ)) (W₂ : Finset ((Fin d₂ → ℤ) × ℤ)) :
    Finset ((Fin (d₁ + d₂) → ℤ) × ℤ) := by
  classical
  exact W₁.image (fun p => (padLeftVec d₁ d₂ p.1, p.2)) ∪
    W₂.image (fun p => (padRightVec d₁ d₂ p.1, p.2))

def leftPart (d₁ d₂ : ℕ) (x : Fin (d₁ + d₂) → ℤ) : Fin d₁ → ℤ :=
  fun j => x (Fin.castAdd d₂ j)

def rightPart (d₁ d₂ : ℕ) (x : Fin (d₁ + d₂) → ℤ) : Fin d₂ → ℤ :=
  fun j => x (Fin.natAdd d₁ j)

def blockDiagMat {d₁ d₂ : ℕ} (Φ₁ : Matrix (Fin d₁) (Fin d₁) ℤ)
    (Φ₂ : Matrix (Fin d₂) (Fin d₂) ℤ) :
    Matrix (Fin (d₁ + d₂)) (Fin (d₁ + d₂)) ℤ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks Φ₁ 0 0 Φ₂)

theorem sum_abs_padLeftVec (d₁ d₂ : ℕ) (w : Fin d₁ → ℤ) :
    ∑ s, |padLeftVec d₁ d₂ w s| = ∑ s, |w s| := by
  rw [Fin.sum_univ_add]
  simp [padLeftVec]

theorem sum_abs_padRightVec (d₁ d₂ : ℕ) (w : Fin d₂ → ℤ) :
    ∑ s, |padRightVec d₁ d₂ w s| = ∑ s, |w s| := by
  rw [Fin.sum_univ_add]
  simp [padRightVec]

theorem polyPZ_oplusConstraints (d₁ d₂ : ℕ)
    (W₁ : Finset ((Fin d₁ → ℤ) × ℤ)) (W₂ : Finset ((Fin d₂ → ℤ) × ℤ)) :
    polyPZ (d₁ + d₂) (oplusConstraints d₁ d₂ W₁ W₂) =
      {x : Fin (d₁ + d₂) → ℤ |
        leftPart d₁ d₂ x ∈ polyPZ d₁ W₁ ∧
          rightPart d₁ d₂ x ∈ polyPZ d₂ W₂} := by
  classical
  ext x
  simp only [polyPZ, Set.mem_setOf_eq, oplusConstraints,
    Finset.forall_mem_union, Finset.forall_mem_image]
  simp [padLeftVec, padRightVec, Fin.sum_univ_add, leftPart, rightPart]

theorem mem_boxZ_append (d₁ d₂ : ℕ)
    (lo₁ hi₁ : Fin d₁ → ℤ) (lo₂ hi₂ : Fin d₂ → ℤ)
    (x : Fin (d₁ + d₂) → ℤ) :
    x ∈ boxZ (d₁ + d₂) (Fin.append lo₁ lo₂) (Fin.append hi₁ hi₂) ↔
      leftPart d₁ d₂ x ∈ boxZ d₁ lo₁ hi₁ ∧
        rightPart d₁ d₂ x ∈ boxZ d₂ lo₂ hi₂ := by
  simp [boxZ, Fintype.mem_piFinset, Fin.forall_fin_add, leftPart, rightPart]

theorem constraintRho_oplusConstraints_le (d₁ d₂ : ℕ)
    (W₁ : Finset ((Fin d₁ → ℤ) × ℤ)) (W₂ : Finset ((Fin d₂ → ℤ) × ℤ)) :
    constraintRho (d₁ + d₂) (oplusConstraints d₁ d₂ W₁ W₂) ≤
      constraintRho d₁ W₁ + constraintRho d₂ W₂ := by
  classical
  apply (constraintRho_le_iff _ _ _).2
  constructor
  · exact (Finset.card_union_le _ _).trans
      ((add_le_add Finset.card_image_le Finset.card_image_le).trans
        (add_le_add (card_le_constraintRho _ _) (card_le_constraintRho _ _)))
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨p, hp1, rfl⟩ := Finset.mem_image.mp hp
      simp only [sum_abs_padLeftVec]
      have := l1_le_constraintRho d₁ W₁ p hp1
      push_cast
      omega
    · obtain ⟨p, hp1, rfl⟩ := Finset.mem_image.mp hp
      simp only [sum_abs_padRightVec]
      have := l1_le_constraintRho d₂ W₂ p hp1
      push_cast
      omega

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

theorem Piece.prod_quad {d₁ d₂ : ℕ} (p : Piece d₁) (p' : Piece d₂)
    (x : Fin (d₁ + d₂) → ℤ) :
    (p.prod p').quad x =
      p.quad (leftPart d₁ d₂ x) + p'.quad (rightPart d₁ d₂ x) := by
  simp [Piece.quad, Piece.prod, Fin.sum_univ_add, leftPart, rightPart]

theorem Piece.prod_isPiece {d₁ d₂ : ℕ} (p : Piece d₁) (p' : Piece d₂) :
    polyPZ (d₁ + d₂) (oplusConstraints d₁ d₂ p.W p'.W) ⊆
        (boxZ (d₁ + d₂) (Fin.append p.lo p'.lo) (Fin.append p.hi p'.hi) :
          Set (Fin (d₁ + d₂) → ℤ)) ∧
      d₁ + d₂ ≤ p.A + p'.A ∧
      constraintRho (d₁ + d₂) (oplusConstraints d₁ d₂ p.W p'.W) ≤ p.A + p'.A ∧
      (∀ j, 1 ≤ Fin.append p.gamma p'.gamma j) ∧
      ∀ j, Fin.append p.gamma p'.gamma j ≤ p.A + p'.A := by
  exact ⟨(p.prod p').poly_subset_box, (p.prod p').dim_le_A,
    (p.prod p').rho_le_A, (p.prod p').one_le_gamma, (p.prod p').gamma_le_A⟩

private lemma agent4_block_left {d₁ d₂ : ℕ}
    (Φ₁ : Matrix (Fin d₁) (Fin d₁) ℤ) (Φ₂ : Matrix (Fin d₂) (Fin d₂) ℤ)
    (x : Fin (d₁ + d₂) → ℤ) :
    leftPart d₁ d₂ (blockDiagMat Φ₁ Φ₂ *ᵥ x) =
      Φ₁ *ᵥ leftPart d₁ d₂ x := by
  funext i
  change (∑ j, blockDiagMat Φ₁ Φ₂ (Fin.castAdd d₂ i) j * x j) = _
  rw [Fin.sum_univ_add]
  simp [blockDiagMat, Matrix.reindex_apply, Matrix.submatrix_apply,
    leftPart, Matrix.mulVec, dotProduct]

private lemma agent4_block_right {d₁ d₂ : ℕ}
    (Φ₁ : Matrix (Fin d₁) (Fin d₁) ℤ) (Φ₂ : Matrix (Fin d₂) (Fin d₂) ℤ)
    (x : Fin (d₁ + d₂) → ℤ) :
    rightPart d₁ d₂ (blockDiagMat Φ₁ Φ₂ *ᵥ x) =
      Φ₂ *ᵥ rightPart d₁ d₂ x := by
  funext i
  change (∑ j, blockDiagMat Φ₁ Φ₂ (Fin.natAdd d₁ i) j * x j) = _
  rw [Fin.sum_univ_add]
  simp [blockDiagMat, Matrix.reindex_apply, Matrix.submatrix_apply,
    rightPart, Matrix.mulVec, dotProduct]

theorem blockDiagMat_det_ne_zero {d₁ d₂ : ℕ}
    (Φ₁ : Matrix (Fin d₁) (Fin d₁) ℤ)
    (Φ₂ : Matrix (Fin d₂) (Fin d₂) ℤ) (h₁ : Φ₁.det ≠ 0) (h₂ : Φ₂.det ≠ 0) :
    (blockDiagMat Φ₁ Φ₂).det ≠ 0 := by
  rw [blockDiagMat, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂]
  exact mul_ne_zero h₁ h₂

theorem transitionSize_blockDiagMat_le {d₁ d₂ : ℕ}
    (Φ₁ : Matrix (Fin d₁) (Fin d₁) ℤ)
    (Φ₂ : Matrix (Fin d₂) (Fin d₂) ℤ) :
    transitionSize (blockDiagMat Φ₁ Φ₂) ≤
      max (transitionSize Φ₁) (transitionSize Φ₂) := by
  apply (matInftyNorm_le_iff _ _).2
  have h₁ := (matInftyNorm_le_iff Φ₁ (transitionSize Φ₁)).1 le_rfl
  have h₂ := (matInftyNorm_le_iff Φ₂ (transitionSize Φ₂)).1 le_rfl
  have hl : (transitionSize Φ₁ : ℤ) ≤
      (max (transitionSize Φ₁) (transitionSize Φ₂) : ℕ) := by
    exact_mod_cast le_max_left (transitionSize Φ₁) (transitionSize Φ₂)
  have hr : (transitionSize Φ₂ : ℤ) ≤
      (max (transitionSize Φ₁) (transitionSize Φ₂) : ℕ) := by
    exact_mod_cast le_max_right (transitionSize Φ₁) (transitionSize Φ₂)
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa [blockDiagMat, Matrix.reindex_apply, Matrix.submatrix_apply]
      using (h₁ i j).trans hl
  · simp [blockDiagMat, Matrix.reindex_apply, Matrix.submatrix_apply]
  · simp [blockDiagMat, Matrix.reindex_apply, Matrix.submatrix_apply]
  · simpa [blockDiagMat, Matrix.reindex_apply, Matrix.submatrix_apply]
      using (h₂ i j).trans hr

private lemma agent4_prod_left {d₁ d₂ : ℕ}
    (u : Fin d₁ → ℤ) (v : Fin d₂ → ℤ)
    (Φ : Matrix (Fin d₁) (Fin d₁) ℤ) (Ψ : Matrix (Fin d₂) (Fin d₂) ℤ)
    (x : Fin (d₁+d₂) → ℤ) :
    leftPart d₁ d₂ (Fin.append u v + blockDiagMat Φ Ψ *ᵥ x) =
      u + Φ *ᵥ leftPart d₁ d₂ x := by
  change leftPart _ _ (Fin.append u v) +
    leftPart _ _ (blockDiagMat Φ Ψ *ᵥ x) = _
  rw [agent4_block_left]
  congr 1
  funext j
  simp [leftPart]

private lemma agent4_prod_right {d₁ d₂ : ℕ}
    (u : Fin d₁ → ℤ) (v : Fin d₂ → ℤ)
    (Φ : Matrix (Fin d₁) (Fin d₁) ℤ) (Ψ : Matrix (Fin d₂) (Fin d₂) ℤ)
    (x : Fin (d₁+d₂) → ℤ) :
    rightPart d₁ d₂ (Fin.append u v + blockDiagMat Φ Ψ *ᵥ x) =
      v + Ψ *ᵥ rightPart d₁ d₂ x := by
  change rightPart _ _ (Fin.append u v) +
    rightPart _ _ (blockDiagMat Φ Ψ *ᵥ x) = _
  rw [agent4_block_right]
  congr 1
  funext j
  simp [rightPart]

theorem IsTransition.prod {d₁ d₂ : ℕ}
    {p₁ p₁' : Piece d₁} {p₂ p₂' : Piece d₂}
    {u₁ : Fin d₁ → ℤ} {u₂ : Fin d₂ → ℤ}
    {Φ₁ : Matrix (Fin d₁) (Fin d₁) ℤ} {Φ₂ : Matrix (Fin d₂) (Fin d₂) ℤ}
    (h₁ : IsTransition p₁ p₁' u₁ Φ₁) (h₂ : IsTransition p₂ p₂' u₂ Φ₂) :
    IsTransition (p₁.prod p₂) (p₁'.prod p₂') (Fin.append u₁ u₂)
      (blockDiagMat Φ₁ Φ₂) := by
  refine ⟨blockDiagMat_det_ne_zero _ _ h₁.det_ne_zero h₂.det_ne_zero, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    change y ∈ polyPZ _ (oplusConstraints _ _ p₁'.W p₂'.W) at hy
    rw [polyPZ_oplusConstraints] at hy
    change _ ∈ polyPZ _ (oplusConstraints _ _ p₁.W p₂.W)
    rw [polyPZ_oplusConstraints]
    change _ ∈ polyPZ _ p₁.W ∧ _ ∈ polyPZ _ p₂.W
    rw [agent4_prod_left, agent4_prod_right]
    exact ⟨h₁.image_subset ⟨_, hy.1, rfl⟩,
      h₂.image_subset ⟨_, hy.2, rfl⟩⟩
  · intro y
    rw [Piece.prod_quad, Piece.prod_quad, agent4_block_left,
      agent4_block_right, h₁.quad_eq, h₂.quad_eq]

private lemma agent4_left_append (d₁ d₂ : ℕ)
    (y : Fin d₁ → ℤ) (z : Fin d₂ → ℤ) :
    leftPart d₁ d₂ (Fin.append y z) = y := by
  funext j
  simp [leftPart]

private lemma agent4_right_append (d₁ d₂ : ℕ)
    (y : Fin d₁ → ℤ) (z : Fin d₂ → ℤ) :
    rightPart d₁ d₂ (Fin.append y z) = z := by
  funext j
  simp [rightPart]

private lemma agent4_prod_image_iff {d₁ d₂ : ℕ}
    (p : Piece d₁) (p' : Piece d₂)
    (u : Fin d₁ → ℤ) (v : Fin d₂ → ℤ)
    (Φ : Matrix (Fin d₁) (Fin d₁) ℤ) (Ψ : Matrix (Fin d₂) (Fin d₂) ℤ)
    (x : Fin (d₁+d₂) → ℤ) :
    x ∈ pieceAffineImage (Fin.append u v) (blockDiagMat Φ Ψ)
        (polyPZ _ (p.prod p').W) ↔
      leftPart _ _ x ∈ pieceAffineImage u Φ (polyPZ _ p.W) ∧
      rightPart _ _ x ∈ pieceAffineImage v Ψ (polyPZ _ p'.W) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y ∈ polyPZ _ (oplusConstraints _ _ p.W p'.W) at hy
    rw [polyPZ_oplusConstraints] at hy
    rw [agent4_prod_left, agent4_prod_right]
    exact ⟨⟨_, hy.1, rfl⟩, ⟨_, hy.2, rfl⟩⟩
  · rintro ⟨⟨y, hy, he⟩, ⟨z, hz, hf⟩⟩
    refine ⟨Fin.append y z, ?_, ?_⟩
    · change _ ∈ polyPZ _ (oplusConstraints _ _ p.W p'.W)
      rw [polyPZ_oplusConstraints]
      exact ⟨by rw [agent4_left_append]; exact hy,
        by rw [agent4_right_append]; exact hz⟩
    · have hl :
          leftPart d₁ d₂
              (Fin.append u v + blockDiagMat Φ Ψ *ᵥ Fin.append y z) =
            leftPart d₁ d₂ x := by
        rw [agent4_prod_left]
        simpa only [agent4_left_append] using he
      have hr :
          rightPart d₁ d₂
              (Fin.append u v + blockDiagMat Φ Ψ *ᵥ Fin.append y z) =
            rightPart d₁ d₂ x := by
        rw [agent4_prod_right]
        simpa only [agent4_right_append] using hf
      funext j
      exact Fin.addCases (fun i => congrFun hl i) (fun i => congrFun hr i) j

theorem IsDecomposition.prod {d₁ d₂ M₁ M₂ : ℕ} {p₁ : Piece d₁} {p₂ : Piece d₂}
    {q₁ : Fin M₁ → Piece d₁} {q₂ : Fin M₂ → Piece d₂}
    {u₁ : Fin M₁ → Fin d₁ → ℤ} {u₂ : Fin M₂ → Fin d₂ → ℤ}
    {Φ₁ : Fin M₁ → Matrix (Fin d₁) (Fin d₁) ℤ}
    {Φ₂ : Fin M₂ → Matrix (Fin d₂) (Fin d₂) ℤ}
    (h₁ : IsDecomposition p₁ q₁ u₁ Φ₁) (h₂ : IsDecomposition p₂ q₂ u₂ Φ₂) :
    IsDecomposition (M := M₁ * M₂) (p₁.prod p₂)
      (fun t =>
        (q₁ (finProdFinEquiv.symm t).1).prod (q₂ (finProdFinEquiv.symm t).2))
      (fun t =>
        Fin.append (u₁ (finProdFinEquiv.symm t).1) (u₂ (finProdFinEquiv.symm t).2))
      (fun t =>
        blockDiagMat (Φ₁ (finProdFinEquiv.symm t).1)
          (Φ₂ (finProdFinEquiv.symm t).2)) := by
  classical
  have hx₁ := (isDecomposition_iff p₁ q₁ u₁ Φ₁).mp h₁
  have hx₂ := (isDecomposition_iff p₂ q₂ u₂ Φ₂).mp h₂
  apply (isDecomposition_iff _ _ _ _).mpr
  refine ⟨fun t => (h₁.transitions _).prod (h₂.transitions _), ?_⟩
  intro x
  change x ∈ polyPZ _ (oplusConstraints _ _ p₁.W p₂.W) ↔ _
  rw [polyPZ_oplusConstraints]
  change (leftPart d₁ d₂ x ∈ polyPZ d₁ p₁.W ∧
    rightPart d₁ d₂ x ∈ polyPZ d₂ p₂.W) ↔ _
  constructor
  · rintro ⟨hx, hy⟩
    obtain ⟨m, hm, hum⟩ := (hx₁.2 _).mp hx
    obtain ⟨n, hn, hun⟩ := (hx₂.2 _).mp hy
    refine ⟨finProdFinEquiv (m,n), ?_, ?_⟩
    · simp only [Equiv.symm_apply_apply]
      exact (agent4_prod_image_iff _ _ _ _ _ _ _).mpr ⟨hm, hn⟩
    · intro t ht
      have ht' := (agent4_prod_image_iff _ _ _ _ _ _ _).mp ht
      apply finProdFinEquiv.symm.injective
      simp only [Equiv.symm_apply_apply]
      exact Prod.ext (hum _ ht'.1) (hun _ ht'.2)
  · rintro ⟨t, ht, _⟩
    have ht' := (agent4_prod_image_iff _ _ _ _ _ _ _).mp ht
    exact ⟨(h₁.transitions _).image_subset ht'.1,
      (h₂.transitions _).image_subset ht'.2⟩
def restrictVec (d : ℕ) (S : Finset (Fin d)) (w : Fin d → ℤ) : Fin d → ℤ :=
  fun j => if j ∈ S then w j else 0

theorem restrictVec_add_sub (d : ℕ) (S : Finset (Fin d)) (w : Fin d → ℤ) :
    restrictVec d S w + (w - restrictVec d S w) = w := by
  abel

theorem restrictVec_support_subset (d : ℕ) (S : Finset (Fin d)) (w : Fin d → ℤ) :
    vecSupport (restrictVec d S w) ⊆ S := by
  intro j hj
  by_contra hn
  have := (Finset.mem_filter.mp hj).2
  simp [restrictVec, hn] at this

theorem sub_restrictVec_support_subset (d : ℕ) (S : Finset (Fin d)) (w : Fin d → ℤ) :
    vecSupport (w - restrictVec d S w) ⊆ Finset.univ \ S := by
  intro j hj
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hn
  have := (Finset.mem_filter.mp hj).2
  simp [restrictVec, hn] at this

theorem sum_abs_restrictVec_le (d : ℕ) (S : Finset (Fin d)) (w : Fin d → ℤ) :
    ∑ j, |restrictVec d S w j| ≤ ∑ j, |w j| := by
  apply Finset.sum_le_sum
  intro j hj
  by_cases h : j ∈ S <;> simp [restrictVec, h, abs_nonneg]

theorem sum_abs_sub_restrictVec_le (d : ℕ) (S : Finset (Fin d)) (w : Fin d → ℤ) :
    ∑ j, |(w - restrictVec d S w) j| ≤ ∑ j, |w j| := by
  apply Finset.sum_le_sum
  intro j hj
  by_cases h : j ∈ S <;> simp [restrictVec, h, abs_nonneg]

def coordVec (d : ℕ) (j : Fin d) : Fin d → ℤ := fun s => if s = j then 1 else 0

noncomputable def boxConstraints (d : ℕ) (lo hi : Fin d → ℤ) :
    Finset ((Fin d → ℤ) × ℤ) := by
  classical
  exact (Finset.univ.image fun j : Fin d => (coordVec d j, -lo j)) ∪
    (Finset.univ.image fun j : Fin d => (-coordVec d j, hi j))

theorem polyPZ_boxConstraints (d : ℕ) (lo hi : Fin d → ℤ) :
    polyPZ d (boxConstraints d lo hi) = (boxZ d lo hi : Set (Fin d → ℤ)) := by
  classical
  ext x
  have hdot (j : Fin d) : (∑ s, coordVec d j s * x s) = x j := by
    simp [coordVec]
  have hneg (j : Fin d) : (∑ s, (-coordVec d j) s * x s) = -x j := by
    simp [coordVec]
  change (∀ p ∈ boxConstraints d lo hi, 0 ≤ (∑ s, p.1 s * x s) + p.2) ↔
    x ∈ boxZ d lo hi
  constructor
  · intro hx
    apply Fintype.mem_piFinset.mpr
    intro j
    have hlo := hx (coordVec d j, -lo j)
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
    have hhi := hx (-coordVec d j, hi j)
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
    simp only [hdot, hneg] at hlo hhi
    exact Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩
  · intro hx p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
      have hj := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hx j)
      simp only [hdot]
      linarith
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
      have hj := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hx j)
      simp only [hneg]
      linarith

theorem card_boxConstraints_le (d : ℕ) (lo hi : Fin d → ℤ) :
    (boxConstraints d lo hi).card ≤ 2 * d := by
  classical
  unfold boxConstraints
  have h₁ : (Finset.univ.image (fun j : Fin d => (coordVec d j, -lo j))).card ≤ d :=
    Finset.card_image_le.trans (by simp)
  have h₂ : (Finset.univ.image (fun j : Fin d => (-coordVec d j, hi j))).card ≤ d :=
    Finset.card_image_le.trans (by simp)
  exact (Finset.card_union_le _ _).trans (by omega)

theorem sum_abs_boxConstraints (d : ℕ) (lo hi : Fin d → ℤ) :
    ∀ p ∈ boxConstraints d lo hi, ∑ s, |p.1 s| = 1 := by
  classical
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    simp [coordVec, apply_ite abs]
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    simp [coordVec, apply_ite abs]

noncomputable def boxMinAffine (d : ℕ) (lo hi : Fin d → ℤ) (w : Fin d → ℤ) (b : ℤ) : ℤ :=
  b + ∑ j, min (w j * lo j) (w j * hi j)

theorem boxMinAffine_spec (d : ℕ) (lo hi : Fin d → ℤ) (hle : ∀ j, lo j ≤ hi j)
    (w : Fin d → ℤ) (b : ℤ) :
    (∀ x ∈ boxZ d lo hi, boxMinAffine d lo hi w b ≤ (∑ s, w s * x s) + b) ∧
      ∃ x ∈ boxZ d lo hi, (∑ s, w s * x s) + b = boxMinAffine d lo hi w b := by
  classical
  constructor
  · intro x hx
    have hsum : (∑ j, min (w j * lo j) (w j * hi j)) ≤ ∑ j, w j * x j := by
      apply Finset.sum_le_sum
      intro j hj
      have hxj := Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hx) j)
      by_cases hw : 0 ≤ w j
      · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hxj.1 hw)
      · exact (min_le_right _ _).trans
          (mul_le_mul_of_nonpos_left hxj.2 (le_of_not_ge hw))
    unfold boxMinAffine
    linarith
  · let x : Fin d → ℤ := fun j => if 0 ≤ w j then lo j else hi j
    refine ⟨x, ?_, ?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro j
      apply Finset.mem_Icc.mpr
      have := hle j
      dsimp [x]
      split_ifs <;> exact ⟨by omega, by omega⟩
    · have he (j : Fin d) : w j * x j = min (w j * lo j) (w j * hi j) := by
        dsimp [x]
        by_cases hw : 0 ≤ w j
        · rw [if_pos hw, min_eq_left (mul_le_mul_of_nonneg_left (hle j) hw)]
        · rw [if_neg hw, min_eq_right
            (mul_le_mul_of_nonpos_left (hle j) (le_of_not_ge hw))]
      simp only [he, boxMinAffine]
      ring

noncomputable def Piece.shortPart {d : ℕ} (p : Piece d) (w : Fin d → ℤ) : Fin d → ℤ :=
  restrictVec d p.shortCoords w

noncomputable def Piece.longPart {d : ℕ} (p : Piece d) (w : Fin d → ℤ) : Fin d → ℤ :=
  w - p.shortPart w

theorem Piece.shortPart_add_longPart {d : ℕ} (p : Piece d) (w : Fin d → ℤ) :
    p.shortPart w + p.longPart w = w := by
  exact restrictVec_add_sub d p.shortCoords w

noncomputable def Piece.splitLambda {d : ℕ} (p : Piece d) (w : Fin d → ℤ) (b : ℤ) : ℤ :=
  boxMinAffine d p.lo p.hi (p.shortPart w) b

theorem Piece.splitLambda_spec {d : ℕ} (p : Piece d) (hJ : ∀ j, p.lo j ≤ p.hi j)
    (w : Fin d → ℤ) (b : ℤ) :
    (∀ x ∈ boxZ d p.lo p.hi,
        p.splitLambda w b ≤ (∑ s, p.shortPart w s * x s) + b) ∧
      ∃ x ∈ boxZ d p.lo p.hi,
        (∑ s, p.shortPart w s * x s) + b = p.splitLambda w b := by
  exact boxMinAffine_spec d p.lo p.hi hJ (p.shortPart w) b

noncomputable def Piece.splitPlusW {d : ℕ} (p : Piece d) (w : Fin d → ℤ) (b : ℤ) :
    Finset ((Fin d → ℤ) × ℤ) := by
  classical
  exact insert (p.longPart w, p.splitLambda w b) (p.W.erase (w, b)) ∪
    boxConstraints d p.lo p.hi

noncomputable def Piece.splitMinusW {d : ℕ} (p : Piece d) (w : Fin d → ℤ) (b : ℤ) :
    Finset ((Fin d → ℤ) × ℤ) := by
  classical
  exact insert (-p.longPart w, -p.splitLambda w b - 1) p.W

theorem Piece.sum_abs_longPart_le {d : ℕ} (p : Piece d) (w : Fin d → ℤ) (b : ℤ)
    (hmem : (w, b) ∈ p.W) :
    ∑ s, |p.longPart w s| ≤ ∑ s, |w s| ∧ ∑ s, |w s| ≤ (p.A : ℤ) := by
  refine ⟨sum_abs_sub_restrictVec_le d p.shortCoords w, ?_⟩
  exact (l1_le_constraintRho d p.W (w,b) hmem).trans (by exact_mod_cast p.rho_le_A)

theorem Piece.splitPlusW_poly_subset_box {d : ℕ} (p : Piece d)
    (hJ : ∀ j, p.lo j ≤ p.hi j) (w : Fin d → ℤ) (b : ℤ) :
    polyPZ d (p.splitPlusW w b) ⊆ (boxZ d p.lo p.hi : Set (Fin d → ℤ)) := by
  classical
  rw [← polyPZ_boxConstraints]
  intro x hx q hq
  exact hx q (Finset.mem_union_right _ hq)

theorem Piece.splitPlusW_rho_le {d : ℕ} (p : Piece d) (hJ : ∀ j, p.lo j ≤ p.hi j)
    (w : Fin d → ℤ) (b : ℤ) (hmem : (w, b) ∈ p.W) :
    constraintRho d (p.splitPlusW w b) ≤ p.A + 2 * d := by
  classical
  apply (constraintRho_le_iff _ _ _).2
  constructor
  · have h₁ := Finset.card_union_le
      (insert (p.longPart w, p.splitLambda w b) (p.W.erase (w,b)))
      (boxConstraints d p.lo p.hi)
    have h₂ := Finset.card_insert_le (p.longPart w, p.splitLambda w b)
      (p.W.erase (w,b))
    have h₃ := Finset.card_erase_add_one hmem
    have h₄ := card_boxConstraints_le d p.lo p.hi
    have h₅ := p.card_W_le_A
    unfold splitPlusW
    omega
  · intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · have hh := p.sum_abs_longPart_le w b hmem
        have ha : (p.A : ℤ) ≤ (p.A + 2*d : ℕ) := by
          exact_mod_cast (Nat.le_add_right p.A (2*d))
        exact (hh.1.trans hh.2).trans ha
      · have hh := l1_le_constraintRho d p.W q (Finset.mem_of_mem_erase hq)
        have ha : (constraintRho d p.W : ℤ) ≤ (p.A + 2*d : ℕ) := by
          exact_mod_cast p.rho_le_A.trans (Nat.le_add_right p.A (2*d))
        exact hh.trans ha
    · rw [sum_abs_boxConstraints d p.lo p.hi q hq]
      have := p.one_le_A
      exact_mod_cast (show 1 ≤ p.A+2*d by omega)

theorem Piece.splitMinusW_poly_subset {d : ℕ} (p : Piece d)
    (hJ : ∀ j, p.lo j ≤ p.hi j) (w : Fin d → ℤ) (b : ℤ) :
    polyPZ d (p.splitMinusW w b) ⊆ polyPZ d p.W ∧
      polyPZ d (p.splitMinusW w b) ⊆ (boxZ d p.lo p.hi : Set (Fin d → ℤ)) := by
  classical
  have hs : polyPZ d (p.splitMinusW w b) ⊆ polyPZ d p.W := by
    intro x hx q hq
    exact hx q (Finset.mem_insert_of_mem hq)
  exact ⟨hs, hs.trans p.poly_subset_box⟩

theorem Piece.splitMinusW_card_le {d : ℕ} (p : Piece d) (w : Fin d → ℤ) (b : ℤ) :
    (p.splitMinusW w b).card ≤ p.W.card + 1 := by
  classical
  exact Finset.card_insert_le _ _

theorem Piece.splitMinusW_rho_le {d : ℕ} (p : Piece d) (hJ : ∀ j, p.lo j ≤ p.hi j)
    (w : Fin d → ℤ) (b : ℤ) (hmem : (w, b) ∈ p.W) :
    constraintRho d (p.splitMinusW w b) ≤ p.A + 1 := by
  classical
  apply (constraintRho_le_iff _ _ _).2
  refine ⟨(p.splitMinusW_card_le w b).trans
    (Nat.add_le_add_right p.card_W_le_A 1), ?_⟩
  intro q hq
  have ha : (p.A : ℤ) ≤ (p.A+1 : ℕ) := by omega
  rcases Finset.mem_insert.mp hq with rfl | hq
  · simpa only [Pi.neg_apply, abs_neg] using
      ((p.sum_abs_longPart_le w b hmem).1.trans
        (p.sum_abs_longPart_le w b hmem).2).trans ha
  · exact (l1_le_constraintRho d p.W q hq).trans
      ((by exact_mod_cast p.rho_le_A :
        (constraintRho d p.W : ℤ) ≤ p.A).trans ha)

theorem Piece.splitPlus_isPiece {d : ℕ} (p : Piece d) (hJ : ∀ j, p.lo j ≤ p.hi j)
    (w : Fin d → ℤ) (b : ℤ) (hmem : (w, b) ∈ p.W) (hmix : p.IsMixed (w, b)) :
    ∃ p' : Piece d, p'.W = p.splitPlusW w b ∧ p'.lo = p.lo ∧ p'.hi = p.hi ∧
      p'.gamma = p.gamma ∧ p'.A = p.A + 2 * d := by
  refine ⟨⟨p.splitPlusW w b, p.lo, p.hi, p.gamma, p.A+2*d,
    p.one_le_dim, p.one_le_gamma,
    p.one_le_A.trans (Nat.le_add_right _ _),
    p.splitPlusW_poly_subset_box hJ w b,
    p.dim_le_A.trans (Nat.le_add_right _ _),
    p.splitPlusW_rho_le hJ w b hmem,
    fun j => (p.gamma_le_A j).trans (Nat.le_add_right _ _)⟩,
    rfl, rfl, rfl, rfl, rfl⟩

theorem Piece.splitMinus_isPiece {d : ℕ} (p : Piece d) (hJ : ∀ j, p.lo j ≤ p.hi j)
    (w : Fin d → ℤ) (b : ℤ) (hmem : (w, b) ∈ p.W) (hmix : p.IsMixed (w, b)) :
    ∃ p' : Piece d, p'.W = p.splitMinusW w b ∧ p'.lo = p.lo ∧ p'.hi = p.hi ∧
      p'.gamma = p.gamma ∧ p'.A = p.A + 1 := by
  refine ⟨⟨p.splitMinusW w b, p.lo, p.hi, p.gamma, p.A+1,
    p.one_le_dim, p.one_le_gamma,
    p.one_le_A.trans (Nat.le_add_right _ _),
    (p.splitMinusW_poly_subset hJ w b).2,
    p.dim_le_A.trans (Nat.le_add_right _ _),
    p.splitMinusW_rho_le hJ w b hmem,
    fun j => (p.gamma_le_A j).trans (Nat.le_add_right _ _)⟩,
    rfl, rfl, rfl, rfl, rfl⟩
open scoped Matrix in
theorem Piece.split_identity_decomposition {d : ℕ} (p pPlus pMinus : Piece d)
    (hJ : ∀ j, p.lo j ≤ p.hi j) (w : Fin d → ℤ) (b : ℤ)
    (hmem : (w, b) ∈ p.W) (hmix : p.IsMixed (w, b))
    (hPlusW : pPlus.W = p.splitPlusW w b) (hPluslo : pPlus.lo = p.lo)
    (hPlushi : pPlus.hi = p.hi) (hPlusgamma : pPlus.gamma = p.gamma)
    (hPlusA : pPlus.A = p.A + 2 * d)
    (hMinusW : pMinus.W = p.splitMinusW w b) (hMinuslo : pMinus.lo = p.lo)
    (hMinushi : pMinus.hi = p.hi) (hMinusgamma : pMinus.gamma = p.gamma)
    (hMinusA : pMinus.A = p.A + 1) :
    IsTransition p pPlus 0 1 ∧ IsTransition p pMinus 0 1 ∧
      Disjoint (polyPZ d pPlus.W) (polyPZ d pMinus.W) ∧
      polyPZ d p.W = polyPZ d pPlus.W ∪ polyPZ d pMinus.W ∧
      IsDecomposition (M := 2) p ![pPlus, pMinus] (fun _ => 0) (fun _ => 1) := by
  classical
  have hpiff (x : Fin d → ℤ) : x ∈ polyPZ d pPlus.W ↔
      (0 ≤ (∑ j, p.longPart w j * x j) + p.splitLambda w b) ∧
      (∀ z ∈ p.W.erase (w,b), 0 ≤ (∑ j, z.1 j * x j) + z.2) ∧
      x ∈ boxZ d p.lo p.hi := by
    rw [hPlusW]
    simp only [polyPZ, splitPlusW, Set.mem_setOf_eq, Finset.forall_mem_union,
      Finset.forall_mem_insert]
    rw [show (∀ z ∈ boxConstraints d p.lo p.hi,
      0 ≤ (∑ j, z.1 j * x j) + z.2) ↔ x ∈ boxZ d p.lo p.hi from
      Set.ext_iff.mp (polyPZ_boxConstraints d p.lo p.hi) x]
    tauto
  have hmiff (x : Fin d → ℤ) : x ∈ polyPZ d pMinus.W ↔
      (∑ j, p.longPart w j * x j) + p.splitLambda w b < 0 ∧ x ∈ polyPZ d p.W := by
    rw [hMinusW]
    simp only [polyPZ, splitMinusW, Set.mem_setOf_eq, Finset.forall_mem_insert,
      Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    constructor
    · rintro ⟨hn, hx⟩
      refine ⟨?_, hx⟩
      omega
    · rintro ⟨hn, hx⟩
      refine ⟨?_, hx⟩
      omega
  have hplus : polyPZ d pPlus.W ⊆ polyPZ d p.W := by
    intro x hx
    obtain ⟨hl, he, hxbox⟩ := (hpiff x).mp hx
    have hs := (p.splitLambda_spec hJ w b).1 x hxbox
    have hsum : (∑ j, w j * x j) =
        (∑ j, p.shortPart w j * x j) + ∑ j, p.longPart w j * x j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hh := congrFun (p.shortPart_add_longPart w) j
      change p.shortPart w j + p.longPart w j = w j at hh
      rw [← add_mul, hh]
    intro z hz
    by_cases heq : z = (w,b)
    · subst z
      linarith
    · exact he z (Finset.mem_erase.mpr ⟨heq,hz⟩)
  have hminus : polyPZ d pMinus.W ⊆ polyPZ d p.W :=
    fun x hx => ((hmiff x).mp hx).2
  have hdis : Disjoint (polyPZ d pPlus.W) (polyPZ d pMinus.W) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge ((hpiff x).mp hx).1) ((hmiff x).mp hy).1
  have hunion : polyPZ d p.W = polyPZ d pPlus.W ∪ polyPZ d pMinus.W := by
    ext x
    constructor
    · intro hx
      by_cases hl : 0 ≤ (∑ j, p.longPart w j * x j) + p.splitLambda w b
      · exact Or.inl ((hpiff x).mpr ⟨hl,
          fun z hz => hx z (Finset.mem_of_mem_erase hz), p.poly_subset_box hx⟩)
      · exact Or.inr ((hmiff x).mpr ⟨lt_of_not_ge hl,hx⟩)
    · rintro (hx | hx)
      · exact hplus hx
      · exact hminus hx
  have himage (S : Set (Fin d → ℤ)) : pieceAffineImage 0 1 S = S := by
    simp [pieceAffineImage]
  have htplus : IsTransition p pPlus 0 1 := by
    refine ⟨by simp, ?_, ?_⟩
    · simpa only [himage] using hplus
    · intro y
      simp [Piece.quad, hPlusgamma]
  have htminus : IsTransition p pMinus 0 1 := by
    refine ⟨by simp, ?_, ?_⟩
    · simpa only [himage] using hminus
    · intro y
      simp [Piece.quad, hMinusgamma]
  refine ⟨htplus, htminus, hdis, hunion, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro m
    fin_cases m
    · simpa using htplus
    · simpa using htminus
  · intro m m' hne
    fin_cases m <;> fin_cases m'
    · exact (hne rfl).elim
    · simpa [pieceAffineImage] using hdis
    · simpa [pieceAffineImage] using hdis.symm
    · exact (hne rfl).elim
  · rw [hunion]
    ext x
    constructor
    · rintro (hx | hx)
      · exact Set.mem_iUnion.mpr ⟨0, by simpa [pieceAffineImage] using hx⟩
      · exact Set.mem_iUnion.mpr ⟨1, by simpa [pieceAffineImage] using hx⟩
    · intro hx
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
      fin_cases m
      · exact Or.inl (by simpa [pieceAffineImage] using hm)
      · exact Or.inr (by simpa [pieceAffineImage] using hm)
theorem Piece.splitPlus_side_eq {d : ℕ} (p pPlus : Piece d)
    (hlo : pPlus.lo = p.lo) (hhi : pPlus.hi = p.hi) (j : Fin d) :
    pPlus.side j = p.side j := by
  simp only [Piece.side, hlo, hhi]

theorem Piece.splitPlus_minSide_eq {d : ℕ} (p pPlus : Piece d)
    (hlo : pPlus.lo = p.lo) (hhi : pPlus.hi = p.hi) :
    pPlus.minSide = p.minSide := by
  unfold Piece.minSide
  congr 1
  funext j
  exact p.splitPlus_side_eq pPlus hlo hhi j

theorem Piece.splitPlus_shortCoords_subset {d : ℕ} (p pPlus : Piece d)
    (hlo : pPlus.lo = p.lo) (hhi : pPlus.hi = p.hi) (hA : pPlus.A = p.A + 2 * d) :
    p.shortCoords ⊆ pPlus.shortCoords := by
  intro j hj
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [p.splitPlus_side_eq pPlus hlo hhi, p.splitPlus_minSide_eq pPlus hlo hhi, hA]
  exact (Finset.mem_filter.mp hj).2 |>.trans
    (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))

theorem Piece.splitPlus_longCoords_subset {d : ℕ} (p pPlus : Piece d)
    (hlo : pPlus.lo = p.lo) (hhi : pPlus.hi = p.hi) (hA : pPlus.A = p.A + 2 * d) :
    pPlus.longCoords ⊆ p.longCoords := by
  intro j hj
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro hs
  have hh := p.splitPlus_shortCoords_subset pPlus hlo hhi hA
    (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hs⟩)
  exact (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hh).2

theorem Piece.splitPlus_nLong_le {d : ℕ} (p pPlus : Piece d)
    (hlo : pPlus.lo = p.lo) (hhi : pPlus.hi = p.hi) (hA : pPlus.A = p.A + 2 * d) :
    pPlus.nLong ≤ p.nLong := by
  exact Finset.card_le_card (p.splitPlus_longCoords_subset pPlus hlo hhi hA)

theorem Piece.splitPlus_shortCoords_eq_of_nLong_eq {d : ℕ} (p pPlus : Piece d)
    (hlo : pPlus.lo = p.lo) (hhi : pPlus.hi = p.hi) (hA : pPlus.A = p.A + 2 * d)
    (hn : pPlus.nLong = p.nLong) :
    pPlus.shortCoords = p.shortCoords := by
  have he : pPlus.longCoords = p.longCoords :=
    Finset.eq_of_subset_of_card_le (p.splitPlus_longCoords_subset pPlus hlo hhi hA)
      (by change p.nLong ≤ pPlus.nLong; omega)
  ext j
  have hh := Finset.ext_iff.mp he j
  simp only [Piece.longCoords, Piece.shortCoords, Finset.mem_filter,
    Finset.mem_univ, true_and] at hh ⊢
  tauto

theorem Piece.splitPlus_longPart_not_isMixed {d : ℕ} (p pPlus : Piece d)
    (hshort : pPlus.shortCoords = p.shortCoords) (w : Fin d → ℤ) (b : ℤ) :
    ¬ pPlus.IsMixed (p.longPart w, p.splitLambda w b) := by
  intro hm
  obtain ⟨j, hj⟩ := hm.1
  obtain ⟨hjv, hjs⟩ := Finset.mem_inter.mp hj
  rw [hshort] at hjs
  have hn := (Finset.mem_filter.mp hjv).2
  change p.longPart w j ≠ 0 at hn
  simp [Piece.longPart, Piece.shortPart, restrictVec, hjs] at hn

theorem Piece.boxConstraints_not_isMixed {d : ℕ} (p pPlus : Piece d)
    (hlo : pPlus.lo = p.lo) (hhi : pPlus.hi = p.hi) :
    ∀ q ∈ boxConstraints d p.lo p.hi, ¬ pPlus.IsMixed q := by
  classical
  have hsingle (v : Fin d → ℤ) (j : Fin d) (b : ℤ)
      (hv : ∀ s, s ≠ j → v s = 0) : ¬ pPlus.IsMixed (v, b) := by
    intro hm
    obtain ⟨s, hs⟩ := hm.1
    obtain ⟨t, ht⟩ := hm.2
    obtain ⟨hsv, hss⟩ := Finset.mem_inter.mp hs
    obtain ⟨htv, htl⟩ := Finset.mem_inter.mp ht
    have hsj : s = j := by
      by_contra hn
      exact (Finset.mem_filter.mp hsv).2 (hv s hn)
    have htj : t = j := by
      by_contra hn
      exact (Finset.mem_filter.mp htv).2 (hv t hn)
    subst s
    subst t
    exact (Finset.mem_filter.mp htl).2 (Finset.mem_filter.mp hss).2
  intro q hq
  rcases Finset.mem_union.mp hq with hq | hq
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    apply hsingle (coordVec d j) j (-p.lo j)
    intro s hs
    simp [coordVec, hs]
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    apply hsingle (-coordVec d j) j (p.hi j)
    intro s hs
    simp [coordVec, hs]

theorem Piece.splitPlus_nMix_lt_of_nLong_eq {d : ℕ} (p pPlus : Piece d)
    (hJ : ∀ j, p.lo j ≤ p.hi j) (w : Fin d → ℤ) (b : ℤ)
    (hmem : (w, b) ∈ p.W) (hmix : p.IsMixed (w, b))
    (hPlusW : pPlus.W = p.splitPlusW w b) (hlo : pPlus.lo = p.lo) (hhi : pPlus.hi = p.hi)
    (hA : pPlus.A = p.A + 2 * d) (hn : pPlus.nLong = p.nLong) :
    pPlus.nMix < p.nMix := by
  classical
  have hs := p.splitPlus_shortCoords_eq_of_nLong_eq pPlus hlo hhi hA hn
  have hl : pPlus.longCoords = p.longCoords :=
    Finset.eq_of_subset_of_card_le (p.splitPlus_longCoords_subset pPlus hlo hhi hA)
      (by change p.nLong ≤ pPlus.nLong; omega)
  have hsub : pPlus.mixedIneqs ⊆ p.mixedIneqs.erase (w,b) := by
    intro z hz
    obtain ⟨hzW, hzm⟩ := Finset.mem_filter.mp hz
    rw [hPlusW] at hzW
    rcases Finset.mem_union.mp hzW with hzW | hzW
    · rcases Finset.mem_insert.mp hzW with he | he
      · subst z
        exact False.elim (p.splitPlus_longPart_not_isMixed pPlus hs w b hzm)
      · refine Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp he).1, ?_⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_of_mem_erase he, ?_⟩
        simpa only [Piece.IsMixed, hs, hl] using hzm
    · exact False.elim (p.boxConstraints_not_isMixed pPlus hlo hhi z hzW hzm)
  exact (Finset.card_le_card hsub).trans_lt
    (Finset.card_erase_lt_of_mem (Finset.mem_filter.mpr ⟨hmem, hmix⟩))

theorem Piece.splitPlus_index_lt {d : ℕ} (p pPlus : Piece d)
    (hJ : ∀ j, p.lo j ≤ p.hi j) (w : Fin d → ℤ) (b : ℤ)
    (hmem : (w, b) ∈ p.W) (hmix : p.IsMixed (w, b))
    (hPlusW : pPlus.W = p.splitPlusW w b) (hlo : pPlus.lo = p.lo) (hhi : pPlus.hi = p.hi)
    (hgamma : pPlus.gamma = p.gamma) (hA : pPlus.A = p.A + 2 * d) :
    pPlus.index < p.index := by
  apply (Piece.index_lt_iff pPlus p).mpr
  refine Or.inr ⟨rfl, ?_⟩
  rcases lt_or_eq_of_le (p.splitPlus_nLong_le pPlus hlo hhi hA) with ht | he
  · exact Or.inl ht
  · exact Or.inr ⟨he, p.splitPlus_nMix_lt_of_nLong_eq pPlus hJ w b hmem hmix
      hPlusW hlo hhi hA he⟩
private lemma agent4SplitVariationFinal_short_bound {d : ℕ} (p : Piece d)
    (hJ : ∀ j, p.lo j ≤ p.hi j) (w : Fin d → ℤ) (b : ℤ)
    (hmem : (w,b) ∈ p.W) (x y : Fin d → ℤ)
    (hx : x ∈ boxZ d p.lo p.hi) (hy : y ∈ boxZ d p.lo p.hi) :
    (∑ j, p.shortPart w j * x j) - (∑ j, p.shortPart w j * y j) ≤
      (p.A : ℤ)^2 * (p.minSide : ℤ) := by
  have hcoord (j : Fin d) (hj : j ∈ p.shortCoords) :
      |x j-y j| ≤ (p.A : ℤ)*(p.minSide : ℤ) := by
    have hxj := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hx j)
    have hyj := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hy j)
    have hs := (Finset.mem_filter.mp hj).2
    have hcard : (p.side j : ℤ) = p.hi j + 1 - p.lo j := by
      unfold Piece.side boxSide
      rw [Int.card_Icc, Int.toNat_of_nonneg (by have := hJ j; omega)]
    have hs' : (p.side j : ℤ) ≤ (p.A : ℤ)*(p.minSide : ℤ) := by
      exact_mod_cast hs
    rw [hcard] at hs'
    apply abs_le.mpr
    constructor <;> omega
  have hterm (j : Fin d) :
      p.shortPart w j * (x j-y j) ≤ |w j| *((p.A : ℤ)*(p.minSide : ℤ)) := by
    by_cases hj : j ∈ p.shortCoords
    · simp only [Piece.shortPart, restrictVec, if_pos hj]
      exact (le_abs_self _).trans (by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hcoord j hj) (abs_nonneg _))
    · simp only [Piece.shortPart, restrictVec, if_neg hj, zero_mul]
      positivity
  have hw := (p.sum_abs_longPart_le w b hmem).2
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ j, p.shortPart w j * (x j-y j) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ ∑ j, |w j| *((p.A : ℤ)*(p.minSide : ℤ)) :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = (∑ j, |w j|)*((p.A : ℤ)*(p.minSide : ℤ)) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (p.A : ℤ)*((p.A : ℤ)*(p.minSide : ℤ)) :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    _ = _ := by ring

theorem Piece.splitMinus_longPart_variation_lt {d : ℕ} (p : Piece d)
    (hJ : ∀ j, p.lo j ≤ p.hi j) (w : Fin d → ℤ) (b : ℤ)
    (hmem : (w, b) ∈ p.W) (hmix : p.IsMixed (w, b))
    (x x' : Fin d → ℤ) (hx : x ∈ polyPZ d (p.splitMinusW w b))
    (hx' : x' ∈ polyPZ d (p.splitMinusW w b)) :
    |∑ j, p.longPart w j * (x j - x' j)| < (p.A : ℤ) ^ 2 * (p.minSide : ℤ) := by
  classical
  obtain ⟨y, hy, he⟩ := (p.splitLambda_spec hJ w b).2
  have hbound (z z' : Fin d → ℤ)
      (hz : z ∈ polyPZ d (p.splitMinusW w b))
      (hz' : z' ∈ polyPZ d (p.splitMinusW w b)) :
      (∑ j, p.longPart w j * z j) - (∑ j, p.longPart w j * z' j) <
        (p.A : ℤ)^2 * (p.minSide : ℤ) := by
    have hupper := hz (-p.longPart w, -p.splitLambda w b - 1)
      (Finset.mem_insert_self _ _)
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at hupper
    have horig := (p.splitMinusW_poly_subset hJ w b).1 hz' (w,b) hmem
    have hbox := (p.splitMinusW_poly_subset hJ w b).2 hz'
    have hshort := agent4SplitVariationFinal_short_bound p hJ w b hmem z' y hbox hy
    have hsum : (∑ j, w j * z' j) =
        (∑ j, p.shortPart w j * z' j) + ∑ j, p.longPart w j * z' j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hh := congrFun (p.shortPart_add_longPart w) j
      change p.shortPart w j + p.longPart w j = w j at hh
      rw [← add_mul, hh]
    change 0 ≤ (∑ j, w j * z' j) + b at horig
    rw [hsum] at horig
    omega
  have h₁ := hbound x x' hx hx'
  have h₂ := hbound x' x hx' hx
  have heq : (∑ j, p.longPart w j * (x j-x' j)) =
      (∑ j, p.longPart w j * x j) - ∑ j, p.longPart w j * x' j := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  exact abs_lt.mpr ⟨by linarith, h₁⟩
def shortCoordInner (d : ℕ) (γ : Fin d → ℕ) (ξ η : Fin d → ℚ) : ℚ :=
  ∑ i, ξ i * η i / (γ i : ℚ)

def shortCoordTau (d : ℕ) (γ : Fin d → ℕ) (a : Fin d → ℤ) (j : Fin d) : ℚ :=
  ∑ i ∈ Finset.Iic j, (a i : ℚ) ^ 2 / (γ i : ℚ)

def shortCoordRow (d : ℕ) (γ : Fin d → ℕ) (a : Fin d → ℤ) (j : Fin d) : Fin d → ℚ :=
  if j.val = 0 then fun i => (a i : ℚ)
  else fun i =>
    (if i = j then (1 : ℚ) else 0) -
      (a j : ℚ) / ((γ j : ℚ) * shortCoordTau d γ a j) *
        (if i ≤ j then (a i : ℚ) else 0)

def shortCoordMatrix (d : ℕ) (γ : Fin d → ℕ) (a : Fin d → ℤ) :
    Matrix (Fin d) (Fin d) ℚ :=
  Matrix.of fun j i => shortCoordRow d γ a j i

private lemma sc2026_linear {ι : Type*} [Fintype ι]
    (d : ℕ) (γ : Fin d → ℕ) (r : ι → Fin d → ℚ)
    (c : ι → ℚ) (v : Fin d → ℚ) :
    shortCoordInner d γ (∑ j, c j • r j) v =
      ∑ j, c j * shortCoordInner d γ (r j) v := by
  simp only [shortCoordInner, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma sc2026_symm (d : ℕ) (γ : Fin d → ℕ) (u v : Fin d → ℚ) :
    shortCoordInner d γ u v = shortCoordInner d γ v u := by
  simp only [shortCoordInner, mul_comm]

private lemma sc2026_pos (d : ℕ) (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j)
    (v : Fin d → ℚ) (hv : v ≠ 0) :
    0 < shortCoordInner d γ v v := by
  have hg (j) : (0 : ℚ) < γ j := by
    exact_mod_cast (show 0 < γ j by have := hγ j; omega)
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    simpa using not_exists.mp h i
  exact (div_pos (mul_self_pos.mpr hi) (hg i)).trans_le
    (Finset.single_le_sum
      (fun j _ => div_nonneg (mul_self_nonneg _) (hg j).le)
      (Finset.mem_univ i))

private lemma sc2026_pair (d : ℕ) (γ : Fin d → ℕ)
    (r : Fin d → Fin d → ℚ)
    (ho : ∀ j k, j ≠ k → shortCoordInner d γ (r j) (r k) = 0)
    (c : Fin d → ℚ) (i : Fin d) :
    shortCoordInner d γ (∑ j, c j • r j) (r i) =
      c i * shortCoordInner d γ (r i) (r i) := by
  rw [sc2026_linear]
  apply Finset.sum_eq_single i
  · intro j hj hji
    rw [ho j i hji, mul_zero]
  · simp

private lemma sc2026_li (d : ℕ) (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j)
    (r : Fin d → Fin d → ℚ) (hr : ∀ j, r j ≠ 0)
    (ho : ∀ j k, j ≠ k → shortCoordInner d γ (r j) (r k) = 0) :
    LinearIndependent ℚ r := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have he := sc2026_pair d γ r ho c i
  rw [hc] at he
  simp only [shortCoordInner, Pi.zero_apply, zero_mul, zero_div,
    Finset.sum_const_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_right
    (sc2026_pos d γ hγ (r i) (hr i)).ne'

theorem shortCoord_parseval (d : ℕ) (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j)
    (r : Fin d → Fin d → ℚ) (hr : ∀ j, r j ≠ 0)
    (hortho : ∀ j k, j ≠ k → shortCoordInner d γ (r j) (r k) = 0) (x : Fin d → ℚ) :
    (∀ j, 0 < shortCoordInner d γ (r j) (r j)) ∧
      (∀ j, shortCoordInner d γ (fun i => (γ i : ℚ) * x i) (r j) = ∑ i, r j i * x i) ∧
      (∑ j, (γ j : ℚ) * x j ^ 2)
          = shortCoordInner d γ (fun i => (γ i : ℚ) * x i) (fun i => (γ i : ℚ) * x i) ∧
      (∑ j, (γ j : ℚ) * x j ^ 2)
          = ∑ j, shortCoordInner d γ (fun i => (γ i : ℚ) * x i) (r j) ^ 2
              / shortCoordInner d γ (r j) (r j) ∧
      (∑ j, (γ j : ℚ) * x j ^ 2)
          = ∑ j, (∑ i, r j i * x i) ^ 2 / shortCoordInner d γ (r j) (r j) := by
  classical
  have hpos (j) := sc2026_pos d γ hγ (r j) (hr j)
  have hg (j) : (γ j : ℚ) ≠ 0 := by
    exact_mod_cast (show γ j ≠ 0 by have := hγ j; omega)
  have hdot (j) :
      shortCoordInner d γ (fun i => (γ i : ℚ) * x i) (r j) =
        ∑ i, r j i * x i := by
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [hg i]
    <;> ring
  have hnorm :
      (∑ j, (γ j : ℚ) * x j ^ 2) =
        shortCoordInner d γ (fun i => (γ i : ℚ) * x i)
          (fun i => (γ i : ℚ) * x i) := by
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [hg i]
    <;> ring
  have hli := sc2026_li d γ hγ r hr hortho
  have hcard : Fintype.card (Fin d) = Module.finrank ℚ (Fin d → ℚ) := by
    simp [Module.finrank_fintype_fun_eq_card]
  let b := basisOfLinearIndependentOfCardEqFinrank' r hli hcard
  have hb : (b : Fin d → Fin d → ℚ) = r :=
    coe_basisOfLinearIndependentOfCardEqFinrank' r hli hcard
  let y : Fin d → ℚ := fun i => (γ i : ℚ) * x i
  let c : Fin d → ℚ := fun i => b.repr y i
  have hy : (∑ i, c i • r i) = y := by
    simpa only [hb] using b.sum_repr y
  have hc (i) :
      shortCoordInner d γ y (r i) =
        c i * shortCoordInner d γ (r i) (r i) := by
    rw [← hy]
    exact sc2026_pair d γ r hortho c i
  have hparse :
      shortCoordInner d γ y y =
        ∑ i, shortCoordInner d γ y (r i) ^ 2 /
          shortCoordInner d γ (r i) (r i) := by
    calc
      _ = shortCoordInner d γ (∑ i, c i • r i) y :=
        congrArg (fun z => shortCoordInner d γ z y) hy.symm
      _ = ∑ i, c i * shortCoordInner d γ (r i) y :=
        sc2026_linear d γ r c y
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [sc2026_symm d γ (r i) y, hc i]
        field_simp [(hpos i).ne']
        <;> ring
  refine ⟨hpos, hdot, hnorm, hnorm.trans hparse, ?_⟩
  simpa only [y, hdot] using hnorm.trans hparse

private lemma sc_tau_pos (d : ℕ) (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j)
    (a : Fin d → ℤ) (ha : ∀ j, a j ≠ 0) (j : Fin d) :
    0 < shortCoordTau d γ a j := by
  apply Finset.sum_pos
  · intro i hi
    have hgp : (0 : ℚ) < γ i := by
      exact_mod_cast (show 0 < γ i by have := hγ i; omega)
    have hap : (a i : ℚ) ≠ 0 := by exact_mod_cast ha i
    exact div_pos (sq_pos_of_ne_zero hap) hgp
  · exact ⟨j, Finset.mem_Iic.mpr le_rfl⟩

private lemma sc_row_ne_ok (d : ℕ) (hd : 1 ≤ d)
    (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j)
    (a : Fin d → ℤ) (ha : ∀ j, a j ≠ 0) (j : Fin d) :
    shortCoordRow d γ a j ≠ 0 := by
  let z : Fin d := ⟨0, hd⟩
  have haz : (a z : ℚ) ≠ 0 := by exact_mod_cast ha z
  have haj : (a j : ℚ) ≠ 0 := by exact_mod_cast ha j
  have hgj : (γ j : ℚ) ≠ 0 := by
    exact_mod_cast (show γ j ≠ 0 by have := hγ j; omega)
  have ht := (sc_tau_pos d γ hγ a ha j).ne'
  intro he
  have hz := congrFun he z
  by_cases hj : j.val = 0
  · simp [shortCoordRow, hj, haz] at hz
  · have hzj : z ≠ j := by
      intro he
      have := congrArg Fin.val he
      simp [z] at this
      omega
    have hzle : z ≤ j := by change 0 ≤ j.val; omega
    simp [shortCoordRow, hj, hzj, hzle, haj, hgj, ht, haz] at hz

private lemma sc_inner_row_ok (d : ℕ) (γ : Fin d → ℕ) (a : Fin d → ℤ)
    (v : Fin d → ℚ) (j : Fin d) (hj : j.val ≠ 0) :
    shortCoordInner d γ v (shortCoordRow d γ a j) =
      v j / (γ j : ℚ) -
        ((a j : ℚ) / ((γ j : ℚ) * shortCoordTau d γ a j)) *
          ∑ i ∈ Finset.Iic j, v i * (a i : ℚ) / (γ i : ℚ) := by
  classical
  unfold shortCoordInner
  simp only [shortCoordRow, if_neg hj]
  calc
    _ = ∑ i,
        ((if i = j then v j / (γ j : ℚ) else 0) -
          ((a j : ℚ) / ((γ j : ℚ) * shortCoordTau d γ a j)) *
            (if i ≤ j then v i * (a i : ℚ) / (γ i : ℚ) else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases he : i = j
      · subst i
        simp
        ring
      · by_cases hl : i ≤ j <;> simp [he, hl] <;> ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← Finset.sum_filter, Finset.filter_ge_eq_Iic]

private lemma sc_a_row_zero_ok (d : ℕ) (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j)
    (a : Fin d → ℤ) (ha : ∀ j, a j ≠ 0) (j : Fin d) (hj : j.val ≠ 0) :
    shortCoordInner d γ (fun i => (a i : ℚ)) (shortCoordRow d γ a j) = 0 := by
  rw [sc_inner_row_ok d γ a _ j hj]
  have he :
      (∑ i ∈ Finset.Iic j, (a i : ℚ) * (a i : ℚ) / (γ i : ℚ)) =
        shortCoordTau d γ a j := by
    simp only [shortCoordTau, pow_two]
  rw [he]
  have ht := (sc_tau_pos d γ hγ a ha j).ne'
  have hg : (γ j : ℚ) ≠ 0 := by
    exact_mod_cast (show γ j ≠ 0 by have := hγ j; omega)
  field_simp [ht, hg]
  <;> ring

private lemma sc_support_ok (d : ℕ) (γ : Fin d → ℕ) (a : Fin d → ℤ)
    (j t : Fin d) (hj : j.val ≠ 0) (hjt : j < t) :
    shortCoordRow d γ a j t = 0 := by
  simp [shortCoordRow, hj, ne_of_gt hjt, not_le_of_gt hjt]

private lemma sc_ortho_ok (d : ℕ) (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j)
    (a : Fin d → ℤ) (ha : ∀ j, a j ≠ 0) :
    ∀ j k, j ≠ k →
      shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a k) = 0 := by
  have hord (j k : Fin d) (hjk : j < k) :
      shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a k) = 0 := by
    have hk : k.val ≠ 0 := by
      have hh : j.val < k.val := hjk
      omega
    by_cases hj : j.val = 0
    · simpa only [shortCoordRow, if_pos hj] using
        sc_a_row_zero_ok d γ hγ a ha k hk
    · rw [sc_inner_row_ok d γ a _ k hk, sc_support_ok d γ a j k hj hjk]
      have he :
          (∑ t ∈ Finset.Iic k,
            shortCoordRow d γ a j t * (a t : ℚ) / (γ t : ℚ)) =
          shortCoordInner d γ (shortCoordRow d γ a j) (fun t => (a t : ℚ)) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro t ht htk
        have hkt : k < t :=
          lt_of_not_ge (by simpa only [Finset.mem_Iic] using htk)
        rw [sc_support_ok d γ a j t hj (hjk.trans hkt)]
        simp
      rw [he, sc2026_symm, sc_a_row_zero_ok d γ hγ a ha j hj]
      simp
  intro j k hjk
  rcases lt_or_gt_of_ne hjk with h | h
  · exact hord j k h
  · rw [sc2026_symm]
    exact hord k j h

theorem shortCoord_gramSchmidt (d : ℕ) (hd : 1 ≤ d) (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j)
    (a : Fin d → ℤ) (ha : ∀ j, a j ≠ 0) :
    shortCoordRow d γ a ⟨0, hd⟩ = (fun i => (a i : ℚ)) ∧
      (∀ j, 0 < shortCoordTau d γ a j) ∧
      (∀ j, shortCoordRow d γ a j ≠ 0) ∧
      (∀ j k, j ≠ k →
        shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a k) = 0) ∧
      (∀ j, 0 < shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a j)) ∧
      (∀ (j : Fin d) (x : Fin d → ℚ),
        shortCoordInner d γ (fun i => (γ i : ℚ) * x i) (shortCoordRow d γ a j)
          = ∑ i, shortCoordRow d γ a j i * x i) ∧
      (∀ x : Fin d → ℚ,
        (∑ j, (γ j : ℚ) * x j ^ 2)
          = shortCoordInner d γ (fun i => (γ i : ℚ) * x i) (fun i => (γ i : ℚ) * x i)) ∧
      (∀ x : Fin d → ℚ,
        (∑ j, (γ j : ℚ) * x j ^ 2)
          = ∑ j, (∑ i, shortCoordRow d γ a j i * x i) ^ 2
              / shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a j)) ∧
      (shortCoordMatrix d γ a).det ≠ 0 ∧
      (∀ (j : Fin d) (x : Fin d → ℚ),
        Matrix.mulVec (shortCoordMatrix d γ a) x j = ∑ i, shortCoordRow d γ a j i * x i) ∧
      (∀ x : Fin d → ℚ,
        Matrix.mulVec (shortCoordMatrix d γ a) x ⟨0, hd⟩ = ∑ i, (a i : ℚ) * x i) ∧
      ∃ c : Fin d → ℚ, (∀ j, 0 < c j) ∧
        ∀ x : Fin d → ℚ,
          (∑ j, (γ j : ℚ) * x j ^ 2)
            = ∑ j, c j * Matrix.mulVec (shortCoordMatrix d γ a) x j ^ 2 := by
  classical
  have hrow := sc_row_ne_ok d hd γ hγ a ha
  have ho := sc_ortho_ok d γ hγ a ha
  have hp (x : Fin d → ℚ) :=
    shortCoord_parseval d γ hγ (shortCoordRow d γ a) hrow ho x
  have hpos (j : Fin d) :
      0 < shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a j) :=
    sc2026_pos d γ hγ _ (hrow j)
  have hmat (j : Fin d) (x : Fin d → ℚ) :
      Matrix.mulVec (shortCoordMatrix d γ a) x j =
        ∑ i, shortCoordRow d γ a j i * x i := rfl
  refine ⟨by simp [shortCoordRow], sc_tau_pos d γ hγ a ha, hrow, ho, hpos,
    (fun j x => (hp x).2.1 j), (fun x => (hp x).2.2.1),
    (fun x => (hp x).2.2.2.2), ?_, hmat, ?_, ?_⟩
  · have hli : LinearIndependent ℚ (shortCoordMatrix d γ a).row :=
      sc2026_li d γ hγ (shortCoordRow d γ a) hrow ho
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hli)).ne_zero
  · intro x
    rw [hmat]
    simp [shortCoordRow]
  · refine ⟨fun j =>
        (shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a j))⁻¹,
      fun j => inv_pos.mpr (hpos j), ?_⟩
    intro x
    rw [(hp x).2.2.2.2]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hmat, div_eq_mul_inv, mul_comm]
private lemma scv_final_coord (d : ℕ) (lo hi : Fin d → ℤ) (x y : Fin d → ℤ)
    (hx : x ∈ boxZ d lo hi) (hy : y ∈ boxZ d lo hi) (j : Fin d) :
    |(x j : ℚ) - (y j : ℚ)| ≤ (boxSide d lo hi j : ℚ) := by
  have hxj := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hx j)
  have hyj := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hy j)
  have hc : (boxSide d lo hi j : ℤ) = hi j + 1 - lo j := by
    unfold boxSide
    rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
  have hh : |x j-y j| ≤ (boxSide d lo hi j : ℤ) := by
    rw [hc]
    exact abs_le.mpr ⟨by omega, by omega⟩
  exact_mod_cast hh

private lemma scv_final_tail (d R : ℕ) (a : Fin d → ℤ)
    (haR : ∑ i, |a i| ≤ (R : ℤ)) (lo hi : Fin d → ℤ)
    (hside : ∀ i j : Fin d, i ≤ j → boxSide d lo hi j ≤ boxSide d lo hi i)
    (x y : Fin d → ℤ) (hx : x ∈ boxZ d lo hi) (hy : y ∈ boxZ d lo hi)
    (j : Fin d) :
    |(∑ i ∈ Finset.univ.filter (fun i : Fin d => j < i), (a i : ℚ)*(x i : ℚ)) -
      ∑ i ∈ Finset.univ.filter (fun i : Fin d => j < i), (a i : ℚ)*(y i : ℚ)| ≤
      (R : ℚ) * (boxSide d lo hi j : ℚ) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin d => j < i),
        |(a i : ℚ)*((x i : ℚ)-(y i : ℚ))| := by
      simp only [← mul_sub]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin d => j < i),
        |(a i : ℚ)| * (boxSide d lo hi j : ℚ) := by
      apply Finset.sum_le_sum
      intro i hi'
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (scv_final_coord d lo hi x y hx hy i).trans
        (by exact_mod_cast hside j i (Finset.mem_filter.mp hi').2.le)
    _ = (∑ i ∈ Finset.univ.filter (fun i : Fin d => j < i), |(a i : ℚ)|) *
        (boxSide d lo hi j : ℚ) := (Finset.sum_mul _ _ _).symm
    _ ≤ (R : ℚ) * (boxSide d lo hi j : ℚ) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by intros; positivity)).trans
      exact_mod_cast haR

private lemma scv_final_coefficient (d : ℕ) (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j)
    (a : Fin d → ℤ) (ha : ∀ j, a j ≠ 0) (j : Fin d) :
    |(a j : ℚ)| / ((γ j : ℚ) * shortCoordTau d γ a j) ≤ 1 := by
  have hg : (0 : ℚ) < γ j := by
    exact_mod_cast (show 0 < γ j by have := hγ j; omega)
  have ht := sc_tau_pos d γ hγ a ha j
  have hs : (a j : ℚ)^2 / (γ j : ℚ) ≤ shortCoordTau d γ a j := by
    unfold shortCoordTau
    exact Finset.single_le_sum
      (f := fun i : Fin d => (a i : ℚ)^2 / (γ i : ℚ))
      (fun i _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      (Finset.mem_Iic.mpr le_rfl)
  have hs' := (div_le_iff₀ hg).mp hs
  have ha1 : (1 : ℚ) ≤ |(a j : ℚ)| := by
    have hh : (1 : ℤ) ≤ |a j| := by
      have := abs_pos.mpr (ha j)
      omega
    exact_mod_cast hh
  apply (div_le_one (mul_pos hg ht)).2
  nlinarith [sq_abs (a j : ℚ)]

private lemma scv_final_identity (d : ℕ) (γ : Fin d → ℕ) (a : Fin d → ℤ)
    (j : Fin d) (hj : j.val ≠ 0) (x : Fin d → ℤ) :
    (∑ i, shortCoordRow d γ a j i * (x i : ℚ)) =
      (x j : ℚ) - (a j : ℚ) / ((γ j : ℚ) * shortCoordTau d γ a j) *
        (∑ i, (a i : ℚ) * (x i : ℚ)) +
        (a j : ℚ) / ((γ j : ℚ) * shortCoordTau d γ a j) *
        ∑ i ∈ Finset.univ.filter (fun i : Fin d => j < i), (a i : ℚ) * (x i : ℚ) := by
  classical
  let c : ℚ := (a j : ℚ) / ((γ j : ℚ) * shortCoordTau d γ a j)
  have hrow : (∑ i, shortCoordRow d γ a j i * (x i : ℚ)) =
      (x j : ℚ) - c * (∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ j),
        (a i : ℚ) * (x i : ℚ)) := by
    calc
      _ = ∑ i, ((if i = j then (x j : ℚ) else 0) -
          c * (if i ≤ j then (a i : ℚ) * (x i : ℚ) else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases he : i = j
        · subst i
          simp [shortCoordRow, hj, c]
          <;> ring
        · by_cases hl : i ≤ j <;> simp [shortCoordRow, hj, he, hl, c] <;> ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
          if_true, ← Finset.mul_sum, Finset.sum_filter]
  have hsplit :
      (∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ j), (a i : ℚ)*(x i : ℚ)) +
      (∑ i ∈ Finset.univ.filter (fun i : Fin d => j < i), (a i : ℚ)*(x i : ℚ)) =
      ∑ i, (a i : ℚ)*(x i : ℚ) := by
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hi : i ≤ j
    · simp [hi, not_lt_of_ge hi]
    · simp [hi, lt_of_not_ge hi]
  change _ = (x j : ℚ) - c * _ + c * _
  rw [hrow, ← hsplit]
  ring

theorem shortCoord_variation (d : ℕ) (hd : 1 ≤ d) (R : ℕ) (hR : 1 ≤ R)
    (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j) (hγR : ∀ j, γ j ≤ R)
    (a : Fin d → ℤ) (ha : ∀ j, a j ≠ 0) (haR : ∑ j, |a j| ≤ (R : ℤ))
    (W : Finset ((Fin d → ℤ) × ℤ)) (lo hi : Fin d → ℤ)
    (hbox : polyPZ d W ⊆ (boxZ d lo hi : Set (Fin d → ℤ)))
    (hside : ∀ i j : Fin d, i ≤ j → boxSide d lo hi j ≤ boxSide d lo hi i)
    (H : ℕ) (hH : 1 ≤ H) (hHJ : ∀ j, H ≤ boxSide d lo hi j)
    (hvar : ∀ x ∈ polyPZ d W, ∀ x' ∈ polyPZ d W,
      |∑ i, (a i : ℚ) * ((x i : ℚ) - (x' i : ℚ))| ≤ (R : ℚ) * (H : ℚ)) :
    (∀ x ∈ polyPZ d W, ∀ x' ∈ polyPZ d W,
        |(∑ i, shortCoordRow d γ a ⟨0, hd⟩ i * (x i : ℚ)) -
            ∑ i, shortCoordRow d γ a ⟨0, hd⟩ i * (x' i : ℚ)| ≤ (R : ℚ) * (H : ℚ)) ∧
      ∀ j : Fin d, j.val ≠ 0 →
        |(a j : ℚ)| / ((γ j : ℚ) * shortCoordTau d γ a j) ≤ 1 ∧
        (∀ x : Fin d → ℤ,
          (∑ i, shortCoordRow d γ a j i * (x i : ℚ)) =
            (x j : ℚ) -
              (a j : ℚ) / ((γ j : ℚ) * shortCoordTau d γ a j) *
                (∑ i, (a i : ℚ) * (x i : ℚ)) +
              (a j : ℚ) / ((γ j : ℚ) * shortCoordTau d γ a j) *
                ∑ i ∈ Finset.univ.filter (fun i : Fin d => j < i),
                  (a i : ℚ) * (x i : ℚ)) ∧
        ∀ x ∈ polyPZ d W, ∀ x' ∈ polyPZ d W,
          |(∑ i, shortCoordRow d γ a j i * (x i : ℚ)) -
              ∑ i, shortCoordRow d γ a j i * (x' i : ℚ)| ≤
            (2 * (R : ℚ) + 1) * (boxSide d lo hi j : ℚ) := by
  classical
  constructor
  · intro x hx y hy
    simpa only [shortCoordRow, ite_true, mul_sub, Finset.sum_sub_distrib]
      using hvar x hx y hy
  · intro j hj
    have hcoef := scv_final_coefficient d γ hγ a ha j
    refine ⟨hcoef, scv_final_identity d γ a j hj, ?_⟩
    intro x hx y hy
    let c : ℚ := (a j : ℚ) / ((γ j : ℚ) * shortCoordTau d γ a j)
    have hc : |c| ≤ 1 := by
      dsimp [c]
      rw [abs_div, abs_of_pos (mul_pos
        (show (0 : ℚ) < γ j by
          exact_mod_cast (show 0 < γ j by have := hγ j; omega))
        (sc_tau_pos d γ hγ a ha j))]
      exact hcoef
    have hb := scv_final_coord d lo hi x y (hbox hx) (hbox hy) j
    have ht := scv_final_tail d R a haR lo hi hside x y (hbox hx) (hbox hy) j
    have hv :
        |(∑ i, (a i : ℚ)*(x i : ℚ)) - ∑ i, (a i : ℚ)*(y i : ℚ)| ≤
          (R : ℚ)*(H : ℚ) := by
      simpa only [mul_sub, Finset.sum_sub_distrib] using hvar x hx y hy
    have hHJ' : (H : ℚ) ≤ boxSide d lo hi j := by exact_mod_cast hHJ j
    rw [scv_final_identity d γ a j hj x, scv_final_identity d γ a j hj y]
    change |((x j : ℚ) - c * _ + c * _) - ((y j : ℚ) - c * _ + c * _)| ≤ _
    have halg (X Y A B T U : ℚ) :
        (X-c*A+c*T)-(Y-c*B+c*U) = (X-Y)-c*(A-B)+c*(T-U) := by ring
    rw [halg]
    calc
      _ ≤ |(x j : ℚ)-(y j : ℚ)| +
          |c * ((∑ i, (a i : ℚ)*(x i : ℚ)) - ∑ i, (a i : ℚ)*(y i : ℚ))| +
          |c * ((∑ i ∈ Finset.univ.filter (fun i : Fin d => j < i),
              (a i : ℚ)*(x i : ℚ)) -
            ∑ i ∈ Finset.univ.filter (fun i : Fin d => j < i),
              (a i : ℚ)*(y i : ℚ))| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ (boxSide d lo hi j : ℚ) + (R : ℚ)*(H : ℚ) +
          (R : ℚ)*(boxSide d lo hi j : ℚ) := by
        apply add_le_add (add_le_add hb ?_) ?_
        · rw [abs_mul]
          exact (mul_le_of_le_one_left (abs_nonneg _) hc).trans hv
        · rw [abs_mul]
          exact (mul_le_of_le_one_left (abs_nonneg _) hc).trans ht
      _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_left hHJ' (Nat.cast_nonneg (α := ℚ) R)]
open scoped Matrix

def fundParaReps (d : ℕ) (D : Matrix (Fin d) (Fin d) ℤ) : Set (Fin d → ℤ) :=
  {u | ∃ t : Fin d → ℚ, (∀ j, t j ∈ Set.Ico (0 : ℚ) 1) ∧
    ∀ j, (u j : ℚ) = ∑ i, (D j i : ℚ) * t i}

def IsIntegralScaling (d : ℕ) (T : Matrix (Fin d) (Fin d) ℚ) (s : ℕ) : Prop :=
  ∃ D : Matrix (Fin d) (Fin d) ℤ,
    D.map (fun z : ℤ => (z : ℚ)) = (s : ℚ) • T⁻¹

noncomputable def shiftPullbackConstraints (d : ℕ) (D : Matrix (Fin d) (Fin d) ℤ)
    (u : Fin d → ℤ) (W : Finset ((Fin d → ℤ) × ℤ)) : Finset ((Fin d → ℤ) × ℤ) := by
  classical
  exact W.image fun p => (Dᵀ *ᵥ p.1, p.2 + ∑ s, p.1 s * u s)

theorem mulVec_add_left_injective (d : ℕ) (D : Matrix (Fin d) (Fin d) ℤ)
    (hD : D.det ≠ 0) (u : Fin d → ℤ) :
    Function.Injective fun y : Fin d → ℤ => u + D *ᵥ y := by
  intro x y h
  exact Matrix.mulVec_injective_of_det_ne_zero hD (add_left_cancel h)

theorem dotProduct_shift_mulVec (d : ℕ) (D : Matrix (Fin d) (Fin d) ℤ)
    (u : Fin d → ℤ) (w : Fin d → ℤ) (b : ℤ) (y : Fin d → ℤ) :
    (∑ s, w s * (u + D *ᵥ y) s) + b =
      (∑ s, (Dᵀ *ᵥ w) s * y s) + (b + ∑ s, w s * u s) := by
  change w ⬝ᵥ (u + D *ᵥ y) + b = (Dᵀ *ᵥ w) ⬝ᵥ y + (b + w ⬝ᵥ u)
  rw [dotProduct_add, dotProduct_comm (Dᵀ *ᵥ w), Matrix.dotProduct_transpose_mulVec]
  ring

theorem polyPZ_shiftPullbackConstraints (d : ℕ) (D : Matrix (Fin d) (Fin d) ℤ)
    (u : Fin d → ℤ) (W : Finset ((Fin d → ℤ) × ℤ)) :
    polyPZ d (shiftPullbackConstraints d D u W) =
      {y : Fin d → ℤ | u + D *ᵥ y ∈ polyPZ d W} := by
  classical
  ext y
  simp only [polyPZ, Set.mem_setOf_eq, shiftPullbackConstraints,
    Finset.forall_mem_image, dotProduct_shift_mulVec]

theorem polyPZ_inter_coset (d : ℕ) (D : Matrix (Fin d) (Fin d) ℤ) (hD : D.det ≠ 0)
    (u : Fin d → ℤ) (W : Finset ((Fin d → ℤ) × ℤ)) :
    polyPZ d W ∩ pieceAffineImage u D (Set.univ : Set (Fin d → ℤ)) =
      pieceAffineImage u D (polyPZ d (shiftPullbackConstraints d D u W)) := by
  rw [polyPZ_shiftPullbackConstraints]
  ext x
  constructor
  · rintro ⟨hx, y, _, rfl⟩
    exact ⟨y, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y, Set.mem_univ _, rfl⟩

theorem exists_least_integralScaling (d : ℕ) (T : Matrix (Fin d) (Fin d) ℚ)
    (hT : T.det ≠ 0) :
    ∃ s : ℕ, 1 ≤ s ∧ IsIntegralScaling d T s ∧
      ∀ s' : ℕ, 1 ≤ s' → IsIntegralScaling d T s' → s ≤ s' := by
  classical
  let f : Fin d × Fin d → ℕ := fun p => (T⁻¹ p.1 p.2).den
  let s : ℕ := ∏ p, f p
  have hs : 0 < s := Finset.prod_pos (fun p _ => Rat.den_pos _)
  have hInt : IsIntegralScaling d T s := by
    refine ⟨fun i j => ((∏ p ∈ Finset.univ.erase (i,j), f p : ℕ) : ℤ) *
      (T⁻¹ i j).num, ?_⟩
    ext i j
    change (((((∏ p ∈ Finset.univ.erase (i,j), f p : ℕ) : ℤ) *
      (T⁻¹ i j).num) : ℤ) : ℚ) = (s : ℚ) * T⁻¹ i j
    have he : (∏ p ∈ Finset.univ.erase (i,j), f p) * f (i,j) = s :=
      Finset.prod_erase_mul _ _ (Finset.mem_univ (i,j))
    rw [← he]
    push_cast
    dsimp only [f]
    rw [mul_assoc, Rat.den_mul_eq_num]
  have hex : ∃ s : ℕ, 1 ≤ s ∧ IsIntegralScaling d T s := ⟨s, by omega, hInt⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro s' hs' hInt'
  exact Nat.find_min' hex ⟨hs', hInt'⟩

theorem det_ne_zero_of_isIntegralScaling (d : ℕ) (T : Matrix (Fin d) (Fin d) ℚ)
    (hT : T.det ≠ 0) (s : ℕ) (hs : 1 ≤ s) (D : Matrix (Fin d) (Fin d) ℤ)
    (hD : D.map (fun z : ℤ => (z : ℚ)) = (s : ℚ) • T⁻¹) :
    D.det ≠ 0 := by
  have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  have hInv : (T⁻¹).det ≠ 0 :=
    (Matrix.isUnit_nonsing_inv_det T (isUnit_iff_ne_zero.mpr hT)).ne_zero
  have hnon : ((s : ℚ) • T⁻¹).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hs0) hInv
  have hcast : (D.det : ℚ) ≠ 0 := by
    rw [Int.cast_det, hD]
    exact hnon
  exact fun hz => hcast (by rw [hz]; simp)

theorem fundParaReps_cosets_partition (d : ℕ) (D : Matrix (Fin d) (Fin d) ℤ)
    (hD : D.det ≠ 0) (x : Fin d → ℤ) :
    ∃! p : (Fin d → ℤ) × (Fin d → ℤ),
      p.1 ∈ fundParaReps d D ∧ x = p.1 + D *ᵥ p.2 := by
  classical
  let A : Matrix (Fin d) (Fin d) ℚ := D.map (fun z : ℤ => (z : ℚ))
  have hA : A.det ≠ 0 := by
    dsimp [A]
    rw [← Int.cast_det]
    exact_mod_cast hD
  have hsur : Function.Surjective A.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA))
  obtain ⟨z,hz⟩ := hsur (fun j => (x j : ℚ))
  let y : Fin d → ℤ := fun j => ⌊z j⌋
  let u : Fin d → ℤ := x - D *ᵥ y
  have hcast (v : Fin d → ℤ) :
      A *ᵥ (fun j => (v j : ℚ)) = fun j => ((D *ᵥ v) j : ℚ) := by
    funext j
    simp [A, Matrix.mulVec, dotProduct]
  have hu : u ∈ fundParaReps d D := by
    refine ⟨fun j => z j - (y j : ℚ), ?_, ?_⟩
    · intro j
      have h₁ := Int.floor_le (z j)
      have h₂ := Int.lt_floor_add_one (z j)
      change 0 ≤ z j - (⌊z j⌋ : ℚ) ∧ z j - (⌊z j⌋ : ℚ) < 1
      constructor <;> linarith
    · intro j
      have he := congrFun (Matrix.mulVec_sub A z (fun j => (y j : ℚ))) j
      rw [hz, hcast] at he
      simpa [u, A, Matrix.mulVec, dotProduct] using he.symm
  have hxy : x = u + D *ᵥ y := by dsimp [u]; abel
  refine ⟨(u,y), ⟨hu,hxy⟩, ?_⟩
  rintro ⟨u',y'⟩ ⟨⟨t,ht,htu⟩,hx⟩
  have htvec : A *ᵥ t = fun j => (u' j : ℚ) := by
    funext j
    exact (htu j).symm
  have htz : t + (fun j => (y' j : ℚ)) = z := by
    apply Matrix.mulVec_injective_of_det_ne_zero hA
    rw [Matrix.mulVec_add, htvec, hcast, hz]
    funext j
    have hh := congrFun hx j
    change (u' j : ℚ) + ((D *ᵥ y') j : ℚ) = (x j : ℚ)
    have hh' : u' j + (D *ᵥ y') j = x j := hh.symm
    exact_mod_cast hh'
  have hy : y' = y := by
    funext j
    have hh := congrArg (fun v : Fin d → ℚ => ⌊v j⌋) htz
    simp only [Pi.add_apply, Int.floor_add_intCast,
      Int.floor_eq_zero_iff.mpr (ht j), zero_add] at hh
    exact hh
  have hu' : u' = u := by
    rw [hy] at hx
    exact add_right_cancel (hx.symm.trans hxy)
  exact Prod.ext hu' hy

theorem fundParaReps_finite_ncard (d : ℕ) (D : Matrix (Fin d) (Fin d) ℤ)
    (hD : D.det ≠ 0) :
    (fundParaReps d D).Finite ∧
      (fundParaReps d D).ncard = (D.det).natAbs := by
  classical
  let f := Matrix.toLin' D
  let N := f.range
  let e := LinearEquiv.ofInjective f (Matrix.mulVec_injective_of_det_ne_zero hD)
  have hc := Submodule.natAbs_det_equiv N e.toAddEquiv
  have hef : N.subtype ∘ₗ (e.toAddEquiv : (Fin d → ℤ) →+ N).toIntLinearMap = f := by
    ext x
    rfl
  rw [hef, LinearMap.det_toLin'] at hc
  let p : ↥(fundParaReps d D) → ((Fin d → ℤ) ⧸ N) :=
    fun u => Submodule.Quotient.mk u.val
  have hp : Function.Bijective p := by
    constructor
    · intro u v huv
      obtain ⟨y,hy⟩ := (Submodule.Quotient.eq N).mp huv
      change D *ᵥ y = u.val - v.val at hy
      obtain ⟨z,hz,huniq⟩ := fundParaReps_cosets_partition d D hD u.val
      have hu' := huniq (u.val, (0 : Fin d → ℤ)) ⟨u.property, by simp⟩
      have hv' := huniq (v.val,y) ⟨v.property, by rw [hy]; abel⟩
      exact Subtype.ext (congrArg Prod.fst (hu'.trans hv'.symm))
    · intro z
      obtain ⟨x,rfl⟩ := Submodule.Quotient.mk_surjective N z
      obtain ⟨⟨u,y⟩,⟨hu,hx⟩,huniq⟩ := fundParaReps_cosets_partition d D hD x
      refine ⟨⟨u,hu⟩, (Submodule.Quotient.eq N).2 ?_⟩
      refine ⟨-y, ?_⟩
      change D *ᵥ (-y) = u-x
      rw [hx, Matrix.mulVec_neg]
      abel
  have hcard : Nat.card ↥(fundParaReps d D) = D.det.natAbs :=
    (Nat.card_congr (Equiv.ofBijective p hp)).trans hc.symm
  have hn : Nat.card ↥(fundParaReps d D) ≠ 0 := by
    rw [hcard]
    exact Int.natAbs_ne_zero.mpr hD
  letI := Nat.finite_of_card_ne_zero hn
  exact ⟨Set.toFinite _, (Nat.card_coe_set_eq _).symm.trans hcard⟩

private lemma fund_cover_aux (d : ℕ) (D : Matrix (Fin d) (Fin d) ℤ)
    (hp : ∀ x, ∃! p : (Fin d → ℤ) × (Fin d → ℤ),
      p.1 ∈ fundParaReps d D ∧ x = p.1 + D *ᵥ p.2) :
    (Set.univ : Set (Fin d → ℤ)) =
        ⋃ u ∈ fundParaReps d D, pieceAffineImage u D (Set.univ : Set (Fin d → ℤ)) ∧
      ∀ u ∈ fundParaReps d D, ∀ u' ∈ fundParaReps d D, u ≠ u' →
        Disjoint (pieceAffineImage u D (Set.univ : Set (Fin d → ℤ)))
          (pieceAffineImage u' D (Set.univ : Set (Fin d → ℤ))) := by
  constructor
  · ext x
    constructor
    · intro _
      obtain ⟨⟨u,y⟩, ⟨hu, he⟩, _⟩ := hp x
      exact Set.mem_iUnion.mpr
        ⟨u, Set.mem_iUnion.mpr ⟨hu, y, Set.mem_univ _, he.symm⟩⟩
    · intro _
      trivial
  · intro u hu u' hu' hne
    apply Set.disjoint_left.mpr
    rintro x ⟨y, _, he⟩ ⟨y', _, he'⟩
    obtain ⟨p, hp', huniq⟩ := hp x
    have hh := (huniq (u,y) ⟨hu,he.symm⟩).trans
      (huniq (u',y') ⟨hu',he'.symm⟩).symm
    exact hne (congrArg Prod.fst hh)

private lemma fund_partition_aux (d : ℕ) (D : Matrix (Fin d) (Fin d) ℤ)
    (hD : D.det ≠ 0) (W : Finset ((Fin d → ℤ) × ℤ))
    (hp : ∀ x, ∃! p : (Fin d → ℤ) × (Fin d → ℤ),
      p.1 ∈ fundParaReps d D ∧ x = p.1 + D *ᵥ p.2) :
    (∀ u ∈ fundParaReps d D,
        pieceAffineImage u D (polyPZ d (shiftPullbackConstraints d D u W)) ⊆
          polyPZ d W) ∧
      (∀ u ∈ fundParaReps d D, ∀ u' ∈ fundParaReps d D, u ≠ u' →
        Disjoint (pieceAffineImage u D (polyPZ d (shiftPullbackConstraints d D u W)))
          (pieceAffineImage u' D (polyPZ d (shiftPullbackConstraints d D u' W)))) ∧
      polyPZ d W =
        ⋃ u ∈ fundParaReps d D,
          pieceAffineImage u D (polyPZ d (shiftPullbackConstraints d D u W)) ∧
      ∀ x ∈ polyPZ d W,
        ∃! p : (Fin d → ℤ) × (Fin d → ℤ),
          p.1 ∈ fundParaReps d D ∧
            p.2 ∈ polyPZ d (shiftPullbackConstraints d D p.1 W) ∧
            x = p.1 + D *ᵥ p.2 := by
  have hsub (u) :
      pieceAffineImage u D (polyPZ d (shiftPullbackConstraints d D u W)) ⊆
        polyPZ d W := by
    rw [← polyPZ_inter_coset d D hD]
    exact Set.inter_subset_left
  have hex (x) (hx : x ∈ polyPZ d W) :
      ∃! p : (Fin d → ℤ) × (Fin d → ℤ), p.1 ∈ fundParaReps d D ∧
        p.2 ∈ polyPZ d (shiftPullbackConstraints d D p.1 W) ∧
        x = p.1 + D *ᵥ p.2 := by
    obtain ⟨p, ⟨hu, he⟩, huniq⟩ := hp x
    refine ⟨p, ⟨hu, ?_, he⟩, ?_⟩
    · rw [polyPZ_shiftPullbackConstraints]
      change p.1 + D *ᵥ p.2 ∈ polyPZ d W
      rwa [← he]
    · intro p' hp'
      exact huniq p' ⟨hp'.1,hp'.2.2⟩
  refine ⟨fun u _ => hsub u, ?_, ?_, hex⟩
  · intro u hu u' hu' hne
    exact ((fund_cover_aux d D hp).2 u hu u' hu' hne).mono
      (Set.image_mono (Set.subset_univ _)) (Set.image_mono (Set.subset_univ _))
  · ext x
    constructor
    · intro hx
      obtain ⟨⟨u,y⟩, ⟨hu,hy,he⟩, _⟩ := hex x hx
      exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu,y,hy,he.symm⟩⟩
    · intro hx
      obtain ⟨u,hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hu,hx⟩ := Set.mem_iUnion.mp hx
      exact hsub u hx

theorem fundParaReps_cosets_cover (d : ℕ) (D : Matrix (Fin d) (Fin d) ℤ)
    (hD : D.det ≠ 0) :
    (Set.univ : Set (Fin d → ℤ)) =
        ⋃ u ∈ fundParaReps d D, pieceAffineImage u D (Set.univ : Set (Fin d → ℤ)) ∧
      ∀ u ∈ fundParaReps d D, ∀ u' ∈ fundParaReps d D, u ≠ u' →
        Disjoint (pieceAffineImage u D (Set.univ : Set (Fin d → ℤ)))
          (pieceAffineImage u' D (Set.univ : Set (Fin d → ℤ))) := by
  exact fund_cover_aux d D (fundParaReps_cosets_partition d D hD)

theorem polyPZ_partition_of_cosets (d : ℕ) (D : Matrix (Fin d) (Fin d) ℤ)
    (hD : D.det ≠ 0) (W : Finset ((Fin d → ℤ) × ℤ)) :
    (∀ u ∈ fundParaReps d D,
        pieceAffineImage u D (polyPZ d (shiftPullbackConstraints d D u W)) ⊆
          polyPZ d W) ∧
      (∀ u ∈ fundParaReps d D, ∀ u' ∈ fundParaReps d D, u ≠ u' →
        Disjoint (pieceAffineImage u D (polyPZ d (shiftPullbackConstraints d D u W)))
          (pieceAffineImage u' D (polyPZ d (shiftPullbackConstraints d D u' W)))) ∧
      polyPZ d W =
        ⋃ u ∈ fundParaReps d D,
          pieceAffineImage u D (polyPZ d (shiftPullbackConstraints d D u W)) ∧
      ∀ x ∈ polyPZ d W,
        ∃! p : (Fin d → ℤ) × (Fin d → ℤ),
          p.1 ∈ fundParaReps d D ∧
            p.2 ∈ polyPZ d (shiftPullbackConstraints d D p.1 W) ∧
            x = p.1 + D *ᵥ p.2 := by
  exact fund_partition_aux d D hD W (fundParaReps_cosets_partition d D hD)
open scoped Matrix

/-- An integer matrix viewed over `ℚ`. -/
def ratMat {d : ℕ} (D : Matrix (Fin d) (Fin d) ℤ) : Matrix (Fin d) (Fin d) ℚ :=
  D.map (fun z : ℤ => (z : ℚ))

/-- The diagonal quadratic form `Q(x) = ∑ⱼ γⱼ xⱼ²` over `ℚ`. -/
def quadFormQ (d : ℕ) (γ : Fin d → ℕ) (x : Fin d → ℚ) : ℚ :=
  ∑ j, (γ j : ℚ) * x j ^ 2

theorem shortCoord_newQuadForm (d : ℕ) (hd : 1 ≤ d) (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j)
    (a : Fin d → ℤ) (ha : ∀ j, a j ≠ 0) (s : ℕ) (hs : 1 ≤ s)
    (hdet : IsUnit (shortCoordMatrix d γ a).det)
    (D : Matrix (Fin d) (Fin d) ℤ)
    (hD : ratMat D = (s : ℚ) • (shortCoordMatrix d γ a)⁻¹) :
    (∀ j : Fin d,
        0 < shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a j)) ∧
      (∀ (y : Fin d → ℚ) (j : Fin d),
        (∑ i, shortCoordRow d γ a j i * (ratMat D *ᵥ y) i) = (s : ℚ) * y j) ∧
      (∀ y : Fin d → ℚ,
        quadFormQ d γ (ratMat D *ᵥ y) =
          ∑ j, (∑ i, shortCoordRow d γ a j i * (ratMat D *ᵥ y) i) ^ 2 /
            shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a j)) ∧
      (∀ y : Fin d → ℚ,
        quadFormQ d γ (ratMat D *ᵥ y) =
          (s : ℚ) ^ 2 *
            ∑ j, y j ^ 2 /
              shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a j)) ∧
      (∀ j : Fin d,
        quadFormQ d γ (ratMat D *ᵥ (Pi.single j 1 : Fin d → ℚ)) =
          (s : ℚ) ^ 2 /
            shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a j)) ∧
      (∀ j : Fin d, D *ᵥ (Pi.single j 1 : Fin d → ℤ) ≠ 0) ∧
      ∃ γ' : Fin d → ℕ,
        (∀ j, 1 ≤ γ' j) ∧
        (∀ j, (γ' j : ℚ) =
          (s : ℚ) ^ 2 /
            shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a j)) ∧
        (∀ j, (γ' j : ℚ) =
          quadFormQ d γ (ratMat D *ᵥ (Pi.single j 1 : Fin d → ℚ))) ∧
        (∀ j, (γ' j : ℤ) =
          ∑ i, (γ i : ℤ) * (D *ᵥ (Pi.single j 1 : Fin d → ℤ)) i ^ 2) ∧
        ∀ y : Fin d → ℚ, quadFormQ d γ (ratMat D *ᵥ y) = quadFormQ d γ' y := by
  classical
  have hg := shortCoord_gramSchmidt d hd γ hγ a ha
  have hpos := hg.2.2.2.2.1
  have hTD : shortCoordMatrix d γ a * ratMat D = (s : ℚ) • 1 := by
    rw [hD, Matrix.mul_smul, Matrix.mul_nonsing_inv _ hdet]
  have hrow (y : Fin d → ℚ) (j : Fin d) :
      (∑ i, shortCoordRow d γ a j i * (ratMat D *ᵥ y) i) = (s : ℚ) * y j := by
    change (shortCoordMatrix d γ a *ᵥ (ratMat D *ᵥ y)) j = _
    rw [Matrix.mulVec_mulVec, hTD, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  have hparse (y : Fin d → ℚ) :
      quadFormQ d γ (ratMat D *ᵥ y) =
        ∑ j, (∑ i, shortCoordRow d γ a j i * (ratMat D *ᵥ y) i)^2 /
          shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a j) :=
    hg.2.2.2.2.2.2.2.1 _
  have hdiag (y : Fin d → ℚ) : quadFormQ d γ (ratMat D *ᵥ y) =
      (s : ℚ)^2 * ∑ j, y j^2 /
        shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a j) := by
    rw [hparse, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hrow]
    ring
  have hb (j : Fin d) : quadFormQ d γ (ratMat D *ᵥ (Pi.single j 1)) =
      (s : ℚ)^2 / shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a j) := by
    rw [hdiag]
    simp [Pi.single_apply, ite_pow, zero_pow, div_eq_mul_inv]
  have hsp : (0 : ℚ) < s := by exact_mod_cast (show 0 < s by omega)
  let Z (j : Fin d) : ℤ :=
    ∑ i, (γ i : ℤ) * (D *ᵥ (Pi.single j 1 : Fin d → ℤ)) i ^ 2
  have hZ (j : Fin d) : (Z j : ℚ) =
      quadFormQ d γ (ratMat D *ᵥ (Pi.single j 1)) := by
    simp [Z, quadFormQ, ratMat, Int.cast_sum, Int.cast_mul, Int.cast_pow]
  have hZpos (j : Fin d) : 0 < Z j := by
    have hh : (0 : ℚ) < (Z j : ℚ) := by
      rw [hZ, hb]
      exact div_pos (sq_pos_of_pos hsp) (hpos j)
    exact_mod_cast hh
  have hcol (j : Fin d) : D *ᵥ (Pi.single j 1 : Fin d → ℤ) ≠ 0 := by
    intro hz
    have he : Z j = 0 := by
      dsimp only [Z]
      rw [hz]
      simp
    exact (hZpos j).ne' he
  have hcast (j : Fin d) : ((Z j).toNat : ℚ) = (Z j : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (hZpos j).le
  refine ⟨hpos, hrow, hparse, hdiag, hb, hcol, (fun j => (Z j).toNat),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    change 1 ≤ (Z j).toNat
    have := hZpos j
    omega
  · intro j
    exact (hcast j).trans ((hZ j).trans (hb j))
  · intro j
    exact (hcast j).trans (hZ j)
  · intro j
    exact Int.toNat_of_nonneg (hZpos j).le
  · intro y
    rw [hdiag, quadFormQ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    change _ = ((Z j).toNat : ℚ) * y j ^ 2
    rw [hcast, hZ, hb]
    ring
private lemma agent4_sc_complete23_tau_partial_oct13v2 (d : ℕ) (hd : 1 ≤ d)
    (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j)
    (a : Fin d → ℤ) (ha : a ⟨0, hd⟩ ≠ 0) (j : Fin d) :
    0 < shortCoordTau d γ a j := by
  have hg : (0 : ℚ) < γ ⟨0, hd⟩ := by
    exact_mod_cast (show 0 < γ ⟨0, hd⟩ by have := hγ ⟨0, hd⟩; omega)
  have haz : (a ⟨0, hd⟩ : ℚ) ≠ 0 := by exact_mod_cast ha
  exact (div_pos (sq_pos_of_ne_zero haz) hg).trans_le
    (Finset.single_le_sum (f := fun i : Fin d => (a i : ℚ)^2 / (γ i : ℚ))
      (fun i _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      (Finset.mem_Iic.mpr (show (⟨0, hd⟩ : Fin d) ≤ j by exact Nat.zero_le _)))

private lemma agent4_sc_complete23_row_partial_oct13v2 (d : ℕ) (hd : 1 ≤ d)
    (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j)
    (a : Fin d → ℤ) (ha : a ⟨0, hd⟩ ≠ 0) (j : Fin d) :
    shortCoordRow d γ a j ≠ 0 := by
  classical
  let z : Fin d := ⟨0, hd⟩
  have haz : (a z : ℚ) ≠ 0 := by exact_mod_cast ha
  intro he
  by_cases hj : j.val = 0
  · have hz := congrFun he z
    simp [shortCoordRow, hj, haz] at hz
  · by_cases haj : a j = 0
    · have hh := congrFun he j
      simp [shortCoordRow, hj, haj] at hh
    · have haj' : (a j : ℚ) ≠ 0 := by exact_mod_cast haj
      have hgj : (γ j : ℚ) ≠ 0 := by
        exact_mod_cast (show γ j ≠ 0 by have := hγ j; omega)
      have ht := (agent4_sc_complete23_tau_partial_oct13v2 d hd γ hγ a ha j).ne'
      have hzj : z ≠ j := by
        intro h
        have := congrArg Fin.val h
        simp [z] at this
        omega
      have hz := congrFun he z
      simp [shortCoordRow, hj, hzj, show z ≤ j from Nat.zero_le _,
        haj', hgj, ht, haz] at hz

private lemma agent4_sc_complete23_a_row_partial_oct13 (d : ℕ) (hd : 1 ≤ d)
    (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j)
    (a : Fin d → ℤ) (ha : a ⟨0, hd⟩ ≠ 0) (j : Fin d) (hj : j.val ≠ 0) :
    shortCoordInner d γ (fun i => (a i : ℚ)) (shortCoordRow d γ a j) = 0 := by
  rw [sc_inner_row_ok d γ a _ j hj]
  have he : (∑ i ∈ Finset.Iic j, (a i : ℚ) * (a i : ℚ) / (γ i : ℚ)) =
      shortCoordTau d γ a j := by simp only [shortCoordTau, pow_two]
  rw [he]
  have ht := (agent4_sc_complete23_tau_partial_oct13v2 d hd γ hγ a ha j).ne'
  have hg : (γ j : ℚ) ≠ 0 := by
    exact_mod_cast (show γ j ≠ 0 by have := hγ j; omega)
  field_simp [ht, hg]
  <;> ring

private lemma agent4_sc_complete23_ortho_partial_oct13 (d : ℕ) (hd : 1 ≤ d)
    (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j)
    (a : Fin d → ℤ) (ha : a ⟨0, hd⟩ ≠ 0) :
    ∀ j k, j ≠ k →
      shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a k) = 0 := by
  have hord (j k : Fin d) (hjk : j < k) :
      shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a k) = 0 := by
    have hk : k.val ≠ 0 := by have hh : j.val < k.val := hjk; omega
    by_cases hj : j.val = 0
    · simpa only [shortCoordRow, if_pos hj] using
        agent4_sc_complete23_a_row_partial_oct13 d hd γ hγ a ha k hk
    · rw [sc_inner_row_ok d γ a _ k hk, sc_support_ok d γ a j k hj hjk]
      have he : (∑ t ∈ Finset.Iic k,
          shortCoordRow d γ a j t * (a t : ℚ) / (γ t : ℚ)) =
          shortCoordInner d γ (shortCoordRow d γ a j) (fun t => (a t : ℚ)) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro t ht htk
        have hkt : k < t := lt_of_not_ge (by simpa only [Finset.mem_Iic] using htk)
        rw [sc_support_ok d γ a j t hj (hjk.trans hkt)]
        simp
      rw [he, sc2026_symm, agent4_sc_complete23_a_row_partial_oct13 d hd γ hγ a ha j hj]
      simp
  intro j k hjk
  rcases lt_or_gt_of_ne hjk with h | h
  · exact hord j k h
  · rw [sc2026_symm]
    exact hord k j h

private lemma agent4_sc_complete23_frame_partial_oct13 (d : ℕ) (hd : 1 ≤ d)
    (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j)
    (a : Fin d → ℤ) (ha : a ⟨0, hd⟩ ≠ 0) :
    (shortCoordMatrix d γ a).det ≠ 0 ∧
      (∀ j : Fin d, a j = 0 → ∀ i,
        shortCoordMatrix d γ a j i = if i = j then 1 else 0) ∧
      ∀ x : Fin d → ℚ,
        (∑ j, (γ j : ℚ) * x j ^ 2) =
          ∑ j, (∑ i, shortCoordRow d γ a j i * x i) ^ 2 /
            shortCoordInner d γ (shortCoordRow d γ a j) (shortCoordRow d γ a j) := by
  have hrow := agent4_sc_complete23_row_partial_oct13v2 d hd γ hγ a ha
  have ho := agent4_sc_complete23_ortho_partial_oct13 d hd γ hγ a ha
  refine ⟨?_, ?_, fun x => (shortCoord_parseval d γ hγ _ hrow ho x).2.2.2.2⟩
  · have hli : LinearIndependent ℚ (shortCoordMatrix d γ a).row :=
      sc2026_li d γ hγ (shortCoordRow d γ a) hrow ho
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hli)).ne_zero
  · intro j hj i
    have hj0 : j.val ≠ 0 := by
      intro he
      have hz : j = ⟨0, hd⟩ := Fin.ext he
      exact ha (hz ▸ hj)
    simp [shortCoordMatrix, shortCoordRow, hj0, hj]

private lemma agent4_sc_complete23_unused_column_oct13 (d : ℕ) (hd : 1 ≤ d)
    (γ : Fin d → ℕ) (a : Fin d → ℤ) (ha : a ⟨0, hd⟩ ≠ 0)
    (j : Fin d) (hj : a j = 0) (i : Fin d) :
    shortCoordMatrix d γ a i j = if i = j then 1 else 0 := by
  classical
  have hj0 : j.val ≠ 0 := by
    intro he
    have hz : j = ⟨0, hd⟩ := Fin.ext he
    exact ha (hz ▸ hj)
  by_cases hi : i.val = 0
  · have hij : i ≠ j := by intro he; exact hj0 (he ▸ hi)
    simp [shortCoordMatrix, shortCoordRow, hi, hj, hij]
  · simp [shortCoordMatrix, shortCoordRow, hi, hj, eq_comm]

private lemma agent4_sc_complete23_inverse_unused_oct13v5 {d : ℕ}
    (T : Matrix (Fin d) (Fin d) ℚ) (hT : T.det ≠ 0) (j : Fin d)
    (hr : ∀ i, T j i = if i = j then 1 else 0)
    (hc : ∀ i, T i j = if i = j then 1 else 0) :
    (∀ i, T⁻¹ j i = if i = j then 1 else 0) ∧
      (∀ i, T⁻¹ i j = if i = j then 1 else 0) := by
  classical
  have hu : IsUnit T.det := isUnit_iff_ne_zero.mpr hT
  constructor
  · intro i
    have he := congrArg (fun A : Matrix (Fin d) (Fin d) ℚ => A j i)
      (Matrix.mul_nonsing_inv T hu)
    simpa [Matrix.mul_apply, hr, Matrix.one_apply, eq_comm] using he
  · intro i
    have he := congrArg (fun A : Matrix (Fin d) (Fin d) ℚ => A i j)
      (Matrix.nonsing_inv_mul T hu)
    simpa [Matrix.mul_apply, hc, Matrix.one_apply] using he

private lemma agent4_sc_complete23_support_scaling_oct13v7 {d : ℕ}
    (R : ℕ) (T : Matrix (Fin d) (Fin d) ℚ) (hT : T.det ≠ 0)
    (S : Finset (Fin d))
    (hr : ∀ j ∉ S, ∀ i, T j i = if i = j then 1 else 0)
    (hc : ∀ j ∉ S, ∀ i, T i j = if i = j then 1 else 0) :
    ∃ (s : ℕ) (D : Matrix (Fin d) (Fin d) ℤ), R < s ∧ D.det ≠ 0 ∧
      (∀ j ∉ S, ∀ i, D j i = if i = j then 1 else 0) ∧
      (∀ j ∉ S, ∀ i, D i j = if i = j then 1 else 0) ∧
      T * ratMat D = Matrix.diagonal (fun j => if j ∈ S then (s : ℚ) else 1) := by
  classical
  obtain ⟨s₀, hs₀, ⟨D₀, hD₀⟩, _⟩ := exists_least_integralScaling d T hT
  let s := (R + 1) * s₀
  let A : Matrix (Fin d) (Fin d) ℤ := fun i j => (R + 1 : ℕ) * D₀ i j
  let D : Matrix (Fin d) (Fin d) ℤ := fun i j =>
    if j ∈ S then A i j else if i = j then 1 else 0
  have hs : R < s := by dsimp [s]; nlinarith
  have hA : ratMat A = (s : ℚ) • T⁻¹ := by
    ext i j
    have hh := congrArg (fun M : Matrix (Fin d) (Fin d) ℚ => M i j) hD₀
    change (D₀ i j : ℚ) = (s₀ : ℚ) * T⁻¹ i j at hh
    change (((((R + 1 : ℕ) : ℤ) * D₀ i j) : ℤ) : ℚ) =
      (s : ℚ) * T⁻¹ i j
    push_cast
    rw [hh]
    simp only [s, Nat.cast_mul]
    push_cast
    ring
  have hTA : T * ratMat A = (s : ℚ) • 1 := by
    rw [hA, Matrix.mul_smul, Matrix.mul_nonsing_inv T (isUnit_iff_ne_zero.mpr hT)]
  have hTD : T * ratMat D =
      Matrix.diagonal (fun j => if j ∈ S then (s : ℚ) else 1) := by
    ext i j
    change (∑ k, T i k * (D k j : ℚ)) =
      (if i = j then (if i ∈ S then (s : ℚ) else 1) else 0)
    by_cases hj : j ∈ S
    · have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℚ => M i j) hTA
      change (∑ k, T i k * (A k j : ℚ)) =
        (s : ℚ) * (if i = j then 1 else 0) at he
      simp only [D, hj, ite_true]
      by_cases hij : i = j
      · subst i
        simpa [hj] using he
      · simpa [hij] using he
    · simp only [D, hj, ite_false]
      by_cases hij : i = j
      · subst i
        simp [hj, hc j hj]
      · simp [hij, hc j hj]
  have hrow (j : Fin d) (hj : j ∉ S) (i : Fin d) :
      D j i = if i = j then 1 else 0 := by
    by_cases hi : i ∈ S
    · have hij : i ≠ j := by intro he; exact hj (he ▸ hi)
      have hInv := (agent4_sc_complete23_inverse_unused_oct13v5 T hT j (hr j hj) (hc j hj)).1 i
      have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℚ => M j i) hA
      change (A j i : ℚ) = (s : ℚ) * T⁻¹ j i at he
      rw [hInv, if_neg hij, mul_zero] at he
      have haz : A j i = 0 := by exact_mod_cast he
      simp [D, hi, hij, haz]
    · simp [D, hi, eq_comm]
  have hd : D.det ≠ 0 := by
    have hdiag : (Matrix.diagonal (fun j => if j ∈ S then (s : ℚ) else 1)).det ≠ 0 := by
      rw [Matrix.det_diagonal]
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      split_ifs
      · exact_mod_cast (show s ≠ 0 by omega)
      · norm_num
    rw [← hTD, Matrix.det_mul] at hdiag
    have hrat : (ratMat D).det ≠ 0 := (mul_ne_zero_iff.mp hdiag).2
    intro hz
    apply hrat
    simpa only [ratMat, ← Int.cast_det, hz, Int.cast_zero]
  exact ⟨s, D, hs, hd, hrow, fun j hj i => by simp [D, hj], hTD⟩

private lemma agent4_sc_complete23_integral_diagonal_oct13v10 {d : ℕ}
    (gamma : Fin d → ℕ) (hg : ∀ j, 1 ≤ gamma j)
    (T : Matrix (Fin d) (Fin d) ℚ) (c : Fin d → ℚ)
    (hc : ∀ j, 0 < c j)
    (hform : ∀ x : Fin d → ℚ,
      quadFormQ d gamma x = ∑ j, c j * (T *ᵥ x) j ^ 2)
    (D : Matrix (Fin d) (Fin d) ℤ) (b : Fin d → ℚ)
    (hb : ∀ j, b j ≠ 0)
    (hTD : T * ratMat D = Matrix.diagonal b) :
    ∃ gamma' : Fin d → ℕ, (∀ j, 1 ≤ gamma' j) ∧
      (∀ j, (gamma' j : ℚ) = c j * b j ^ 2) ∧
      (∀ y : Fin d → ℤ,
        (∑ j, (gamma' j : ℤ) * y j ^ 2) =
          ∑ j, (gamma j : ℤ) * (D *ᵥ y) j ^ 2) := by
  classical
  have hdiag (y : Fin d → ℚ) :
      quadFormQ d gamma (ratMat D *ᵥ y) = ∑ j, (c j * b j^2) * y j^2 := by
    rw [hform]
    simp only [Matrix.mulVec_mulVec, hTD, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  let Z (j : Fin d) : ℤ := ∑ i, (gamma i : ℤ) * D i j ^ 2
  have hZ (j : Fin d) : (Z j : ℚ) = c j * b j^2 := by
    have he := hdiag (Pi.single j 1)
    simpa [quadFormQ, ratMat, Z, Matrix.mulVec_single,
      Pi.single_apply, ite_pow, mul_ite] using he
  have hpos (j : Fin d) : 0 < Z j := by
    have hh : (0 : ℚ) < (Z j : ℚ) := by
      rw [hZ]
      exact mul_pos (hc j) (sq_pos_of_ne_zero (hb j))
    exact_mod_cast hh
  have hcast (j : Fin d) : ((Z j).toNat : ℚ) = (Z j : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (hpos j).le
  refine ⟨fun j => (Z j).toNat, fun j => by change 1 ≤ (Z j).toNat; have := hpos j; omega,
    fun j => (hcast j).trans (hZ j), ?_⟩
  intro y
  have he := hdiag (fun j => (y j : ℚ))
  have hmul (j : Fin d) : (ratMat D *ᵥ (fun i => (y i : ℚ))) j =
      ((D *ᵥ y) j : ℚ) := by
    simp [ratMat, Matrix.mulVec, dotProduct]
  simp only [quadFormQ, hmul] at he
  have he' : (∑ j, ((Z j).toNat : ℚ) * (y j : ℚ)^2) =
      ∑ j, (gamma j : ℚ) * (((D *ᵥ y) j : ℤ) : ℚ)^2 := by
    simp_rw [hcast, hZ]
    exact he.symm
  exact_mod_cast he'

private lemma agent4_sc_complete23_order_oct13v12 {d : ℕ} (hd : 1 ≤ d)
    (side : Fin d → ℕ) (a : Fin d → ℤ) (qc : Fin d)
    (hmax : ∀ j ∈ vecSupport a, side j ≤ side qc) :
    ∃ e : Fin d ≃ Fin d,
      e ⟨0, hd⟩ = qc ∧
      ∀ i j : Fin d, i ≤ j → e j ∈ vecSupport a →
        side (e j) ≤ side (e i) := by
  classical
  letI : NeZero d := ⟨by omega⟩
  let key : Fin d → ℕ ×ₗ OrderDual ℕ :=
    fun j => toLex (if j = qc then 0 else 1, OrderDual.toDual (side j))
  let e := Tuple.sort key
  have hmono := Tuple.monotone_sort key
  have hezero : e ⟨0, hd⟩ = qc := by
    have hz := hmono (show (⟨0, hd⟩ : Fin d) ≤ e.symm qc from Fin.zero_le _)
    change key (e ⟨0, hd⟩) ≤ key (e (e.symm qc)) at hz
    rw [e.apply_symm_apply] at hz
    by_contra hn
    simp [key, Prod.Lex.toLex_le_toLex] at hz
    apply hn
    have h0 : (⟨0, hd⟩ : Fin d) = 0 := Fin.ext rfl
    rw [h0]
    exact hz.1
  refine ⟨e, hezero, ?_⟩
  intro i j hij hj
  by_cases hi : i = ⟨0, hd⟩
  · subst i
    rw [hezero]
    exact hmax _ hj
  · have hnei : e i ≠ qc := by
      intro h
      exact hi (e.injective (h.trans hezero.symm))
    have hnej : e j ≠ qc := by
      intro h
      have hjzero : j = ⟨0, hd⟩ := e.injective (h.trans hezero.symm)
      subst j
      apply hi
      exact le_antisymm hij (Fin.zero_le _)
    have hz := hmono hij
    change key (e i) ≤ key (e j) at hz
    simpa [key, hnei, hnej, Prod.Lex.toLex_le_toLex,
      OrderDual.toDual_le_toDual] using hz

private lemma agent4_sc_complete23_pullback_rho_v3 {d R : ℕ}
    (W : Finset ((Fin d → ℤ) × ℤ)) (hW : constraintRho d W ≤ R)
    (D : Matrix (Fin d) (Fin d) ℤ) (u : Fin d → ℤ) :
    constraintRho d (shiftPullbackConstraints d D u W) ≤
      max R (d * transitionSize D * R) := by
  classical
  apply (constraintRho_le_iff _ _ _).2
  refine ⟨?_, ?_⟩
  · exact Finset.card_image_le.trans
      (((card_le_constraintRho d W).trans hW).trans (le_max_left _ _))
  · intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    have hnorm := (matInftyNorm_le_iff D (transitionSize D)).1 le_rfl
    have hl1 : (∑ i, |w.1 i|) ≤ (R : ℤ) :=
      (l1_le_constraintRho d W w hw).trans (by exact_mod_cast hW)
    have hcoord (j : Fin d) : |(Dᵀ *ᵥ w.1) j| ≤
        (transitionSize D : ℤ) * (R : ℤ) := by
      change |∑ i, D i j * w.1 i| ≤ _
      calc
        _ ≤ ∑ i, |D i j * w.1 i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, (transitionSize D : ℤ) * |w.1 i| :=
          Finset.sum_le_sum (fun i _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hnorm i j) (abs_nonneg _))
        _ = (transitionSize D : ℤ) * ∑ i, |w.1 i| :=
          (Finset.mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hl1 (by positivity)
    apply (Finset.sum_le_sum (fun j _ => hcoord j)).trans
    have hbound : (d * transitionSize D * R : ℤ) ≤
        (max R (d * transitionSize D * R) : ℕ) := by
      exact_mod_cast le_max_right R (d * transitionSize D * R)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_mul, mul_assoc] using hbound

private lemma agent4_sc_complete23_coset_decomposition_v3 {d R G : ℕ}
    (p : Piece d) (hp : p.A ≤ R)
    (D : Matrix (Fin d) (Fin d) ℤ) (hD : D.det ≠ 0)
    (gamma : Fin d → ℕ) (hg1 : ∀ j, 1 ≤ gamma j) (hgG : ∀ j, gamma j ≤ G)
    (hquad : ∀ y : Fin d → ℤ,
      (∑ j, (gamma j : ℤ) * y j ^ 2) = p.quad (D *ᵥ y))
    (lo hi : ↥(fundParaReps d D) → Fin d → ℤ)
    (hbox : ∀ u : ↥(fundParaReps d D),
      polyPZ d (shiftPullbackConstraints d D u.val p.W) ⊆
        (boxZ d (lo u) (hi u) : Set (Fin d → ℤ))) :
    ∃ (M : ℕ) (U : Fin M → Fin d → ℤ) (q : Fin M → Piece d),
      M = D.det.natAbs ∧ IsDecomposition p q U (fun _ => D) ∧
      Function.Injective U ∧
      (∀ m, (q m).A = max R (d * transitionSize D * R) + d + G + 1) ∧
      (∀ m, (q m).gamma = gamma) ∧
      ∀ m, ∃ u : ↥(fundParaReps d D), U m = u.val ∧
        (q m).lo = lo u ∧ (q m).hi = hi u := by
  classical
  have hfinite := (fundParaReps_finite_ncard d D hD).1
  letI : Fintype ↥(fundParaReps d D) := hfinite.fintype
  let M := Fintype.card ↥(fundParaReps d D)
  let e : Fin M ≃ ↥(fundParaReps d D) := (Fintype.equivFin _).symm
  let U : Fin M → Fin d → ℤ := fun m => (e m).val
  let C := max R (d * transitionSize D * R) + d + G + 1
  have hrho (m : Fin M) :
      constraintRho d (shiftPullbackConstraints d D (U m) p.W) ≤ C := by
    exact (agent4_sc_complete23_pullback_rho_v3 p.W (p.rho_le_A.trans hp) D (U m)).trans
      (by dsimp [C]; omega)
  let q : Fin M → Piece d := fun m =>
    { W := shiftPullbackConstraints d D (U m) p.W
      lo := lo (e m)
      hi := hi (e m)
      gamma := gamma
      A := C
      one_le_dim := p.one_le_dim
      one_le_gamma := hg1
      one_le_A := by dsimp [C]; omega
      poly_subset_box := hbox (e m)
      dim_le_A := by dsimp [C]; omega
      rho_le_A := hrho m
      gamma_le_A := fun j => (hgG j).trans (by dsimp [C]; omega) }
  have htrans (m : Fin M) : IsTransition p (q m) (U m) D := by
    refine ⟨hD, ?_, hquad⟩
    rintro x ⟨y, hy, rfl⟩
    change y ∈ polyPZ d (shiftPullbackConstraints d D (U m) p.W) at hy
    rw [polyPZ_shiftPullbackConstraints] at hy
    exact hy
  refine ⟨M, U, q, ?_, ?_, fun m m' h => e.injective (Subtype.ext h),
    fun _ => rfl, fun _ => rfl, ?_⟩
  · change Fintype.card ↥(fundParaReps d D) = _
    rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]
    exact (fundParaReps_finite_ncard d D hD).2
  · apply (isDecomposition_iff p q U (fun _ => D)).2
    refine ⟨htrans, ?_⟩
    intro x
    constructor
    · intro hx
      obtain ⟨⟨u, y⟩, ⟨hu, hy, hxy⟩, huniq⟩ :=
        (polyPZ_partition_of_cosets d D hD p.W).2.2.2 x hx
      let m : Fin M := e.symm ⟨u, hu⟩
      have hem : e m = ⟨u, hu⟩ := e.apply_symm_apply _
      have hUm : U m = u := congrArg Subtype.val hem
      refine ⟨m, ?_, ?_⟩
      · refine ⟨y, ?_, ?_⟩
        · change y ∈ polyPZ d (shiftPullbackConstraints d D (U m) p.W)
          rwa [hUm]
        · rw [hUm]
          exact hxy.symm
      · intro m' hm'
        obtain ⟨y', hy', hxy'⟩ := hm'
        have heq := huniq (U m', y')
          ⟨(e m').property, hy', hxy'.symm⟩
        have hu' : U m' = u := congrArg Prod.fst heq
        apply e.injective
        apply Subtype.ext
        exact hu'.trans hUm.symm
    · rintro ⟨m, hm, _⟩
      exact (htrans m).image_subset hm
  · intro m
    exact ⟨e m, rfl, rfl, rfl⟩

private lemma agent4_sc_complete23_rep_zero_v3 {d : ℕ}
    (D : Matrix (Fin d) (Fin d) ℤ) (j : Fin d)
    (hrow : ∀ i, D j i = if i = j then 1 else 0)
    (u : Fin d → ℤ) (hu : u ∈ fundParaReps d D) : u j = 0 := by
  classical
  obtain ⟨t, ht, he⟩ := hu
  have hej : (u j : ℚ) = t j := by
    rw [he j]
    simp [hrow]
  have hlow : (0 : ℤ) ≤ u j := by
    exact_mod_cast (hej.symm ▸ (ht j).1)
  have hhigh : u j < (1 : ℤ) := by
    exact_mod_cast (hej.symm ▸ (ht j).2)
  omega

private lemma agent4_sc_complete23_interval_20261013v3 (S : Set ℤ) (hS : S.Finite)
    (N : ℕ) (_hN : 1 ≤ N)
    (hvar : ∀ x ∈ S, ∀ y ∈ S, |x - y| < (N : ℤ)) :
    ∃ lo hi : ℤ, (Finset.Icc lo hi).card = N ∧
      S ⊆ (Finset.Icc lo hi : Set ℤ) := by
  classical
  obtain ⟨z, hz⟩ : ∃ z : ℤ, ∀ x ∈ S, z ≤ x ∧ x ≤ z + (N : ℤ) - 1 := by
    by_cases hn : S.Nonempty
    · obtain ⟨z, hzm, hmin⟩ := Set.exists_min_image S id hS hn
      refine ⟨z, ?_⟩
      intro x hx
      have hu := (abs_lt.mp (hvar x hx z hzm)).2
      exact ⟨hmin x hx, by omega⟩
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hn ⟨x, hx⟩)
  refine ⟨z, z + (N : ℤ) - 1, ?_, ?_⟩
  · rw [Int.card_Icc]
    have he : z + (N : ℤ) - 1 + 1 - z = (N : ℤ) := by omega
    rw [he, Int.toNat_natCast]
  · intro x hx
    exact Finset.mem_Icc.mpr (hz x hx)

private lemma agent4_sc_complete23_pullback_finite_20261013v3 {d : ℕ} (p : Piece d)
    (D : Matrix (Fin d) (Fin d) ℤ) (hD : D.det ≠ 0) (u : Fin d → ℤ) :
    (polyPZ d (shiftPullbackConstraints d D u p.W)).Finite := by
  rw [polyPZ_shiftPullbackConstraints]
  exact ((boxZ d p.lo p.hi).finite_toSet.subset p.poly_subset_box).preimage
    (mulVec_add_left_injective d D hD u).injOn

private lemma agent4_sc_complete23_enclosing_box_20261013v3 {d : ℕ}
    (S : Set (Fin d → ℤ)) (hS : S.Finite)
    (T : Finset (Fin d)) (lo hi : Fin d → ℤ) (N : Fin d → ℕ)
    (hN : ∀ j ∈ T, 1 ≤ N j)
    (hvar : ∀ j ∈ T, ∀ x ∈ S, ∀ y ∈ S, |x j - y j| < (N j : ℤ))
    (hout : ∀ j ∉ T, ∀ x ∈ S, lo j ≤ x j ∧ x j ≤ hi j) :
    ∃ lo' hi' : Fin d → ℤ,
      S ⊆ (boxZ d lo' hi' : Set (Fin d → ℤ)) ∧
      (∀ j ∈ T, boxSide d lo' hi' j = N j) ∧
      ∀ j ∉ T, lo' j = lo j ∧ hi' j = hi j := by
  classical
  have hex (j : Fin d) (hj : j ∈ T) :
      ∃ l h : ℤ, (Finset.Icc l h).card = N j ∧
        (fun x : Fin d → ℤ => x j) '' S ⊆ (Finset.Icc l h : Set ℤ) := by
    apply agent4_sc_complete23_interval_20261013v3 _ (hS.image _) _ (hN j hj)
    rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩
    exact hvar j hj x hx y hy
  let l (j : Fin d) : ℤ := if hj : j ∈ T then Classical.choose (hex j hj) else lo j
  let h (j : Fin d) : ℤ := if hj : j ∈ T then
    Classical.choose (Classical.choose_spec (hex j hj)) else hi j
  refine ⟨l, h, ?_, ?_, ?_⟩
  · intro x hx
    apply Fintype.mem_piFinset.mpr
    intro j
    by_cases hj : j ∈ T
    · have hh := (Classical.choose_spec (Classical.choose_spec (hex j hj))).2
      simpa only [l, h, dite_eq_left hj] using
        (show x j ∈ Finset.Icc (Classical.choose (hex j hj))
          (Classical.choose (Classical.choose_spec (hex j hj))) from hh ⟨x, hx, rfl⟩)
    · simpa only [l, h, dite_eq_right hj] using Finset.mem_Icc.mpr (hout j hj x hx)
  · intro j hj
    exact (by simpa only [boxSide, l, h, dite_eq_left hj] using
      (Classical.choose_spec (Classical.choose_spec (hex j hj))).1)
  · intro j hj
    simp only [l, h, dite_eq_right hj, and_self]

private lemma agent4_sc_complete23_assemble_geometry_v4 {d R G H : ℕ}
    (p : Piece d) (hp : p.A ≤ R) (hH : 1 ≤ H) (hHJ : H ≤ p.minSide)
    (a : Fin d → ℤ) (qc : Fin d) (hqc : qc ∈ vecSupport a)
    (D : Matrix (Fin d) (Fin d) ℤ) (hD : D.det ≠ 0)
    (gamma : Fin d → ℕ) (hg1 : ∀ j, 1 ≤ gamma j) (hgG : ∀ j, gamma j ≤ G)
    (hquad : ∀ y : Fin d → ℤ,
      (∑ j, (gamma j : ℤ) * y j ^ 2) = p.quad (D *ᵥ y))
    (hrow : ∀ j ∉ vecSupport a, ∀ i, D j i = if i = j then 1 else 0)
    (hvar : ∀ u : ↥(fundParaReps d D), ∀ j ∈ vecSupport a,
      ∀ y ∈ polyPZ d (shiftPullbackConstraints d D u.val p.W),
      ∀ z ∈ polyPZ d (shiftPullbackConstraints d D u.val p.W),
      |y j - z j| < ((if j = qc then H else 3 * p.side j : ℕ) : ℤ)) :
    ∃ (M : ℕ) (U : Fin M → Fin d → ℤ) (q : Fin M → Piece d),
      M = D.det.natAbs ∧ IsDecomposition p q U (fun _ => D) ∧
      Function.Injective U ∧
      (∀ m, (q m).A = max R (d * transitionSize D * R) + d + G + 1) ∧
      (∀ m m', (q m).gamma = (q m').gamma) ∧
      (∀ m, (q m).side qc = H) ∧
      (∀ (m : Fin M) (j : Fin d), j ≠ qc →
        p.side j ≤ (q m).side j ∧ (q m).side j ≤ 3 * p.side j) ∧
      ∀ (m : Fin M) (j : Fin d), j ∉ vecSupport a →
        (q m).lo j = p.lo j ∧ (q m).hi j = p.hi j := by
  classical
  let N : Fin d → ℕ := fun j => if j = qc then H else 3 * p.side j
  have hside (j : Fin d) : 1 ≤ p.side j := by
    have hmin : p.minSide ≤ p.side j := Finset.inf'_le p.side (Finset.mem_univ j)
    omega
  have hboxes (u : ↥(fundParaReps d D)) :
      ∃ lo hi : Fin d → ℤ,
        polyPZ d (shiftPullbackConstraints d D u.val p.W) ⊆
          (boxZ d lo hi : Set (Fin d → ℤ)) ∧
        (∀ j ∈ vecSupport a, boxSide d lo hi j = N j) ∧
        ∀ j ∉ vecSupport a, lo j = p.lo j ∧ hi j = p.hi j := by
    apply agent4_sc_complete23_enclosing_box_20261013v3 _
      (agent4_sc_complete23_pullback_finite_20261013v3 p D hD u.val)
      (vecSupport a) p.lo p.hi N
    · intro j hj
      dsimp [N]
      split_ifs <;> have := hside j <;> omega
    · exact hvar u
    · intro j hj y hy
      rw [polyPZ_shiftPullbackConstraints] at hy
      have hybox := p.poly_subset_box hy
      have hu : u.val j = 0 :=
        agent4_sc_complete23_rep_zero_v3 D j (hrow j hj) u.val u.property
      have hm : (D *ᵥ y) j = y j := by
        simp [Matrix.mulVec, dotProduct, hrow j hj]
      have hh := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hybox j)
      simpa only [Pi.add_apply, hu, hm, zero_add] using hh
  choose lo hi hbox hlength hout using hboxes
  obtain ⟨M, U, q, hM, hdecomp, hinj, hA, hgamma, hends⟩ :=
    agent4_sc_complete23_coset_decomposition_v3 p hp D hD gamma hg1 hgG hquad lo hi hbox
  have hs (m : Fin M) (j : Fin d) (hj : j ∈ vecSupport a) : (q m).side j = N j := by
    obtain ⟨u, hU, hl, hh⟩ := hends m
    simpa only [Piece.side, hl, hh] using hlength u j hj
  have ho (m : Fin M) (j : Fin d) (hj : j ∉ vecSupport a) :
      (q m).lo j = p.lo j ∧ (q m).hi j = p.hi j := by
    obtain ⟨u, hU, hl, hh⟩ := hends m
    rw [hl, hh]
    exact hout u j hj
  refine ⟨M, U, q, hM, hdecomp, hinj, hA,
    fun m m' => (hgamma m).trans (hgamma m').symm, ?_, ?_, ho⟩
  · intro m
    simpa [N] using hs m qc hqc
  · intro m j hj
    by_cases hja : j ∈ vecSupport a
    · rw [hs m j hja]
      simp only [N, if_neg hj]
      omega
    · obtain ⟨hl, hh⟩ := ho m j hja
      have he : (q m).side j = p.side j := by simp only [Piece.side, boxSide, hl, hh]
      rw [he]
      omega

private lemma agent4_sc_complete23_supported_tail_oct13v13 (d R : ℕ) (a : Fin d → ℤ)
    (haR : ∑ i, |a i| ≤ (R : ℤ)) (lo hi : Fin d → ℤ)
    (hside : ∀ i j : Fin d, i ≤ j → a j ≠ 0 →
      boxSide d lo hi j ≤ boxSide d lo hi i)
    (x y : Fin d → ℤ) (hx : x ∈ boxZ d lo hi) (hy : y ∈ boxZ d lo hi)
    (j : Fin d) :
    |(∑ i ∈ Finset.univ.filter (fun i : Fin d => j < i), (a i : ℚ)*(x i : ℚ)) -
      ∑ i ∈ Finset.univ.filter (fun i : Fin d => j < i), (a i : ℚ)*(y i : ℚ)| ≤
      (R : ℚ) * (boxSide d lo hi j : ℚ) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin d => j < i),
        |(a i : ℚ)*((x i : ℚ)-(y i : ℚ))| := by
      simp only [← mul_sub]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin d => j < i),
        |(a i : ℚ)| * (boxSide d lo hi j : ℚ) := by
      apply Finset.sum_le_sum
      intro i hi'
      by_cases hai : a i = 0
      · simp [hai]
      · rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (scv_final_coord d lo hi x y hx hy i).trans
          (by exact_mod_cast hside j i (Finset.mem_filter.mp hi').2.le hai)
    _ = (∑ i ∈ Finset.univ.filter (fun i : Fin d => j < i), |(a i : ℚ)|) *
        (boxSide d lo hi j : ℚ) := (Finset.sum_mul _ _ _).symm
    _ ≤ (R : ℚ) * (boxSide d lo hi j : ℚ) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by intros; positivity)).trans
      exact_mod_cast haR

private lemma agent4_sc_complete23_supported_coefficient_oct13v14 (d : ℕ)
    (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j) (a : Fin d → ℤ)
    (j : Fin d) (haj : a j ≠ 0) :
    |(a j : ℚ)| / ((γ j : ℚ) * shortCoordTau d γ a j) ≤ 1 := by
  have hg : (0 : ℚ) < γ j := by
    exact_mod_cast (show 0 < γ j by have := hγ j; omega)
  have hs : (a j : ℚ)^2 / (γ j : ℚ) ≤ shortCoordTau d γ a j := by
    unfold shortCoordTau
    exact Finset.single_le_sum
      (f := fun i : Fin d => (a i : ℚ)^2 / (γ i : ℚ))
      (fun i _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      (Finset.mem_Iic.mpr le_rfl)
  have ha0 : (a j : ℚ) ≠ 0 := by exact_mod_cast haj
  have ht : 0 < shortCoordTau d γ a j :=
    (div_pos (sq_pos_of_ne_zero ha0) hg).trans_le hs
  have hs' := (div_le_iff₀ hg).mp hs
  have ha1 : (1 : ℚ) ≤ |(a j : ℚ)| := by
    have hh : (1 : ℤ) ≤ |a j| := by have := abs_pos.mpr haj; omega
    exact_mod_cast hh
  apply (div_le_one (mul_pos hg ht)).2
  nlinarith [sq_abs (a j : ℚ)]

private lemma agent4_sc_complete23_supported_variation_oct13v14
    (d : ℕ) (R : ℕ) (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j)
    (a : Fin d → ℤ) (haR : ∑ j, |a j| ≤ (R : ℤ))
    (lo hi : Fin d → ℤ)
    (hside : ∀ i j : Fin d, i ≤ j → a j ≠ 0 →
      boxSide d lo hi j ≤ boxSide d lo hi i)
    (H : ℕ) (hHJ : ∀ j, H ≤ boxSide d lo hi j)
    (x y : Fin d → ℤ) (hx : x ∈ boxZ d lo hi) (hy : y ∈ boxZ d lo hi)
    (hvar : |∑ i, (a i : ℚ) * ((x i : ℚ) - (y i : ℚ))| ≤
      (R : ℚ) * (H : ℚ))
    (j : Fin d) (hj : j.val ≠ 0) (haj : a j ≠ 0) :
    |(∑ i, shortCoordRow d γ a j i * (x i : ℚ)) -
      ∑ i, shortCoordRow d γ a j i * (y i : ℚ)| ≤
      (2 * (R : ℚ) + 1) * (boxSide d lo hi j : ℚ) := by
  classical
  let c : ℚ := (a j : ℚ) / ((γ j : ℚ) * shortCoordTau d γ a j)
  have hc : |c| ≤ 1 := by
    dsimp [c]
    have hg : (0 : ℚ) < γ j := by
      exact_mod_cast (show 0 < γ j by have := hγ j; omega)
    have ha0 : (a j : ℚ) ≠ 0 := by exact_mod_cast haj
    have ht : 0 < shortCoordTau d γ a j := by
      apply (div_pos (sq_pos_of_ne_zero ha0) hg).trans_le
      unfold shortCoordTau
      exact Finset.single_le_sum
        (f := fun i : Fin d => (a i : ℚ)^2 / (γ i : ℚ))
        (fun i _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
        (Finset.mem_Iic.mpr le_rfl)
    rw [abs_div, abs_of_pos (mul_pos hg ht)]
    exact agent4_sc_complete23_supported_coefficient_oct13v14 d γ hγ a j haj
  have hb := scv_final_coord d lo hi x y hx hy j
  have ht := agent4_sc_complete23_supported_tail_oct13v13 d R a haR lo hi hside x y hx hy j
  have hv : |(∑ i, (a i : ℚ)*(x i : ℚ)) -
      ∑ i, (a i : ℚ)*(y i : ℚ)| ≤ (R : ℚ)*(H : ℚ) := by
    simpa only [mul_sub, Finset.sum_sub_distrib] using hvar
  have hHJ' : (H : ℚ) ≤ boxSide d lo hi j := by exact_mod_cast hHJ j
  rw [scv_final_identity d γ a j hj x, scv_final_identity d γ a j hj y]
  change |((x j : ℚ) - c * _ + c * _) - ((y j : ℚ) - c * _ + c * _)| ≤ _
  have halg (X Y A B T U : ℚ) :
      (X-c*A+c*T)-(Y-c*B+c*U) = (X-Y)-c*(A-B)+c*(T-U) := by ring
  rw [halg]
  calc
    _ ≤ |(x j : ℚ)-(y j : ℚ)| +
        |c * ((∑ i, (a i : ℚ)*(x i : ℚ)) - ∑ i, (a i : ℚ)*(y i : ℚ))| +
        |c * ((∑ i ∈ Finset.univ.filter (fun i : Fin d => j < i),
            (a i : ℚ)*(x i : ℚ)) -
          ∑ i ∈ Finset.univ.filter (fun i : Fin d => j < i),
            (a i : ℚ)*(y i : ℚ))| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (boxSide d lo hi j : ℚ) + (R : ℚ)*(H : ℚ) +
        (R : ℚ)*(boxSide d lo hi j : ℚ) := by
      apply add_le_add (add_le_add hb ?_) ?_
      · rw [abs_mul]
        exact (mul_le_of_le_one_left (abs_nonneg _) hc).trans hv
      · rw [abs_mul]
        exact (mul_le_of_le_one_left (abs_nonneg _) hc).trans ht
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_left hHJ' (Nat.cast_nonneg (α := ℚ) R)]

private lemma agent4_sc_complete23_rescaled_difference_oct13v14 {d : ℕ}
    (T : Matrix (Fin d) (Fin d) ℚ) (D : Matrix (Fin d) (Fin d) ℤ)
    (b : Fin d → ℚ) (hTD : T * ratMat D = Matrix.diagonal b)
    (u y z : Fin d → ℤ) (j : Fin d) :
    (T *ᵥ (fun i => ((u + D *ᵥ y) i : ℚ))) j -
      (T *ᵥ (fun i => ((u + D *ᵥ z) i : ℚ))) j =
      b j * ((y j : ℚ) - (z j : ℚ)) := by
  have hcast (v : Fin d → ℤ) :
      (fun i => ((u + D *ᵥ v) i : ℚ)) =
        (fun i => (u i : ℚ)) + ratMat D *ᵥ (fun i => (v i : ℚ)) := by
    funext i
    simp [ratMat, Matrix.mulVec, dotProduct]
  rw [hcast y, hcast z, Matrix.mulVec_add, Matrix.mulVec_add]
  simp only [Pi.add_apply, Matrix.mulVec_mulVec, hTD, Matrix.mulVec_diagonal]
  ring

private lemma agent4_sc_complete23_strict_scaled_variation_oct13v14
    (R s H L : ℕ) (hs : R < s) (hH : 1 ≤ H) (hL : 1 ≤ L)
    (v : ℤ) :
    ((s : ℚ) * |(v : ℚ)| ≤ (R : ℚ) * (H : ℚ) → |v| < (H : ℤ)) ∧
    ((s : ℚ) * |(v : ℚ)| ≤ (2 * (R : ℚ) + 1) * (L : ℚ) →
      |v| < (3 * L : ℕ)) := by
  have hs' : (R : ℚ) + 1 ≤ s := by exact_mod_cast hs
  have hHp : (0 : ℚ) < H := by exact_mod_cast (show 0 < H by omega)
  have hLp : (0 : ℚ) < L := by exact_mod_cast (show 0 < L by omega)
  have hv : (0 : ℚ) ≤ |(v : ℚ)| := abs_nonneg _
  have hm := mul_le_mul_of_nonneg_right hs' hv
  constructor
  · intro h
    have hh : |(v : ℚ)| < (H : ℚ) := by
      by_contra hn
      have ht := mul_le_mul_of_nonneg_left (le_of_not_gt hn)
        (show (0 : ℚ) ≤ R from Nat.cast_nonneg R)
      nlinarith
    exact_mod_cast hh
  · intro h
    have hh : |(v : ℚ)| < 3 * (L : ℚ) := by
      by_contra hn
      have ht := mul_le_mul_of_nonneg_left (le_of_not_gt hn)
        (show (0 : ℚ) ≤ R from Nat.cast_nonneg R)
      nlinarith
    exact_mod_cast hh

private lemma agent4_sc_complete23_permuted_frame_v16 {d : ℕ} (hd : 1 ≤ d)
    (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j) (a : Fin d → ℤ)
    (e : Fin d ≃ Fin d) (ha : a (e ⟨0, hd⟩) ≠ 0) :
    let T := (shortCoordMatrix d (γ ∘ e) (a ∘ e)).submatrix e.symm e.symm
    T.det ≠ 0 ∧
    (∀ j ∉ vecSupport a, ∀ i, T j i = if i = j then 1 else 0) ∧
    (∀ j ∉ vecSupport a, ∀ i, T i j = if i = j then 1 else 0) ∧
    ∃ c : Fin d → ℚ, (∀ j, 0 < c j) ∧
      ∀ x : Fin d → ℚ, quadFormQ d γ x = ∑ j, c j * (T *ᵥ x) j ^ 2 := by
  classical
  dsimp only
  let γe := γ ∘ e
  let ae := a ∘ e
  let T₀ := shortCoordMatrix d γe ae
  have hf := agent4_sc_complete23_frame_partial_oct13 d hd γe (fun j => hγ (e j)) ae ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_submatrix_equiv_self]
    exact hf.1
  · intro j hj i
    have haj : ae (e.symm j) = 0 := by simpa [ae, vecSupport] using hj
    simpa using hf.2.1 (e.symm j) haj (e.symm i)
  · intro j hj i
    have haj : ae (e.symm j) = 0 := by simpa [ae, vecSupport] using hj
    simpa using agent4_sc_complete23_unused_column_oct13 d hd γe ae ha (e.symm j) haj (e.symm i)
  · let c₀ : Fin d → ℚ := fun j =>
      (shortCoordInner d γe (shortCoordRow d γe ae j) (shortCoordRow d γe ae j))⁻¹
    have hc (j : Fin d) : 0 < c₀ j := inv_pos.mpr
      (sc2026_pos d γe (fun j => hγ (e j)) _
        (agent4_sc_complete23_row_partial_oct13v2 d hd γe (fun j => hγ (e j)) ae ha j))
    refine ⟨c₀ ∘ e.symm, fun j => hc _, ?_⟩
    intro x
    have hmul (j : Fin d) :
        ((T₀.submatrix e.symm e.symm) *ᵥ x) (e j) =
          ∑ i, shortCoordRow d γe ae j i * x (e i) := by
      change (∑ i, T₀ (e.symm (e j)) (e.symm i) * x i) = _
      rw [← e.sum_comp]
      simp [T₀, shortCoordMatrix]
    change quadFormQ d γ x = ∑ j, c₀ (e.symm j) * ((T₀.submatrix e.symm e.symm) *ᵥ x) j ^ 2
    unfold quadFormQ
    rw [← e.sum_comp (fun j => (γ j : ℚ) * x j ^ 2),
      ← e.sum_comp (fun j => c₀ (e.symm j) * ((T₀.submatrix e.symm e.symm) *ᵥ x) j ^ 2)]
    simp only [Equiv.symm_apply_apply, hmul]
    have hh := hf.2.2 (x ∘ e)
    simpa only [quadFormQ, γe, ae, Function.comp_apply, c₀, div_eq_mul_inv,
      mul_comm] using hh

private lemma agent4_sc_complete23_data_v17 {d : ℕ} (hd : 1 ≤ d) (R : ℕ)
    (γ : Fin d → ℕ) (hγ : ∀ j, 1 ≤ γ j) (a : Fin d → ℤ)
    (e : Fin d ≃ Fin d) (ha : a (e ⟨0, hd⟩) ≠ 0) :
    let T := (shortCoordMatrix d (γ ∘ e) (a ∘ e)).submatrix e.symm e.symm
    ∃ (s : ℕ) (D : Matrix (Fin d) (Fin d) ℤ) (γ' : Fin d → ℕ),
      R < s ∧ D.det ≠ 0 ∧
      (∀ j ∉ vecSupport a, ∀ i, D j i = if i = j then 1 else 0) ∧
      T * ratMat D = Matrix.diagonal (fun j => if j ∈ vecSupport a then (s : ℚ) else 1) ∧
      (∀ j, 1 ≤ γ' j) ∧
      ∀ y : Fin d → ℤ, (∑ j, (γ' j : ℤ) * y j ^ 2) =
        ∑ j, (γ j : ℤ) * (D *ᵥ y) j ^ 2 := by
  classical
  dsimp only
  let T := (shortCoordMatrix d (γ ∘ e) (a ∘ e)).submatrix e.symm e.symm
  obtain ⟨hT, hr, hc, c, hcp, hform⟩ :=
    agent4_sc_complete23_permuted_frame_v16 hd γ hγ a e ha
  obtain ⟨s,D,hs,hD,hrow,hcol,hTD⟩ :=
    agent4_sc_complete23_support_scaling_oct13v7 R T hT (vecSupport a) hr hc
  have hb (j : Fin d) : (if j ∈ vecSupport a then (s : ℚ) else 1) ≠ 0 := by
    split_ifs
    · exact_mod_cast (show s ≠ 0 by omega)
    · norm_num
  obtain ⟨γ',hg,hge,hquad⟩ :=
    agent4_sc_complete23_integral_diagonal_oct13v10 γ hγ T c hcp hform D _ hb hTD
  exact ⟨s,D,γ',hs,hD,hrow,hTD,hg,hquad⟩

private lemma agent4_sc_complete23_permuted_variation_v19 {d R H : ℕ} (p : Piece d)
    (a : Fin d → ℤ) (haR : ∑ j, |a j| ≤ (R : ℤ))
    (Hpos : 1 ≤ H) (Hle : H ≤ p.minSide)
    (qc : Fin d) (e : Fin d ≃ Fin d) (he : e ⟨0,p.one_le_dim⟩ = qc)
    (horder : ∀ i j : Fin d, i ≤ j → e j ∈ vecSupport a → p.side (e j) ≤ p.side (e i))
    (hvar : ∀ x ∈ polyPZ d p.W, ∀ y ∈ polyPZ d p.W,
      |∑ j, a j * (x j-y j)| ≤ (R : ℤ)*(H : ℤ))
    (s : ℕ) (hs : R < s) (D : Matrix (Fin d) (Fin d) ℤ)
    (hTD : ((shortCoordMatrix d (p.gamma ∘ e) (a ∘ e)).submatrix e.symm e.symm) * ratMat D =
      Matrix.diagonal (fun j => if j ∈ vecSupport a then (s : ℚ) else 1)) :
    ∀ u : ↥(fundParaReps d D), ∀ j ∈ vecSupport a,
      ∀ y ∈ polyPZ d (shiftPullbackConstraints d D u.val p.W),
      ∀ z ∈ polyPZ d (shiftPullbackConstraints d D u.val p.W),
      |y j-z j| < ((if j = qc then H else 3*p.side j : ℕ) : ℤ) := by
  classical
  intro u j hj y hy z hz
  let x := u.val + D *ᵥ y
  let x' := u.val + D *ᵥ z
  have hx : x ∈ polyPZ d p.W := by
    rw [polyPZ_shiftPullbackConstraints] at hy
    exact hy
  have hx' : x' ∈ polyPZ d p.W := by
    rw [polyPZ_shiftPullbackConstraints] at hz
    exact hz
  let T := (shortCoordMatrix d (p.gamma ∘ e) (a ∘ e)).submatrix e.symm e.symm
  have hmul (v : Fin d → ℤ) : (T *ᵥ (fun i => (v i : ℚ))) j =
      ∑ i, shortCoordRow d (p.gamma ∘ e) (a ∘ e) (e.symm j) i * (v (e i) : ℚ) := by
    change (∑ i, shortCoordMatrix d (p.gamma ∘ e) (a ∘ e) (e.symm j) (e.symm i) * (v i : ℚ)) = _
    rw [← e.sum_comp]
    simp [shortCoordMatrix]
  have hdiff := agent4_sc_complete23_rescaled_difference_oct13v14 T D _ hTD u.val y z j
  rw [if_pos hj] at hdiff
  have hv : |∑ i, ((a ∘ e) i : ℚ) * ((x (e i) : ℚ)-(x' (e i) : ℚ))| ≤
      (R : ℚ)*(H : ℚ) := by
    have ht : |∑ i, (a i : ℚ) * ((x i : ℚ)-(x' i : ℚ))| ≤ (R : ℚ)*(H : ℚ) := by
      exact_mod_cast hvar x hx x' hx'
    rw [← e.sum_comp (fun i => (a i : ℚ) * ((x i : ℚ)-(x' i : ℚ)))] at ht
    exact ht
  have hside (i : Fin d) : H ≤ boxSide d (p.lo ∘ e) (p.hi ∘ e) i :=
    Hle.trans (Finset.inf'_le p.side (Finset.mem_univ (e i)))
  have hbox (v : Fin d → ℤ) (hv : v ∈ polyPZ d p.W) :
      (v ∘ e) ∈ boxZ d (p.lo ∘ e) (p.hi ∘ e) := by
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Fintype.mem_piFinset.mp (p.poly_subset_box hv) (e i)
  have hscaled : |(T *ᵥ (fun i => (x i : ℚ))) j -
      (T *ᵥ (fun i => (x' i : ℚ))) j| = (s : ℚ)*|(y j : ℚ)-(z j : ℚ)| := by
    rw [hdiff, abs_mul, abs_of_nonneg (Nat.cast_nonneg s)]
  have hcast : |(y j : ℚ)-(z j : ℚ)| = |((y j-z j : ℤ) : ℚ)| := by push_cast; rfl
  have hJ : 1 ≤ p.side j :=
    Hpos.trans (Hle.trans (Finset.inf'_le p.side (Finset.mem_univ j)))
  by_cases hjq : j = qc
  · subst j
    have hzero : e.symm qc = ⟨0,p.one_le_dim⟩ := by rw [← he]; simp
    have hb : |(T *ᵥ (fun i => (x i : ℚ))) qc -
        (T *ᵥ (fun i => (x' i : ℚ))) qc| ≤ (R : ℚ)*(H : ℚ) := by
      rw [hmul, hmul, hzero]
      simpa only [shortCoordRow, ite_true, mul_sub, Finset.sum_sub_distrib] using hv
    rw [hscaled, hcast] at hb
    simpa only [ite_true] using
      (agent4_sc_complete23_strict_scaled_variation_oct13v14 R s H
        (p.side qc) hs Hpos hJ (y qc-z qc)).1 hb
  · have hnonzero : (e.symm j).val ≠ 0 := by
      intro h
      have hz : e.symm j = ⟨0,p.one_le_dim⟩ := Fin.ext h
      have hh := congrArg e hz
      simp only [Equiv.apply_symm_apply, he] at hh
      exact hjq hh
    have hb := agent4_sc_complete23_supported_variation_oct13v14 d R (p.gamma ∘ e)
      (fun i => p.one_le_gamma (e i)) (a ∘ e)
      (by rw [← e.sum_comp (fun i => |a i|)] at haR; exact haR)
      (p.lo ∘ e) (p.hi ∘ e)
      (by intro i k hik hak; exact horder i k hik (by simpa [vecSupport] using hak))
      H hside (x ∘ e) (x' ∘ e) (hbox x hx) (hbox x' hx') hv
      (e.symm j) hnonzero (by simpa [vecSupport] using hj)
    have hb' : |(T *ᵥ (fun i => (x i : ℚ))) j -
        (T *ᵥ (fun i => (x' i : ℚ))) j| ≤ (2*(R : ℚ)+1)*(p.side j : ℚ) := by
      simpa only [hmul, Function.comp_apply, Equiv.apply_symm_apply, Piece.side, boxSide] using hb
    rw [hscaled, hcast] at hb'
    simpa only [if_neg hjq] using
      (agent4_sc_complete23_strict_scaled_variation_oct13v14 R s H
        (p.side j) hs Hpos hJ (y j-z j)).2 hb'

private def agent4_sc_complete23_config_property_v20 (R d : ℕ) (γ : Fin d → ℕ)
    (a : Fin d → ℤ) (e : Equiv.Perm (Fin d)) (N : ℕ) : Prop :=
  ∀ hd : 1 ≤ d, (∀ j, 1 ≤ γ j) → a (e ⟨0,hd⟩) ≠ 0 →
  ∃ (s : ℕ) (D : Matrix (Fin d) (Fin d) ℤ) (γ' : Fin d → ℕ),
    R < s ∧ D.det ≠ 0 ∧ D.det.natAbs ≤ N ∧ transitionSize D ≤ N ∧
    max R (d * transitionSize D * R) + d + (Finset.univ.sup γ') + 1 ≤ N ∧
    (∀ j ∉ vecSupport a, ∀ i, D j i = if i = j then 1 else 0) ∧
    ((shortCoordMatrix d (γ ∘ e) (a ∘ e)).submatrix e.symm e.symm) * ratMat D =
      Matrix.diagonal (fun j => if j ∈ vecSupport a then (s : ℚ) else 1) ∧
    (∀ j, 1 ≤ γ' j) ∧
    ∀ y : Fin d → ℤ, (∑ j, (γ' j : ℤ) * y j ^ 2) =
      ∑ j, (γ j : ℤ) * (D *ᵥ y) j ^ 2

private lemma agent4_sc_complete23_config_exists_v20 (R d : ℕ) (γ : Fin d → ℕ)
    (a : Fin d → ℤ) (e : Equiv.Perm (Fin d)) :
    ∃ N, agent4_sc_complete23_config_property_v20 R d γ a e N := by
  classical
  by_cases hd : 1 ≤ d
  · by_cases hg : ∀ j, 1 ≤ γ j
    · by_cases ha : a (e ⟨0,hd⟩) ≠ 0
      · obtain ⟨s,D,γ',hs,hD,hr,hTD,hg',hquad⟩ :=
          agent4_sc_complete23_data_v17 hd R γ hg a e ha
        let A := max R (d * transitionSize D * R) + d + Finset.univ.sup γ' + 1
        refine ⟨D.det.natAbs + transitionSize D + A, ?_⟩
        intro hd' hg'' ha'
        refine ⟨s,D,γ',hs,hD,by omega,by omega,by dsimp [A]; omega,hr,hTD,hg',hquad⟩
      · exact ⟨0,fun hd' hg' ha' => False.elim (ha ha')⟩
    · exact ⟨0,fun hd' hg' ha' => False.elim (hg hg')⟩
  · exact ⟨0,fun hd' hg' ha' => False.elim (hd hd')⟩

private lemma agent4_sc_complete23_uniform_data_v20 (R : ℕ) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ d, d ≤ R → ∀ γ : Fin d → ℕ,
      (∀ j, γ j ≤ R) → ∀ a : Fin d → ℤ, (∀ j, |a j| ≤ (R : ℤ)) →
      ∀ e : Equiv.Perm (Fin d), ∃ N, N ≤ C ∧
        agent4_sc_complete23_config_property_v20 R d γ a e N := by
  classical
  let I := Σ d : Fin (R+1), (Fin d.val → Fin (R+1)) ×
    (Fin d.val → ↥(Finset.Icc (-(R : ℤ)) (R : ℤ))) × Equiv.Perm (Fin d.val)
  have hex (t : I) : ∃ N, agent4_sc_complete23_config_property_v20 R t.1.val
      (fun j => (t.2.1 j).val) (fun j => (t.2.2.1 j).val) t.2.2.2 N :=
    agent4_sc_complete23_config_exists_v20 R _ _ _ _
  choose N hN using hex
  refine ⟨Finset.univ.sup N + 1, by omega, ?_⟩
  intro d hd γ hγ a ha e
  let t : I := ⟨⟨d, by omega⟩, (fun j => ⟨γ j, by have := hγ j; omega⟩),
    (fun j => ⟨a j, Finset.mem_Icc.mpr (abs_le.mp (ha j))⟩), e⟩
  refine ⟨N t, (Finset.le_sup (Finset.mem_univ t)).trans (Nat.le_add_right _ 1), ?_⟩
  exact hN t

/-- **Lemma (a short linear combination as a coordinate).**
Let `(W, J, Q, R)` be a piece of dimension `d` (so `p.A ≤ R`), let `H` be an integer with
`1 ≤ H ≤ min_j #J_j`, and let `a ∈ ℤ^d \ {0}` satisfy `|a|₁ ≤ R` and `|a · (x - x')| ≤ R H`
for all `x, x' ∈ 𝒫(W)`.  Choose `qc ∈ supp a` with largest `#J_{qc}`.  Then there are a set
`U ⊂ ℤ^d` of size `≪_R 1` (here indexed by `Fin M` with `M ≤ C`) and a matrix `D ∈ ℤ^{d×d}`
such that the transitions `x = u + D y`, `u ∈ U`, give a decomposition of `(W, J, Q, R)` into
pieces `(W'_u, J'_u, Q', R')` with `R' ≪_R 1` (and a common new diagonal form `Q'`), and
`#J'_{u,qc} = H`, `#J_j ≤ #J'_{u,j} ≤ 3 #J_j` for `j ≠ qc`, and `J'_{u,j} = J_j` for
`j ∉ supp a`. -/
theorem lem_short_coordinate (R : ℕ) (hR : 1 ≤ R) :
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
                  (q m).lo j = p.lo j ∧ (q m).hi j = p.hi j := by
  classical
  obtain ⟨C,hC,huniform⟩ := agent4_sc_complete23_uniform_data_v20 R
  refine ⟨C,hC,?_⟩
  intro d p hp hJ H hH hHJ a ha haR hvar qc hqc hmax
  obtain ⟨e,he,horder⟩ :=
    agent4_sc_complete23_order_oct13v12 p.one_le_dim p.side a qc hmax
  have hab (j : Fin d) : |a j| ≤ (R : ℤ) :=
    (Finset.single_le_sum (fun i _ => abs_nonneg (a i)) (Finset.mem_univ j)).trans haR
  obtain ⟨N,hNC,hdata⟩ := huniform d (p.dim_le_A.trans hp) p.gamma
    (fun j => (p.gamma_le_A j).trans hp) a hab e
  have haz : a (e ⟨0,p.one_le_dim⟩) ≠ 0 := by
    rw [he]
    exact (Finset.mem_filter.mp hqc).2
  obtain ⟨s,D,γ',hs,hD,hdet,hsize,hA,hrow,hTD,hγ',hquad⟩ :=
    hdata p.one_le_dim p.one_le_gamma haz
  obtain ⟨M,U,q,hM,hdecomp,hinj,hqA,hgamma,hside,hother,hout⟩ :=
    agent4_sc_complete23_assemble_geometry_v4 p hp hH hHJ a qc hqc D hD γ' hγ'
      (fun j => Finset.le_sup (Finset.mem_univ j)) hquad hrow
      (agent4_sc_complete23_permuted_variation_v19 p a haR hH hHJ qc e he horder hvar s hs D hTD)
  let R' := max R (d * transitionSize D * R) + d + Finset.univ.sup γ' + 1
  refine ⟨M,U,D,q,R',?_,?_,hdecomp,hinj,hsize.trans hNC,?_,hgamma,hside,hother,hout⟩
  · rw [hM]
    exact hdet.trans hNC
  · dsimp only [R']
    exact hA.trans hNC
  · intro m
    exact hqA m
private def a4f67_raise {d : ℕ} (p : Piece d) (B : ℕ)
    (hB : p.A ≤ B) : Piece d :=
  { p with A := B
           one_le_A := p.one_le_A.trans hB
           dim_le_A := p.dim_le_A.trans hB
           rho_le_A := p.rho_le_A.trans hB
           gamma_le_A := fun j => (p.gamma_le_A j).trans hB }

private lemma a4f67_reduce {d : ℕ}
    (p t : Piece d) (qc : Fin d) (hqc : qc ∈ p.longCoords)
    (hside : t.side qc = p.minSide)
    (hother : ∀ j, j ≠ qc → p.side j ≤ t.side j ∧ t.side j ≤ 3 * p.side j)
    (hshort : ∀ j ∈ p.shortCoords, t.side j = p.side j)
    (hA : p.A ≤ t.A) :
    t.minSide = p.minSide ∧ t.nLong < p.nLong := by
  classical
  have hmin (j : Fin d) : p.minSide ≤ t.side j := by
    by_cases hj : j = qc
    · subst j; rw [hside]
    · exact (Finset.inf'_le p.side (Finset.mem_univ j)).trans (hother j hj).1
  have he : t.minSide = p.minSide := by
    apply le_antisymm
    · exact (Finset.inf'_le t.side (Finset.mem_univ qc)).trans_eq hside
    · exact Finset.le_inf' _ _ (fun j _ => hmin j)
  refine ⟨he, ?_⟩
  have hsub : t.longCoords ⊆ p.longCoords.erase qc := by
    intro j hj
    have hlong := (Finset.mem_filter.mp hj).2
    apply Finset.mem_erase.mpr
    constructor
    · intro hjq
      subst j
      rw [hside, he] at hlong
      exact hlong (by simpa using Nat.mul_le_mul_right p.minSide t.one_le_A)
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hs
      have hjs : j ∈ p.shortCoords := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
      apply hlong
      rw [hshort j hjs, he]
      exact hs.trans (Nat.mul_le_mul_right _ hA)
  exact (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem hqc)

private lemma a4f67_vol {d : ℕ}
    (p t : Piece d) (qc : Fin d)
    (hside : t.side qc = p.minSide)
    (hother : ∀ j, j ≠ qc → t.side j ≤ 3 * p.side j) :
    boxVol d t.lo t.hi ≤ 3 ^ d * boxVol d p.lo p.hi := by
  have hs (j : Fin d) : t.side j ≤ 3 * p.side j := by
    by_cases hj : j = qc
    · subst j
      rw [hside]
      exact (Finset.inf'_le p.side (Finset.mem_univ qc)).trans (by omega)
    · exact hother j hj
  change (∏ j, t.side j) ≤ 3 ^ d * ∏ j, p.side j
  calc
    _ ≤ ∏ j, 3 * p.side j := Finset.prod_le_prod (fun j _ => hs j)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

private lemma a4f67_minus (d A : ℕ) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ p : Piece d, p.A = A →
      (∀ j, p.lo j ≤ p.hi j) →
      ∀ w b, (w,b) ∈ p.W → p.IsMixed (w,b) →
      ∀ pm : Piece d, pm.W = p.splitMinusW w b →
        pm.lo = p.lo → pm.hi = p.hi → pm.gamma = p.gamma → pm.A = A+1 →
        ∃ (M : ℕ) (q : Fin M → Piece d) (u : Fin M → Fin d → ℤ)
          (D : Matrix (Fin d) (Fin d) ℤ),
          M ≤ C ∧ IsDecomposition pm q u (fun _ => D) ∧
          transitionSize D ≤ C ∧ (∀ m, (q m).A ≤ C) ∧
          (∀ m, (q m).nLong < p.nLong) ∧
          (∀ m j, (q m).lo j ≤ (q m).hi j) ∧
          ∀ m, boxVol d (q m).lo (q m).hi ≤ 3^d * boxVol d p.lo p.hi := by
  classical
  let R := (A+1)^2
  obtain ⟨C,hC,hsc⟩ := lem_short_coordinate R (by
    have hh : 0 < R := by dsimp [R]; positivity
    omega)
  refine ⟨max C A,hC.trans (le_max_left _ _),?_⟩
  intro p hA hJ w b hw hm pm hW hlo hhi hg hpmA
  have hpR : pm.A ≤ R := by rw [hpmA]; dsimp [R]; nlinarith
  let pr := a4f67_raise pm R hpR
  have hprJ : ∀ j, pr.lo j ≤ pr.hi j := by
    simpa [pr,a4f67_raise,hlo,hhi] using hJ
  have hmin : pr.minSide = p.minSide := by
    exact p.splitPlus_minSide_eq pr hlo hhi
  have hH : 1 ≤ p.minSide := by
    apply Finset.le_inf'
    intro j hj
    exact Finset.card_pos.mpr ⟨p.lo j,Finset.mem_Icc.mpr ⟨le_rfl,hJ j⟩⟩
  let a := p.longPart w
  have ha : a ≠ 0 := by
    obtain ⟨j,hj⟩ := hm.2
    obtain ⟨hjw,hjl⟩ := Finset.mem_inter.mp hj
    have hjs : j ∉ p.shortCoords := by
      intro h
      exact (Finset.mem_filter.mp hjl).2 (Finset.mem_filter.mp h).2
    intro he
    have hn := (Finset.mem_filter.mp hjw).2
    have hh := congrFun he j
    simp [a,Piece.longPart,Piece.shortPart,restrictVec,hjs] at hh
    exact hn hh
  have haR : (∑ j, |a j|) ≤ (R : ℤ) := by
    apply ((p.sum_abs_longPart_le w b hw).1.trans
      (p.sum_abs_longPart_le w b hw).2).trans
    have hh : p.A ≤ R := by rw [hA]; dsimp [R]; nlinarith
    exact_mod_cast hh
  have havar : ∀ x ∈ polyPZ d pr.W, ∀ y ∈ polyPZ d pr.W,
      |∑ j, a j*(x j-y j)| ≤ (R : ℤ)*(p.minSide : ℤ) := by
    intro x hx y hy
    change x ∈ polyPZ d pm.W at hx
    change y ∈ polyPZ d pm.W at hy
    rw [hW] at hx hy
    have hv := (p.splitMinus_longPart_variation_lt hJ w b hw hm x y hx hy).le
    apply hv.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [hA]
    dsimp [R]
    push_cast
    nlinarith
  have hsupport : vecSupport a ⊆ p.longCoords := by
    intro j hj
    have hjs : j ∉ p.shortCoords := by
      intro h
      have hn := (Finset.mem_filter.mp hj).2
      simp [a,Piece.longPart,Piece.shortPart,restrictVec,h] at hn
    simpa [Piece.longCoords,Piece.shortCoords] using hjs
  have hsne : (vecSupport a).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    apply ha
    funext j
    by_contra hj
    have hj' : j ∈ vecSupport a := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
    simpa [he] using hj'
  obtain ⟨qc,hqc,hmax⟩ := Finset.exists_max_image (vecSupport a) p.side hsne
  have hmax' : ∀ j ∈ vecSupport a, pr.side j ≤ pr.side qc := by
    simpa only [pr,a4f67_raise,Piece.side,hlo,hhi] using hmax
  obtain ⟨M,u,D,q,R',hMC,hR'C,hdec,_hinj,hDC,hqR',hgamma,hqcside,hother,hout⟩ :=
    hsc d pr le_rfl hprJ p.minSide hH (by rw [hmin]) a ha haR havar qc hqc hmax'
  have hqC (m : Fin M) : (q m).A ≤ C := by
    rw [hqR' m]
    exact hR'C
  let q' : Fin M → Piece d := fun m =>
    a4f67_raise (q m) (max C A) ((hqC m).trans (le_max_left _ _))
  have hdec' : IsDecomposition pm q' u (fun _ => D) := by
    refine ⟨?_,hdec.pieces_disjoint,hdec.iUnion_eq⟩
    intro m
    exact ⟨(hdec.transitions m).det_ne_zero,
      (hdec.transitions m).image_subset,(hdec.transitions m).quad_eq⟩
  have hs (m : Fin M) : (q' m).side qc = p.minSide := hqcside m
  have ho (m : Fin M) : ∀ j, j ≠ qc →
      p.side j ≤ (q' m).side j ∧ (q' m).side j ≤ 3*p.side j := by
    simpa only [pr,q',a4f67_raise,Piece.side,hlo,hhi] using hother m
  have hshort (m : Fin M) : ∀ j ∈ p.shortCoords, (q' m).side j = p.side j := by
    intro j hj
    have hja : j ∉ vecSupport a := by
      intro hh
      exact (Finset.mem_filter.mp (hsupport hh)).2 (Finset.mem_filter.mp hj).2
    obtain ⟨hl,hh⟩ := hout m j hja
    simp only [q',a4f67_raise,Piece.side,boxSide,hl,hh,pr,hlo,hhi]
  have hred (m : Fin M) := a4f67_reduce p (q' m)
    qc (hsupport hqc) (hs m) (ho m) (hshort m)
    (by change p.A ≤ max C A; rw [hA]; exact le_max_right _ _)
  refine ⟨M,q',u,D,hMC.trans (le_max_left _ _),hdec',
    hDC.trans (le_max_left _ _),fun _ => le_rfl,fun m => (hred m).2,?_,?_⟩
  · intro m j
    have hpos : 1 ≤ (q' m).side j := by
      have hh := Finset.inf'_le (q' m).side (Finset.mem_univ j)
      change (q' m).minSide ≤ (q' m).side j at hh
      rw [(hred m).1] at hh
      omega
    obtain ⟨x,hx⟩ := Finset.card_pos.mp
      (show 0 < (Finset.Icc ((q' m).lo j) ((q' m).hi j)).card from hpos)
    exact (Finset.mem_Icc.mp hx).1.trans (Finset.mem_Icc.mp hx).2
  · intro m
    exact a4f67_vol p (q' m) qc (hs m) (fun j hj => (ho m j hj).2)

private lemma a4f67_identity {d : ℕ} (p : Piece d)
    (hbal : ∀ i j, (constraintGraph d p.W).Reachable i j →
      p.side i ≤ p.A * p.side j) :
    ∃ (M : ℕ) (q : Fin M → Piece d) (u : Fin M → Fin d → ℤ)
      (Φ : Fin M → Matrix (Fin d) (Fin d) ℤ),
      M ≤ p.A + 1 ∧ IsDecomposition p q u Φ ∧
      (∀ m, transitionSize (Φ m) ≤ p.A + 1) ∧
      (∀ m, (q m).A ≤ p.A + 1) ∧
      (∀ m, boxVol d (q m).lo (q m).hi ≤ (p.A + 1) * boxVol d p.lo p.hi) ∧
      ∀ m, IsBalancedWrt d (p.A + 1) (q m).W (q m).lo (q m).hi := by
  classical
  by_cases hne : (polyPZ d p.W).Nonempty
  · obtain ⟨x, hx⟩ := hne
    let W := p.W.filter (fun z => z.1 ≠ 0)
    have hpoly : polyPZ d W = polyPZ d p.W := by
      ext y
      constructor
      · intro hy z hz
        by_cases hnz : z.1 = 0
        · have hb := hx z hz
          simpa only [hnz, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
            zero_add] using hb
        · exact hy z (Finset.mem_filter.mpr ⟨hz, hnz⟩)
      · intro hy z hz
        exact hy z (Finset.mem_filter.mp hz).1
    have hrho : constraintRho d W ≤ p.A := by
      apply (constraintRho_le_iff _ _ _).2
      refine ⟨(Finset.card_filter_le _ _).trans p.card_W_le_A, ?_⟩
      intro z hz
      exact (l1_le_constraintRho d p.W z (Finset.mem_filter.mp hz).1).trans
        (by exact_mod_cast p.rho_le_A)
    let p' : Piece d :=
      { W := W, lo := p.lo, hi := p.hi, gamma := p.gamma, A := p.A
        one_le_dim := p.one_le_dim, one_le_gamma := p.one_le_gamma
        one_le_A := p.one_le_A
        poly_subset_box := by rw [hpoly]; exact p.poly_subset_box
        dim_le_A := p.dim_le_A, rho_le_A := hrho, gamma_le_A := p.gamma_le_A }
    have himage : pieceAffineImage (0 : Fin d → ℤ) 1 (polyPZ d p'.W) =
        polyPZ d p.W := by
      simpa [pieceAffineImage, p'] using hpoly
    have htrans : IsTransition p p' 0 1 := by
      refine ⟨by simp, ?_, ?_⟩
      · rw [himage]
      · intro y
        simp [Piece.quad, p']
    have hgraph : constraintGraph d W ≤ constraintGraph d p.W := by
      intro i j hij
      obtain ⟨hne, z, hz, hmul⟩ := (constraintGraph_adj_iff d W i j).1 hij
      exact (constraintGraph_adj_iff d p.W i j).2
        ⟨hne, z, (Finset.mem_filter.mp hz).1, hmul⟩
    refine ⟨1, (fun _ => p'), (fun _ => 0), (fun _ => 1), by omega,
      ?_, ?_, (fun _ => Nat.le_add_right _ _), ?_, ?_⟩
    · refine ⟨fun _ => htrans, ?_, ?_⟩
      · intro m m' hne
        exact (hne (Subsingleton.elim _ _)).elim
      · simpa only [Set.iUnion_const] using himage.symm
    · intro m
      apply (matInftyNorm_le_iff _ _).2
      intro i j
      simp only [Matrix.one_apply]
      split_ifs <;> simp <;> omega
    · intro m
      change boxVol d p.lo p.hi ≤ (p.A + 1) * boxVol d p.lo p.hi
      nlinarith
    · intro m
      refine ⟨p.one_le_dim, by omega, ?_, ?_⟩
      · intro z hz
        exact (Finset.mem_filter.mp hz).2
      · intro i j hij
        have hr : (constraintGraph d W).Reachable i j :=
          SimpleGraph.ConnectedComponent.eq.mp hij
        change p.side i ≤ (p.A + 1) * p.side j
        exact (hbal i j (hr.mono hgraph)).trans
          (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  · have hempty : polyPZ d p.W = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, by omega, ?_,
      (fun m => Fin.elim0 m), (fun m => Fin.elim0 m),
      (fun m => Fin.elim0 m), (fun m => Fin.elim0 m)⟩
    refine ⟨(fun m => Fin.elim0 m), (fun m => Fin.elim0 m), ?_⟩
    simp [hempty]

private def a4f67_BP {d : ℕ} (p : Piece d) (C : ℕ) : Prop :=
  ∃ (M : ℕ) (q : Fin M → Piece d) (u : Fin M → Fin d → ℤ)
    (Φ : Fin M → Matrix (Fin d) (Fin d) ℤ),
    M ≤ C ∧ IsDecomposition p q u Φ ∧
    (∀ m, transitionSize (Φ m) ≤ C) ∧ (∀ m, (q m).A ≤ C) ∧
    (∀ m, boxVol d (q m).lo (q m).hi ≤ C * boxVol d p.lo p.hi) ∧
    ∀ m, IsBalancedWrt d C (q m).W (q m).lo (q m).hi

private lemma a4f67_mono {d : ℕ} {p : Piece d} {C B : ℕ}
    (h : a4f67_BP p C) (hCB : C ≤ B) : a4f67_BP p B := by
  obtain ⟨M,q,u,Φ,hM,hD,hΦ,hA,hV,hBal⟩ := h
  refine ⟨M,q,u,Φ,hM.trans hCB,hD,fun m => (hΦ m).trans hCB,
    fun m => (hA m).trans hCB,fun m => (hV m).trans (Nat.mul_le_mul_right _ hCB),?_⟩
  intro m
  obtain ⟨hd,hC,hn,hs⟩ := hBal m
  exact ⟨hd,hC.trans hCB,hn,
    fun i j hij => (hs i j hij).trans (Nat.mul_le_mul_right _ hCB)⟩

private lemma a4f67_comp {d M : ℕ} {p : Piece d}
    {q : Fin M → Piece d} {u : Fin M → Fin d → ℤ}
    {Φ : Fin M → Matrix (Fin d) (Fin d) ℤ}
    (hdec : IsDecomposition p q u Φ) (L V B : ℕ)
    (hM : M ≤ L) (hΦ : ∀ m, transitionSize (Φ m) ≤ L)
    (hV : ∀ m, boxVol d (q m).lo (q m).hi ≤ V * boxVol d p.lo p.hi)
    (hB : ∀ m, a4f67_BP (q m) B) :
    a4f67_BP p (L*B + d*L*B + V*B + B) := by
  classical
  choose N q' v Ψ hN hdec' hΨ hA hvol hbal using hB
  let e := sigmaPieceIndexEquiv N
  refine ⟨∑ m, N m,fun t => q' (e.symm t).1 (e.symm t).2,
    fun t => u (e.symm t).1 + Φ (e.symm t).1 *ᵥ v (e.symm t).1 (e.symm t).2,
    fun t => Φ (e.symm t).1 * Ψ (e.symm t).1 (e.symm t).2,?_,
    hdec.comp N q' v Ψ hdec',?_,?_,?_,?_⟩
  · have hn : (∑ m, N m) ≤ M*B := by
      calc
        _ ≤ ∑ _m : Fin M, B := Finset.sum_le_sum (fun m _ => hN m)
        _ = _ := by simp
    exact (hn.trans (Nat.mul_le_mul_right B hM)).trans (by omega)
  · intro t
    apply (transitionSize_mul_le _ _).trans
    have hh := Nat.mul_le_mul (Nat.mul_le_mul_left d (hΦ (e.symm t).1))
      (hΨ (e.symm t).1 (e.symm t).2)
    exact hh.trans (by omega)
  · intro t
    exact (hA (e.symm t).1 (e.symm t).2).trans (by omega)
  · intro t
    apply (hvol (e.symm t).1 (e.symm t).2).trans
    calc
      B * boxVol d (q (e.symm t).1).lo (q (e.symm t).1).hi ≤
        B * (V * boxVol d p.lo p.hi) := Nat.mul_le_mul_left _ (hV _)
      _ ≤ _ := by
        rw [← Nat.mul_assoc, Nat.mul_comm B V]
        exact Nat.mul_le_mul_right _ (by omega)
  · intro t
    obtain ⟨hd,hB,hn,hs⟩ := hbal (e.symm t).1 (e.symm t).2
    refine ⟨hd,by omega,hn,?_⟩
    intro i j hij
    exact (hs i j hij).trans (Nat.mul_le_mul_right _ (by omega))

private lemma a4f67_uniform (d B : ℕ) (K : ℕ → ℕ → Prop)
    (h : ∀ l m A, K l m → ∃ C : ℕ, 1 ≤ C ∧
      ∀ p : Piece d, p.A = A → p.nLong = l → p.nMix = m →
        (∀ j, p.lo j ≤ p.hi j) → a4f67_BP p C) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ p : Piece d, p.A ≤ B →
      K p.nLong p.nMix → (∀ j, p.lo j ≤ p.hi j) → a4f67_BP p C := by
  classical
  let I := Fin d × Fin (B+1) × Fin (B+1)
  have hex (i : I) : ∃ C : ℕ, 1 ≤ C ∧
      ∀ p : Piece d, p.A = i.2.2.val → p.nLong = i.1.val →
        p.nMix = i.2.1.val → K i.1.val i.2.1.val →
        (∀ j, p.lo j ≤ p.hi j) → a4f67_BP p C := by
    by_cases hk : K i.1.val i.2.1.val
    · obtain ⟨C,hC,hp⟩ := h i.1.val i.2.1.val i.2.2.val hk
      exact ⟨C,hC,fun p hA hl hm _ hj => hp p hA hl hm hj⟩
    · exact ⟨1,le_rfl,fun p hA hl hm hk' hj => False.elim (hk hk')⟩
  choose c hc hp using hex
  refine ⟨Finset.univ.sup c + 1, by omega, ?_⟩
  intro p hB hK hj
  let i : I := ⟨⟨p.nLong,p.nLong_lt_dim⟩,
    ⟨⟨p.nMix,by have := p.nMix_le_A; omega⟩,⟨p.A,by omega⟩⟩⟩
  exact a4f67_mono (hp i p rfl rfl rfl hK hj)
    ((Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_add_right _ 1))

private lemma a4f67_mixed (d nlong nmix A : ℕ) (hmix : 0 < nmix)
    (hIH : ∀ l m B, l < nlong ∨ (l = nlong ∧ m < nmix) →
      ∃ C : ℕ, 1 ≤ C ∧ ∀ p : Piece d, p.A = B → p.nLong = l → p.nMix = m →
        (∀ j, p.lo j ≤ p.hi j) → a4f67_BP p C) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ p : Piece d, p.A = A → p.nLong = nlong → p.nMix = nmix →
      (∀ j, p.lo j ≤ p.hi j) → a4f67_BP p C := by
  classical
  let K := fun l m => l < nlong ∨ (l = nlong ∧ m < nmix)
  obtain ⟨Cp,hCp,hp⟩ := a4f67_uniform d (A+2*d) K hIH
  obtain ⟨L,hL,hshort⟩ := a4f67_minus d A
  obtain ⟨B,hB,hb⟩ := a4f67_uniform d L K hIH
  let Cm := L*B + d*L*B + 3^d*B + B
  let T := max Cp Cm
  let C := 2*T + d*2*T + 1*T + T
  have hT : 1 ≤ T := hCp.trans (le_max_left _ _)
  refine ⟨C,by dsimp [C]; omega,?_⟩
  intro p hA hn hm hJ
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (show 0 < p.mixedIneqs.card by
    change 0 < p.nMix; omega)
  obtain ⟨hzW,hzMix⟩ := Finset.mem_filter.mp hz
  obtain ⟨pp,hpW,hplo,hphi,hpg,hpA⟩ := p.splitPlus_isPiece hJ z.1 z.2 hzW hzMix
  obtain ⟨pm,hmW,hmlo,hmhi,hmg,hmA⟩ := p.splitMinus_isPiece hJ z.1 z.2 hzW hzMix
  have hppJ : ∀ j, pp.lo j ≤ pp.hi j := by simpa only [hplo,hphi] using hJ
  have hppK : K pp.nLong pp.nMix := by
    have hl := p.splitPlus_nLong_le pp hplo hphi hpA
    rcases lt_or_eq_of_le hl with hl | hl
    · exact Or.inl (by omega)
    · exact Or.inr ⟨hl.trans hn,by
        have hh := p.splitPlus_nMix_lt_of_nLong_eq pp hJ z.1 z.2 hzW hzMix
          hpW hplo hphi hpA hl
        omega⟩
  have hpp : a4f67_BP pp Cp := hp pp (by rw [hpA,hA]) hppK hppJ
  obtain ⟨M,q,u,D,hML,hdec,hDL,hqA,hql,hqJ,hqV⟩ :=
    hshort p hA hJ z.1 z.2 hzW hzMix pm hmW hmlo hmhi hmg (by rw [hmA,hA])
  have hqB : ∀ m, a4f67_BP (q m) B := by
    intro m
    apply hb (q m) (hqA m) (Or.inl (by have := hql m; omega)) (hqJ m)
  have hpm : a4f67_BP pm Cm := by
    apply a4f67_comp hdec L (3^d) B hML (fun _ => hDL) ?_ hqB
    intro m
    simpa only [hmlo,hmhi] using hqV m
  have hsplit := (p.split_identity_decomposition pp pm hJ z.1 z.2 hzW hzMix
    hpW hplo hphi hpg hpA hmW hmlo hmhi hmg hmA).2.2.2.2
  have hbranch : ∀ m : Fin 2, a4f67_BP (![pp,pm] m) T := by
    intro m
    fin_cases m
    · exact a4f67_mono hpp (le_max_left _ _)
    · exact a4f67_mono hpm (le_max_right _ _)
  apply a4f67_comp hsplit 2 1 T le_rfl ?_ ?_ hbranch
  · intro m
    apply (matInftyNorm_le_iff _ _).2
    intro i j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  · intro m
    fin_cases m
    · simpa [hplo,hphi]
    · simpa [hmlo,hmhi]

private lemma a4fac67_sum (d n : ℕ) (S : Finset (Fin d)) (e : Fin n ≃ ↥S)
    (g : Fin d → ℤ) :
    (∑ i : Fin n, g (e i).val) = ∑ j ∈ S, g j := by
  exact (e.sum_comp (fun j : ↥S => g j.val)).trans (Finset.sum_coe_sort S g)

private noncomputable def a4fac67_ext {d n : ℕ} (S : Finset (Fin d)) (e : Fin n ≃ ↥S)
    (x₀ : Fin d → ℤ) (y : Fin n → ℤ) : Fin d → ℤ := by
  classical
  exact fun j => if hj : j ∈ S then y (e.symm ⟨j,hj⟩) else x₀ j

private lemma a4fac67_ext_at {d n : ℕ} (S : Finset (Fin d)) (e : Fin n ≃ ↥S)
    (x₀ : Fin d → ℤ) (y : Fin n → ℤ) (i : Fin n) :
    a4fac67_ext S e x₀ y (e i).val = y i := by
  simp [a4fac67_ext, (e i).property]

private lemma a4fac67_dot {d n : ℕ} (S : Finset (Fin d)) (e : Fin n ≃ ↥S)
    (w x : Fin d → ℤ) (hw : ∀ j ∉ S, w j = 0) :
    (∑ j, w j*x j) = ∑ i : Fin n, w (e i).val*x (e i).val := by
  rw [a4fac67_sum d n S e (fun j => w j * x j)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j hj hjs
  rw [hw j hjs, zero_mul]

private noncomputable def a4fac67_W {d n : ℕ} (p : Piece d)
    (S : Finset (Fin d)) (e : Fin n ≃ ↥S) : Finset ((Fin n → ℤ) × ℤ) := by
  classical
  exact (p.W.filter (fun z => ∀ j ∉ S, z.1 j = 0)).image
    (fun z => (fun i => z.1 (e i).val, z.2))

private lemma a4fac67_rho {d n : ℕ} (p : Piece d)
    (S : Finset (Fin d)) (e : Fin n ≃ ↥S) :
    constraintRho n (a4fac67_W p S e) ≤ p.A := by
  classical
  apply (constraintRho_le_iff _ _ _).2
  refine ⟨Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans p.card_W_le_A), ?_⟩
  intro z hz
  obtain ⟨z,hzf,rfl⟩ := Finset.mem_image.mp hz
  change (∑ i : Fin n, |z.1 (e i).val|) ≤ (p.A : ℤ)
  rw [a4fac67_sum d n S e (fun j => |z.1 j|)]
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (by intros; positivity)).trans
    ((l1_le_constraintRho d p.W z (Finset.mem_filter.mp hzf).1).trans
      (by exact_mod_cast p.rho_le_A))

private lemma a4fac67_extension_mem {d n : ℕ} (p : Piece d)
    (S : Finset (Fin d)) (e : Fin n ≃ ↥S)
    (x₀ : Fin d → ℤ) (hx₀ : x₀ ∈ polyPZ d p.W)
    (hsep : ∀ z ∈ p.W, (∀ j ∉ S, z.1 j = 0) ∨ (∀ j ∈ S, z.1 j = 0))
    (y : Fin n → ℤ) (hy : y ∈ polyPZ n (a4fac67_W p S e)) :
    a4fac67_ext S e x₀ y ∈ polyPZ d p.W := by
  classical
  intro z hz
  rcases hsep z hz with hout | hin
  · have hzy := hy (fun i => z.1 (e i).val, z.2)
      (Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨hz,hout⟩,rfl⟩)
    rw [a4fac67_dot S e z.1 _ hout]
    simpa only [a4fac67_ext_at] using hzy
  · have he : (∑ j, z.1 j*a4fac67_ext S e x₀ y j) = ∑ j, z.1 j*x₀ j := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hjs : j ∈ S
      · rw [hin j hjs, zero_mul, zero_mul]
      · simp [a4fac67_ext,hjs]
    rw [he]
    exact hx₀ z hz

private noncomputable def a4fac67_piece {d n : ℕ} (p : Piece d)
    (S : Finset (Fin d)) (e : Fin n ≃ ↥S) (hn : 1 ≤ n) (hnA : n ≤ p.A)
    (x₀ : Fin d → ℤ) (hx₀ : x₀ ∈ polyPZ d p.W)
    (hsep : ∀ z ∈ p.W, (∀ j ∉ S, z.1 j = 0) ∨ (∀ j ∈ S, z.1 j = 0)) : Piece n where
  W := a4fac67_W p S e
  lo := fun i => p.lo (e i).val
  hi := fun i => p.hi (e i).val
  gamma := fun i => p.gamma (e i).val
  A := p.A
  one_le_dim := hn
  one_le_gamma := fun i => p.one_le_gamma _
  one_le_A := p.one_le_A
  poly_subset_box := by
    intro y hy
    have hext := p.poly_subset_box (a4fac67_extension_mem p S e x₀ hx₀ hsep y hy)
    apply Fintype.mem_piFinset.mpr
    intro i
    simpa only [a4fac67_ext_at] using Fintype.mem_piFinset.mp hext (e i).val
  dim_le_A := hnA
  rho_le_A := a4fac67_rho p S e
  gamma_le_A := fun i => p.gamma_le_A _

private lemma a4fac67_projection_mem {d n : ℕ} (p : Piece d)
    (S : Finset (Fin d)) (e : Fin n ≃ ↥S)
    (x : Fin d → ℤ) (hx : x ∈ polyPZ d p.W) :
    (fun i => x (e i).val) ∈ polyPZ n (a4fac67_W p S e) := by
  classical
  intro z hz
  obtain ⟨z,hzf,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hz,hout⟩ := Finset.mem_filter.mp hzf
  have he := hx z hz
  rw [a4fac67_dot S e z.1 x hout] at he
  exact he

private lemma a4fac67_nomix_separation {d : ℕ} (p : Piece d) (hm : p.nMix = 0)
    (z : (Fin d → ℤ) × ℤ) (hz : z ∈ p.W) :
    (∀ j ∉ p.shortCoords, z.1 j = 0) ∨ (∀ j ∈ p.shortCoords, z.1 j = 0) := by
  classical
  have hnot : ¬p.IsMixed z := by
    intro hmix
    have hz' : z ∈ p.mixedIneqs := Finset.mem_filter.mpr ⟨hz,hmix⟩
    have he : p.mixedIneqs = ∅ := Finset.card_eq_zero.mp hm
    simpa [he] using hz'
  by_cases hs : ∃ j ∈ p.shortCoords, z.1 j ≠ 0
  · left
    intro j hj
    by_contra hwj
    obtain ⟨i,hi,hwi⟩ := hs
    have hjl : j ∈ p.longCoords := by
      simpa [Piece.shortCoords,Piece.longCoords] using hj
    exact hnot ⟨⟨i,Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwi⟩,hi⟩⟩,
      ⟨j,Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwj⟩,hjl⟩⟩⟩
  · right
    intro j hj
    by_contra hwj
    exact hs ⟨j,hj,hwj⟩

private lemma a4b67_edge {a b : ℕ}
    (W : Finset ((Fin a → ℤ) × ℤ)) (V : Finset ((Fin b → ℤ) × ℤ))
    (i : Fin a) (j : Fin (a+b))
    (h : (constraintGraph (a+b) (oplusConstraints a b W V)).Adj (Fin.castAdd b i) j) :
    ∃ t : Fin a, j = Fin.castAdd b t ∧ (constraintGraph a W).Adj i t := by
  classical
  revert h
  refine Fin.addCases (fun t => ?_) (fun t => ?_) j
  · intro h
    obtain ⟨hne,z,hz,hm⟩ := (constraintGraph_adj_iff _ _ _ _).mp h
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨z,hzf,rfl⟩ := Finset.mem_image.mp hz
      refine ⟨t,rfl,(constraintGraph_adj_iff _ _ _ _).mpr ⟨?_,z,hzf,?_⟩⟩
      · intro he; subst t; exact hne rfl
      · simpa [padLeftVec] using hm
    · obtain ⟨z,hzf,rfl⟩ := Finset.mem_image.mp hz
      simp [padRightVec] at hm
  · intro h
    obtain ⟨hne,z,hz,hm⟩ := (constraintGraph_adj_iff _ _ _ _).mp h
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨z,hzf,rfl⟩ := Finset.mem_image.mp hz
      simp [padLeftVec] at hm
    · obtain ⟨z,hzf,rfl⟩ := Finset.mem_image.mp hz
      simp [padRightVec] at hm

private lemma a4b67_redge {a b : ℕ}
    (W : Finset ((Fin a → ℤ) × ℤ)) (V : Finset ((Fin b → ℤ) × ℤ))
    (i : Fin b) (j : Fin (a+b))
    (h : (constraintGraph (a+b) (oplusConstraints a b W V)).Adj (Fin.natAdd a i) j) :
    ∃ t : Fin b, j = Fin.natAdd a t ∧ (constraintGraph b V).Adj i t := by
  classical
  revert h
  refine Fin.addCases (fun t => ?_) (fun t => ?_) j
  · intro h
    obtain ⟨hne,z,hz,hm⟩ := (constraintGraph_adj_iff _ _ _ _).mp h
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨z,hzf,rfl⟩ := Finset.mem_image.mp hz
      simp [padLeftVec] at hm
    · obtain ⟨z,hzf,rfl⟩ := Finset.mem_image.mp hz
      simp [padRightVec] at hm
  · intro h
    obtain ⟨hne,z,hz,hm⟩ := (constraintGraph_adj_iff _ _ _ _).mp h
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨z,hzf,rfl⟩ := Finset.mem_image.mp hz
      simp [padLeftVec] at hm
    · obtain ⟨z,hzf,rfl⟩ := Finset.mem_image.mp hz
      refine ⟨t,rfl,(constraintGraph_adj_iff _ _ _ _).mpr ⟨?_,z,hzf,?_⟩⟩
      · intro he; subst t; exact hne rfl
      · simpa [padRightVec] using hm

private lemma a4b67_reach {a b : ℕ}
    (W : Finset ((Fin a → ℤ) × ℤ)) (V : Finset ((Fin b → ℤ) × ℤ))
    (i : Fin a) (j : Fin (a+b))
    (h : (constraintGraph (a+b) (oplusConstraints a b W V)).Reachable (Fin.castAdd b i) j) :
    ∃ t : Fin a, j = Fin.castAdd b t ∧ (constraintGraph a W).Reachable i t := by
  have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).mp h
  clear h
  induction hr with
  | refl => exact ⟨i,rfl,SimpleGraph.Reachable.refl i⟩
  | @tail u v huv huv' ih =>
    obtain ⟨t,rfl,ht⟩ := ih
    obtain ⟨s,rfl,hs⟩ := a4b67_edge W V t v huv'
    exact ⟨s,rfl,ht.trans hs.reachable⟩

private lemma a4b67_rreach {a b : ℕ}
    (W : Finset ((Fin a → ℤ) × ℤ)) (V : Finset ((Fin b → ℤ) × ℤ))
    (i : Fin b) (j : Fin (a+b))
    (h : (constraintGraph (a+b) (oplusConstraints a b W V)).Reachable (Fin.natAdd a i) j) :
    ∃ t : Fin b, j = Fin.natAdd a t ∧ (constraintGraph b V).Reachable i t := by
  have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).mp h
  clear h
  induction hr with
  | refl => exact ⟨i,rfl,SimpleGraph.Reachable.refl i⟩
  | @tail u v huv huv' ih =>
    obtain ⟨t,rfl,ht⟩ := ih
    obtain ⟨s,rfl,hs⟩ := a4b67_redge W V t v huv'
    exact ⟨s,rfl,ht.trans hs.reachable⟩

private lemma a4b67_prod {a b C : ℕ} (p : Piece a) (q : Piece b)
    (hp : IsBalancedWrt a C p.W p.lo p.hi)
    (hq : IsBalancedWrt b C q.W q.lo q.hi) :
    IsBalancedWrt (a+b) C (p.prod q).W (p.prod q).lo (p.prod q).hi := by
  classical
  obtain ⟨ha,hC,hnp,hbp⟩ := (isBalancedWrt_iff_reachable _ _ _ _ _).mp hp
  obtain ⟨hb,hC',hnq,hbq⟩ := (isBalancedWrt_iff_reachable _ _ _ _ _).mp hq
  apply (isBalancedWrt_iff_reachable _ _ _ _ _).mpr
  refine ⟨by omega,hC,?_,?_⟩
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨z,hzf,rfl⟩ := Finset.mem_image.mp hz
      intro he
      apply hnp z hzf
      funext j
      have hh := congrFun he (Fin.castAdd b j)
      simpa [padLeftVec] using hh
    · obtain ⟨z,hzf,rfl⟩ := Finset.mem_image.mp hz
      intro he
      apply hnq z hzf
      funext j
      have hh := congrFun he (Fin.natAdd a j)
      simpa [padRightVec] using hh
  · intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · intro hij
      obtain ⟨t,rfl,ht⟩ := a4b67_reach p.W q.W i j hij
      simpa [Piece.prod,boxSide] using hbp i t ht
    · intro hij
      obtain ⟨t,rfl,ht⟩ := a4b67_rreach p.W q.W i j hij
      simpa [Piece.prod,boxSide] using hbq i t ht

private lemma a4b67_vol {a b : ℕ} (p : Piece a) (q : Piece b) :
    boxVol (a+b) (p.prod q).lo (p.prod q).hi =
      boxVol a p.lo p.hi * boxVol b q.lo q.hi := by
  simp [boxVol, Piece.prod, boxSide, Fin.prod_univ_add]

private noncomputable def a4p67_W {d n : ℕ} (e : Fin d ≃ Fin n)
    (W : Finset ((Fin n → ℤ) × ℤ)) : Finset ((Fin d → ℤ) × ℤ) := by
  classical
  exact W.image (fun z => (z.1 ∘ e,z.2))

private lemma a4p67_poly {d n : ℕ} (e : Fin d ≃ Fin n)
    (W : Finset ((Fin n → ℤ) × ℤ)) (x : Fin d → ℤ) :
    x ∈ polyPZ d (a4p67_W e W) ↔ (x ∘ e.symm) ∈ polyPZ n W := by
  classical
  simp only [polyPZ,a4p67_W,Set.mem_setOf_eq,Finset.forall_mem_image]
  have hs (z : (Fin n → ℤ) × ℤ) :
      (∑ j, z.1 (e j)*x j) = ∑ j, z.1 j*x (e.symm j) := by
    rw [← e.sum_comp (fun j => z.1 j*x (e.symm j))]
    simp
  simpa only [Function.comp_apply,hs]

private noncomputable def a4p67_piece {d n : ℕ} (e : Fin d ≃ Fin n)
    (p : Piece n) : Piece d where
  W := a4p67_W e p.W
  lo := p.lo ∘ e
  hi := p.hi ∘ e
  gamma := p.gamma ∘ e
  A := p.A
  one_le_dim := by
    have he : d = n := by simpa using Fintype.card_congr e
    rw [he]
    exact p.one_le_dim
  one_le_gamma := fun j => p.one_le_gamma (e j)
  one_le_A := p.one_le_A
  poly_subset_box := by
    intro x hx
    have hh := p.poly_subset_box ((a4p67_poly e p.W x).1 hx)
    apply Fintype.mem_piFinset.mpr
    intro j
    simpa using Fintype.mem_piFinset.mp hh (e j)
  dim_le_A := by
    have he : d = n := by simpa using Fintype.card_congr e
    rw [he]
    exact p.dim_le_A
  rho_le_A := by
    classical
    apply (constraintRho_le_iff _ _ _).2
    refine ⟨Finset.card_image_le.trans p.card_W_le_A,?_⟩
    intro z hz
    obtain ⟨z,hzf,rfl⟩ := Finset.mem_image.mp hz
    change (∑ j, |z.1 (e j)|) ≤ (p.A : ℤ)
    rw [e.sum_comp (fun j => |z.1 j|)]
    exact (l1_le_constraintRho n p.W z hzf).trans (by exact_mod_cast p.rho_le_A)
  gamma_le_A := fun j => p.gamma_le_A (e j)

private lemma a4p67_vol {d n : ℕ} (e : Fin d ≃ Fin n) (p : Piece n) :
    boxVol d (a4p67_piece e p).lo (a4p67_piece e p).hi = boxVol n p.lo p.hi := by
  exact e.prod_comp (fun j => boxSide n p.lo p.hi j)

private lemma a4p67_bal {d n C : ℕ} (e : Fin d ≃ Fin n) (p : Piece n)
    (h : IsBalancedWrt n C p.W p.lo p.hi) :
    IsBalancedWrt d C (a4p67_piece e p).W (a4p67_piece e p).lo (a4p67_piece e p).hi := by
  classical
  rw [isBalancedWrt_iff_reachable] at h ⊢
  let f : constraintGraph d (a4p67_W e p.W) →g constraintGraph n p.W :=
    { toFun := e
      map_rel' := by
        intro i j hij
        obtain ⟨hne,z,hz,hprod⟩ := (constraintGraph_adj_iff _ _ _ _).1 hij
        obtain ⟨z,hzf,rfl⟩ := Finset.mem_image.mp hz
        exact (constraintGraph_adj_iff _ _ _ _).2
          ⟨fun he => hne (e.injective he),z,hzf,hprod⟩ }
  refine ⟨(a4p67_piece e p).one_le_dim,h.2.1,?_,?_⟩
  · intro z hz
    obtain ⟨z,hzf,rfl⟩ := Finset.mem_image.mp hz
    intro he
    apply h.2.2.1 z hzf
    funext j
    have hh := congrFun he (e.symm j)
    simpa only [Function.comp_apply,Equiv.apply_symm_apply,Pi.zero_apply] using hh
  · intro i j hij
    exact h.2.2.2 (e i) (e j) (hij.map f)

private lemma a4p67_affine {d n : ℕ} (e : Fin d ≃ Fin n) (p : Piece n)
    (u : Fin n → ℤ) (Φ : Matrix (Fin n) (Fin n) ℤ) (x : Fin d → ℤ) :
    x ∈ pieceAffineImage (u ∘ e) (Φ.submatrix e e) (polyPZ d (a4p67_piece e p).W) ↔
      (x ∘ e.symm) ∈ pieceAffineImage u Φ (polyPZ n p.W) := by
  constructor
  · rintro ⟨y,hy,he⟩
    refine ⟨y ∘ e.symm,(a4p67_poly e p.W y).1 hy,?_⟩
    funext j
    have hh := congrFun he (e.symm j)
    change u (e (e.symm j)) + ((Φ.submatrix e e) *ᵥ y) (e.symm j) = x (e.symm j) at hh
    rw [Matrix.submatrix_mulVec_equiv] at hh
    simpa [Function.comp_def] using hh
  · rintro ⟨y,hy,he⟩
    refine ⟨y ∘ e,?_,?_⟩
    · apply (a4p67_poly e p.W _).2
      simpa [Function.comp_def] using hy
    · funext j
      change u (e j) + ((Φ.submatrix e e) *ᵥ (y ∘ e)) j = x j
      rw [Matrix.submatrix_mulVec_equiv]
      simpa [Function.comp_def] using congrFun he (e j)

private lemma a4p67_decomp {d n M : ℕ} (e : Fin d ≃ Fin n) (p : Piece d) (p' : Piece n)
    (hp : ∀ x : Fin d → ℤ, x ∈ polyPZ d p.W ↔ (x ∘ e.symm) ∈ polyPZ n p'.W)
    (hg : ∀ j, p'.gamma (e j) = p.gamma j)
    (q : Fin M → Piece n) (u : Fin M → Fin n → ℤ)
    (Φ : Fin M → Matrix (Fin n) (Fin n) ℤ)
    (h : IsDecomposition p' q u Φ) :
    IsDecomposition p (fun m => a4p67_piece e (q m)) (fun m => u m ∘ e)
      (fun m => (Φ m).submatrix e e) := by
  classical
  apply (isDecomposition_iff _ _ _ _).2
  refine ⟨?_,?_⟩
  · intro m
    refine ⟨?_,?_,?_⟩
    · rw [Matrix.det_submatrix_equiv_self]
      exact (h.transitions m).det_ne_zero
    · intro x hx
      exact (hp x).2 ((h.transitions m).image_subset ((a4p67_affine e (q m) _ _ x).1 hx))
    · intro y
      have he : (a4p67_piece e (q m)).quad y = (q m).quad (y ∘ e.symm) := by
        unfold Piece.quad
        simpa only [a4p67_piece, Function.comp_apply, Equiv.symm_apply_apply] using
          e.sum_comp (fun j => ((q m).gamma j : ℤ) * (y (e.symm j))^2)
      rw [he,(h.transitions m).quad_eq]
      unfold Piece.quad
      rw [← e.sum_comp (fun j => (p'.gamma j : ℤ) * ((Φ m *ᵥ (y ∘ e.symm)) j)^2)]
      simp only [Matrix.submatrix_mulVec_equiv, Function.comp_apply,hg]
  · intro x
    rw [hp x]
    simp_rw [a4p67_affine]
    exact (isDecomposition_iff _ _ _ _).1 h |>.2 _

private lemma a4c67_prod {a b C : ℕ} (p : Piece a) (q : Piece b)
    (hp : a4f67_BP p C) (hq : a4f67_BP q C) :
    a4f67_BP (p.prod q) (C*C+2*C+1) := by
  classical
  obtain ⟨M,p',u,Φ,hM,hd,hΦ,hA,hV,hB⟩ := hp
  obtain ⟨N,q',v,Ψ,hN,he,hΨ,hA',hV',hB'⟩ := hq
  refine ⟨M*N,_,_,_,?_,hd.prod he,?_,?_,?_,?_⟩
  · exact (Nat.mul_le_mul hM hN).trans (by omega)
  · intro m
    apply (transitionSize_blockDiagMat_le _ _).trans
    exact (max_le (hΦ _) (hΨ _)).trans (by omega)
  · intro m
    change (p' _).A + (q' _).A ≤ _
    have := hA (finProdFinEquiv.symm m).1
    have := hA' (finProdFinEquiv.symm m).2
    omega
  · intro m
    rw [a4b67_vol,a4b67_vol]
    apply (Nat.mul_le_mul (hV _) (hV' _)).trans
    rw [show C * boxVol a p.lo p.hi * (C * boxVol b q.lo q.hi) =
      (C*C) * (boxVol a p.lo p.hi * boxVol b q.lo q.hi) by ring]
    exact Nat.mul_le_mul_right _ (by omega)
  · intro m
    obtain ⟨hdim,hC,hn,hs⟩ := a4b67_prod (p' _) (q' _) (hB _) (hB' _)
    exact ⟨hdim,by omega,hn,fun i j hij => (hs i j hij).trans
      (Nat.mul_le_mul_right _ (by omega))⟩

private lemma a4c67_pull {d n C : ℕ} (e : Fin d ≃ Fin n) (p : Piece d) (p' : Piece n)
    (hp : ∀ x : Fin d → ℤ, x ∈ polyPZ d p.W ↔ (x ∘ e.symm) ∈ polyPZ n p'.W)
    (hg : ∀ j, p'.gamma (e j) = p.gamma j)
    (hv : boxVol n p'.lo p'.hi = boxVol d p.lo p.hi)
    (h : a4f67_BP p' C) : a4f67_BP p C := by
  classical
  obtain ⟨M,q,u,Φ,hM,hd,hΦ,hA,hV,hB⟩ := h
  refine ⟨M,fun m => a4p67_piece e (q m),fun m => u m ∘ e,
    fun m => (Φ m).submatrix e e,hM,a4p67_decomp e p p' hp hg q u Φ hd,?_,hA,?_,?_⟩
  · intro m
    apply (matInftyNorm_le_iff _ _).2
    intro i j
    exact (matInftyNorm_le_iff _ _).1 (hΦ m) (e i) (e j)
  · intro m
    rw [a4p67_vol,← hv]
    exact hV m
  · intro m
    exact a4p67_bal e (q m) (hB m)

private lemma a4c67_uniform (d A : ℕ)
    (ih : ∀ n < d, ∀ l m A, ∃ C, 1 ≤ C ∧ ∀ p : Piece n,
      p.A = A → p.nLong = l → p.nMix = m →
      (∀ j, p.lo j ≤ p.hi j) → a4f67_BP p C) :
    ∃ C, 1 ≤ C ∧ ∀ n < d, ∀ p : Piece n, p.A = A →
      (∀ j, p.lo j ≤ p.hi j) → a4f67_BP p C := by
  classical
  let I := Fin d × Fin (A+1) × Fin (A+1)
  have hx (i : I) := ih i.1.val i.1.isLt i.2.1.val i.2.2.val A
  choose c hc hp using hx
  refine ⟨Finset.univ.sup c + 1,by omega,?_⟩
  intro n hn p hA hJ
  have hl : p.nLong ≤ A := (Nat.le_of_lt p.nLong_lt_dim).trans
    (p.dim_le_A.trans_eq hA)
  have hm : p.nMix ≤ A := p.nMix_le_A.trans_eq hA
  let i : I := ⟨⟨n,hn⟩,⟨⟨p.nLong,by omega⟩,⟨p.nMix,by omega⟩⟩⟩
  exact a4f67_mono (hp i p hA rfl rfl hJ)
    ((Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_add_right _ 1))

private lemma a4s67_split {d : ℕ} (p : Piece d) (S : Finset (Fin d))
    (hS : S.Nonempty) (hT : Sᶜ.Nonempty)
    (hsep : ∀ z ∈ p.W, (∀ j ∉ S, z.1 j = 0) ∨ (∀ j ∈ S, z.1 j = 0))
    (x₀ : Fin d → ℤ) (hx₀ : x₀ ∈ polyPZ d p.W)
    (hJ : ∀ j, p.lo j ≤ p.hi j) (C : ℕ)
    (hIH : ∀ n < d, ∀ p' : Piece n, p'.A = p.A →
      (∀ j, p'.lo j ≤ p'.hi j) → a4f67_BP p' C) :
    a4f67_BP p (C*C+2*C+1) := by
  classical
  let a := S.card
  let b := Sᶜ.card
  let eS : Fin a ≃ ↥S := (Finset.equivFin S).symm
  let eT : Fin b ≃ ↥Sᶜ := (Finset.equivFin Sᶜ).symm
  have ha : 1 ≤ a := Finset.card_pos.mpr hS
  have hb : 1 ≤ b := Finset.card_pos.mpr hT
  have hab : a+b=d := by
    have hs := Finset.card_le_univ S
    simp only [Fintype.card_fin] at hs
    dsimp [a,b]
    rw [Finset.card_compl,Fintype.card_fin]
    omega
  have hat : a < d := by omega
  have hbt : b < d := by omega
  have hsepT : ∀ z ∈ p.W,
      (∀ j ∉ Sᶜ, z.1 j = 0) ∨ (∀ j ∈ Sᶜ, z.1 j = 0) := by
    intro z hz
    have hh := hsep z hz
    simpa only [Finset.mem_compl, not_not] using hh.symm
  let pS := a4fac67_piece p S eS ha (hat.le.trans p.dim_le_A) x₀ hx₀ hsep
  let pT := a4fac67_piece p Sᶜ eT hb (hbt.le.trans p.dim_le_A) x₀ hx₀ hsepT
  have hSbp : a4f67_BP pS C := hIH a hat pS rfl (fun j => hJ _)
  have hTbp : a4f67_BP pT C := hIH b hbt pT rfl (fun j => hJ _)
  let E : Fin a ⊕ Fin b ≃ Fin d :=
    { toFun := Sum.elim (fun i => (eS i).val) (fun i => (eT i).val)
      invFun := fun j => if hj : j ∈ S then Sum.inl (eS.symm ⟨j,hj⟩)
        else Sum.inr (eT.symm ⟨j,Finset.mem_compl.mpr hj⟩)
      left_inv := by
        intro j
        cases j with
        | inl j => simp [(eS j).property]
        | inr j => simp [Finset.mem_compl.mp (eT j).property]
      right_inv := by
        intro j
        dsimp only
        split_ifs <;> simp }
  let e : Fin d ≃ Fin (a+b) := E.symm.trans finSumFinEquiv
  have hel (j : Fin a) : e.symm (Fin.castAdd b j) = (eS j).val := by
    simp [e,E]
  have her (j : Fin b) : e.symm (Fin.natAdd a j) = (eT j).val := by
    simp [e,E]
  let pp := pS.prod pT
  have hpoly : ∀ x : Fin d → ℤ,
      x ∈ polyPZ d p.W ↔ (x ∘ e.symm) ∈ polyPZ (a+b) pp.W := by
    intro x
    change _ ↔ (x ∘ e.symm) ∈ polyPZ _ (oplusConstraints _ _ pS.W pT.W)
    rw [polyPZ_oplusConstraints]
    change _ ↔ leftPart a b (x ∘ e.symm) ∈ polyPZ a pS.W ∧
      rightPart a b (x ∘ e.symm) ∈ polyPZ b pT.W
    have hl : leftPart a b (x ∘ e.symm) = fun i => x (eS i).val := by
      funext j
      simp [leftPart,hel]
    have hr : rightPart a b (x ∘ e.symm) = fun i => x (eT i).val := by
      funext j
      simp [rightPart,her]
    rw [hl,hr]
    constructor
    · intro hx
      exact ⟨a4fac67_projection_mem p S eS x hx,
        a4fac67_projection_mem p Sᶜ eT x hx⟩
    · rintro ⟨hx,hy⟩ z hz
      rcases hsep z hz with hs | ht
      · have hh := hx (fun i => z.1 (eS i).val,z.2)
          (Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨hz,hs⟩,rfl⟩)
        rw [a4fac67_dot S eS z.1 x hs]
        exact hh
      · have ht' : ∀ j ∉ Sᶜ, z.1 j = 0 := by simpa using ht
        have hh := hy (fun i => z.1 (eT i).val,z.2)
          (Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨hz,ht'⟩,rfl⟩)
        rw [a4fac67_dot Sᶜ eT z.1 x ht']
        exact hh
  have hg : ∀ j, pp.gamma (e j) = p.gamma j := by
    intro j
    obtain ⟨k,rfl⟩ := e.symm.surjective j
    simp only [Equiv.apply_symm_apply]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp [pp,Piece.prod,pS,a4fac67_piece,hel]
    · simp [pp,Piece.prod,pT,a4fac67_piece,her]
  have hside : ∀ j, boxSide (a+b) pp.lo pp.hi (e j) = boxSide d p.lo p.hi j := by
    intro j
    obtain ⟨k,rfl⟩ := e.symm.surjective j
    simp only [Equiv.apply_symm_apply]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp [pp,Piece.prod,pS,a4fac67_piece,boxSide,hel]
    · simp [pp,Piece.prod,pT,a4fac67_piece,boxSide,her]
  have hv : boxVol (a+b) pp.lo pp.hi = boxVol d p.lo p.hi := by
    unfold boxVol
    rw [← e.prod_comp (fun j => boxSide (a+b) pp.lo pp.hi j)]
    simp_rw [hside]
  exact a4c67_pull e p pp hpoly hg hv (a4c67_prod pS pT hSbp hTbp)

private lemma a4n67_step (d nlong A : ℕ) (hn : 0 < nlong)
    (ih : ∀ n < d, ∀ l m A, ∃ C, 1 ≤ C ∧ ∀ p : Piece n,
      p.A = A → p.nLong = l → p.nMix = m →
      (∀ j, p.lo j ≤ p.hi j) → a4f67_BP p C) :
    ∃ C, 1 ≤ C ∧ ∀ p : Piece d, p.A = A → p.nLong = nlong → p.nMix = 0 →
      (∀ j, p.lo j ≤ p.hi j) → a4f67_BP p C := by
  classical
  obtain ⟨C,hC,huniform⟩ := a4c67_uniform d A ih
  refine ⟨C*C+2*C+1,by omega,?_⟩
  intro p hA hl hm hJ
  by_cases hne : (polyPZ d p.W).Nonempty
  · obtain ⟨x,hx⟩ := hne
    have he : p.shortCoordsᶜ = p.longCoords := by
      ext j
      simp [Piece.shortCoords,Piece.longCoords]
    have hlong : p.longCoords.Nonempty := Finset.card_pos.mp (by
      change 0 < p.nLong
      omega)
    have hcompl : p.shortCoordsᶜ.Nonempty := by rwa [he]
    exact a4s67_split p p.shortCoords p.shortCoords_nonempty hcompl
      (a4fac67_nomix_separation p hm) x hx hJ C
      (fun n hn p' hp hj => huniform n hn p' (hp.trans hA) hj)
  · have hempty : polyPZ d p.W = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨0,Fin.elim0,Fin.elim0,Fin.elim0,by omega,?_,
      (fun m => Fin.elim0 m),(fun m => Fin.elim0 m),
      (fun m => Fin.elim0 m),(fun m => Fin.elim0 m)⟩
    refine ⟨(fun m => Fin.elim0 m),(fun m => Fin.elim0 m),?_⟩
    simp [hempty]

/-- **Proposition (decomposition of pieces).**
For all `d`, `n_long`, `n_mix`, `A` there is `C = C(d, n_long, n_mix, A)` such that every
piece `(W, J, Q, A)` of index `(d, n_long, n_mix)` has a decomposition by at most `C`
transitions `x = u_m + Φ_m y` of size at most `C` to pieces `(W_m, J_m, Q_m, A_m)` with
`A_m ≤ C`, `vol(J_m) ≤ C vol(J)`, and `J_m` `C`-balanced with respect to `W_m`. -/
theorem prop_pieces (d nlong nmix A : ℕ) :
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
          ∀ m, IsBalancedWrt d C (q m).W (q m).lo (q m).hi := by
  have h : ∀ d nlong nmix A : ℕ,
    ∃ C : ℕ, 1 ≤ C ∧ ∀ p : Piece d, p.A = A → p.nLong = nlong → p.nMix = nmix →
      (∀ j, p.lo j ≤ p.hi j) → a4f67_BP p C := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ihd =>
      intro nlong
      induction nlong using Nat.strong_induction_on with
      | h nlong ihn =>
        intro nmix
        induction nmix using Nat.strong_induction_on with
        | h nmix ihm =>
          intro A
          by_cases hn : nlong = 0
          · refine ⟨A+1,by omega,?_⟩
            intro p hA hl hm hJ
            have hbal : ∀ i j, (constraintGraph d p.W).Reachable i j →
                p.side i ≤ p.A * p.side j := by
              intro i j hij
              have he : p.longCoords = ∅ := Finset.card_eq_zero.mp (hl.trans hn)
              have hi : i ∉ p.longCoords := by rw [he]; simp
              have hs : p.side i ≤ p.A*p.minSide := by
                simpa [Piece.longCoords] using hi
              exact hs.trans (Nat.mul_le_mul_left _
                (Finset.inf'_le p.side (Finset.mem_univ j)))
            simpa only [a4f67_BP,hA] using a4f67_identity p hbal
          · by_cases hm : nmix = 0
            · subst nmix
              exact a4n67_step d nlong A (by omega) ihd
            · apply a4f67_mixed d nlong nmix A (by omega)
              intro l m B hlt
              rcases hlt with hl | ⟨rfl,hm⟩
              · exact ihn l hl m B
              · exact ihm m hm B
  exact h d nlong nmix A
private def a4fixed20261014_BP {d : ℕ} (p : Piece d) (C : ℕ) : Prop :=
  ∃ (M : ℕ) (q : Fin M → Piece d) (u : Fin M → Fin d → ℤ)
    (Φ : Fin M → Matrix (Fin d) (Fin d) ℤ),
    M ≤ C ∧ IsDecomposition p q u Φ ∧
    (∀ m, transitionSize (Φ m) ≤ C) ∧ (∀ m, (q m).A ≤ C) ∧
    (∀ m, boxVol d (q m).lo (q m).hi ≤ C * boxVol d p.lo p.hi) ∧
    ∀ m, IsBalancedWrt d C (q m).W (q m).lo (q m).hi

private lemma a4fixed20261014_uniform (d A : ℕ) :
    ∃ C, 1 ≤ C ∧ ∀ p : Piece d, p.A ≤ A →
      (∀ j, p.lo j ≤ p.hi j) → a4fixed20261014_BP p C := by
  classical
  have hex (t : Fin (A+1) × Fin (d+1) × Fin (A+1)) :=
    prop_pieces d t.2.1.val t.2.2.val t.1.val
  choose C hC hp using hex
  let B := Finset.univ.sup C + 1
  refine ⟨B, by dsimp [B]; omega, ?_⟩
  intro p hA hJ
  let t : Fin (A+1) × Fin (d+1) × Fin (A+1) :=
    (⟨p.A, by omega⟩, ⟨p.nLong, by have := p.nLong_lt_dim; omega⟩,
      ⟨p.nMix, by have := p.nMix_le_A; omega⟩)
  have hCB : C t ≤ B :=
    (Finset.le_sup (Finset.mem_univ t)).trans (Nat.le_add_right _ 1)
  obtain ⟨M,q,u,Φ,hM,hd,hs,ha,hv,hb⟩ := hp t p rfl rfl rfl hJ
  refine ⟨M,q,u,Φ,hM.trans hCB,hd,fun m => (hs m).trans hCB,
    fun m => (ha m).trans hCB,
    fun m => (hv m).trans (Nat.mul_le_mul_right _ hCB),?_⟩
  intro m
  obtain ⟨hk,hc,hw,hbal⟩ := hb m
  exact ⟨hk,by dsimp [B]; omega,hw,fun i j hij =>
    (hbal i j hij).trans (Nat.mul_le_mul_right _ hCB)⟩

private lemma a4fixed20261014_len_max {d : ℕ} (p : Piece d) (a : Fin d → ℤ)
    (q : Fin d) (hq : q ∈ vecSupport a)
    (hm : ∀ j ∈ vecSupport a, p.side j ≤ p.side q)
    (hpos : 1 ≤ p.side q) : boxLen d a p.lo p.hi = p.side q := by
  apply le_antisymm
  · apply max_le hpos
    exact Finset.sup_le (fun j hj => hm j hj)
  · exact (Finset.le_sup (f := p.side) hq).trans (le_max_right _ _)

private lemma a4fixed20261014_section_vol {d : ℕ} (p t : Piece d) (q : Fin d)
    (hq : t.side q = 1)
    (hs : ∀ j, j ≠ q → t.side j ≤ 3 * p.side j) :
    boxVol d t.lo t.hi * p.side q ≤ 3^d * boxVol d p.lo p.hi := by
  classical
  have he : (∏ j, t.side j) = ∏ j ∈ Finset.univ.erase q, t.side j := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ q), hq, mul_one]
  change (∏ j, t.side j) * p.side q ≤ 3^d * ∏ j, p.side j
  rw [he]
  calc
    _ ≤ (∏ j ∈ Finset.univ.erase q, 3*p.side j) * p.side q :=
      Nat.mul_le_mul_right _
        (Finset.prod_le_prod (fun j hj => hs j (Finset.ne_of_mem_erase hj)))
    _ = 3^(d-1) * ∏ j, p.side j := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_univ q)]
      simp only [Finset.card_univ, Fintype.card_fin]
      rw [mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ q)]
    _ ≤ _ :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))

private lemma a4fixed20261014_short_stage (d A : ℕ) (hA : 1 ≤ A) :
    ∃ C, 1 ≤ C ∧ ∀ p : Piece d, p.A ≤ A →
      (∀ j, p.lo j ≤ p.hi j) → (∀ z ∈ p.W, z.1 ≠ 0) →
      ∃ (M : ℕ) (q : Fin M → Piece d) (u : Fin M → Fin d → ℤ)
        (Φ : Fin M → Matrix (Fin d) (Fin d) ℤ),
        M ≤ C ∧ IsDecomposition p q u Φ ∧
        (∀ m, transitionSize (Φ m) ≤ C) ∧ (∀ m, (q m).A ≤ C) ∧
        (∀ m j, (q m).lo j ≤ (q m).hi j) ∧
        (∀ m, boxVol d (q m).lo (q m).hi ≤ 3^d * boxVol d p.lo p.hi) ∧
        ∀ w b, (w,b) ∈ p.W → (-w,-b) ∈ p.W → ∀ m,
          boxVol d (q m).lo (q m).hi * boxLen d w p.lo p.hi ≤
            3^d * boxVol d p.lo p.hi := by
  classical
  obtain ⟨C,hC,hshort⟩ := lem_short_coordinate A hA
  refine ⟨C+A+1,by omega,?_⟩
  intro p hp hJ hw
  have hside (j : Fin d) : 1 ≤ p.side j :=
    Finset.card_pos.mpr ⟨p.lo j,Finset.mem_Icc.mpr ⟨le_rfl,hJ j⟩⟩
  let E := p.W.filter (fun z => (-z.1,-z.2) ∈ p.W)
  by_cases hE : E.Nonempty
  · obtain ⟨z,hz,hmax⟩ := Finset.exists_max_image E
      (fun z => boxLen d z.1 p.lo p.hi) hE
    obtain ⟨hzW,hzneg⟩ := Finset.mem_filter.mp hz
    have hsupp : (vecSupport z.1).Nonempty := by
      by_contra hn
      apply hw z hzW
      funext j
      by_contra hj
      exact hn ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
    obtain ⟨qc,hqc,hqmax⟩ := Finset.exists_max_image (vecSupport z.1) p.side hsupp
    have hlen := a4fixed20261014_len_max p z.1 qc hqc hqmax (hside qc)
    have hvar : ∀ x ∈ polyPZ d p.W, ∀ y ∈ polyPZ d p.W,
        |∑ j, z.1 j*(x j-y j)| ≤ (A : ℤ)*1 := by
      intro x hx y hy
      have hx1 := hx z hzW
      have hx2 := hx (-z.1,-z.2) hzneg
      have hy1 := hy z hzW
      have hy2 := hy (-z.1,-z.2) hzneg
      simp only [Pi.neg_apply,neg_mul,Finset.sum_neg_distrib] at hx2 hy2
      rw [show (∑ j, z.1 j*(x j-y j)) =
        (∑ j,z.1 j*x j)-(∑ j,z.1 j*y j) by
          simp [mul_sub,Finset.sum_sub_distrib]]
      have he : (∑ j,z.1 j*x j)-(∑ j,z.1 j*y j) = 0 := by linarith
      rw [he,abs_zero]
      positivity
    have hl1 : (∑ j, |z.1 j|) ≤ (A : ℤ) :=
      (l1_le_constraintRho d p.W z hzW).trans
        (by exact_mod_cast p.rho_le_A.trans hp)
    have hmin : 1 ≤ p.minSide := by
      apply Finset.le_inf'
      intro j hj
      exact hside j
    obtain ⟨M,u,D,q,R',hMC,hR'C,hdec,_hinj,hDC,hqR',hg,hqcside,hother,hout⟩ :=
      hshort d p hp hJ 1 (by omega) hmin z.1 (hw z hzW) hl1
        hvar qc hqc hqmax
    have hqC (m : Fin M) : (q m).A ≤ C := by
      rw [hqR' m]
      exact hR'C
    have hsect (m : Fin M) : boxVol d (q m).lo (q m).hi *
        boxLen d z.1 p.lo p.hi ≤ 3^d * boxVol d p.lo p.hi := by
      rw [hlen]
      exact a4fixed20261014_section_vol p (q m) qc (hqcside m)
        (fun j hj => (hother m j hj).2)
    have hlenpos : 1 ≤ boxLen d z.1 p.lo p.hi := le_max_left _ _
    refine ⟨M,q,u,fun _ => D,by omega,hdec,fun m => hDC.trans (by omega),
      fun m => (hqC m).trans (by omega),?_,?_,?_⟩
    · intro m j
      have hpos : 1 ≤ (q m).side j := by
        by_cases hj : j = qc
        · subst j; simpa only [hqcside] using (le_refl 1)
        · exact (hside j).trans (hother m j hj).1
      obtain ⟨x,hx⟩ := Finset.card_pos.mp
        (show 0 < (Finset.Icc ((q m).lo j) ((q m).hi j)).card from by
          change 0 < (q m).side j; omega)
      exact (Finset.mem_Icc.mp hx).1.trans (Finset.mem_Icc.mp hx).2
    · intro m
      exact (by nlinarith [hsect m])
    · intro w b hw1 hw2 m
      have hh := hmax (w,b) (Finset.mem_filter.mpr ⟨hw1,hw2⟩)
      exact (Nat.mul_le_mul_left _ hh).trans (hsect m)
  · refine ⟨1,fun _ => p,fun _ => 0,fun _ => 1,by omega,?_,?_,
      fun _ => hp.trans (by omega),fun _ => hJ,?_,?_⟩
    · refine ⟨fun _ => ⟨by simp,by simpa [pieceAffineImage],
        by intro y; simp⟩,?_,?_⟩
      · intro m m' hne
        have he : m=m' := Subsingleton.elim _ _
        exact (hne he).elim
      · ext x
        simp [pieceAffineImage]
    · intro m
      apply (matInftyNorm_le_iff _ _).2
      intro i j
      simp only [Matrix.one_apply]
      split_ifs <;> norm_num <;> omega
    · intro m
      exact Nat.le_mul_of_pos_left _ (by positivity)
    · intro w b hw1 hw2 m
      exact (hE ⟨(w,b),Finset.mem_filter.mpr ⟨hw1,hw2⟩⟩).elim

private lemma a4fixed20261014_full (d A : ℕ) (hA : 1 ≤ A) :
    ∃ C, 1 ≤ C ∧ ∀ p : Piece d, p.A ≤ A →
      (∀ j, p.lo j ≤ p.hi j) → (∀ z ∈ p.W, z.1 ≠ 0) →
      ∃ (M : ℕ) (q : Fin M → Piece d) (u : Fin M → Fin d → ℤ)
        (Φ : Fin M → Matrix (Fin d) (Fin d) ℤ),
        M ≤ C ∧ IsDecomposition p q u Φ ∧
        (∀ m, transitionSize (Φ m) ≤ C) ∧ (∀ m, (q m).A ≤ C) ∧
        (∀ m, boxVol d (q m).lo (q m).hi ≤ C * boxVol d p.lo p.hi) ∧
        (∀ m, IsBalancedWrt d C (q m).W (q m).lo (q m).hi) ∧
        ∀ w b, (w,b) ∈ p.W → (-w,-b) ∈ p.W → ∀ m,
          boxVol d (q m).lo (q m).hi * boxLen d w p.lo p.hi ≤
            C * boxVol d p.lo p.hi := by
  classical
  obtain ⟨S,hS,hs⟩ := a4fixed20261014_short_stage d A hA
  obtain ⟨B,hB,hb⟩ := a4fixed20261014_uniform d S
  let C := S*B+d*S*B+B*3^d+B+1
  have hBC : B ≤ C := by dsimp [C]; omega
  have hVC : B*3^d ≤ C := by dsimp [C]; omega
  refine ⟨C,by dsimp [C]; omega,?_⟩
  intro p hp hJ hw
  obtain ⟨M,q,u,Φ,hM,hdec,hΦ,hq,hqJ,hvol,hsect⟩ := hs p hp hJ hw
  have hex (m : Fin M) := hb (q m) (hq m) (hqJ m)
  choose N t v Ψ hN ht hΨ htA htvol htbal using hex
  let e := sigmaPieceIndexEquiv N
  let t' := fun z : Fin (∑ m,N m) => t (e.symm z).1 (e.symm z).2
  let v' := fun z : Fin (∑ m,N m) =>
    u (e.symm z).1 + Φ (e.symm z).1 *ᵥ v (e.symm z).1 (e.symm z).2
  let Ψ' := fun z : Fin (∑ m,N m) =>
    Φ (e.symm z).1 * Ψ (e.symm z).1 (e.symm z).2
  have htotal : (∑ m,N m) ≤ S*B := by
    calc
      _ ≤ ∑ _m : Fin M, B := Finset.sum_le_sum (fun m _ => hN m)
      _ = M*B := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hM
  have hcomp : IsDecomposition p t' v' Ψ' := hdec.comp N t v Ψ ht
  have hv (z : Fin (∑ m,N m)) : boxVol d (t' z).lo (t' z).hi ≤
      B * boxVol d (q (e.symm z).1).lo (q (e.symm z).1).hi := htvol _ _
  refine ⟨∑ m,N m,t',v',Ψ',htotal.trans (by dsimp [C]; omega),hcomp,?_,
    fun z => (htA _ _).trans hBC,?_,?_,?_⟩
  · intro z
    apply (transitionSize_mul_le _ _).trans
    apply (Nat.mul_le_mul (Nat.mul_le_mul_left d (hΦ _)) (hΨ _ _)).trans
    dsimp [C]
    omega
  · intro z
    exact (hv z).trans ((Nat.mul_le_mul_left B (hvol _)).trans
      (by simpa only [Nat.mul_assoc] using
        Nat.mul_le_mul_right (boxVol d p.lo p.hi) hVC))
  · intro z
    obtain ⟨hd,hB,hw,hbal⟩ := htbal (e.symm z).1 (e.symm z).2
    exact ⟨hd,by dsimp [C]; omega,hw,fun i j hij =>
      (hbal i j hij).trans (Nat.mul_le_mul_right _ hBC)⟩
  · intro w b hw1 hw2 z
    calc
      _ ≤ (B * boxVol d (q (e.symm z).1).lo (q (e.symm z).1).hi) *
          boxLen d w p.lo p.hi :=
        Nat.mul_le_mul_right _ (hv z)
      _ = B * (boxVol d (q (e.symm z).1).lo (q (e.symm z).1).hi *
          boxLen d w p.lo p.hi) := by ring
      _ ≤ B * (3^d * boxVol d p.lo p.hi) :=
        Nat.mul_le_mul_left _ (hsect w b hw1 hw2 _)
      _ ≤ _ := by
        simpa only [Nat.mul_assoc] using
          Nat.mul_le_mul_right (boxVol d p.lo p.hi) hVC

private lemma a4fixed20261014_diagonal {d : ℕ} {p p' : Piece d}
    {u : Fin d → ℤ} {Φ : Matrix (Fin d) (Fin d) ℤ}
    (h : IsTransition p p' u Φ) :
    Φᵀ * Matrix.diagonal (fun t => (p.gamma t : ℤ)) * Φ =
      Matrix.diagonal (fun t => (p'.gamma t : ℤ)) := by
  classical
  have hsingle (i : Fin d) :
      (∑ t, (p.gamma t : ℤ) * Φ t i ^ 2) = (p'.gamma i : ℤ) := by
    have he := h.quad_eq (Pi.single i 1)
    rw [Matrix.mulVec_single_one] at he
    simpa [Piece.quad, Pi.single_apply, mul_ite] using he.symm
  have hentry (i j : Fin d) :
      (Φᵀ * Matrix.diagonal (fun t => (p.gamma t : ℤ)) * Φ) i j =
        ∑ t, (p.gamma t : ℤ) * Φ t i * Φ t j := by
    rw [Matrix.mul_mul_apply]
    simp only [Matrix.transpose_apply, Matrix.mulVec_diagonal, dotProduct]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  ext i j
  rw [hentry]
  by_cases hij : i = j
  · subst j
    simpa [Matrix.diagonal_apply, pow_two, mul_assoc] using hsingle i
  · have he := h.quad_eq ((Pi.single i 1 : Fin d → ℤ) + Pi.single j 1)
    have hleft : p'.quad ((Pi.single i 1 : Fin d → ℤ) + Pi.single j 1) =
        (p'.gamma i : ℤ) + (p'.gamma j : ℤ) := by
      have hterm (t : Fin d) :
          (p'.gamma t : ℤ) *
              ((Pi.single i 1 + Pi.single j 1 : Fin d → ℤ) t)^2 =
            (if t = i then (p'.gamma i : ℤ) else 0) +
              (if t = j then (p'.gamma j : ℤ) else 0) := by
        by_cases hti : t = i <;> by_cases htj : t = j <;>
          simp_all [Pi.single_apply]
      unfold Piece.quad
      simp_rw [hterm]
      simp [Finset.sum_add_distrib]
    rw [hleft, Matrix.mulVec_add, Matrix.mulVec_single_one,
      Matrix.mulVec_single_one] at he
    have hexpand : p.quad (Φ.col i + Φ.col j) =
        (∑ t, (p.gamma t : ℤ) * Φ t i ^ 2) +
        (∑ t, (p.gamma t : ℤ) * Φ t j ^ 2) +
        2 * (∑ t, (p.gamma t : ℤ) * Φ t i * Φ t j) := by
      simp only [Piece.quad, Pi.add_apply, Matrix.col_apply]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    rw [hexpand, hsingle, hsingle] at he
    simp only [Matrix.diagonal_apply, if_neg hij]
    omega

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

set_option maxHeartbeats 2000000 in
theorem thm_decomp (k V h r : ℕ) (hk : 1 ≤ k) (hV : 1 ≤ V) (hh : 1 ≤ h) :
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
            ∀ m, boxVol k (lo' m) (hi' m) * boxLen k w₀ lo hi ≤ R * boxVol k lo hi := by
  classical
  let A := k+r+V+h
  have hA : 1 ≤ A := by dsimp [A]; omega
  obtain ⟨R,hR,hdecomp⟩ := a4fixed20261014_full k A hA
  refine ⟨R,hR,?_⟩
  intro c hc hch W hW hWV hfinite hnonempty lo hi hbox hmin hmax
  have hJ (j : Fin k) : lo j ≤ hi j := by
    obtain ⟨x,hx⟩ := hnonempty
    have hj := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (hbox hx) j)
    exact hj.1.trans hj.2
  let p : Piece k :=
    { W := W, lo := lo, hi := hi, gamma := c, A := A
      one_le_dim := hk
      one_le_gamma := hc
      one_le_A := hA
      poly_subset_box := hbox
      dim_le_A := by dsimp [A]; omega
      rho_le_A := by
        apply (constraintRho_le_iff _ _ _).2
        refine ⟨hW.trans (by dsimp [A]; omega),?_⟩
        intro z hz
        exact (hWV z hz).2.trans (by dsimp [A]; omega)
      gamma_le_A := fun j => (hch j).trans (by dsimp [A]; omega) }
  have hw (z) (hz : z ∈ p.W) : z.1 ≠ 0 := by
    intro he
    have ht := (hWV z hz).1
    simp [he] at ht
  obtain ⟨M,q,u,Φ,hM,hd,hΦ,hq,hvol,hbal,hsect⟩ := hdecomp p le_rfl hJ hw
  have hdiag (m : Fin M) :
      (Φ m)ᵀ * Matrix.diagonal (fun j => (c j : ℤ)) * Φ m =
        Matrix.diagonal (fun j => ((q m).gamma j : ℤ)) :=
    a4fixed20261014_diagonal (hd.transitions m)
  have hdata : BalancedDecompData k R c W lo hi M u Φ
      (fun m => (q m).W) (fun m => (q m).lo) (fun m => (q m).hi) := by
    refine ⟨hM,fun m => (hd.transitions m).det_ne_zero,
      fun m => (hd.transitions m).image_subset,hd.pieces_disjoint,hd.iUnion_eq,
      fun m => (hbal m).2.2.1,hbal,fun m => (q m).poly_subset_box,hvol,?_,hΦ,?_,
      fun m => (q m).rho_le_A.trans (hq m)⟩
    · intro m
      rw [hdiag]
      exact Matrix.isDiag_diagonal _
    · intro m
      rw [hdiag]
      apply (matInftyNorm_le_iff _ _).2
      intro i j
      by_cases hij : i=j
      · subst j
        simp only [Matrix.diagonal_apply,if_pos rfl,Int.abs_natCast]
        exact_mod_cast ((q m).gamma_le_A i).trans (hq m)
      · simp [Matrix.diagonal_apply,hij]
  refine ⟨⟨M,u,Φ,fun m => (q m).W,fun m => (q m).lo,fun m => (q m).hi,hdata⟩,?_⟩
  intro w b hw1 hw2
  exact ⟨M,u,Φ,fun m => (q m).W,fun m => (q m).lo,fun m => (q m).hi,
    hdata,hsect w b hw1 hw2⟩
open scoped Matrix

private lemma a4boxOct14_mem {d : ℕ} (p : Piece d) (x : Fin d → ℤ) :
    x ∈ polyBoxZ d p.W p.lo p.hi ↔ x ∈ polyPZ d p.W := by
  exact ⟨fun hx => (Finset.mem_filter.mp hx).2,
    fun hx => Finset.mem_filter.mpr ⟨p.poly_subset_box hx,hx⟩⟩

private lemma a4boxOct14_append_v2 {a b : ℕ} (p : Piece a) (q : Piece b) (α : ℝ)
    (θ : Fin a → ℝ) (η : Fin b → ℝ) :
    quadExpSum (a+b) α (Fin.append p.gamma q.gamma) (Fin.append θ η)
      (polyBoxZ (a+b) (p.prod q).W (p.prod q).lo (p.prod q).hi) =
    quadExpSum a α p.gamma θ (polyBoxZ a p.W p.lo p.hi) *
      quadExpSum b α q.gamma η (polyBoxZ b q.W q.lo q.hi) := by
  classical
  have hmem (x : Fin a → ℤ) (y : Fin b → ℤ) :
      Fin.append x y ∈ polyBoxZ (a+b) (p.prod q).W (p.prod q).lo (p.prod q).hi ↔
      x ∈ polyBoxZ a p.W p.lo p.hi ∧ y ∈ polyBoxZ b q.W q.lo q.hi := by
    rw [a4boxOct14_mem, a4boxOct14_mem, a4boxOct14_mem]
    change Fin.append x y ∈ polyPZ (a+b) (oplusConstraints a b p.W q.W) ↔ _
    rw [polyPZ_oplusConstraints]
    change (leftPart a b (Fin.append x y) ∈ polyPZ a p.W ∧
      rightPart a b (Fin.append x y) ∈ polyPZ b q.W) ↔ _
    rw [agent4_left_append,agent4_right_append]
  unfold quadExpSum
  rw [Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  symm
  apply Finset.sum_bij (fun z _ => Fin.append z.1 z.2)
  · intro z hz
    exact (hmem _ _).2 (Finset.mem_product.mp hz)
  · intro z hz z' hz' he
    exact Prod.ext (by simpa only [agent4_left_append] using congrArg (leftPart a b) he)
      (by simpa only [agent4_right_append] using congrArg (rightPart a b) he)
  · intro z hz
    have he : Fin.append (leftPart a b z) (rightPart a b z) = z := by
      funext j
      exact Fin.addCases (fun i => by simp [leftPart]) (fun i => by simp [rightPart]) j
    refine ⟨(leftPart a b z,rightPart a b z),Finset.mem_product.mpr ?_,he⟩
    apply (hmem _ _).1
    rwa [he]
  · intro z hz
    rw [← onb_exp_add]
    congr 1
    rw [Fin.sum_univ_add,Fin.sum_univ_add]
    simp only [Fin.append_left,Fin.append_right]
    ring

private lemma a4boxOct14_reindex_v2 {d n : ℕ} (e : Fin d ≃ Fin n) (p : Piece d) (q : Piece n)
    (hp : ∀ x : Fin d → ℤ, x ∈ polyPZ d p.W ↔ (x ∘ e.symm) ∈ polyPZ n q.W)
    (hg : ∀ j, q.gamma (e j) = p.gamma j)
    (α : ℝ) (θ : Fin d → ℝ) (η : Fin n → ℝ) (hθ : ∀ j, η (e j) = θ j) :
    quadExpSum d α p.gamma θ (polyBoxZ d p.W p.lo p.hi) =
      quadExpSum n α q.gamma η (polyBoxZ n q.W q.lo q.hi) := by
  classical
  unfold quadExpSum
  apply Finset.sum_bij (fun x _ => x ∘ e.symm)
  · intro x hx
    exact (a4boxOct14_mem q _).2 ((hp x).1 ((a4boxOct14_mem p _).1 hx))
  · intro x hx y hy he
    funext j
    simpa only [Function.comp_apply,Equiv.symm_apply_apply] using congrFun he (e j)
  · intro y hy
    refine ⟨y ∘ e,?_,?_⟩
    · apply (a4boxOct14_mem p _).2
      apply (hp _).2
      simpa [Function.comp_def] using (a4boxOct14_mem q _).1 hy
    · funext j
      simp
  · intro x hx
    congr 1
    simp only [Function.comp_apply]
    rw [← e.sum_comp (fun j => (q.gamma j : ℝ) * (x (e.symm j) : ℝ)^2),
      ← e.sum_comp (fun j => η j * (x (e.symm j) : ℝ))]
    simp only [hg,hθ,Function.comp_apply,Equiv.symm_apply_apply]

private lemma a4boxOct14_restrict_bal_v2 {d n R : ℕ} (p : Piece d)
    (S : Finset (Fin d)) (e : Fin n ≃ ↥S)
    (hn : 1 ≤ n) (hnA : n ≤ p.A) (x₀ : Fin d → ℤ)
    (hx₀ : x₀ ∈ polyPZ d p.W)
    (hsep : ∀ z ∈ p.W, (∀ j ∉ S, z.1 j = 0) ∨ (∀ j ∈ S, z.1 j = 0))
    (hb : IsBalancedWrt d R p.W p.lo p.hi) :
    IsBalancedWrt n R (a4fac67_piece p S e hn hnA x₀ hx₀ hsep).W
      (a4fac67_piece p S e hn hnA x₀ hx₀ hsep).lo
      (a4fac67_piece p S e hn hnA x₀ hx₀ hsep).hi := by
  classical
  obtain ⟨hd,hR,hzero,hbal⟩ := (isBalancedWrt_iff_reachable _ _ _ _ _).1 hb
  let f : constraintGraph n (a4fac67_W p S e) →g constraintGraph d p.W :=
    { toFun := fun i => (e i).val
      map_rel' := by
        intro i j hij
        obtain ⟨hne,z,hz,hmul⟩ := (constraintGraph_adj_iff _ _ _ _).1 hij
        obtain ⟨z,hzf,rfl⟩ := Finset.mem_image.mp hz
        exact (constraintGraph_adj_iff _ _ _ _).2
          ⟨fun he => hne (e.injective (Subtype.ext he)),z,
            (Finset.mem_filter.mp hzf).1,hmul⟩ }
  apply (isBalancedWrt_iff_reachable _ _ _ _ _).2
  refine ⟨hn,hR,?_,?_⟩
  · intro z hz
    obtain ⟨z,hzf,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hz,hout⟩ := Finset.mem_filter.mp hzf
    intro he
    apply hzero z hz
    funext j
    change z.1 j = 0
    by_cases hj : j ∈ S
    · obtain ⟨i,hi⟩ := e.surjective ⟨j,hj⟩
      have hh := congrFun he i
      change z.1 (e i).val = 0 at hh
      simpa only [hi] using hh
    · exact hout j hj
  · intro i j hij
    exact hbal (e i).val (e j).val (hij.map f)

private lemma a4boxOct14_split_data {d : ℕ} (p : Piece d) (S : Finset (Fin d))
    (hS : S.Nonempty) (hT : Sᶜ.Nonempty)
    (hsep : ∀ z ∈ p.W, (∀ j ∉ S, z.1 j = 0) ∨ (∀ j ∈ S, z.1 j = 0))
    (x₀ : Fin d → ℤ) (hx₀ : x₀ ∈ polyPZ d p.W) :
    ∃ (a b : ℕ) (pS : Piece a) (pT : Piece b) (e : Fin d ≃ Fin (a+b)),
      a < d ∧ b < d ∧ a+b=d ∧ pS.A=p.A ∧ pT.A=p.A ∧
      (∀ x : Fin d → ℤ, x ∈ polyPZ d p.W ↔ (x ∘ e.symm) ∈ polyPZ (a+b) (pS.prod pT).W) ∧
      (∀ j, (pS.prod pT).gamma (e j) = p.gamma j) ∧
      boxVol (a+b) (pS.prod pT).lo (pS.prod pT).hi = boxVol d p.lo p.hi ∧
      (∀ R, IsBalancedWrt d R p.W p.lo p.hi →
        IsBalancedWrt a R pS.W pS.lo pS.hi ∧ IsBalancedWrt b R pT.W pT.lo pT.hi) := by
  classical
  let a := S.card
  let b := Sᶜ.card
  let eS : Fin a ≃ ↥S := (Finset.equivFin S).symm
  let eT : Fin b ≃ ↥Sᶜ := (Finset.equivFin Sᶜ).symm
  have ha : 1 ≤ a := Finset.card_pos.mpr hS
  have hbpos : 1 ≤ b := Finset.card_pos.mpr hT
  have hab : a+b=d := by
    have hs := Finset.card_le_univ S
    simp only [Fintype.card_fin] at hs
    dsimp [a,b]
    rw [Finset.card_compl,Fintype.card_fin]
    omega
  have hat : a < d := by omega
  have hbt : b < d := by omega
  have hsepT : ∀ z ∈ p.W,
      (∀ j ∉ Sᶜ, z.1 j = 0) ∨ (∀ j ∈ Sᶜ, z.1 j = 0) := by
    intro z hz
    have hh := hsep z hz
    simpa only [Finset.mem_compl, not_not] using hh.symm
  let pS := a4fac67_piece p S eS ha (hat.le.trans p.dim_le_A) x₀ hx₀ hsep
  let pT := a4fac67_piece p Sᶜ eT hbpos (hbt.le.trans p.dim_le_A) x₀ hx₀ hsepT
  let E : Fin a ⊕ Fin b ≃ Fin d :=
    { toFun := Sum.elim (fun i => (eS i).val) (fun i => (eT i).val)
      invFun := fun j => if hj : j ∈ S then Sum.inl (eS.symm ⟨j,hj⟩)
        else Sum.inr (eT.symm ⟨j,Finset.mem_compl.mpr hj⟩)
      left_inv := by
        intro j
        cases j with
        | inl j => simp [(eS j).property]
        | inr j => simp [Finset.mem_compl.mp (eT j).property]
      right_inv := by
        intro j
        dsimp only
        split_ifs <;> simp }
  let e : Fin d ≃ Fin (a+b) := E.symm.trans finSumFinEquiv
  have hel (j : Fin a) : e.symm (Fin.castAdd b j) = (eS j).val := by
    simp [e,E]
  have her (j : Fin b) : e.symm (Fin.natAdd a j) = (eT j).val := by
    simp [e,E]
  let pp := pS.prod pT
  have hpoly : ∀ x : Fin d → ℤ,
      x ∈ polyPZ d p.W ↔ (x ∘ e.symm) ∈ polyPZ (a+b) pp.W := by
    intro x
    change _ ↔ (x ∘ e.symm) ∈ polyPZ _ (oplusConstraints _ _ pS.W pT.W)
    rw [polyPZ_oplusConstraints]
    change _ ↔ leftPart a b (x ∘ e.symm) ∈ polyPZ a pS.W ∧
      rightPart a b (x ∘ e.symm) ∈ polyPZ b pT.W
    have hl : leftPart a b (x ∘ e.symm) = fun i => x (eS i).val := by
      funext j
      simp [leftPart,hel]
    have hr : rightPart a b (x ∘ e.symm) = fun i => x (eT i).val := by
      funext j
      simp [rightPart,her]
    rw [hl,hr]
    constructor
    · intro hx
      exact ⟨a4fac67_projection_mem p S eS x hx,
        a4fac67_projection_mem p Sᶜ eT x hx⟩
    · rintro ⟨hx,hy⟩ z hz
      rcases hsep z hz with hs | ht
      · have hh := hx (fun i => z.1 (eS i).val,z.2)
          (Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨hz,hs⟩,rfl⟩)
        rw [a4fac67_dot S eS z.1 x hs]
        exact hh
      · have ht' : ∀ j ∉ Sᶜ, z.1 j = 0 := by simpa using ht
        have hh := hy (fun i => z.1 (eT i).val,z.2)
          (Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨hz,ht'⟩,rfl⟩)
        rw [a4fac67_dot Sᶜ eT z.1 x ht']
        exact hh
  have hg : ∀ j, pp.gamma (e j) = p.gamma j := by
    intro j
    obtain ⟨k,rfl⟩ := e.symm.surjective j
    simp only [Equiv.apply_symm_apply]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp [pp,Piece.prod,pS,a4fac67_piece,hel]
    · simp [pp,Piece.prod,pT,a4fac67_piece,her]
  have hside : ∀ j, boxSide (a+b) pp.lo pp.hi (e j) = boxSide d p.lo p.hi j := by
    intro j
    obtain ⟨k,rfl⟩ := e.symm.surjective j
    simp only [Equiv.apply_symm_apply]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp [pp,Piece.prod,pS,a4fac67_piece,boxSide,hel]
    · simp [pp,Piece.prod,pT,a4fac67_piece,boxSide,her]
  have hv : boxVol (a+b) pp.lo pp.hi = boxVol d p.lo p.hi := by
    unfold boxVol
    rw [← e.prod_comp (fun j => boxSide (a+b) pp.lo pp.hi j)]
    simp_rw [hside]
  exact ⟨a,b,pS,pT,e,hat,hbt,hab,rfl,rfl,hpoly,hg,hv,
    fun R hb => ⟨a4boxOct14_restrict_bal_v2 p S eS ha (hat.le.trans p.dim_le_A) x₀ hx₀ hsep hb,
      a4boxOct14_restrict_bal_v2 p Sᶜ eT hbpos (hbt.le.trans p.dim_le_A) x₀ hx₀ hsepT hb⟩⟩

private lemma a4boxOct14_component_v2 (k R : ℕ) (α : ℝ) (B : ℝ) (hB : 1 ≤ B)
    (hG : ∀ d, d ≤ k → ∀ p : Piece d, p.A ≤ R →
      IsBalancedPair d R p.W p.lo p.hi → ∀ θ : Fin d → ℝ,
      ‖quadExpSum d α p.gamma θ (polyBoxZ d p.W p.lo p.hi)‖ ≤
        B * Real.sqrt (boxVol d p.lo p.hi)) :
    ∀ d, d ≤ k → ∀ p : Piece d, p.A ≤ R →
      IsBalancedWrt d R p.W p.lo p.hi → ∀ θ : Fin d → ℝ,
      ‖quadExpSum d α p.gamma θ (polyBoxZ d p.W p.lo p.hi)‖ ≤
        B^d * Real.sqrt (boxVol d p.lo p.hi) := by
  classical
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd p hp hb θ
    by_cases hne : (polyPZ d p.W).Nonempty
    swap
    · have he : polyBoxZ d p.W p.lo p.hi = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hne ⟨x,(a4boxOct14_mem p x).1 hx⟩
      simp only [he,quadExpSum,Finset.sum_empty,norm_zero]
      positivity
    obtain ⟨x₀,hx₀⟩ := hne
    by_cases hconnected : ∀ i j : Fin d, (constraintGraph d p.W).Reachable i j
    · have hpair : IsBalancedPair d R p.W p.lo p.hi := by
        refine ⟨p.card_W_le_A.trans hp,?_,?_⟩
        · intro z hz
          have hn := hb.2.2.1 z hz
          obtain ⟨j,hj⟩ : ∃ j, z.1 j ≠ 0 := by
            by_contra h
            apply hn
            funext j
            simpa using not_exists.mp h j
          exact ⟨(abs_pos.mpr hj).trans_le
            (Finset.single_le_sum (fun i _ => abs_nonneg (z.1 i)) (Finset.mem_univ j)),
            (l1_le_constraintRho d p.W z hz).trans (by exact_mod_cast p.rho_le_A.trans hp)⟩
        · intro i j
          exact hb.2.2.2 i j (SimpleGraph.ConnectedComponent.eq.mpr (hconnected i j))
      apply (hG d hd p hp hpair θ).trans
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      have hdpos := p.one_le_dim
      obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hdpos
      rw [hn,pow_add,pow_one]
      exact le_mul_of_one_le_right (by linarith) (one_le_pow₀ hB)
    · push Not at hconnected
      obtain ⟨q,q',hqq'⟩ := hconnected
      let S := Finset.univ.filter (fun j => (constraintGraph d p.W).Reachable q j)
      have hS : S.Nonempty := ⟨q,Finset.mem_filter.mpr ⟨Finset.mem_univ _,SimpleGraph.Reachable.refl q⟩⟩
      have hT : Sᶜ.Nonempty := ⟨q',by simpa [S] using hqq'⟩
      have hsep (z) (hz : z ∈ p.W) :
          (∀ j ∉ S, z.1 j = 0) ∨ (∀ j ∈ S, z.1 j = 0) := by
        by_cases hs : ∃ i ∈ S, z.1 i ≠ 0
        · left
          intro j hj
          by_contra hjz
          obtain ⟨i,hi,hiz⟩ := hs
          have hreach := (Finset.mem_filter.mp hi).2
          have hij : (constraintGraph d p.W).Reachable i j := by
            by_cases he : i = j
            · subst j
              exact SimpleGraph.Reachable.refl i
            · exact ((constraintGraph_adj_iff _ _ _ _).2 ⟨he,z,hz,mul_ne_zero hiz hjz⟩).reachable
          exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hreach.trans hij⟩)
        · right
          intro j hj
          by_contra hjz
          exact hs ⟨j,hj,hjz⟩
      obtain ⟨a,b,pS,pT,e,ha,hbt,hab,hAS,hAT,hpoly,hg,hv,hbal⟩ :=
        a4boxOct14_split_data p S hS hT hsep x₀ hx₀
      let η := θ ∘ e.symm
      let θS : Fin a → ℝ := fun j => η (Fin.castAdd b j)
      let θT : Fin b → ℝ := fun j => η (Fin.natAdd a j)
      have ht : ∀ j, Fin.append θS θT (e j) = θ j := by
        intro j
        have he : Fin.append θS θT = η := by
          funext t
          exact Fin.addCases (fun i => by simp [θS]) (fun i => by simp [θT]) t
        rw [he]
        simp [η]
      rw [a4boxOct14_reindex_v2 e p (pS.prod pT) hpoly hg α θ (Fin.append θS θT) ht]
      rw [show (pS.prod pT).gamma = Fin.append pS.gamma pT.gamma from rfl,
        a4boxOct14_append_v2,norm_mul]
      have hs := ih a ha (ha.le.trans hd) pS (hAS ▸ hp) (hbal R hb).1 θS
      have hts := ih b hbt (hbt.le.trans hd) pT (hAT ▸ hp) (hbal R hb).2 θT
      apply (mul_le_mul hs hts (norm_nonneg _) (by positivity)).trans_eq
      rw [show (B^a * Real.sqrt (boxVol a pS.lo pS.hi)) *
          (B^b * Real.sqrt (boxVol b pT.lo pT.hi)) =
          (B^a*B^b) * (Real.sqrt (boxVol a pS.lo pS.hi) * Real.sqrt (boxVol b pT.lo pT.hi)) by ring,
        ← pow_add,hab,← Real.sqrt_mul (by positivity),← Nat.cast_mul,← a4b67_vol,hv]

private lemma a4boxOct14_uniform (k R : ℕ) (hR : 1 ≤ R) (a : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ α : ℝ, Irrational α →
      (∀ i x, (GenContFract.of α).partDens.get? i = some x → x ≤ a) →
      ∀ p : Piece k, p.A ≤ R → IsBalancedWrt k R p.W p.lo p.hi →
      ∀ θ : Fin k → ℝ, ‖quadExpSum k α p.gamma θ (polyBoxZ k p.W p.lo p.hi)‖ ≤
        B * Real.sqrt (boxVol k p.lo p.hi) := by
  classical
  let Q := max R ⌈a⌉₊
  have hQ : 1 ≤ Q := hR.trans (le_max_left _ _)
  have haQ : a ≤ (Q : ℝ) := (Nat.le_ceil a).trans (by exact_mod_cast le_max_right R ⌈a⌉₊)
  have hex (d : Fin (k+1)) : ∃ C : ℝ, 0 < C ∧
      ∀ hd : 1 ≤ d.val, ∀ α : ℝ, Irrational α →
      (∀ i x, (GenContFract.of α).partDens.get? i = some x → x ≤ a) →
      ∀ p : Piece d.val, p.A ≤ Q → IsBalancedPair d.val Q p.W p.lo p.hi →
      ∀ θ, ‖quadExpSum d.val α p.gamma θ (polyBoxZ d.val p.W p.lo p.hi)‖ ≤
        C * Real.sqrt (boxVol d.val p.lo p.hi) := by
    by_cases hd : 1 ≤ d.val
    · obtain ⟨C,hC,hbound⟩ := thm_general d.val Q hd hQ
      refine ⟨C,hC,?_⟩
      intro hd' α hα hbp p hp hb θ
      by_cases hne : (polyPZ d.val p.W).Nonempty
      swap
      · have he : polyBoxZ d.val p.W p.lo p.hi=∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          exact hne ⟨x,(a4boxOct14_mem p x).1 hx⟩
        simp only [he,quadExpSum,Finset.sum_empty,norm_zero]
        positivity
      obtain ⟨x,hx⟩ := hne
      have hJ : ∀ j, p.lo j ≤ p.hi j := by
        intro j
        have hh := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (p.poly_subset_box hx) j)
        exact hh.1.trans hh.2
      exact hbound α hα (fun i x hx => (hbp i x hx).trans haQ)
        p.gamma p.one_le_gamma (fun j => (p.gamma_le_A j).trans hp)
        p.lo p.hi hJ p.W hb θ
    · exact ⟨1,by norm_num,fun hd' => False.elim (hd hd')⟩
  choose C hC hc using hex
  let B := (∑ d : Fin (k+1), C d)+1
  have hB : 1 ≤ B := by
    have hh : 0 ≤ ∑ d : Fin (k+1), C d := Finset.sum_nonneg (fun d _ => (hC d).le)
    dsimp [B]
    linarith
  refine ⟨B^k,one_le_pow₀ hB,?_⟩
  intro α hα hbp p hp hb θ
  apply a4boxOct14_component_v2 k Q α B hB ?_ k le_rfl p
    (hp.trans (le_max_left _ _)) ?_ θ
  · intro d hd p hp hbal θ
    let t : Fin (k+1) := ⟨d,by omega⟩
    have hh := hc t p.one_le_dim α hα hbp p hp hbal θ
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    have hle : C t ≤ ∑ d : Fin (k+1), C d :=
      Finset.single_le_sum (fun d _ => (hC d).le) (Finset.mem_univ t)
    dsimp [B]
    linarith
  · obtain ⟨hk,hR',hn,hbal⟩ := hb
    exact ⟨hk,hQ,hn,fun i j hij => (hbal i j hij).trans
      (Nat.mul_le_mul_right _ (le_max_left _ _))⟩

private lemma a4boxOct14_phase_piece_mem (d : ℕ) (p : Piece d) (x : Fin d → ℤ) :
    x ∈ polyBoxZ d p.W p.lo p.hi ↔ x ∈ polyPZ d p.W := by
  classical
  exact ⟨fun hx => (Finset.mem_filter.mp hx).2,
    fun hx => Finset.mem_filter.mpr ⟨p.poly_subset_box hx,hx⟩⟩

private lemma a4boxOct14_phase_decomp_sum {d M : ℕ} (p : Piece d)
    (q : Fin M → Piece d) (u : Fin M → Fin d → ℤ)
    (Φ : Fin M → Matrix (Fin d) (Fin d) ℤ)
    (h : IsDecomposition p q u Φ) (f : (Fin d → ℤ) → ℂ) :
    (∑ x ∈ polyBoxZ d p.W p.lo p.hi, f x) =
      ∑ m : Fin M, ∑ y ∈ polyBoxZ d (q m).W (q m).lo (q m).hi,
        f (u m + Φ m *ᵥ y) := by
  classical
  let S (m : Fin M) := polyBoxZ d (q m).W (q m).lo (q m).hi
  let F (m : Fin M) (y : Fin d → ℤ) := u m + Φ m *ᵥ y
  have hset : polyBoxZ d p.W p.lo p.hi =
      Finset.univ.biUnion (fun m => (S m).image (F m)) := by
    ext x
    rw [a4boxOct14_phase_piece_mem, h.iUnion_eq]
    simp only [Set.mem_iUnion, pieceAffineImage, Set.mem_image,
      Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨m, y, hy, he⟩
      exact ⟨m, y, (a4boxOct14_phase_piece_mem d (q m) y).2 hy, he⟩
    · rintro ⟨m, y, hy, he⟩
      exact ⟨m, y, (a4boxOct14_phase_piece_mem d (q m) y).1 hy, he⟩
  have hdis : ∀ m ∈ (Finset.univ : Finset (Fin M)),
      ∀ m' ∈ (Finset.univ : Finset (Fin M)), m ≠ m' →
        Disjoint ((S m).image (F m)) ((S m').image (F m')) := by
    intro m hm m' hm' hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', he'⟩ := Finset.mem_image.mp hx'
    exact Set.disjoint_left.mp (h.pieces_disjoint m m' hne)
      ⟨y, (a4boxOct14_phase_piece_mem d (q m) y).1 hy, he⟩
      ⟨y', (a4boxOct14_phase_piece_mem d (q m') y').1 hy', he'⟩
  rw [hset, Finset.sum_biUnion hdis]
  apply Finset.sum_congr rfl
  intro m hm
  exact Finset.sum_image (fun y hy z hz he =>
    mulVec_add_left_injective d (Φ m) (h.transitions m).det_ne_zero (u m) he)

private lemma a4boxOct14_phase_decomp_phase_bound_v4 {d M : ℕ} (p : Piece d)
    (q : Fin M → Piece d) (u : Fin M → Fin d → ℤ)
    (Φ : Fin M → Matrix (Fin d) (Fin d) ℤ)
    (h : IsDecomposition p q u Φ) (α : ℝ) (θ : Fin d → ℝ) :
    ∃ β : Fin M → Fin d → ℝ,
      ‖∑ x ∈ polyBoxZ d p.W p.lo p.hi,
        expTwoPiI (α * (p.quad x : ℝ) + ∑ j, θ j * (x j : ℝ))‖ ≤
      ∑ m : Fin M,
        ‖∑ y ∈ polyBoxZ d (q m).W (q m).lo (q m).hi,
          expTwoPiI (α * ((q m).quad y : ℝ) + ∑ j, β m j * (y j : ℝ))‖ := by
  classical
  have hex (m : Fin M) := (h.transitions m).exists_affine_correction
  choose a κ ha using hex
  let β (m : Fin M) (j : Fin d) : ℝ :=
    α * (a m j : ℝ) + ∑ i, θ i * (Φ m i j : ℝ)
  let K (m : Fin M) : ℝ :=
    α * (κ m : ℝ) + ∑ j, θ j * (u m j : ℝ)
  have hlin (m : Fin M) (y : Fin d → ℤ) :
      (∑ j, θ j * ((u m + Φ m *ᵥ y) j : ℝ)) =
        (∑ j, θ j * (u m j : ℝ)) +
          ∑ j, (∑ i, θ i * (Φ m i j : ℝ)) * (y j : ℝ) := by
    simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hphase (m : Fin M) (y : Fin d → ℤ) :
      expTwoPiI (α * (p.quad (u m + Φ m *ᵥ y) : ℝ) +
        ∑ j, θ j * ((u m + Φ m *ᵥ y) j : ℝ)) =
        expTwoPiI (K m) *
          expTwoPiI (α * ((q m).quad y : ℝ) +
            ∑ j, β m j * (y j : ℝ)) := by
    rw [← onb_exp_add]
    congr 1
    have hquad :
        (p.quad (u m + Φ m *ᵥ y) : ℝ) =
          ((q m).quad y : ℝ) + ((a m ⬝ᵥ y : ℤ) : ℝ) + (κ m : ℝ) := by
      exact_mod_cast ha m y
    rw [hquad, hlin]
    simp only [β, K, dotProduct, Int.cast_sum, Int.cast_mul,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    ring_nf
    simp only [Finset.mul_sum, mul_assoc]
    ring
  refine ⟨β, ?_⟩
  rw [a4boxOct14_phase_decomp_sum p q u Φ h]
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro m hm
  simp_rw [hphase]
  rw [← Finset.mul_sum, norm_mul,
    LocalizedFourierFinal.FourierMassBounds.exp_norm, one_mul]

private lemma a4boxOct14_decomp_bound {d M D : ℕ} (p : Piece d)
    (q : Fin M → Piece d) (u : Fin M → Fin d → ℤ)
    (Φ : Fin M → Matrix (Fin d) (Fin d) ℤ)
    (hdec : IsDecomposition p q u Φ) (hM : M ≤ D) (α : ℝ) (B T : ℝ)
    (hB : 0 ≤ B)
    (hvol : ∀ m, (boxVol d (q m).lo (q m).hi : ℝ) ≤ (D : ℝ)*T)
    (hbound : ∀ m θ, ‖quadExpSum d α (q m).gamma θ
      (polyBoxZ d (q m).W (q m).lo (q m).hi)‖ ≤ B*Real.sqrt (boxVol d (q m).lo (q m).hi))
    (θ : Fin d → ℝ) :
    ‖quadExpSum d α p.gamma θ (polyBoxZ d p.W p.lo p.hi)‖ ≤
      ((D : ℝ)*B*Real.sqrt D)*Real.sqrt T := by
  classical
  obtain ⟨β,hβ⟩ := a4boxOct14_phase_decomp_phase_bound_v4 p q u Φ hdec α θ
  have hβ' : ‖quadExpSum d α p.gamma θ (polyBoxZ d p.W p.lo p.hi)‖ ≤
      ∑ m : Fin M, ‖quadExpSum d α (q m).gamma (β m)
        (polyBoxZ d (q m).W (q m).lo (q m).hi)‖ := by
    simpa only [quadExpSum,Piece.quad,Int.cast_sum,Int.cast_mul,Int.cast_natCast,Int.cast_pow] using hβ
  calc
    _ ≤ ∑ m : Fin M, B*Real.sqrt (boxVol d (q m).lo (q m).hi) :=
      hβ'.trans (Finset.sum_le_sum (fun m _ => hbound m (β m)))
    _ ≤ ∑ _m : Fin M, B*Real.sqrt ((D : ℝ)*T) :=
      Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hvol m)) hB)
    _ = (M : ℝ)*(B*Real.sqrt ((D : ℝ)*T)) := by simp
    _ ≤ (D : ℝ)*(B*Real.sqrt ((D : ℝ)*T)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hM) (by positivity)
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg D)]; ring

private lemma a4boxOct14_new_min_new3 {k : ℕ} (S : Finset (Fin k → ℤ)) (hne : S.Nonempty)
    (lo hi : Fin k → ℤ) (hS : ∀ x ∈ S, x ∈ boxZ k lo hi) :
    ∃ l h : Fin k → ℤ, (∀ j, l j ≤ h j) ∧
      (∀ x ∈ S, x ∈ boxZ k l h) ∧
      (∀ j, ∃ x ∈ S, x j = l j) ∧ (∀ j, ∃ x ∈ S, x j = h j) ∧
      (∀ j, boxSide k l h j ≤ boxSide k lo hi j) := by
  classical
  have hex (j : Fin k) : ∃ xl xh : Fin k → ℤ,
      xl ∈ S ∧ xh ∈ S ∧ ∀ x ∈ S, xl j ≤ x j ∧ x j ≤ xh j := by
    obtain ⟨xl, hxl, hl⟩ := Set.exists_min_image (S : Set (Fin k → ℤ))
      (fun x => x j) S.finite_toSet (by simpa using hne)
    obtain ⟨xh, hxh, hh⟩ := Set.exists_max_image (S : Set (Fin k → ℤ))
      (fun x => x j) S.finite_toSet (by simpa using hne)
    exact ⟨xl,xh,hxl,hxh,fun x hx => ⟨hl x hx, hh x hx⟩⟩
  choose xl xh hxl hxh hb using hex
  refine ⟨fun j => xl j j, fun j => xh j j, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (hb j (xl j) (hxl j)).2
  · intro x hx
    exact Fintype.mem_piFinset.mpr (fun j => Finset.mem_Icc.mpr (hb j x hx))
  · intro j
    exact ⟨xl j,hxl j,rfl⟩
  · intro j
    exact ⟨xh j,hxh j,rfl⟩
  · intro j
    apply Finset.card_le_card
    intro t ht
    obtain ⟨htl,hth⟩ := Finset.mem_Icc.mp ht
    have hl := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (hS (xl j) (hxl j)) j)
    have hh := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (hS (xh j) (hxh j)) j)
    exact Finset.mem_Icc.mpr ⟨hl.1.trans htl,hth.trans hh.2⟩

private lemma a4boxOct14_new_section_mono_new (k : ℕ) (w : Fin k → ℤ) (hw : w ≠ 0)
    (lo hi lo' hi' : Fin k → ℤ) (hle : ∀ j, lo j ≤ hi j)
    (hs : ∀ j, boxSide k lo' hi' j ≤ boxSide k lo hi j) :
    boxSect k w lo' hi' ≤ boxSect k w lo hi := by
  classical
  have hne : (vecSupport w).Nonempty := by
    by_contra hn
    apply hw
    funext j
    by_contra hj
    exact hn ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  obtain ⟨q,hq,hmax⟩ := Finset.exists_max_image (vecSupport w) (boxSide k lo hi) hne
  have hsup : (vecSupport w).sup (boxSide k lo hi) = boxSide k lo hi q :=
    le_antisymm (Finset.sup_le hmax) (Finset.le_sup hq)
  have hp : 1 ≤ boxSide k lo hi q :=
    Finset.card_pos.mpr ⟨lo q, Finset.mem_Icc.mpr ⟨le_rfl, hle q⟩⟩
  have hlen : boxLen k w lo hi = boxSide k lo hi q := by
    change max 1 ((vecSupport w).sup (boxSide k lo hi)) = _
    rw [hsup, max_eq_right hp]
  have he : boxSect k w lo hi = ∏ j ∈ Finset.univ.erase q, (boxSide k lo hi j : ℝ) := by
    unfold boxSect boxVol
    rw [hlen, Nat.cast_prod, ← Finset.prod_erase_mul Finset.univ
      (fun j => (boxSide k lo hi j : ℝ)) (Finset.mem_univ q)]
    exact mul_div_cancel_right₀ _ (by exact_mod_cast (show boxSide k lo hi q ≠ 0 by omega))
  rw [he]
  apply (ShiftedBoundProof.section_le_product k w lo' hi' q (Finset.mem_filter.mp hq).2).trans
  exact Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => by exact_mod_cast hs j)

private lemma a4boxOct14_new_data_bridge_v4 {k R M : ℕ} (p : Piece k)
    (u : Fin M → Fin k → ℤ) (Φ : Fin M → Matrix (Fin k) (Fin k) ℤ)
    (W : Fin M → Finset ((Fin k → ℤ) × ℤ))
    (lo hi : Fin M → Fin k → ℤ)
    (h : BalancedDecompData k R p.gamma p.W p.lo p.hi M u Φ W lo hi) :
    ∃ q : Fin M → Piece k, IsDecomposition p q u Φ ∧
      (∀ m, (q m).W = W m ∧ (q m).lo = lo m ∧ (q m).hi = hi m) ∧
      (∀ m, (q m).A ≤ k+R+1) ∧
      (∀ m, IsBalancedWrt k (k+R+1) (q m).W (q m).lo (q m).hi) := by
  classical
  obtain ⟨hM,hdet,hsub,hdis,hunion,hn,hbal,hbox,hvol,hdiag,hΦ,hQ,hrho⟩ := h
  let Q (m : Fin M) := (Φ m)ᵀ * Matrix.diagonal (fun j => (p.gamma j : ℤ)) * Φ m
  have hentry (m : Fin M) (j : Fin k) :
      Q m j j = ∑ i, (p.gamma i : ℤ) * (Φ m i j)^2 := by
    dsimp only [Q]
    rw [Matrix.mul_mul_apply]
    simp only [Matrix.transpose_apply, Matrix.mulVec_diagonal, dotProduct]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hpos (m : Fin M) (j : Fin k) : 0 < Q m j j := by
    have hcol : Φ m *ᵥ (Pi.single j 1 : Fin k → ℤ) ≠ 0 := by
      intro he
      have hs := Matrix.mulVec_injective_of_det_ne_zero (hdet m)
        (he.trans (Matrix.mulVec_zero _).symm)
      have ht := congrFun hs j
      simp at ht
    rw [Matrix.mulVec_single_one] at hcol
    obtain ⟨i,hi⟩ : ∃ i, Φ m i j ≠ 0 := by
      by_contra hn
      apply hcol
      funext i
      simpa using not_exists.mp hn i
    rw [hentry]
    have hg : (0 : ℤ) < p.gamma i := by exact_mod_cast p.one_le_gamma i
    exact (mul_pos hg (sq_pos_of_ne_zero hi)).trans_le
      (Finset.single_le_sum (fun t _ => mul_nonneg (Int.natCast_nonneg _) (sq_nonneg _))
        (Finset.mem_univ i))
  let γ (m : Fin M) (j : Fin k) := (Q m j j).toNat
  have hcast (m : Fin M) (j : Fin k) : (γ m j : ℤ) = Q m j j :=
    Int.toNat_of_nonneg (hpos m j).le
  have hγ (m : Fin M) (j : Fin k) : 1 ≤ γ m j := by
    have := hpos m j
    dsimp [γ]
    omega
  have hγR (m : Fin M) (j : Fin k) : γ m j ≤ R := by
    have ht := (matInftyNorm_le_iff _ _).1 (hQ m) j j
    change |Q m j j| ≤ (R : ℤ) at ht
    rw [abs_of_pos (hpos m j)] at ht
    dsimp [γ]
    omega
  have hform (m : Fin M) (y : Fin k → ℤ) :
      (∑ j, (γ m j : ℤ)*y j^2) = p.quad (Φ m *ᵥ y) := by
    rw [p.quad_eq_dotProduct_diagonal_mulVec]
    rw [dotProduct_comm (Φ m *ᵥ y)]
    rw [← Matrix.dotProduct_transpose_mulVec (Φ m) y
      (Matrix.diagonal (fun j => (p.gamma j : ℤ)) *ᵥ (Φ m *ᵥ y)),
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    change _ = y ⬝ᵥ (Q m *ᵥ y)
    have hd : (Q m).IsDiag := hdiag m
    rw [← hd.diagonal_diag]
    simp only [Matrix.mulVec_diagonal, dotProduct, Matrix.diag]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcast]
    ring
  let q (m : Fin M) : Piece k :=
    { W := W m, lo := lo m, hi := hi m, gamma := γ m, A := k+R+1
      one_le_dim := p.one_le_dim
      one_le_gamma := hγ m
      one_le_A := by omega
      poly_subset_box := hbox m
      dim_le_A := by omega
      rho_le_A := (hrho m).trans (by omega)
      gamma_le_A := fun j => (hγR m j).trans (by omega) }
  refine ⟨q, ⟨fun m => ⟨hdet m,hsub m,hform m⟩,hdis,hunion⟩,
    fun _ => ⟨rfl,rfl,rfl⟩,fun _ => le_rfl,?_⟩
  intro m
  obtain ⟨hk,hR,hw,hb⟩ := hbal m
  exact ⟨hk,by omega,hw,fun i j hij => (hb i j hij).trans
    (Nat.mul_le_mul_right _ (by omega))⟩

private lemma a4boxOct14_initial_v3 (k r V h : ℕ) (hk : 1 ≤ k) (hV : 1 ≤ V)
    (c : Fin k → ℕ) (hc : ∀ j, 1 ≤ c j) (hch : ∀ j, c j ≤ h)
    (lo hi : Fin k → ℤ) (L : Finset ((Fin k → ℤ) × ℤ))
    (hL : L.card ≤ r) (hLV : ∀ z ∈ L, ∑ j, |z.1 j| ≤ (V : ℤ))
    (hne : (polyBoxZ k L lo hi).Nonempty) :
    ∃ p : Piece k, p.A = k+r+2*k+V+h+1 ∧ p.gamma=c ∧ p.lo=lo ∧ p.hi=hi ∧
      (∀ z ∈ p.W, z.1 ≠ 0) ∧
      (∀ x, x ∈ polyPZ k p.W ↔ x ∈ polyBoxZ k L lo hi) ∧
      (∀ w b, w ≠ 0 → (w,b) ∈ L → (w,b) ∈ p.W) := by
  classical
  let W := L.filter (fun z => z.1 ≠ 0) ∪ boxConstraints k lo hi
  let A := k+r+2*k+V+h+1
  obtain ⟨x₀,hx₀⟩ := hne
  have hpoly (x) : x ∈ polyPZ k W ↔ x ∈ polyBoxZ k L lo hi := by
    have hbox : (∀ z ∈ boxConstraints k lo hi, 0 ≤ (∑ j, z.1 j*x j)+z.2) ↔ x ∈ boxZ k lo hi :=
      Set.ext_iff.mp (polyPZ_boxConstraints k lo hi) x
    simp only [polyPZ,W,Set.mem_setOf_eq,Finset.forall_mem_union]
    rw [hbox]
    constructor
    · rintro ⟨hW,hbox⟩
      apply Finset.mem_filter.mpr
      refine ⟨hbox,?_⟩
      intro z hz
      by_cases hzero : z.1=0
      · have hb := (Finset.mem_filter.mp hx₀).2 z hz
        simpa [hzero] using hb
      · exact hW z (Finset.mem_filter.mpr ⟨hz,hzero⟩)
    · intro hx
      obtain ⟨hb,hl⟩ := Finset.mem_filter.mp hx
      exact ⟨fun z hz => hl z (Finset.mem_filter.mp hz).1,hb⟩
  have hnormal : ∀ z ∈ W, z.1 ≠ 0 := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (Finset.mem_filter.mp hz).2
    · intro he
      have hh := sum_abs_boxConstraints k lo hi z hz
      simp [he] at hh
  have hrho : constraintRho k W ≤ A := by
    apply (constraintRho_le_iff _ _ _).2
    constructor
    · have hcard := Finset.card_union_le (L.filter (fun z => z.1≠0)) (boxConstraints k lo hi)
      have hc := Finset.card_filter_le L (fun z => z.1≠0)
      have hb := card_boxConstraints_le k lo hi
      change (L.filter (fun z => z.1 ≠ 0) ∪ boxConstraints k lo hi).card ≤ k+r+2*k+V+h+1
      exact hcard.trans (by omega)
    · intro z hz
      have hVA : (V : ℤ) ≤ (A : ℤ) := by dsimp [A]; omega
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (hLV z (Finset.mem_filter.mp hz).1).trans hVA
      · rw [sum_abs_boxConstraints k lo hi z hz]
        exact (show (1 : ℤ) ≤ V by exact_mod_cast hV).trans hVA
  let p : Piece k :=
    { W:=W, lo:=lo, hi:=hi, gamma:=c, A:=A,
      one_le_dim:=hk, one_le_gamma:=hc, one_le_A:=by dsimp [A]; omega,
      poly_subset_box:=fun x hx => (Finset.mem_filter.mp ((hpoly x).1 hx)).1,
      dim_le_A:=by dsimp [A]; omega, rho_le_A:=hrho,
      gamma_le_A:=fun j => (hch j).trans (by dsimp [A]; omega) }
  exact ⟨p,rfl,rfl,rfl,rfl,hnormal,hpoly,
    fun w b hw hm => Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm,hw⟩)⟩

private lemma a4boxOct14_new_data_estimate {k D M : ℕ} (p : Piece k)
    (u : Fin M → Fin k → ℤ) (Φ : Fin M → Matrix (Fin k) (Fin k) ℤ)
    (W : Fin M → Finset ((Fin k → ℤ) × ℤ)) (lo hi : Fin M → Fin k → ℤ)
    (hd : BalancedDecompData k D p.gamma p.W p.lo p.hi M u Φ W lo hi)
    (α B T : ℝ) (hB : 0 ≤ B)
    (hb : ∀ q : Piece k, q.A ≤ k+D+1 →
      IsBalancedWrt k (k+D+1) q.W q.lo q.hi → ∀ θ,
      ‖quadExpSum k α q.gamma θ (polyBoxZ k q.W q.lo q.hi)‖ ≤
        B * Real.sqrt (boxVol k q.lo q.hi))
    (hv : ∀ m, (boxVol k (lo m) (hi m) : ℝ) ≤ (D : ℝ)*T) (θ : Fin k → ℝ) :
    ‖quadExpSum k α p.gamma θ (polyBoxZ k p.W p.lo p.hi)‖ ≤
      ((D : ℝ)*B*Real.sqrt D)*Real.sqrt T := by
  obtain ⟨q,hdec,hends,hA,hbal⟩ := a4boxOct14_new_data_bridge_v4 p u Φ W lo hi hd
  apply a4boxOct14_decomp_bound p q u Φ hdec hd.1 α B T hB ?_ ?_ θ
  · intro m
    obtain ⟨hW,hl,hh⟩ := hends m
    simpa only [hl,hh] using hv m
  · intro m η
    exact hb (q m) (hA m) (hbal m) η

private theorem a4boxOct14_new_finished_v2 : ThmBox := by
  classical
  intro k r V h a hk hV hh ha
  let A := k+r+2*k+V+h+1
  have hA : 1 ≤ A := by dsimp [A]; omega
  obtain ⟨D,hD,hdecomp⟩ := thm_decomp k A A A hk hA hA
  obtain ⟨B,hB,hbound⟩ := a4boxOct14_uniform k (k+D+1) (by omega) a
  refine ⟨(D : ℝ)*B*Real.sqrt D,by positivity,?_⟩
  intro α hα hbp c hc hch lo hi hlo L hL hLV θ
  by_cases hne : (polyBoxZ k L lo hi).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [quadExpSum,Finset.sum_empty,norm_zero]
    refine ⟨by positivity,?_⟩
    intro w b hw hm hn
    positivity
  obtain ⟨p,hpA,hpg,hplo,hphi,hpnormal,hpoly,hmemp⟩ :=
    a4boxOct14_initial_v3 k r V h hk hV c hc hch lo hi L hL hLV hne
  obtain ⟨l,t,hlt,hsub,hmin,hmax,hside⟩ := a4boxOct14_new_min_new3
    (polyBoxZ k L lo hi) hne lo hi (fun x hx => (Finset.mem_filter.mp hx).1)
  let p₀ : Piece k :=
    { p with lo := l, hi := t, poly_subset_box := fun x hx => hsub x ((hpoly x).1 hx) }
  have hmem₀ (x) : x ∈ polyBoxZ k p₀.W p₀.lo p₀.hi ↔ x ∈ polyBoxZ k L lo hi :=
    (a4boxOct14_mem p₀ x).trans (hpoly x)
  have hsum : quadExpSum k α p₀.gamma θ (polyBoxZ k p₀.W p₀.lo p₀.hi) =
      quadExpSum k α c θ (polyBoxZ k L lo hi) := by
    have hg : p₀.gamma = c := hpg
    rw [hg]
    congr 1
    ext x
    exact hmem₀ x
  have hW : ∀ z ∈ p.W, 0 < ∑ j, |z.1 j| ∧ ∑ j, |z.1 j| ≤ (A : ℤ) := by
    intro z hz
    have hn := hpnormal z hz
    obtain ⟨j,hj⟩ : ∃ j, z.1 j ≠ 0 := by
      by_contra hn'
      apply hn
      funext j
      simpa using not_exists.mp hn' j
    refine ⟨(abs_pos.mpr hj).trans_le
      (Finset.single_le_sum (fun i _ => abs_nonneg (z.1 i)) (Finset.mem_univ j)),?_⟩
    exact (l1_le_constraintRho k p.W z hz).trans
      (by exact_mod_cast p.rho_le_A.trans_eq hpA)
  have hfinite : (polyPZ k p.W).Finite := (boxZ k lo hi).finite_toSet.subset (by
    intro x hx
    exact (Finset.mem_filter.mp ((hpoly x).1 hx)).1)
  have hnonempty : (polyPZ k p.W).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨x,(hpoly x).2 hx⟩
  have hd := hdecomp p.gamma p.one_le_gamma
    (fun j => (p.gamma_le_A j).trans_eq hpA) p.W
    (p.card_W_le_A.trans_eq hpA) hW hfinite hnonempty l t
    p₀.poly_subset_box
    (fun j => by obtain ⟨x,hx,he⟩ := hmin j; exact ⟨x,(hpoly x).2 hx,he⟩)
    (fun j => by obtain ⟨x,hx,he⟩ := hmax j; exact ⟨x,(hpoly x).2 hx,he⟩)
  have hb := hbound α hα hbp
  have hvolmono : boxVol k l t ≤ boxVol k lo hi :=
    Finset.prod_le_prod (fun j _ => hside j)
  constructor
  · obtain ⟨M,u,Φ,W',lo',hi',hdata⟩ := hd.1
    rw [← hsum]
    apply a4boxOct14_new_data_estimate p₀ u Φ W' lo' hi' hdata α B (boxVol k lo hi)
      (by linarith) hb ?_ θ
    intro m
    obtain ⟨_,_,_,_,_,_,_,_,hv,_,_,_,_⟩ := hdata
    exact_mod_cast (hv m).trans (Nat.mul_le_mul_left D hvolmono)
  · intro w b hw hm hn
    obtain ⟨M,u,Φ,W',lo',hi',hdata,hsect⟩ := hd.2 w b
      (hmemp w b hw hm) (hmemp (-w) (-b) (neg_ne_zero.mpr hw) hn)
    rw [← hsum]
    apply a4boxOct14_new_data_estimate p₀ u Φ W' lo' hi' hdata α B (boxSect k w lo hi)
      (by linarith) hb ?_ θ
    intro m
    have hlen : (0 : ℝ) < boxLen k w l t := by
      have hh : 1 ≤ boxLen k w l t := le_max_left _ _
      exact_mod_cast (show 0 < boxLen k w l t by omega)
    have hsmall : (boxVol k (lo' m) (hi' m) : ℝ) ≤ (D : ℝ) * boxSect k w l t := by
      unfold boxSect
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hlen).2
      exact_mod_cast hsect m
    exact hsmall.trans (mul_le_mul_of_nonneg_left
      (a4boxOct14_new_section_mono_new k w hw lo hi l t hlo hside) (Nat.cast_nonneg D))

private lemma a4boxOct14_volZ (k : ℕ) (lo hi : Fin k → ℤ) :
    boxVol k lo hi = UniformBoundUnit.boxVolZ k lo hi := rfl

private lemma a4boxOct14_lenZ (k : ℕ) (w : Fin k → ℤ) (lo hi : Fin k → ℤ) :
    boxLen k w lo hi = UniformBoundUnit.boxLenZ k w lo hi := rfl

private lemma a4boxOct14_sectZ (k : ℕ) (w : Fin k → ℤ) (lo hi : Fin k → ℤ) :
    boxSect k w lo hi = UniformBoundUnit.boxSectZ k w lo hi := rfl

theorem thm_box :
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
                      fun s => (Finset.Icc (lo s) (hi s)).card) : ℕ) : ℝ)) := by
  simpa only [ThmBox, quadExpSum, polyBoxZ, boxZ, expTwoPiI,
    a4boxOct14_volZ, a4boxOct14_sectZ, UniformBoundUnit.boxSectZ,
    UniformBoundUnit.boxVolZ, UniformBoundUnit.boxLenZ]
    using a4boxOct14_new_finished_v2
def foldPrefixSum (k : ℕ) (x : Fin k → ℕ) (i : ℕ) : ℕ :=
  ∑ ν ∈ Finset.univ.filter (fun ν : Fin k => ν.val < i), x ν

/-- The source piece `𝒞_{k,N,m}` of the fold, for `1 ≤ m ≤ k`: the points `x ∈ 𝒮_{k,N}` with
`∑_{ν ≤ i} x_ν > iN/k` for `1 ≤ i < m` and `∑_{ν ≤ m} x_ν ≤ mN/k`.  The divisions are
cleared by multiplying through by `k`. -/
noncomputable def foldSourcePiece (k N m : ℕ) : Finset (Fin k → ℕ) := by
  classical
  exact (simplexS k N).filter fun x =>
    (∀ i ∈ Finset.Ico 1 m, i * N < k * foldPrefixSum k x i) ∧
      k * foldPrefixSum k x m ≤ m * N

private lemma a4fold_cast (k i : ℕ) (x : Fin k → ℕ) :
    (∑ s, (if s.val < i then (k : ℤ) else 0) * (x s : ℤ)) =
      (k : ℤ) * (foldPrefixSum k x i : ℤ) := by
  simp [foldPrefixSum, Finset.sum_filter, ite_mul, Finset.mul_sum]

private lemma a4fold_poly (k N m : ℕ) :
    ∃ L : Finset ((Fin k → ℤ) × ℤ),
      (foldSourcePiece k N m : Set (Fin k → ℕ)) = polyP k L := by
  classical
  let p : ℕ → ((Fin k → ℤ) × ℤ) := fun i =>
    ((fun s => if s.val < i then (k : ℤ) else 0), -(i*N : ℕ) - 1)
  let z : ((Fin k → ℤ) × ℤ) := ((fun _ => -1), (N : ℤ))
  let t : ((Fin k → ℤ) × ℤ) :=
    ((fun s => -(if s.val < m then (k : ℤ) else 0)), (m*N : ℕ))
  refine ⟨insert z (insert t ((Finset.Ico 1 m).image p)), ?_⟩
  ext x
  simp only [foldSourcePiece, Finset.mem_coe, Finset.mem_filter, onb_mem_simplex,
    polyP, Set.mem_setOf_eq, Finset.forall_mem_insert, Finset.forall_mem_image]
  have hz : (0 ≤ (∑ s, z.1 s * (x s : ℤ)) + z.2) ↔ ∑ s, x s ≤ N := by
    simp only [z, neg_one_mul, Finset.sum_neg_distrib]
    rw [← Nat.cast_sum]
    omega
  have ht : (0 ≤ (∑ s, t.1 s * (x s : ℤ)) + t.2) ↔
      k * foldPrefixSum k x m ≤ m*N := by
    simp only [t, neg_mul, Finset.sum_neg_distrib, a4fold_cast]
    push_cast
    omega
  have hp (i : ℕ) : (0 ≤ (∑ s, (p i).1 s * (x s : ℤ)) + (p i).2) ↔
      i*N < k*foldPrefixSum k x i := by
    simp only [p, a4fold_cast]
    push_cast
    omega
  simp_rw [hz, ht, hp]
  tauto

theorem foldSourcePiece_partition (k N : ℕ) (hk : 2 ≤ k) (hkN : k ∣ N) :
    (∀ m, 1 ≤ m → m ≤ k →
        foldSourcePiece k N m ⊆ simplexS k N ∧
          ∃ L : Finset ((Fin k → ℤ) × ℤ),
            ((foldSourcePiece k N m : Finset (Fin k → ℕ)) : Set (Fin k → ℕ)) = polyP k L) ∧
      ∀ x : Fin k → ℕ, x ∈ simplexS k N ↔
        ∃! m : ℕ, 1 ≤ m ∧ m ≤ k ∧ x ∈ foldSourcePiece k N m := by
  classical
  refine ⟨?_, ?_⟩
  · intro m _ _
    refine ⟨?_, a4fold_poly k N m⟩
    intro x hx
    have hh := hx
    simp only [foldSourcePiece, Finset.mem_filter] at hh
    exact hh.1
  intro x
  constructor
  · intro hx
    have htotal : foldPrefixSum k x k = ∑ j, x j := by
      simp [foldPrefixSum]
    have hlast : k * foldPrefixSum k x k ≤ k * N := by
      rw [htotal]
      exact Nat.mul_le_mul_left k ((onb_mem_simplex k N x).1 hx)
    have hex : ∃ m : ℕ, 1 ≤ m ∧ k * foldPrefixSum k x m ≤ m * N :=
      ⟨k, by omega, hlast⟩
    let m := Nat.find hex
    have hm : 1 ≤ m ∧ k * foldPrefixSum k x m ≤ m * N := Nat.find_spec hex
    have hmk : m ≤ k := Nat.find_min' hex ⟨by omega, hlast⟩
    have hsmall (i : ℕ) (hi : i ∈ Finset.Ico 1 m) :
        i*N < k*foldPrefixSum k x i := by
      have hlt := (Finset.mem_Ico.mp hi).2
      have hge := (Finset.mem_Ico.mp hi).1
      have hh := Nat.find_min hex hlt
      omega
    refine ⟨m, ⟨hm.1, hmk, ?_⟩, ?_⟩
    · simpa only [foldSourcePiece, Finset.mem_filter] using
        And.intro hx (And.intro hsmall hm.2)
    · intro m' hm'
      have hqual := (show x ∈ simplexS k N ∧
          (∀ i ∈ Finset.Ico 1 m', i*N < k*foldPrefixSum k x i) ∧
          k*foldPrefixSum k x m' ≤ m'*N from by
            simpa only [foldSourcePiece, Finset.mem_filter] using hm'.2.2).2
      have hle : m ≤ m' := Nat.find_min' hex ⟨hm'.1, hqual.2⟩
      by_contra hne
      have hlt : m < m' := by omega
      have hh := hqual.1 m (Finset.mem_Ico.mpr ⟨hm.1, hlt⟩)
      omega
  · rintro ⟨m, hm, _⟩
    have hh := hm.2.2
    simp only [foldSourcePiece, Finset.mem_filter] at hh
    exact hh.1
noncomputable section

def foldCoord {k : ℕ} (x : Fin k → ℤ) (i : ℕ) : ℤ :=
  if h : 1 ≤ i ∧ i ≤ k then x ⟨i - 1, by omega⟩ else 0

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

noncomputable def foldMapGlobal (k N : ℕ) (x : Fin k → ℕ) : Fin k → ℤ := by
  classical
  exact
    if h : ∃ m, 1 ≤ m ∧ m ≤ k ∧ x ∈ foldSourcePiece k N m then
      foldMap k N (Nat.find h) (fun t => (x t : ℤ))
    else 0

def foldTargetBase (k N : ℕ) : Set (Fin k → ℤ) :=
  {y | (∀ t, 0 ≤ y t) ∧ foldCoord y 1 ≤ ((N / k : ℕ) : ℤ) ∧
    ∑ j ∈ Finset.Icc 2 k, foldCoord y j ≤ (N : ℤ)}

def foldTargetPiece (k N m : ℕ) : Set (Fin k → ℤ) :=
  {y | y ∈ foldTargetBase k N ∧
    (∀ i ∈ Finset.Ico 1 m,
      ∑ ν ∈ Finset.Icc 2 (i + 1), foldCoord y ν <
        foldCoord y 1 + ((i : ℤ) - 1) * ((N / k : ℕ) : ℤ)) ∧
    (m < k →
      foldCoord y 1 + ((m : ℤ) - 1) * ((N / k : ℕ) : ℤ) ≤
        ∑ ν ∈ Finset.Icc 2 (m + 1), foldCoord y ν)}

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

private lemma a4recordFold20261014_fm2_coord {k : ℕ} (x : Fin k → ℤ)
    (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
    foldCoord x i = x ⟨i - 1, by omega⟩ := by
  simp [foldCoord, hi, hik]

private lemma a4recordFold20261014_fm2_coord_fin {k : ℕ}
    (x : Fin k → ℤ) (t : Fin k) :
    foldCoord x (t.val + 1) = x t := by
  rw [a4recordFold20261014_fm2_coord x _ (by omega) (by have := t.isLt; omega)]
  congr 1

private lemma a4recordFold20261014_fm2_prefix {k : ℕ}
    (x : Fin k → ℕ) (i : ℕ) (hi : i ≤ k) :
    (∑ j ∈ Finset.Icc 1 i, foldCoord (fun t => (x t : ℤ)) j) =
      (foldPrefixSum k x i : ℤ) := by
  classical
  unfold foldPrefixSum
  rw [Nat.cast_sum]
  symm
  apply Finset.sum_bij (fun (t : Fin k) _ => t.val + 1)
  · intro t ht
    have := (Finset.mem_filter.mp ht).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro t ht s hs he
    apply Fin.ext
    omega
  · intro j hj
    obtain ⟨hj, hji⟩ := Finset.mem_Icc.mp hj
    refine ⟨⟨j - 1, by omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩,
      by dsimp; omega⟩
  · intro t ht
    exact (a4recordFold20261014_fm2_coord_fin (fun t => (x t : ℤ)) t).symm

private lemma a4recordFold20261014_fm3_global_piece
    (k N : ℕ) (hk : 2 ≤ k) (hkN : k ∣ N)
    (m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k) (x : Fin k → ℕ)
    (hx : x ∈ foldSourcePiece k N m) :
    foldMapGlobal k N x = foldMap k N m (fun t => (x t : ℤ)) := by
  classical
  have hex : ∃ m, 1 ≤ m ∧ m ≤ k ∧ x ∈ foldSourcePiece k N m :=
    ⟨m, hm, hmk, hx⟩
  obtain ⟨n, hn, hu⟩ := (foldSourcePiece_partition k N hk hkN).2 x |>.1
    (((foldSourcePiece_partition k N hk hkN).1 m hm hmk).1 hx)
  have he : Nat.find hex = m :=
    (hu _ (Nat.find_spec hex)).trans (hu _ ⟨hm, hmk, hx⟩).symm
  simp [foldMapGlobal, dif_pos hex, he]

private lemma a4recordFold20261014_aff2_coord_zero {k}
    (i : ℕ) : foldCoord (0 : Fin k → ℤ) i = 0 := by
  simp [foldCoord]

private lemma a4recordFold20261014_aff2_coord_add {k}
    (x y : Fin k → ℤ) (i : ℕ) :
    foldCoord (x + y) i = foldCoord x i + foldCoord y i := by
  unfold foldCoord
  split_ifs <;> simp [Pi.add_apply]

private lemma a4recordFold20261014_aff2_coord_smul {k}
    (a : ℤ) (x : Fin k → ℤ) (i : ℕ) :
    foldCoord (a • x) i = a * foldCoord x i := by
  unfold foldCoord
  split_ifs <;> simp [Pi.smul_apply, smul_eq_mul]

private lemma a4recordFold20261014_aff2_map (k N m : ℕ) :
    ∃ (A : Matrix (Fin k) (Fin k) ℤ) (c : Fin k → ℤ),
      ∀ x : Fin k → ℤ, foldMap k N m x = A.mulVec x + c := by
  classical
  let L : (Fin k → ℤ) →ₗ[ℤ] (Fin k → ℤ) :=
    { toFun := fun x => foldMap k N m x - foldMap k N m 0
      map_add' := by
        intro x y
        funext t
        simp only [Pi.sub_apply, Pi.add_apply, foldMap,
          a4recordFold20261014_aff2_coord_add,
          a4recordFold20261014_aff2_coord_zero,
          Finset.sum_add_distrib, Finset.sum_const_zero]
        split_ifs <;> ring
      map_smul' := by
        intro a x
        funext t
        simp only [Pi.sub_apply, Pi.smul_apply, foldMap,
          a4recordFold20261014_aff2_coord_smul,
          a4recordFold20261014_aff2_coord_zero, smul_eq_mul,
          RingHom.id_apply, Finset.sum_const_zero, ← Finset.mul_sum]
        split_ifs <;> ring }
  refine ⟨LinearMap.toMatrix' L, foldMap k N m 0, ?_⟩
  intro x
  rw [LinearMap.toMatrix'_mulVec]
  change _ = (foldMap k N m x - foldMap k N m 0) + foldMap k N m 0
  abel

private lemma a4recordFold20261014_aff2_inv (k N m : ℕ) :
    ∃ (B : Matrix (Fin k) (Fin k) ℤ) (c : Fin k → ℤ),
      ∀ y : Fin k → ℤ, foldInv k N m y = B.mulVec y + c := by
  classical
  let L : (Fin k → ℤ) →ₗ[ℤ] (Fin k → ℤ) :=
    { toFun := fun x => foldInv k N m x - foldInv k N m 0
      map_add' := by
        intro x y
        funext t
        simp only [Pi.sub_apply, Pi.add_apply, foldInv,
          a4recordFold20261014_aff2_coord_add,
          a4recordFold20261014_aff2_coord_zero,
          Finset.sum_add_distrib, Finset.sum_const_zero]
        split_ifs <;> ring
      map_smul' := by
        intro a x
        funext t
        simp only [Pi.sub_apply, Pi.smul_apply, foldInv,
          a4recordFold20261014_aff2_coord_smul,
          a4recordFold20261014_aff2_coord_zero, smul_eq_mul,
          RingHom.id_apply, Finset.sum_const_zero, ← Finset.mul_sum]
        split_ifs <;> ring }
  refine ⟨LinearMap.toMatrix' L, foldInv k N m 0, ?_⟩
  intro x
  rw [LinearMap.toMatrix'_mulVec]
  change _ = (foldInv k N m x - foldInv k N m 0) + foldInv k N m 0
  abel

private def a4recordFold20261014_fs_seq
    (f : ℕ → ℤ) (q : ℤ) (m j : ℕ) : ℤ :=
  if j < m then f (m + 2 - j)
  else if j = m then f 1 - q - 1
  else if j = m + 1 then f 2 + f (m + 1) + q + 1
  else f j

private lemma a4recordFold20261014_fs_split
    (f : ℕ → ℤ) (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ j ∈ Finset.Icc a c, f j) =
      (∑ j ∈ Finset.Ico a b, f j) + f b +
        ∑ j ∈ Finset.Icc (b + 1) c, f j := by
  classical
  have hs : Finset.Icc a c =
      Finset.Ico a b ∪ insert b (Finset.Icc (b + 1) c) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico, Finset.mem_union, Finset.mem_insert]
    omega
  have hd : Disjoint (Finset.Ico a b)
      (insert b (Finset.Icc (b + 1) c)) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Icc] at hj hj'
    omega
  rw [hs, Finset.sum_union hd, Finset.sum_insert (by simp)]
  abel

private lemma a4recordFold20261014_fs_reverse (f : ℕ → ℤ) (m : ℕ) :
    (∑ j ∈ Finset.Ico 2 m, f (m + 2 - j)) =
      ∑ j ∈ Finset.Icc 3 m, f j := by
  classical
  apply Finset.sum_bij (fun j _ => m + 2 - j)
  · intro j hj
    apply Finset.mem_Icc.mpr
    have := Finset.mem_Ico.mp hj
    omega
  · intro j hj l hl he
    have := Finset.mem_Ico.mp hj
    have := Finset.mem_Ico.mp hl
    omega
  · intro j hj
    have h := Finset.mem_Icc.mp hj
    exact ⟨m + 2 - j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · intros
    rfl

private lemma a4recordFold20261014_fs3_sum
    (f : ℕ → ℤ) (q : ℤ) (m k : ℕ) (hm : 2 ≤ m) (hmk : m ≤ k) :
    (∑ j ∈ Finset.Icc 2 k, a4recordFold20261014_fs_seq f q m j) =
      (∑ j ∈ Finset.Icc 1 k, f j) -
        (if k = m then f 2 + q + 1 else 0) := by
  classical
  induction k, hmk using Nat.le_induction with
  | base =>
    have hrev :
        (∑ j ∈ Finset.Ico 2 m, a4recordFold20261014_fs_seq f q m j) =
          ∑ j ∈ Finset.Icc 3 m, f j := by
      calc
        _ = ∑ j ∈ Finset.Ico 2 m, f (m + 2 - j) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [a4recordFold20261014_fs_seq,
            if_pos (Finset.mem_Ico.mp hj).2]
        _ = _ := a4recordFold20261014_fs_reverse f m
    have hsrc := a4recordFold20261014_fs_split f 1 2 m (by omega) hm
    have htar :=
      a4recordFold20261014_fs_split (a4recordFold20261014_fs_seq f q m)
        2 m m hm le_rfl
    simp only [Finset.Icc_eq_empty_of_lt (by omega : m < m + 1),
      Finset.sum_empty, add_zero] at htar
    have hmval : a4recordFold20261014_fs_seq f q m m = f 1 - q - 1 := by
      simp [a4recordFold20261014_fs_seq]
    rw [hrev, hmval] at htar
    have hsmall : (∑ j ∈ Finset.Ico 1 2, f j) = f 1 := by norm_num
    rw [hsmall] at hsrc
    rw [htar, hsrc, if_pos rfl]
    ring
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ k + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), ih]
    by_cases hkm : k = m
    · subst k
      simp only [a4recordFold20261014_fs_seq,
        if_neg (by omega : ¬ (m + 1 < m)),
        if_neg (by omega : m + 1 ≠ m), if_pos rfl]
      simp only [ite_true]
      ring
    · simp only [a4recordFold20261014_fs_seq,
        if_neg (by omega : ¬ (k + 1 < m)),
        if_neg (by omega : k + 1 ≠ m),
        if_neg (by omega : k + 1 ≠ m + 1), if_neg hkm]
      ring

private lemma a4recordFold20261014_ft_nonneg {k : ℕ}
    (x : Fin k → ℕ) (i : ℕ) :
    0 ≤ foldCoord (fun t => (x t : ℤ)) i := by
  unfold foldCoord
  split_ifs <;> simp

private lemma a4recordFold20261014_ft_prefix_mono {k : ℕ}
    (x : Fin k → ℕ) {i j : ℕ} (h : i ≤ j) :
    foldPrefixSum k x i ≤ foldPrefixSum k x j := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2.trans_le h⟩
  · intros
    positivity

private lemma a4recordFold20261014_ft_coord_map {k N m : ℕ}
    (x : Fin k → ℤ) (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    foldCoord (foldMap k N m x) j =
      if m = 1 then
        (if j = 2 then foldCoord x 1 + foldCoord x 2 else foldCoord x j)
      else if j = 1 then
        (∑ ν ∈ Finset.Icc 1 m, foldCoord x ν) -
          ((m : ℤ) - 1) * (N / k : ℕ)
      else a4recordFold20261014_fs_seq (foldCoord x) (N / k : ℕ) m j := by
  rw [a4recordFold20261014_fm2_coord _ j hj hjk]
  have he : j - 1 + 1 = j := by omega
  simp only [foldMap, he, a4recordFold20261014_fs_seq]

private lemma a4recordFold20261014_ft_tail_one
    (f : ℕ → ℤ) (k : ℕ) (hk : 2 ≤ k) :
    (∑ j ∈ Finset.Icc 2 k, if j = 2 then f 1 + f 2 else f j) =
      ∑ j ∈ Finset.Icc 1 k, f j := by
  classical
  have hp :
      (∑ j ∈ Finset.Icc 2 k, (if j = 2 then f 1 + f 2 else f j)) =
        f 1 + ∑ j ∈ Finset.Icc 2 k, f j := by
    calc
      _ = ∑ j ∈ Finset.Icc 2 k, (f j + if j = 2 then f 1 else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hj2 : j = 2 <;> simp [hj2, add_comm]
      _ = _ := by
        simp [Finset.sum_add_distrib, Finset.mem_Icc, hk, add_comm]
  have hs := a4recordFold20261014_fs_split f 1 1 k le_rfl (by omega)
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add] at hs
  exact hp.trans hs.symm

private lemma a4recordFold20261014_ft2_source
    (k N m : ℕ) (hk : 2 ≤ k) (hkN : k ∣ N)
    (x : Fin k → ℕ) (hx : x ∈ foldSourcePiece k N m) :
    (∀ i ∈ Finset.Ico 1 m, i * (N / k) < foldPrefixSum k x i) ∧
      foldPrefixSum k x m ≤ m * (N / k) := by
  have hh : x ∈ simplexS k N ∧
      (∀ i ∈ Finset.Ico 1 m, i * N < k * foldPrefixSum k x i) ∧
        k * foldPrefixSum k x m ≤ m * N := by
    simpa only [foldSourcePiece, Finset.mem_filter] using hx
  have hN : N = k * (N / k) := (Nat.mul_div_cancel' hkN).symm
  have hk0 : 0 < k := by omega
  constructor
  · intro i hi
    have h := hh.2.1 i hi
    rw [hN, show i * (k * (N / k)) = k * (i * (N / k)) by ring] at h
    exact (Nat.mul_lt_mul_left hk0).mp h
  · have h := hh.2.2
    rw [hN, show m * (k * (N / k)) = k * (m * (N / k)) by ring] at h
    exact (Nat.mul_le_mul_left_iff hk0).mp h

private lemma a4recordFold20261014_ft3_target
    (k N m : ℕ) (hk : 2 ≤ k) (hkN : k ∣ N)
    (hm : 1 ≤ m) (hmk : m ≤ k) (x : Fin k → ℕ)
    (hx : x ∈ foldSourcePiece k N m) :
    foldMap k N m (fun t => (x t : ℤ)) ∈ foldTargetBase k N := by
  classical
  let X : Fin k → ℤ := fun t => (x t : ℤ)
  let q : ℤ := (N / k : ℕ)
  change (∀ t, 0 ≤ foldMap k N m X t) ∧
    foldCoord (foldMap k N m X) 1 ≤ q ∧
    (∑ j ∈ Finset.Icc 2 k, foldCoord (foldMap k N m X) j) ≤ (N : ℤ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hf (i : ℕ) : 0 ≤ foldCoord X i :=
    a4recordFold20261014_ft_nonneg x i
  have hsrc := a4recordFold20261014_ft2_source k N m hk hkN x hx
  have hupper :
      (∑ j ∈ Finset.Icc 1 m, foldCoord X j) ≤ (m : ℤ) * q := by
    rw [a4recordFold20261014_fm2_prefix x m hmk]
    dsimp [q]
    exact_mod_cast hsrc.2
  have hxs : x ∈ simplexS k N :=
    ((foldSourcePiece_partition k N hk hkN).1 m hm hmk).1 hx
  have htotal :
      (∑ j ∈ Finset.Icc 1 k, foldCoord X j) ≤ (N : ℤ) := by
    rw [a4recordFold20261014_fm2_prefix x k le_rfl]
    have he : foldPrefixSum k x k = ∑ t, x t := by simp [foldPrefixSum]
    rw [he]
    exact_mod_cast (onb_mem_simplex k N x).1 hxs
  by_cases hm1 : m = 1
  · subst m
    have hx1 : foldCoord X 1 ≤ q := by simpa using hupper
    have htail :
        (∑ j ∈ Finset.Icc 2 k, foldCoord (foldMap k N 1 X) j) =
          ∑ j ∈ Finset.Icc 1 k, foldCoord X j := by
      calc
        _ = ∑ j ∈ Finset.Icc 2 k,
            if j = 2 then foldCoord X 1 + foldCoord X 2 else foldCoord X j := by
          apply Finset.sum_congr rfl
          intro j hj
          obtain ⟨hj, hjk⟩ := Finset.mem_Icc.mp hj
          simp only [a4recordFold20261014_ft_coord_map X j (by omega) hjk,
            ite_true]
        _ = _ := a4recordFold20261014_ft_tail_one (foldCoord X) k hk
    refine ⟨?_, ?_, htail ▸ htotal⟩
    · intro t
      simp only [foldMap, ite_true]
      split_ifs
      · exact add_nonneg (hf 1) (hf 2)
      · exact hf _
    · rw [a4recordFold20261014_ft_coord_map X 1 (by omega) (by omega)]
      simpa using hx1
  · have hm2 : 2 ≤ m := by omega
    have hx1 : q + 1 ≤ foldCoord X 1 := by
      have hh := hsrc.1 1 (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
      simp only [one_mul] at hh
      have hh' : q < (foldPrefixSum k x 1 : ℤ) := by
        dsimp [q]
        exact_mod_cast hh
      rw [← a4recordFold20261014_fm2_prefix x 1 (by omega)] at hh'
      have hh'' : q < foldCoord X 1 := by simpa [X] using hh'
      omega
    have hlow :
        ((m : ℤ) - 1) * q ≤ ∑ j ∈ Finset.Icc 1 m, foldCoord X j := by
      have hh := hsrc.1 (m - 1)
        (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
      have hhcast :
          (((m - 1 : ℕ) : ℤ) * ((N / k : ℕ) : ℤ)) <
            (foldPrefixSum k x (m - 1) : ℤ) := by
        exact_mod_cast hh
      have hh' :
          ((m : ℤ) - 1) * q < (foldPrefixSum k x (m - 1) : ℤ) := by
        simpa only [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] using hhcast
      have hmono :
          (foldPrefixSum k x (m - 1) : ℤ) ≤ (foldPrefixSum k x m : ℤ) := by
        exact_mod_cast
          a4recordFold20261014_ft_prefix_mono x (show m - 1 ≤ m by omega)
      rw [a4recordFold20261014_fm2_prefix x m hmk]
      omega
    have htail :
        (∑ j ∈ Finset.Icc 2 k, foldCoord (foldMap k N m X) j) =
          (∑ j ∈ Finset.Icc 1 k, foldCoord X j) -
            (if k = m then foldCoord X 2 + q + 1 else 0) := by
      calc
        _ = ∑ j ∈ Finset.Icc 2 k,
            a4recordFold20261014_fs_seq (foldCoord X) q m j := by
          apply Finset.sum_congr rfl
          intro j hj
          obtain ⟨hj, hjk⟩ := Finset.mem_Icc.mp hj
          rw [a4recordFold20261014_ft_coord_map X j (by omega) hjk,
            if_neg hm1, if_neg (by omega : j ≠ 1)]
        _ = _ := a4recordFold20261014_fs3_sum (foldCoord X) q m k hm2 hmk
    refine ⟨?_, ?_, ?_⟩
    · intro t
      simp only [foldMap, if_neg hm1]
      split_ifs
      · exact sub_nonneg.mpr hlow
      · exact hf _
      · omega
      · have := hf 2
        have := hf (m + 1)
        omega
      · exact hf _
    · rw [a4recordFold20261014_ft_coord_map X 1 (by omega) (by omega),
        if_neg hm1, if_pos rfl]
      dsimp [q] at hupper ⊢
      nlinarith
    · rw [htail]
      apply le_trans (sub_le_self _ ?_) htotal
      split_ifs <;> have := hf 2 <;> omega

theorem foldMap_spec (k N : ℕ) (hk : 2 ≤ k) (hkN : k ∣ N) :
    (∀ x ∈ simplexS k N, foldMapGlobal k N x ∈ foldTargetBase k N) ∧
    (∀ m, 1 ≤ m → m ≤ k → ∀ x ∈ foldSourcePiece k N m,
      foldMapGlobal k N x = foldMap k N m (fun t => (x t : ℤ))) ∧
    (∀ m, 1 ≤ m → m ≤ k →
      ∃ (A : Matrix (Fin k) (Fin k) ℤ) (c : Fin k → ℤ),
        ∀ x : Fin k → ℤ, foldMap k N m x = A.mulVec x + c) ∧
    (∀ m, 1 ≤ m → m ≤ k →
      ∃ (B : Matrix (Fin k) (Fin k) ℤ) (c : Fin k → ℤ),
        ∀ y : Fin k → ℤ, foldInv k N m y = B.mulVec y + c) := by
  refine ⟨?_, a4recordFold20261014_fm3_global_piece k N hk hkN,
    fun m _ _ => a4recordFold20261014_aff2_map k N m,
    fun m _ _ => a4recordFold20261014_aff2_inv k N m⟩
  intro x hx
  obtain ⟨m, hm, _⟩ := (foldSourcePiece_partition k N hk hkN).2 x |>.1 hx
  rw [a4recordFold20261014_fm3_global_piece k N hk hkN m hm.1 hm.2.1 x hm.2.2]
  exact a4recordFold20261014_ft3_target k N m hk hkN hm.1 hm.2.1 x hm.2.2

end
private lemma a4f_source_formula2 (k N m : ℕ) (hk : 2 ≤ k)
    (hkN : k ∣ N) (x : Fin k → ℕ) :
    x ∈ foldSourcePiece k N m ↔
      (∑ s, x s ≤ N) ∧
      (∀ i ∈ Finset.Ico 1 m, i * (N / k) < foldPrefixSum k x i) ∧
      foldPrefixSum k x m ≤ m * (N / k) := by
  classical
  have hN : N = k * (N / k) := (Nat.mul_div_cancel' hkN).symm
  have hk0 : 0 < k := by omega
  have hlt (i : ℕ) : i * N < k * foldPrefixSum k x i ↔
      i * (N / k) < foldPrefixSum k x i := by
    conv_lhs => rw [hN, show i * (k * (N / k)) = k * (i * (N / k)) by ring]
    exact Nat.mul_lt_mul_left hk0
  have hle : k * foldPrefixSum k x m ≤ m * N ↔
      foldPrefixSum k x m ≤ m * (N / k) := by
    conv_lhs => rw [hN, show m * (k * (N / k)) = k * (m * (N / k)) by ring]
    exact Nat.mul_le_mul_left_iff hk0
  simp only [foldSourcePiece, Finset.mem_filter, onb_mem_simplex, hlt, hle]

private lemma a4f_target_partition (k N : ℕ) (hk : 2 ≤ k) :
    ∀ y ∈ foldTargetBase k N,
      ∃! m, 1 ≤ m ∧ m ≤ k ∧ y ∈ foldTargetPiece k N m := by
  classical
  intro y hy
  let T : ℕ → Prop := fun m =>
    foldCoord y 1 + ((m : ℤ) - 1) * ((N / k : ℕ) : ℤ) ≤
      ∑ j ∈ Finset.Icc 2 (m + 1), foldCoord y j
  have hex : ∃ m, 1 ≤ m ∧ m ≤ k ∧ (m = k ∨ T m) :=
    ⟨k, by omega, le_rfl, Or.inl rfl⟩
  let m := Nat.find hex
  have hm : 1 ≤ m ∧ m ≤ k ∧ (m = k ∨ T m) := Nat.find_spec hex
  have hsmall (i : ℕ) (hi : i ∈ Finset.Ico 1 m) :
      ∑ j ∈ Finset.Icc 2 (i + 1), foldCoord y j <
        foldCoord y 1 + ((i : ℤ) - 1) * ((N / k : ℕ) : ℤ) := by
    obtain ⟨hi1, him⟩ := Finset.mem_Ico.mp hi
    have hmin := Nat.find_min hex him
    have hnot : ¬ T i := by
      intro h
      exact hmin ⟨hi1, by omega, Or.inr h⟩
    exact lt_of_not_ge hnot
  have hmem : y ∈ foldTargetPiece k N m := by
    refine ⟨hy, hsmall, ?_⟩
    intro hmk
    rcases hm.2.2 with he | ht
    · omega
    · exact ht
  refine ⟨m, ⟨hm.1, hm.2.1, hmem⟩, ?_⟩
  intro n hn
  have hnmem : y ∈ foldTargetBase k N ∧
      (∀ i ∈ Finset.Ico 1 n,
        ∑ j ∈ Finset.Icc 2 (i + 1), foldCoord y j <
          foldCoord y 1 + ((i : ℤ) - 1) * ((N / k : ℕ) : ℤ)) ∧
      (n < k → T n) := hn.2.2
  rcases lt_trichotomy n m with hnm | he | hmn
  · have ht := hnmem.2.2 (by omega)
    have hlt := hsmall n (Finset.mem_Ico.mpr ⟨hn.1, hnm⟩)
    exact False.elim (not_lt_of_ge ht hlt)
  · exact he
  · have ht := hmem.2.2 (by omega)
    have hlt := hnmem.2.1 m (Finset.mem_Ico.mpr ⟨hm.1, hmn⟩)
    exact False.elim (not_lt_of_ge ht hlt)

private lemma a4f_coord_shift {k : ℕ} (y : Fin k → ℤ) (i : ℕ) :
    foldCoord y (i + 1) = (if h : i < k then y ⟨i, h⟩ else 0) := by
  by_cases hi : i < k
  · simp only [foldCoord, dif_pos hi]
    rw [dif_pos (by omega : 1 ≤ i + 1 ∧ i + 1 ≤ k)]
    congr 1
  · simp [foldCoord, hi, show ¬ (1 ≤ i + 1 ∧ i + 1 ≤ k) by omega]

private lemma a4f_shift_sum (f : ℕ → ℤ) (a b : ℕ) :
    (∑ j ∈ Finset.Icc (a + 1) b, f j) =
      ∑ j ∈ Finset.Ico a b, f (j + 1) := by
  classical
  symm
  apply Finset.sum_bij (fun j _ => j + 1)
  · intro j hj
    have := Finset.mem_Ico.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro j hj i hi he
    omega
  · intro j hj
    have := Finset.mem_Icc.mp hj
    exact ⟨j - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · intros
    rfl

private lemma a4f_tail_sum {k : ℕ} (y : Fin k → ℤ) :
    (∑ j ∈ Finset.Icc 2 k, foldCoord y j) =
      ∑ t ∈ Finset.univ.filter (fun t : Fin k => 0 < t.val), y t := by
  classical
  symm
  apply Finset.sum_bij (fun t _ => t.val + 1)
  · intro t ht
    have := (Finset.mem_filter.mp ht).2
    have := t.isLt
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro t ht u hu he
    apply Fin.ext
    omega
  · intro j hj
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hj
    exact ⟨⟨j - 1, by omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩, by dsimp; omega⟩
  · intro t ht
    exact (a4recordFold20261014_fm2_coord_fin y t).symm

private lemma a4f_base_formula2 (k N : ℕ) (hk : 2 ≤ k) (y : Fin k → ℤ) :
    y ∈ foldTargetBase k N ↔
      (∀ t, 0 ≤ y t) ∧ y ⟨0, by omega⟩ ≤ ((N / k : ℕ) : ℤ) ∧
        ∑ t ∈ Finset.univ.filter (fun t : Fin k => 0 < t.val), y t ≤ (N : ℤ) := by
  change ((∀ t, 0 ≤ y t) ∧ foldCoord y 1 ≤ ((N / k : ℕ) : ℤ) ∧
    (∑ j ∈ Finset.Icc 2 k, foldCoord y j) ≤ (N : ℤ)) ↔ _
  rw [a4recordFold20261014_fm2_coord y 1 (by omega) (by omega), a4f_tail_sum]

private lemma a4f_piece_formula2 (k N m : ℕ) (y : Fin k → ℤ) :
    let g : ℕ → ℤ := fun i => if h : i < k then y ⟨i, h⟩ else 0
    let q : ℤ := ((N / k : ℕ) : ℤ)
    (y ∈ foldTargetPiece k N m ↔ y ∈ foldTargetBase k N ∧
      (∀ i ∈ Finset.Ico 1 m,
        ∑ j ∈ Finset.Ico 1 (i + 1), g j < g 0 + ((i : ℤ) - 1) * q) ∧
      (m < k → g 0 + ((m : ℤ) - 1) * q ≤ ∑ j ∈ Finset.Ico 1 (m + 1), g j)) := by
  dsimp only
  unfold foldTargetPiece
  simp only [Set.mem_setOf_eq]
  simp_rw [a4f_shift_sum (foldCoord y) 1, a4f_coord_shift]

private lemma a4f_map_formula (k N m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k)
    (y : Fin k → ℤ) (t : Fin k) :
    let g : ℕ → ℤ := fun i => if h : i < k then y ⟨i, h⟩ else 0
    let q : ℤ := ((N / k : ℕ) : ℤ)
    foldMap k N m y t =
      (if m = 1 then (if t.val = 1 then g 0 + g 1 else y t)
      else if t.val = 0 then (∑ i ∈ Finset.range m, g i) - ((m : ℤ) - 1) * q
      else if t.val < m - 1 then g (m - t.val)
      else if t.val = m - 1 then g 0 - q - 1
      else if t.val = m then g 1 + g m + q + 1
      else y t) := by
  classical
  dsimp only
  have hcoord (i : ℕ) (hi : 1 ≤ i) :
      foldCoord y i = if h : i - 1 < k then y ⟨i - 1, h⟩ else 0 := by
    have he : i = (i - 1) + 1 := by omega
    conv_lhs => rw [he, a4f_coord_shift]
  have hsum : (∑ i ∈ Finset.Icc 1 m, foldCoord y i) =
      ∑ i ∈ Finset.range m, (if h : i < k then y ⟨i, h⟩ else 0) := by
    rw [a4f_shift_sum (foldCoord y) 0, Nat.Ico_zero_eq_range]
    simp_rw [a4f_coord_shift]
  simp only [foldMap]
  by_cases hm1 : m = 1
  · rw [if_pos hm1, if_pos hm1]
    by_cases ht : t.val = 1
    · simp only [ht, ite_true]
      rw [hcoord 1 (by omega), hcoord 2 (by omega)]
    · simp only [if_neg ht, if_neg (by omega : t.val + 1 ≠ 2)]
      exact a4recordFold20261014_fm2_coord_fin y t
  · rw [if_neg hm1, if_neg hm1]
    have hm2 : 2 ≤ m := by omega
    by_cases ht0 : t.val = 0
    · simp only [ht0, ite_true, hsum]
    · rw [if_neg ht0, if_neg (by omega : t.val + 1 ≠ 1)]
      by_cases htl : t.val < m - 1
      · rw [if_pos htl, if_pos (by omega : t.val + 1 < m)]
        rw [hcoord _ (by omega)]
        have he : m + 2 - (t.val + 1) - 1 = m - t.val := by omega
        rw [he]
      · rw [if_neg htl, if_neg (by omega : ¬ t.val + 1 < m)]
        by_cases htm1 : t.val = m - 1
        · rw [if_pos htm1, if_pos (by omega : t.val + 1 = m)]
          rw [hcoord 1 (by omega)]
        · rw [if_neg htm1, if_neg (by omega : t.val + 1 ≠ m)]
          by_cases htm : t.val = m
          · rw [if_pos htm, if_pos (by omega : t.val + 1 = m + 1)]
            rw [hcoord 2 (by omega), hcoord (m + 1) (by omega)]
            simp only [Nat.add_sub_cancel]
          · rw [if_neg htm, if_neg (by omega : t.val + 1 ≠ m + 1)]
            exact a4recordFold20261014_fm2_coord_fin y t

private lemma a4f_inv_formula (k N m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k)
    (y : Fin k → ℤ) (t : Fin k) :
    let g : ℕ → ℤ := fun i => if h : i < k then y ⟨i, h⟩ else 0
    let q : ℤ := ((N / k : ℕ) : ℤ)
    foldInv k N m y t =
      (if m = 1 then (if t.val = 1 then g 1 - g 0 else y t)
      else if t.val = 0 then g (m - 1) + q + 1
      else if t.val = 1 then
        g 0 + ((m : ℤ) - 2) * q - 1 - ∑ i ∈ Finset.Ico 1 m, g i
      else if t.val < m then g (m - t.val)
      else if t.val = m then
        (∑ i ∈ Finset.Ico 1 (m + 1), g i) - g 0 - ((m : ℤ) - 1) * q
      else y t) := by
  classical
  dsimp only
  have hcoord (i : ℕ) (hi : 1 ≤ i) :
      foldCoord y i = if h : i - 1 < k then y ⟨i - 1, h⟩ else 0 := by
    have he : i = (i - 1) + 1 := by omega
    conv_lhs => rw [he, a4f_coord_shift]
  simp only [foldInv]
  by_cases hm1 : m = 1
  · rw [if_pos hm1, if_pos hm1]
    by_cases ht : t.val = 1
    · simp only [ht, ite_true]
      rw [hcoord 1 (by omega), hcoord 2 (by omega)]
    · simp only [if_neg ht, if_neg (by omega : t.val + 1 ≠ 2)]
      exact a4recordFold20261014_fm2_coord_fin y t
  · rw [if_neg hm1, if_neg hm1]
    have hm2 : 2 ≤ m := by omega
    by_cases ht0 : t.val = 0
    · simp only [ht0, ite_true]
      rw [hcoord m hm]
    · rw [if_neg ht0, if_neg (by omega : t.val + 1 ≠ 1)]
      by_cases ht1 : t.val = 1
      · rw [if_pos ht1, if_pos (by omega : t.val + 1 = 2)]
        rw [hcoord 1 (by omega), a4f_shift_sum (foldCoord y) 1]
        simp_rw [a4f_coord_shift]
      · rw [if_neg ht1, if_neg (by omega : t.val + 1 ≠ 2)]
        by_cases htl : t.val < m
        · rw [if_pos htl, if_pos (by omega : t.val + 1 ≤ m)]
          rw [hcoord _ (by omega)]
          have he : m + 2 - (t.val + 1) - 1 = m - t.val := by omega
          rw [he]
        · rw [if_neg htl, if_neg (by omega : ¬ t.val + 1 ≤ m)]
          by_cases htm : t.val = m
          · rw [if_pos htm, if_pos (by omega : t.val + 1 = m + 1)]
            rw [hcoord 1 (by omega), a4f_shift_sum (foldCoord y) 1]
            simp_rw [a4f_coord_shift]
          · rw [if_neg htm, if_neg (by omega : t.val + 1 ≠ m + 1)]
            exact a4recordFold20261014_fm2_coord_fin y t

private lemma a4f_map_tail (k N m c : ℕ) (hm : 2 ≤ m)
    (hmc : m ≤ c) (hck : c ≤ k) (x : Fin k → ℤ) :
    (∑ j ∈ Finset.Icc 2 c, foldCoord (foldMap k N m x) j) =
      (∑ j ∈ Finset.Icc 1 c, foldCoord x j) -
        (if c = m then foldCoord x 2 + (N / k : ℕ) + 1 else 0) := by
  classical
  calc
    _ = ∑ j ∈ Finset.Icc 2 c,
        a4recordFold20261014_fs_seq (foldCoord x) (N / k : ℕ) m j := by
      apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨hj, hjc⟩ := Finset.mem_Icc.mp hj
      rw [a4recordFold20261014_ft_coord_map x j (by omega) (hjc.trans hck),
        if_neg (by omega : m ≠ 1), if_neg (by omega : j ≠ 1)]
    _ = _ := a4recordFold20261014_fs3_sum (foldCoord x) (N / k : ℕ) m c hm hmc

private lemma a4f_left_inverse2 (k N m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k)
    (x : Fin k → ℤ) : foldInv k N m (foldMap k N m x) = x := by
  classical
  funext t
  have hj : 1 ≤ t.val + 1 := by omega
  have hjk : t.val + 1 ≤ k := by have := t.isLt; omega
  rw [← a4recordFold20261014_fm2_coord_fin x t]
  simp only [foldInv]
  by_cases hm1 : m = 1
  · rw [if_pos hm1]
    subst m
    by_cases ht2 : t.val + 1 = 2
    · rw [if_pos ht2]
      rw [a4recordFold20261014_ft_coord_map x 2 (by omega) (by omega),
        a4recordFold20261014_ft_coord_map x 1 (by omega) (by omega)]
      rw [ht2]
      norm_num
      <;> ring
    · rw [if_neg ht2, a4recordFold20261014_ft_coord_map x _ hj hjk]
      simp [ht2]
  · rw [if_neg hm1]
    have hm2 : 2 ≤ m := by omega
    by_cases ht1 : t.val + 1 = 1
    · rw [if_pos ht1]
      rw [a4recordFold20261014_ft_coord_map x m (by omega) hmk]
      simp [hm1, a4recordFold20261014_fs_seq, show m ≠ 1 by omega, ht1]
      <;> ring
    · rw [if_neg ht1]
      by_cases ht2 : t.val + 1 = 2
      · rw [if_pos ht2]
        rw [a4recordFold20261014_ft_coord_map x 1 (by omega) (by omega),
          a4f_map_tail k N m m hm2 le_rfl hmk x]
        simp only [if_neg hm1, ite_true]
        rw [ht2]
        ring
      · rw [if_neg ht2]
        by_cases htm : t.val + 1 ≤ m
        · rw [if_pos htm]
          have hr : 2 ≤ m + 2 - (t.val + 1) := by omega
          have hrm : m + 2 - (t.val + 1) < m := by omega
          rw [a4recordFold20261014_ft_coord_map x _ (by omega) (by omega)]
          simp only [if_neg hm1, if_neg (by omega : m + 2 - (t.val + 1) ≠ 1),
            a4recordFold20261014_fs_seq, if_pos hrm]
          congr 1
          omega
        · rw [if_neg htm]
          by_cases htlast : t.val + 1 = m + 1
          · rw [if_pos htlast]
            have hmk' : m + 1 ≤ k := by omega
            rw [a4f_map_tail k N m (m + 1) hm2 (by omega) hmk' x,
              a4recordFold20261014_ft_coord_map x 1 (by omega) (by omega),
              Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
            simp only [if_neg (by omega : m + 1 ≠ m), sub_zero, if_neg hm1,
              ite_true]
            rw [htlast]
            ring
          · rw [if_neg htlast, a4recordFold20261014_ft_coord_map x _ hj hjk]
            simp [hm1, ht1, a4recordFold20261014_fs_seq, htm, htlast,
              show ¬ t.val + 1 < m by omega, show t.val + 1 ≠ m by omega,
              show t.val ≠ 0 by omega, show t.val ≠ m by omega]

private lemma a4f_invcoord {k N m : ℕ} (y : Fin k → ℤ)
    (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    foldCoord (foldInv k N m y) j =
      if m = 1 then (if j = 2 then foldCoord y 2 - foldCoord y 1 else foldCoord y j)
      else if j = 1 then foldCoord y m + (N / k : ℕ) + 1
      else if j = 2 then foldCoord y 1 + ((m : ℤ)-2)*(N / k : ℕ)-1-
        ∑ ν ∈ Finset.Icc 2 m, foldCoord y ν
      else if j ≤ m then foldCoord y (m+2-j)
      else if j = m+1 then (∑ ν ∈ Finset.Icc 2 (m+1), foldCoord y ν)-
        foldCoord y 1-((m : ℤ)-1)*(N / k : ℕ)
      else foldCoord y j := by
  rw [a4recordFold20261014_fm2_coord _ j hj hjk]
  have he : j-1+1=j := by omega
  simp only [foldInv, he]

private lemma a4f_invprefix (k N m i : ℕ) (hm : 2 ≤ m)
    (hi : 2 ≤ i) (him : i ≤ m) (hmk : m ≤ k) (y : Fin k → ℤ) :
    (∑ j ∈ Finset.Icc 1 i, foldCoord (foldInv k N m y) j) =
      foldCoord y 1+((m : ℤ)-1)*(N / k : ℕ)-
        ∑ j ∈ Finset.Icc 2 (m+1-i), foldCoord y j := by
  classical
  induction i, hi using Nat.le_induction with
  | base =>
    have hsplit := a4recordFold20261014_fs_split (foldCoord y) 2 m m hm le_rfl
    simp only [Finset.Icc_eq_empty_of_lt (by omega : m < m+1),
      Finset.sum_empty, add_zero] at hsplit
    have he : Finset.Ico 2 m = Finset.Icc 2 (m-1) := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [he] at hsplit
    norm_num [Finset.sum_Icc_succ_top, a4f_invcoord, show 1 ≤ k by omega,
      show 2 ≤ k by omega, show m ≠ 1 by omega]
    rw [hsplit]
    ring
  | succ i hi ih =>
    have him' : i ≤ m := by omega
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ i+1), ih him']
    rw [a4f_invcoord y (i+1) (by omega) (by omega)]
    simp only [if_neg (by omega : m ≠ 1), if_neg (by omega : i+1 ≠ 1),
      if_neg (by omega : i+1 ≠ 2), if_pos him]
    have he : m+1-i = (m-i)+1 := by omega
    rw [he, Finset.sum_Icc_succ_top (by omega : 2 ≤ (m-i)+1)]
    have he' : m+2-(i+1)=(m-i)+1 := by omega
    have he'' : m+1-(i+1)=m-i := by omega
    rw [he', he'']
    ring

private lemma a4f_affine_unit (k N m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k) :
    ∃ (A : Matrix (Fin k) (Fin k) ℤ) (c : Fin k → ℤ),
      IsUnit A.det ∧ ∀ x, foldMap k N m x = A *ᵥ x+c := by
  classical
  obtain ⟨A,c,hA⟩ := a4recordFold20261014_aff2_map k N m
  obtain ⟨B,d,hB⟩ := a4recordFold20261014_aff2_inv k N m
  have hzero := a4f_left_inverse2 k N m hm hmk 0
  rw [hA, hB] at hzero
  simp only [Matrix.mulVec_zero, zero_add] at hzero
  have hlin (x : Fin k → ℤ) : (B*A) *ᵥ x = x := by
    have he := a4f_left_inverse2 k N m hm hmk x
    rw [hA,hB,Matrix.mulVec_add,Matrix.mulVec_mulVec] at he
    rw [add_assoc,hzero,add_zero] at he
    exact he
  have hBA : B*A = 1 := by
    ext i j
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.one_apply,
      Pi.single_apply] using congrFun (hlin (Pi.single j 1)) i
  exact ⟨A,c,Matrix.isUnit_det_of_left_inverse hBA,hA⟩

private lemma a4f_right_inverse (k N m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k)
    (y : Fin k → ℤ) : foldMap k N m (foldInv k N m y) = y := by
  obtain ⟨A,c,hunit,hA⟩ := a4f_affine_unit k N m hm hmk
  have hsur := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr hunit)
  obtain ⟨x,hx⟩ := hsur (y-c)
  have he : foldMap k N m x = y := by rw [hA,hx]; abel
  rw [← he,a4f_left_inverse2 k N m hm hmk]

private lemma a4f_invtotal (k N m c : ℕ) (hm : 2 ≤ m) (hmc : m ≤ c)
    (hck : c ≤ k) (y : Fin k → ℤ) :
    (∑ j ∈ Finset.Icc 1 c, foldCoord (foldInv k N m y) j) =
      if c=m then foldCoord y 1+((m : ℤ)-1)*(N / k : ℕ)
      else ∑ j ∈ Finset.Icc 2 c, foldCoord y j := by
  classical
  induction c, hmc using Nat.le_induction with
  | base =>
    rw [a4f_invprefix k N m m hm hm le_rfl hck y]
    simp
  | succ c hc ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ c+1),ih (by omega),
      a4f_invcoord y (c+1) (by omega) hck]
    simp only [if_neg (by omega : m ≠ 1),if_neg (by omega : c+1 ≠ 1),
      if_neg (by omega : c+1 ≠ 2), if_neg (by omega : ¬ c+1 ≤ m),
      if_neg (by omega : c+1 ≠ m)]
    by_cases he : c=m
    · subst c
      simp only [ite_true]
      ring
    · simp only [if_neg he,if_neg (by omega : c+1 ≠ m+1)]
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ c+1)]

private lemma a4f_invtotal_one (k N : ℕ) (hk : 2 ≤ k) (y : Fin k → ℤ) :
    (∑ j ∈ Finset.Icc 1 k, foldCoord (foldInv k N 1 y) j) =
      ∑ j ∈ Finset.Icc 2 k, foldCoord y j := by
  classical
  have hs : (∑ j ∈ Finset.Icc 1 k, foldCoord (foldInv k N 1 y) j) =
      (∑ j ∈ Finset.Icc 1 k, foldCoord y j)-foldCoord y 1 := by
    calc
      _ = ∑ j ∈ Finset.Icc 1 k,
          (foldCoord y j - if j=2 then foldCoord y 1 else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        obtain ⟨hj,hjk⟩ := Finset.mem_Icc.mp hj
        rw [a4f_invcoord y j hj hjk]
        split_ifs <;> simp_all
      _ = _ := by simp [Finset.sum_sub_distrib,Finset.mem_Icc,hk]
  rw [hs]
  have he := a4recordFold20261014_fs_split (foldCoord y) 1 1 k le_rfl (by omega)
  simpa using congrArg (fun z => z-foldCoord y 1) he

private lemma a4f_inv_nonneg (k N m : ℕ) (hk : 2 ≤ k)
    (hm : 1 ≤ m) (hmk : m ≤ k) (y : Fin k → ℤ)
    (hy : y ∈ foldTargetPiece k N m) : ∀ t, 0 ≤ foldInv k N m y t := by
  have hf (j : ℕ) : 0 ≤ foldCoord y j := by
    unfold foldCoord
    split_ifs <;> simp [hy.1.1]
  have hq : (0 : ℤ) ≤ (N / k : ℕ) := by positivity
  intro t
  rw [← a4recordFold20261014_fm2_coord_fin (foldInv k N m y) t,
    a4f_invcoord y (t.val+1) (by omega) (by have := t.isLt; omega)]
  by_cases hm1 : m=1
  · subst m
    simp only [ite_true]
    split_ifs
    · have hh := hy.2.2 (by omega)
      norm_num at hh
      omega
    · exact hf _
  · rw [if_neg hm1]
    have hm2 : 2 ≤ m := by omega
    split_ifs with ht1 ht2 htm htlast
    · have := hf m; omega
    · have hh := hy.2.1 (m-1) (Finset.mem_Ico.mpr ⟨by omega,by omega⟩)
      have he : m-1+1=m := by omega
      rw [he,Nat.cast_sub (by omega : 1 ≤ m)] at hh
      norm_num only [Nat.cast_one] at hh
      ring_nf at hh ⊢
      omega
    · exact hf _
    · have hh := hy.2.2 (by have := t.isLt; omega)
      omega
    · exact hf _

private lemma a4f_inv_source (k N m : ℕ) (hk : 2 ≤ k) (hkN : k ∣ N)
    (hm : 1 ≤ m) (hmk : m ≤ k) (y : Fin k → ℤ)
    (hy : y ∈ foldTargetPiece k N m) :
    foldInv k N m y ∈ (fun x : Fin k → ℕ => fun t => (x t : ℤ)) ''
      (foldSourcePiece k N m : Set (Fin k → ℕ)) := by
  classical
  let X := foldInv k N m y
  let x : Fin k → ℕ := fun t => (X t).toNat
  have hc : (fun t => (x t : ℤ)) = X := by
    funext t
    exact Int.toNat_of_nonneg (a4f_inv_nonneg k N m hk hm hmk y hy t)
  have hprefix (i : ℕ) (hi : i ≤ k) :
      (foldPrefixSum k x i : ℤ) = ∑ j ∈ Finset.Icc 1 i, foldCoord X j := by
    rw [← a4recordFold20261014_fm2_prefix x i hi,hc]
  have hN : (N : ℤ) = (k : ℤ) * (N / k : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hkN).symm
  have htotal : (∑ t, x t : ℕ) ≤ N := by
    have hp := hprefix k le_rfl
    have ht : foldPrefixSum k x k = ∑ t, x t := by simp [foldPrefixSum]
    rw [ht] at hp
    apply Int.ofNat_le.mp
    rw [hp]
    change (∑ j ∈ Finset.Icc 1 k, foldCoord (foldInv k N m y) j) ≤ (N : ℤ)
    by_cases hm1 : m=1
    · subst m
      rw [a4f_invtotal_one k N hk y]
      exact hy.1.2.2
    · rw [a4f_invtotal k N m k (by omega) hmk le_rfl y]
      split_ifs with he
      · rw [hN]
        have := hy.1.2.1
        have hq : (0 : ℤ) ≤ (N / k : ℕ) := by positivity
        subst k
        nlinarith
      · exact hy.1.2.2
  refine ⟨x,?_,hc⟩
  apply (a4f_source_formula2 k N m hk hkN x).2
  refine ⟨htotal,?_,?_⟩
  · intro i hi
    obtain ⟨hi1,him⟩ := Finset.mem_Ico.mp hi
    have hm2 : 2 ≤ m := by omega
    apply Int.ofNat_lt.mp
    rw [Nat.cast_mul,hprefix i (by omega)]
    change (i : ℤ)*(N / k : ℕ) < ∑ j ∈ Finset.Icc 1 i, foldCoord (foldInv k N m y) j
    by_cases hi2 : i=1
    · subst i
      try simp only [Finset.Icc_self, Finset.sum_singleton]
      rw [a4f_invcoord y 1 le_rfl (by omega)]
      try simp only [if_neg (by omega : m ≠ 1), ite_true]
      have hf : 0 ≤ foldCoord y m := by
        rw [a4recordFold20261014_fm2_coord y m hm hmk]
        exact hy.1.1 _
      norm_num
      omega
    · rw [a4f_invprefix k N m i hm2 (by omega) (by omega) hmk y]
      have hh := hy.2.1 (m-i) (Finset.mem_Ico.mpr ⟨by omega,by omega⟩)
      have he : m-i+1=m+1-i := by omega
      rw [he,Nat.cast_sub (by omega : i ≤ m)] at hh
      nlinarith
  · apply Int.ofNat_le.mp
    rw [Nat.cast_mul,hprefix m hmk]
    change (∑ j ∈ Finset.Icc 1 m, foldCoord (foldInv k N m y) j) ≤ (m : ℤ)*(N / k : ℕ)
    by_cases hm1 : m=1
    · subst m
      try simp only [Finset.Icc_self, Finset.sum_singleton]
      rw [a4f_invcoord y 1 le_rfl (by omega)]
      simpa using hy.1.2.1
    · rw [a4f_invprefix k N m m (by omega) (by omega) le_rfl hmk y]
      rw [show m+1-m=1 by omega]
      simp only [Finset.Icc_eq_empty_of_lt (by omega : 1 < (2:ℕ)),
        Finset.sum_empty,sub_zero]
      have := hy.1.2.1
      nlinarith

private lemma a4f_split_sum (f : ℕ → ℤ) (b c : ℕ) (hb : 1 ≤ b) (hbc : b ≤ c) :
    (∑ j ∈ Finset.Icc 1 c, f j) =
      (∑ j ∈ Finset.Icc 1 b, f j)+∑ j ∈ Finset.Icc (b+1) c, f j := by
  have hs := a4recordFold20261014_fs_split f 1 b c hb hbc
  have ht := a4recordFold20261014_fs_split f 1 b b hb le_rfl
  simp only [Finset.Icc_eq_empty_of_lt (by omega : b < b+1),Finset.sum_empty,add_zero] at ht
  rw [← ht] at hs
  exact hs

private lemma a4f_map_short_tail (k N m i : ℕ) (hi : 1 ≤ i)
    (him : i+1 < m) (hmk : m ≤ k) (x : Fin k → ℤ) :
    (∑ j ∈ Finset.Icc 2 (i+1), foldCoord (foldMap k N m x) j) =
      ∑ j ∈ Finset.Icc (m+1-i) m, foldCoord x j := by
  classical
  calc
    _ = ∑ j ∈ Finset.Icc 2 (i+1), foldCoord x (m+2-j) := by
      apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨hj,hji⟩ := Finset.mem_Icc.mp hj
      rw [a4recordFold20261014_ft_coord_map x j (by omega) (by omega)]
      simp [show m ≠ 1 by omega,show j ≠ 1 by omega,
        a4recordFold20261014_fs_seq,show j < m by omega]
    _ = _ := by
      apply Finset.sum_bij (fun j _ => m+2-j)
      · intro j hj
        have := Finset.mem_Icc.mp hj
        apply Finset.mem_Icc.mpr
        constructor <;> omega
      · intro j hj l hl he
        have := Finset.mem_Icc.mp hj
        have := Finset.mem_Icc.mp hl
        omega
      · intro j hj
        have := Finset.mem_Icc.mp hj
        refine ⟨m+2-j,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
      · intros; rfl

private lemma a4f_map_piece (k N m : ℕ) (hk : 2 ≤ k) (hkN : k ∣ N)
    (hm : 1 ≤ m) (hmk : m ≤ k) (x : Fin k → ℕ)
    (hx : x ∈ foldSourcePiece k N m) :
    foldMap k N m (fun t => (x t : ℤ)) ∈ foldTargetPiece k N m := by
  classical
  let X : Fin k → ℤ := fun t => (x t : ℤ)
  have hs := a4recordFold20261014_ft2_source k N m hk hkN x hx
  have hbase := a4recordFold20261014_ft3_target k N m hk hkN hm hmk x hx
  refine ⟨hbase,?_,?_⟩
  · intro i hi
    obtain ⟨hi1,him⟩ := Finset.mem_Ico.mp hi
    have hm2 : 2 ≤ m := by omega
    rw [a4recordFold20261014_ft_coord_map X 1 le_rfl (by omega)]
    simp only [if_neg (by omega : m ≠ 1),ite_true]
    by_cases him' : i+1 < m
    · rw [a4f_map_short_tail k N m i hi1 him' hmk X]
      have hsplit := a4f_split_sum (foldCoord X) (m-i) m (by omega) (by omega)
      have he : m-i+1=m+1-i := by omega
      rw [he] at hsplit
      have hh := hs.1 (m-i) (Finset.mem_Ico.mpr ⟨by omega,by omega⟩)
      have hh' : (((m-i : ℕ) : ℤ)*(N / k : ℕ)) <
          ∑ j ∈ Finset.Icc 1 (m-i), foldCoord X j := by
        rw [a4recordFold20261014_fm2_prefix x (m-i) (by omega)]
        exact_mod_cast hh
      rw [Nat.cast_sub (by omega : i ≤ m)] at hh'
      nlinarith
    · have he : i+1=m := by omega
      rw [he,a4f_map_tail k N m m hm2 le_rfl hmk X]
      simp only [ite_true]
      have hf := a4recordFold20261014_ft_nonneg x 2
      have hie : (i : ℤ) = (m : ℤ)-1 := by omega
      rw [hie]
      dsimp [X] at *
      nlinarith
  · intro hmk'
    by_cases hm1 : m=1
    · subst m
      rw [a4recordFold20261014_ft_coord_map X 1 le_rfl (by omega)]
      norm_num [a4recordFold20261014_ft_coord_map,show 2 ≤ k by omega]
      have hf := a4recordFold20261014_ft_nonneg x 2
      exact le_add_of_nonneg_right hf
    · have hm2 : 2 ≤ m := by omega
      rw [a4recordFold20261014_ft_coord_map X 1 le_rfl (by omega),
        a4f_map_tail k N m (m+1) hm2 (by omega) (by omega) X,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ m+1)]
      simp only [if_neg (by omega : m+1 ≠ m),sub_zero,if_neg hm1,ite_true]
      have hf := a4recordFold20261014_ft_nonneg x (m+1)
      dsimp [X] at *
      nlinarith

private lemma a4f_coord_single (k : ℕ) (s : Fin k) (i : ℕ) :
    foldCoord (Pi.single s 1 : Fin k → ℤ) i = if i=s.val+1 then 1 else 0 := by
  classical
  by_cases hi : 1 ≤ i ∧ i ≤ k
  · rw [foldCoord, dif_pos hi]
    by_cases he : i = s.val+1
    · rw [if_pos he]
      have hs : (⟨i-1,by omega⟩ : Fin k) = s := by apply Fin.ext; dsimp; omega
      simp [hs]
    · rw [if_neg he]
      have hs : (⟨i-1,by omega⟩ : Fin k) ≠ s := by
        intro hs
        have ht : i-1=s.val := congrArg Fin.val hs
        omega
      simp [hs]
  · rw [foldCoord,dif_neg hi,if_neg (by have := s.isLt; omega : i ≠ s.val+1)]

private lemma a4f_entries (k N m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k) :
    ∃ (A : Matrix (Fin k) (Fin k) ℤ) (c : Fin k → ℤ),
      (A.det=1 ∨ A.det= -1) ∧ (∀ i j, A i j=0 ∨ A i j=1) ∧
      ∀ x, foldMap k N m x=A *ᵥ x+c := by
  classical
  obtain ⟨A,c,hunit,hA⟩ := a4f_affine_unit k N m hm hmk
  refine ⟨A,c,Int.isUnit_iff.mp hunit,?_,hA⟩
  intro i j
  have hsingle := congrFun (hA (Pi.single j 1)) i
  have hzero := congrFun (hA 0) i
  simp only [Matrix.mulVec_single_one,Matrix.col_apply,Pi.add_apply] at hsingle
  simp only [Matrix.mulVec_zero,Pi.add_apply,Pi.zero_apply,zero_add] at hzero
  have he : A i j = foldMap k N m (Pi.single j 1) i-foldMap k N m 0 i := by omega
  rw [he]
  have hsum : (∑ ν ∈ Finset.Icc 1 m, foldCoord (Pi.single j 1 : Fin k → ℤ) ν) =
      if j.val < m then 1 else 0 := by
    simp only [a4f_coord_single,Finset.sum_ite_eq',Finset.mem_Icc]
    have := j.isLt
    simp only [show 1 ≤ j.val+1 by omega,true_and]
    split_ifs <;> omega
  simp only [foldMap]
  simp only [hsum]
  simp only [a4f_coord_single,a4recordFold20261014_aff2_coord_zero,
    Finset.sum_const_zero]
  by_cases hm1 : m=1
  · simp only [if_pos hm1]
    split_ifs <;> omega
  · have hm2 : 2 ≤ m := by omega
    simp only [if_neg hm1]
    split_ifs <;> omega

private lemma a4f_l1 (k : ℕ) (v : Fin k → ℤ) (hv : ∀ t, |v t| ≤ 1) :
    (∑ t, |v t|) ≤ (k : ℤ) := by
  calc
    _ ≤ ∑ _ : Fin k, (1 : ℤ) := Finset.sum_le_sum (fun t _ => hv t)
    _ = _ := by simp

private lemma a4f_source_poly (k N m : ℕ) (hk : 2 ≤ k) (hkN : k ∣ N)
    (hm : 1 ≤ m) (hmk : m ≤ k) :
    ∃ L : Finset ((Fin k → ℤ) × ℤ),
      (fun x : Fin k → ℕ => fun t => (x t : ℤ)) ''
        (foldSourcePiece k N m : Set (Fin k → ℕ)) = polyPZ k L ∧
      L.card ≤ 2*k+1 ∧ ∀ p ∈ L, (∑ t, |p.1 t|) ≤ (k : ℤ) := by
  classical
  let C : Finset ((Fin k → ℤ) × ℤ) := Finset.univ.image (fun j : Fin k => (coordVec k j,0))
  let P : ℕ → ((Fin k → ℤ) × ℤ) := fun i =>
    ((fun t => if t.val < i then 1 else 0),-(i : ℤ)*(N / k : ℕ)-1)
  let T : ((Fin k → ℤ) × ℤ) := ((fun _ => -1),(N : ℤ))
  let F : ((Fin k → ℤ) × ℤ) :=
    ((fun t => if t.val < m then -1 else 0),(m : ℤ)*(N / k : ℕ))
  let L := C ∪ insert T (insert F ((Finset.Ico 1 m).image P))
  have hmem (y : Fin k → ℤ) : y ∈ polyPZ k L ↔
      (∀ t, 0 ≤ y t) ∧ (∑ t,y t) ≤ (N : ℤ) ∧
      (∀ i ∈ Finset.Ico 1 m, (i : ℤ)*(N / k : ℕ) <
        ∑ t ∈ Finset.univ.filter (fun t : Fin k => t.val < i),y t) ∧
      (∑ t ∈ Finset.univ.filter (fun t : Fin k => t.val < m),y t) ≤
        (m : ℤ)*(N / k : ℕ) := by
    simp only [polyPZ,L,C,Finset.forall_mem_union,Finset.forall_mem_image,
      Finset.forall_mem_insert,Set.mem_setOf_eq,Finset.mem_univ,forall_const]
    have hd (j : Fin k) : (∑ t,coordVec k j t*y t) = y j := by simp [coordVec]
    have hp (i : ℕ) : (∑ t,(P i).1 t*y t)+(P i).2 =
        (∑ t ∈ Finset.univ.filter (fun t : Fin k => t.val < i),y t)-
          (i : ℤ)*(N / k : ℕ)-1 := by
      simp [P,Finset.sum_filter,ite_mul]
      ring
    have ht : (∑ t,T.1 t*y t)+T.2 = (N : ℤ)-∑ t,y t := by
      simp [T]
      ring
    have hf : (∑ t,F.1 t*y t)+F.2 = (m : ℤ)*(N / k : ℕ)-
        ∑ t ∈ Finset.univ.filter (fun t : Fin k => t.val < m),y t := by
      simp only [F,ite_mul,neg_one_mul,zero_mul,Finset.sum_filter]
      have he : (∑ t : Fin k,if t.val < m then -y t else 0) =
          -(∑ t : Fin k,if t.val < m then y t else 0) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro t ht
        split_ifs <;> simp
      rw [he]
      ring
    simp only [hd,add_zero,hp,ht,hf]
    have he (a b : ℤ) : 0 ≤ a-b-1 ↔ b<a := by omega
    simp only [he,sub_nonneg]
    tauto
  refine ⟨L,?_,?_,?_⟩
  · ext y
    rw [hmem]
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hs := (a4f_source_formula2 k N m hk hkN x).1 hx
      refine ⟨fun t => Nat.cast_nonneg _,?_,?_,?_⟩
      · dsimp only
        exact_mod_cast hs.1
      · intro i hi
        dsimp only
        exact_mod_cast hs.2.1 i hi
      · dsimp only
        exact_mod_cast hs.2.2
    · rintro ⟨hn,ht,hp,hf⟩
      let x : Fin k → ℕ := fun t => (y t).toNat
      have hc : (fun t => (x t : ℤ)) = y := by
        funext t; exact Int.toNat_of_nonneg (hn t)
      refine ⟨x,?_,hc⟩
      apply (a4f_source_formula2 k N m hk hkN x).2
      have hsum : (∑ t,(x t : ℤ)) = ∑ t,y t := by rw [hc]
      have hs (i) : (foldPrefixSum k x i : ℤ) =
          ∑ t ∈ Finset.univ.filter (fun t : Fin k => t.val < i),y t := by
        simp only [foldPrefixSum,Nat.cast_sum]; rw [hc]
      refine ⟨?_,?_,?_⟩
      · exact_mod_cast (show (∑ t,(x t : ℤ)) ≤ (N : ℤ) by rwa [hsum])
      · intro i hi
        have hh : (i : ℤ)*(N / k : ℕ) < (foldPrefixSum k x i : ℤ) := by
          rw [hs]
          exact hp i hi
        exact_mod_cast hh
      · have hh : (foldPrefixSum k x m : ℤ) ≤ (m : ℤ)*(N / k : ℕ) := by
          rw [hs]
          exact hf
        exact_mod_cast hh
  · have hC : C.card ≤ k := Finset.card_image_le.trans (by simp)
    have hP : ((Finset.Ico 1 m).image P).card ≤ m-1 :=
      Finset.card_image_le.trans (by simp)
    have hF := Finset.card_insert_le F ((Finset.Ico 1 m).image P)
    have hT := Finset.card_insert_le T (insert F ((Finset.Ico 1 m).image P))
    have hL := Finset.card_union_le C (insert T (insert F ((Finset.Ico 1 m).image P)))
    dsimp only [L]
    omega
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
      apply a4f_l1
      intro t
      simp only [coordVec]
      split_ifs <;> norm_num
    · rcases Finset.mem_insert.mp hp with rfl | hp
      · apply a4f_l1; intro t; norm_num [T]
      · rcases Finset.mem_insert.mp hp with rfl | hp
        · apply a4f_l1; intro t; dsimp [F]; split_ifs <;> norm_num
        · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
          apply a4f_l1; intro t; dsimp [P]; split_ifs <;> norm_num

private lemma a4f_tail_filter (k i : ℕ) (hik : i < k) (y : Fin k → ℤ) :
    (∑ t ∈ Finset.univ.filter (fun t : Fin k => 0 < t.val ∧ t.val ≤ i),y t) =
      ∑ j ∈ Finset.Icc 2 (i+1),foldCoord y j := by
  classical
  apply Finset.sum_bij (fun t _ => t.val+1)
  · intro t ht
    have := (Finset.mem_filter.mp ht).2
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  · intro t ht u hu he
    apply Fin.ext; omega
  · intro j hj
    have := Finset.mem_Icc.mp hj
    refine ⟨⟨j-1,by omega⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩,
      by dsimp; omega⟩ <;> dsimp <;> omega
  · intro t ht
    exact (a4recordFold20261014_fm2_coord_fin y t).symm

private lemma a4f_target_poly (k N m : ℕ) (hk : 2 ≤ k)
    (hm : 1 ≤ m) (hmk : m ≤ k) :
    ∃ L : Finset ((Fin k → ℤ) × ℤ), foldTargetPiece k N m = polyPZ k L ∧
      L.card ≤ 2*k+1 ∧ ∀ p ∈ L,(∑ t,|p.1 t|) ≤ (k : ℤ) := by
  classical
  let z : Fin k := ⟨0,by omega⟩
  let q : ℤ := (N / k : ℕ)
  let C : Finset ((Fin k → ℤ) × ℤ) := Finset.univ.image (fun j : Fin k => (coordVec k j,0))
  let P : ℕ → ((Fin k → ℤ) × ℤ) := fun i =>
    ((fun t => coordVec k z t - if 0 < t.val ∧ t.val ≤ i then 1 else 0),
      ((i : ℤ)-1)*q-1)
  let B : ((Fin k → ℤ) × ℤ) := (-coordVec k z,q)
  let T : ((Fin k → ℤ) × ℤ) := ((fun t => if 0 < t.val then -1 else 0),(N : ℤ))
  let F : ((Fin k → ℤ) × ℤ) := (-(P m).1,-((m : ℤ)-1)*q)
  let E : Finset ((Fin k → ℤ) × ℤ) := if m < k then {F} else ∅
  let L := C ∪ insert B (insert T (((Finset.Ico 1 m).image P) ∪ E))
  have hdot (y : Fin k → ℤ) (j : Fin k) : (∑ t,coordVec k j t*y t)=y j := by
    simp [coordVec]
  have hP (y : Fin k → ℤ) (i : ℕ) (hi : i < k) :
      (∑ t,(P i).1 t*y t)+(P i).2 =
        foldCoord y 1+((i : ℤ)-1)*q-1-
          ∑ j ∈ Finset.Icc 2 (i+1),foldCoord y j := by
    simp only [P,sub_mul,Finset.sum_sub_distrib,hdot,ite_mul,one_mul,zero_mul]
    rw [← Finset.sum_filter,a4f_tail_filter k i hi y]
    rw [a4recordFold20261014_fm2_coord y 1 le_rfl (by omega)]
    have hz : (⟨1-1,by omega⟩ : Fin k)=z := rfl
    rw [hz]
    ring
  have hF (y : Fin k → ℤ) (hi : m < k) : (∑ t,F.1 t*y t)+F.2 =
      (∑ j ∈ Finset.Icc 2 (m+1),foldCoord y j)-foldCoord y 1-((m : ℤ)-1)*q := by
    simp only [F,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib]
    have hp := hP y m hi
    dsimp only [P] at hp ⊢
    linarith
  have hT (y : Fin k → ℤ) : (∑ t,T.1 t*y t)+T.2 =
      (N : ℤ)-∑ j ∈ Finset.Icc 2 k,foldCoord y j := by
    simp only [T,ite_mul,neg_one_mul,zero_mul]
    have he : (∑ t : Fin k,if 0 < t.val then -y t else 0) =
        -(∑ t ∈ Finset.univ.filter (fun t : Fin k => 0 < t.val),y t) := by
      simp only [Finset.sum_filter,← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro t ht; split_ifs <;> simp
    rw [he,← a4f_tail_sum]
    ring
  have hB (y : Fin k → ℤ) : (∑ t,B.1 t*y t)+B.2 = q-foldCoord y 1 := by
    simp only [B,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib,hdot]
    rw [a4recordFold20261014_fm2_coord y 1 le_rfl (by omega)]
    change -y z+q=q-y z
    ring
  have hmem (y : Fin k → ℤ) : y ∈ polyPZ k L ↔ y ∈ foldTargetPiece k N m := by
    simp only [polyPZ,L,C,Finset.forall_mem_union,Finset.forall_mem_image,
      Finset.forall_mem_insert,Set.mem_setOf_eq,Finset.mem_univ,forall_const,
      hdot,add_zero,hB,hT]
    change ((∀ t,0 ≤ y t) ∧ 0 ≤ q-foldCoord y 1 ∧
      0 ≤ (N : ℤ)-(∑ j ∈ Finset.Icc 2 k,foldCoord y j) ∧
      (∀ i ∈ Finset.Ico 1 m,0 ≤ (∑ t,(P i).1 t*y t)+(P i).2) ∧
      (∀ p ∈ E,0 ≤ (∑ t,p.1 t*y t)+p.2)) ↔ _
    dsimp only [q] at *
    constructor
    · rintro ⟨hn,hb,ht,hp,he⟩
      refine ⟨⟨hn,by omega,by omega⟩,?_,?_⟩
      · intro i hi
        have hh := hp i hi
        rw [hP y i (by have := Finset.mem_Ico.mp hi; omega)] at hh
        omega
      · intro hmk'
        have hh := he F (by simp [E,hmk'])
        rw [hF y hmk'] at hh
        omega
    · rintro ⟨⟨hn,hb,ht⟩,hp,he⟩
      refine ⟨hn,by omega,by omega,?_,?_⟩
      · intro i hi
        rw [hP y i (by have := Finset.mem_Ico.mp hi; omega)]
        have hh := hp i hi
        omega
      · intro p hp'
        by_cases hmk' : m < k
        · have heq : p=F := by simpa [E,hmk'] using hp'
          subst p
          rw [hF y hmk']
          have hh := he hmk'
          omega
        · simp [E,hmk'] at hp'
  refine ⟨L,Set.ext (fun y => (hmem y).symm),?_,?_⟩
  · have hC : C.card ≤ k := Finset.card_image_le.trans (by simp)
    have hP : ((Finset.Ico 1 m).image P).card ≤ m-1 :=
      Finset.card_image_le.trans (by simp)
    have hU := Finset.card_union_le ((Finset.Ico 1 m).image P) E
    have hT := Finset.card_insert_le T (((Finset.Ico 1 m).image P) ∪ E)
    have hB := Finset.card_insert_le B (insert T (((Finset.Ico 1 m).image P) ∪ E))
    have hL := Finset.card_union_le C
      (insert B (insert T (((Finset.Ico 1 m).image P) ∪ E)))
    by_cases he : m < k
    · have hE : E.card=1 := by simp [E,he]
      dsimp only [L]; omega
    · have hE : E.card=0 := by simp [E,he]
      dsimp only [L]; omega
  · have hnorm (i : ℕ) : (∑ t,|(P i).1 t|) ≤ (k : ℤ) := by
      apply a4f_l1
      intro t
      dsimp [P,coordVec]
      by_cases ht : t=z
      · subst t
        simp [z]
      · simp only [if_neg ht]
        split_ifs <;> norm_num
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
      apply a4f_l1; intro t; dsimp [coordVec]; split_ifs <;> norm_num
    · rcases Finset.mem_insert.mp hp with rfl | hp
      · apply a4f_l1; intro t; dsimp [B,coordVec]; split_ifs <;> norm_num
      · rcases Finset.mem_insert.mp hp with rfl | hp
        · apply a4f_l1; intro t; dsimp [T]; split_ifs <;> norm_num
        · rcases Finset.mem_union.mp hp with hp | hp
          · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
            exact hnorm i
          · by_cases he : m < k
            · have heq : p=F := by simpa [E,he] using hp
              subst p
              simpa only [F,Pi.neg_apply,abs_neg] using hnorm m
            · simp [E,he] at hp

theorem prop_fold (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N) (hkN : k ∣ N) :
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
        ∀ x : Fin k → ℤ, foldMap k N m x = A.mulVec x + c) := by
  classical
  have himage (m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k) :
      foldMap k N m '' ((fun x : Fin k → ℕ => fun t => (x t : ℤ)) ''
        (foldSourcePiece k N m : Set (Fin k → ℕ))) = foldTargetPiece k N m := by
    ext y
    constructor
    · rintro ⟨z,⟨x,hx,rfl⟩,rfl⟩
      exact a4f_map_piece k N m hk hkN hm hmk x hx
    · intro hy
      exact ⟨foldInv k N m y,a4f_inv_source k N m hk hkN hm hmk y hy,
        a4f_right_inverse k N m hm hmk y⟩
  have hpartition := a4f_target_partition k N hk
  refine ⟨?_,a4f_base_formula2 k N hk,?_,himage,?_,hpartition,?_,?_,?_,?_⟩
  · intro m hm hmk x
    exact a4f_source_formula2 k N m hk hkN x
  · intro m hm hmk y
    exact ⟨a4f_piece_formula2 k N m y,
      fun t => ⟨a4f_map_formula k N m hm hmk y t,
        a4f_inv_formula k N m hm hmk y t⟩⟩
  · intro m hm hmk y hy
    exact hy.1
  · intro m hm hmk y hy
    exact ⟨a4f_inv_source k N m hk hkN hm hmk y hy,
      a4f_right_inverse k N m hm hmk y⟩
  · intro m hm hmk x hx
    exact a4f_left_inverse2 k N m hm hmk _
  · refine ⟨(foldMap_spec k N hk hkN).1,?_,?_⟩
    · intro x hx x' hx' he
      obtain ⟨m,hm,_⟩ := (foldSourcePiece_partition k N hk hkN).2 x |>.1 hx
      obtain ⟨m',hm',_⟩ := (foldSourcePiece_partition k N hk hkN).2 x' |>.1 hx'
      have hxmap := a4recordFold20261014_fm3_global_piece k N hk hkN m hm.1 hm.2.1 x hm.2.2
      have hxmap' := a4recordFold20261014_fm3_global_piece k N hk hkN m' hm'.1 hm'.2.1 x' hm'.2.2
      have htarget : foldMapGlobal k N x ∈ foldTargetBase k N :=
        (foldMap_spec k N hk hkN).1 x hx
      obtain ⟨n,hn,hu⟩ := hpartition _ htarget
      have hmem : foldMapGlobal k N x ∈ foldTargetPiece k N m := by
        rw [hxmap]
        exact a4f_map_piece k N m hk hkN hm.1 hm.2.1 x hm.2.2
      have hmem' : foldMapGlobal k N x ∈ foldTargetPiece k N m' := by
        rw [he,hxmap']
        exact a4f_map_piece k N m' hk hkN hm'.1 hm'.2.1 x' hm'.2.2
      have hmm : m'=m := (hu m' ⟨hm'.1,hm'.2.1,hmem'⟩).trans
        (hu m ⟨hm.1,hm.2.1,hmem⟩).symm
      subst m'
      rw [hxmap,hxmap'] at he
      have hcast := congrArg (foldInv k N m) he
      rw [a4f_left_inverse2 k N m hm.1 hm.2.1,
        a4f_left_inverse2 k N m hm.1 hm.2.1] at hcast
      funext t
      exact_mod_cast congrFun hcast t
    · intro y hy
      obtain ⟨m,hm,_⟩ := hpartition y hy
      obtain ⟨x,hx,hcast⟩ := a4f_inv_source k N m hk hkN hm.1 hm.2.1 y hm.2.2
      change (fun t => (x t : ℤ)) = foldInv k N m y at hcast
      refine ⟨x,((foldSourcePiece_partition k N hk hkN).1 m hm.1 hm.2.1).1 hx,?_⟩
      rw [a4recordFold20261014_fm3_global_piece k N hk hkN m hm.1 hm.2.1 x hx,
        hcast,a4f_right_inverse k N m hm.1 hm.2.1]
  · intro m hm hmk
    exact ⟨a4f_source_poly k N m hk hkN hm hmk,
      a4f_target_poly k N m hk hm hmk,a4f_entries k N m hm hmk⟩
noncomputable def foldUN : (k : ℕ) → ℕ → (Fin k → ℕ) → Fin k → ℕ
  | 0, _, x => x
  | 1, _, x => x
  | k + 2, N, x =>
    if N = 0 then 0 else
      let l : Fin (k + 2) → ℕ := fun t => (foldMapGlobal (k + 2) N x t).toNat
      Fin.cons (α := fun _ => ℕ) (l 0) (foldUN (k + 1) N (Fin.tail (α := fun _ => ℕ) l))

noncomputable def foldStage (k N j : ℕ) (y : Fin k → ℤ) : Fin k → ℤ := fun t =>
  if h : t.val < j then y t
  else
    foldMapGlobal (k - j) N
      (fun s : Fin (k - j) => (y ⟨s.val + j, by have := s.isLt; omega⟩).toNat)
      ⟨t.val - j, by have := t.isLt; omega⟩

theorem foldUN_one (N : ℕ) (x : Fin 1 → ℕ) : foldUN 1 N x = x := by
  rfl

theorem foldUN_zero (k : ℕ) : foldUN k 0 0 = 0 := by
  cases k with
  | zero => rfl
  | succ k => cases k <;> simp [foldUN]

private lemma a4un_lcm (k N : ℕ) (hk : 1 ≤ k) (h : lcmUpTo k ∣ N) :
    k ∣ N ∧ lcmUpTo (k - 1) ∣ N := by
  constructor
  · exact (Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hk, le_rfl⟩)).trans h
  · apply dvd_trans _ h
    apply Finset.lcm_dvd
    intro i hi
    apply Finset.dvd_lcm
    obtain ⟨hi1, hik⟩ := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨hi1, by omega⟩

private lemma a4un_tail (k N : ℕ) (hk : 2 ≤ k) (y : Fin k → ℤ)
    (hy : y ∈ foldTargetBase k N) :
    (fun s : Fin (k - 1) => (y ⟨s.val + 1, by have := s.isLt; omega⟩).toNat) ∈
      simplexS (k - 1) N := by
  apply (onb_mem_simplex _ _ _).2
  have hsum : (∑ s : Fin (k - 1), y ⟨s.val + 1, by have := s.isLt; omega⟩) =
      ∑ t ∈ Finset.univ.filter (fun t : Fin k => 0 < t.val), y t := by
    apply Finset.sum_bij (fun (s : Fin (k-1)) _ =>
      (⟨s.val+1, by have := s.isLt; omega⟩ : Fin k))
    · intro s hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩
    · intro s hs t ht he
      apply Fin.ext
      have := congrArg Fin.val he
      simp only [Fin.val_mk] at this
      omega
    · intro t ht
      have hpos := (Finset.mem_filter.mp ht).2
      refine ⟨⟨t.val-1, by have := t.isLt; omega⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    · intros; rfl
  have hb := (a4f_base_formula2 k N hk y).1 hy
  have hc : ((∑ s : Fin (k-1), (y ⟨s.val+1, by have := s.isLt; omega⟩).toNat : ℕ) : ℤ) =
      ∑ s : Fin (k-1), y ⟨s.val+1, by have := s.isLt; omega⟩ := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro s hs
    exact Int.toNat_of_nonneg (hb.1 _)
  apply Int.ofNat_le.mp
  rw [hc, hsum]
  exact hb.2.2

theorem foldUN_recursion (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N)
    (hlcm : lcmUpTo k ∣ N) (x : Fin k → ℕ) (hx : x ∈ simplexS k N) :
    (∀ t, 0 ≤ foldMapGlobal k N x t) ∧
      foldMapGlobal k N x ⟨0, by omega⟩ ≤ ((N / k : ℕ) : ℤ) ∧
      (fun s : Fin (k - 1) =>
          (foldMapGlobal k N x ⟨s.val + 1, by have := s.isLt; omega⟩).toNat) ∈
        simplexS (k - 1) N ∧
      k ∣ N ∧ lcmUpTo (k - 1) ∣ N ∧
      ∀ t : Fin k,
        foldUN k N x t =
          if h : t.val = 0 then (foldMapGlobal k N x t).toNat
          else
            foldUN (k - 1) N
              (fun s : Fin (k - 1) =>
                (foldMapGlobal k N x ⟨s.val + 1, by have := s.isLt; omega⟩).toNat)
              ⟨t.val - 1, by have := t.isLt; omega⟩ := by
  classical
  obtain ⟨hkN,hprev⟩ := a4un_lcm k N (by omega) hlcm
  have hb := (foldMap_spec k N hk hkN).1 x hx
  have hb' := (a4f_base_formula2 k N hk _).1 hb
  refine ⟨hb'.1,hb'.2.1,a4un_tail k N hk _ hb,hkN,hprev,?_⟩
  obtain ⟨n,rfl⟩ : ∃ n, k=n+2 := ⟨k-2,by omega⟩
  have hN0 : N ≠ 0 := by omega
  intro t
  have hdim : n+2-1=n+1 := by omega
  refine Fin.cases ?_ (fun s => ?_) t
  · simp [foldUN,hN0]
  · simp [foldUN,hN0,Fin.tail_def]
    congr 2

private def a4un_suffix (k j : ℕ) (y : Fin k → ℤ) : Fin (k-j) → ℕ :=
  fun s => (y ⟨s.val+j, by have := s.isLt; omega⟩).toNat

private noncomputable def a4un_finish (k N j : ℕ) (y : Fin k → ℤ) : Fin k → ℤ :=
  fun t => if h : t.val < j then y t else
    (foldUN (k-j) N (a4un_suffix k j y)
      ⟨t.val-j, by have := t.isLt; omega⟩ : ℤ)

private lemma a4un_stage_suffix2 (k N j : ℕ) (hj : j < k) (y : Fin k → ℤ) :
    a4un_suffix k (j+1) (foldStage k N j y) =
      fun s : Fin (k-(j+1)) =>
        (foldMapGlobal (k-j) N (a4un_suffix k j y)
          ⟨s.val+1, by have := s.isLt; omega⟩).toNat := by
  funext s
  dsimp [a4un_suffix, foldStage]
  rw [dif_neg (by omega)]
  congr 2
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

private lemma a4un_stage_nonneg2 (k N j : ℕ) (hj : j+2 ≤ k) (hN : 1 ≤ N)
    (hl : lcmUpTo (k-j) ∣ N) (y : Fin k → ℤ) (hy : ∀ t, 0 ≤ y t)
    (hx : a4un_suffix k j y ∈ simplexS (k-j) N) :
    ∀ t, 0 ≤ foldStage k N j y t := by
  have hr := foldUN_recursion (k-j) N (by omega) hN hl _ hx
  intro t
  dsimp [foldStage]
  split_ifs
  · exact hy t
  · exact hr.1 _

private lemma a4un_stage_invariants2 (k N j : ℕ) (hj : j+2 ≤ k) (hN : 1 ≤ N)
    (hl : lcmUpTo (k-j) ∣ N) (y : Fin k → ℤ)
    (hx : a4un_suffix k j y ∈ simplexS (k-j) N) :
    a4un_suffix k (j+1) (foldStage k N j y) ∈ simplexS (k-(j+1)) N ∧
      lcmUpTo (k-(j+1)) ∣ N := by
  have hr := foldUN_recursion (k-j) N (by omega) hN hl _ hx
  have he : (k-j)-1 = k-(j+1) := by omega
  simp only [he] at hr
  refine ⟨?_, hr.2.2.2.2.1⟩
  rw [a4un_stage_suffix2 k N j (by omega) y]
  exact hr.2.2.1

private lemma a4un_finish_step4 (k N j : ℕ) (hj : j+2 ≤ k) (hN : 1 ≤ N)
    (hl : lcmUpTo (k-j) ∣ N) (y : Fin k → ℤ)
    (hx : a4un_suffix k j y ∈ simplexS (k-j) N) :
    a4un_finish k N j y = a4un_finish k N (j+1) (foldStage k N j y) := by
  have hr := foldUN_recursion (k-j) N (by omega) hN hl _ hx
  have he : (k-j)-1 = k-(j+1) := by omega
  simp only [he] at hr
  have htail := a4un_stage_suffix2 k N j (by omega) y
  funext t
  by_cases ht : t.val < j
  · simp [a4un_finish, ht, show t.val < j+1 by omega, foldStage]
  · by_cases htj : t.val = j
    · have hrec := hr.2.2.2.2.2 (⟨t.val-j, by have := t.isLt; omega⟩ : Fin (k-j))
      simp only [Fin.val_mk, dif_pos (show t.val-j = 0 by omega)] at hrec
      simp only [a4un_finish, dif_neg ht, dif_pos (show t.val < j+1 by omega),
        foldStage, dif_neg ht]
      rw [hrec, Int.toNat_of_nonneg (hr.1 _)]
      rfl
    · have ht' : ¬ t.val < j+1 := by omega
      have hrec := hr.2.2.2.2.2 (⟨t.val-j, by have := t.isLt; omega⟩ : Fin (k-j))
      simp only [Fin.val_mk, dif_neg (show t.val-j ≠ 0 by omega)] at hrec
      simp only [a4un_finish, dif_neg ht, dif_neg ht', htail]
      rw [hrec]
      congr 2

private lemma a4un_dim_one (d N : ℕ) (hd : d=1) (x : Fin d → ℕ) :
    foldUN d N x = x := by
  subst d
  rfl

private lemma a4un_finish_closed2 (n k N j : ℕ) (hdim : k-j=n+1)
    (hN : 1 ≤ N) (hl : lcmUpTo (k-j) ∣ N) (y : Fin k → ℤ)
    (hy : ∀ t, 0 ≤ y t) (hx : a4un_suffix k j y ∈ simplexS (k-j) N) :
    a4un_finish k N j y =
      (List.range n).foldl (fun y i => foldStage k N (j+i) y) y := by
  induction n generalizing j y with
  | zero =>
    simp only [List.range_zero, List.foldl_nil]
    funext t
    by_cases ht : t.val < j
    · simp [a4un_finish, ht]
    · dsimp [a4un_finish]
      rw [dif_neg ht]
      simp only [Nat.zero_add] at hdim
      have hval : t.val-j = 0 := by have := t.isLt; omega
      have hr : foldUN (k-j) N (a4un_suffix k j y) = a4un_suffix k j y :=
        a4un_dim_one (k-j) N hdim _
      rw [hr]
      dsimp [a4un_suffix]
      rw [Int.toNat_of_nonneg (hy _)]
      congr 1
      apply Fin.ext
      dsimp
      omega
  | succ n ih =>
    have hj : j+2 ≤ k := by omega
    have hi := a4un_stage_invariants2 k N j hj hN hl y hx
    rw [a4un_finish_step4 k N j hj hN hl y hx]
    rw [ih (j+1) (by omega) hi.2 _
      (a4un_stage_nonneg2 k N j hj hN hl y hy hx) hi.1]
    rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    simp only [Nat.add_zero]
    congr 1
    funext z i
    congr 1
    omega

theorem foldUN_closed_form (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N)
    (hlcm : lcmUpTo k ∣ N) (x : Fin k → ℕ) (hx : x ∈ simplexS k N) :
    (fun t => (foldUN k N x t : ℤ)) =
      (List.range (k - 2)).foldl (fun y j => foldStage k N (j + 1) y)
        (foldMapGlobal k N x) := by
  have hr := foldUN_recursion k N hk hN hlcm x hx
  have hc := a4un_finish_closed2 (k-2) k N 1 (by omega) hN
    hr.2.2.2.2.1 (foldMapGlobal k N x) hr.1 hr.2.2.1
  have hfun : (fun y (j : ℕ) => foldStage k N (1+j) y) =
      (fun y j => foldStage k N (j+1) y) := by
    funext y j
    rw [Nat.add_comm]
  rw [hfun] at hc
  rw [← hc]
  funext t
  rw [hr.2.2.2.2.2 t]
  by_cases ht : t.val=0
  · simp only [dif_pos ht, a4un_finish, dif_pos (show t.val < 1 by omega)]
    exact Int.toNat_of_nonneg (hr.1 t)
  · simp only [dif_neg ht, a4un_finish, dif_neg (show ¬ t.val < 1 by omega)]
    rfl

theorem foldUN_two (N : ℕ) (hN : 2 ∣ N) (x : Fin 2 → ℕ) (hx : x ∈ simplexS 2 N) :
    foldUN 2 N x =
      if x 0 ≤ N / 2 then ![x 0, x 0 + x 1]
      else ![x 0 + x 1 - N / 2, x 0 - N / 2 - 1] := by
  classical
  have hxsum : x 0 + x 1 ≤ N := by
    simpa only [Fin.sum_univ_two] using (onb_mem_simplex 2 N x).1 hx
  have hp1 : foldPrefixSum 2 x 1 = x 0 := by
    simp [foldPrefixSum, Finset.sum_filter, Fin.sum_univ_two]
  have hp2 : foldPrefixSum 2 x 2 = x 0 + x 1 := by
    simp [foldPrefixSum, Finset.sum_filter, Fin.sum_univ_two]
  by_cases hNz : N = 0
  · subst N
    have hx0 : x = 0 := by
      funext t
      fin_cases t
      · change x 0 = 0; omega
      · change x 1 = 0; omega
    rw [hx0, foldUN_zero]
    funext t
    fin_cases t <;> rfl
  · by_cases hh : x 0 ≤ N / 2
    · have hpiece : x ∈ foldSourcePiece 2 N 1 := by
        apply (a4f_source_formula2 2 N 1 (by omega) hN x).2
        refine ⟨hxsum, by simp, ?_⟩
        simpa [hp1] using hh
      have hg := (foldMap_spec 2 N (by omega) hN).2.1 1 (by omega) (by omega) x hpiece
      have hf0 : foldMapGlobal 2 N x 0 = (x 0 : ℤ) := by
        rw [hg]
        simp [foldMap, foldCoord]
      have hf1 : foldMapGlobal 2 N x 1 = (x 0 : ℤ) + (x 1 : ℤ) := by
        rw [hg]
        simp [foldMap, foldCoord]
      rw [if_pos hh]
      funext t
      fin_cases t <;> simp [foldUN, hNz, Fin.tail_def, hf0, hf1] <;> omega
    · have hpiece : x ∈ foldSourcePiece 2 N 2 := by
        apply (a4f_source_formula2 2 N 2 (by omega) hN x).2
        refine ⟨hxsum, ?_, ?_⟩
        · intro i hi
          have hi' := Finset.mem_Ico.mp hi
          have he : i = 1 := by omega
          subst i
          simpa [hp1] using (lt_of_not_ge hh)
        · rw [hp2]
          have he : 2 * (N / 2) = N := Nat.mul_div_cancel' hN
          omega
      have hg := (foldMap_spec 2 N (by omega) hN).2.1 2 (by omega) (by omega) x hpiece
      have hf0 : foldMapGlobal 2 N x 0 = (x 0 : ℤ) + (x 1 : ℤ) - (N / 2 : ℕ) := by
        rw [hg]
        norm_num [foldMap, foldCoord, Finset.sum_Icc_succ_top]
      have hf1 : foldMapGlobal 2 N x 1 = (x 0 : ℤ) - (N / 2 : ℕ) - 1 := by
        rw [hg]
        simp [foldMap, foldCoord]
      rw [if_neg hh]
      funext t
      fin_cases t <;> simp [foldUN, hNz, Fin.tail_def, hf0, hf1] <;> omega
private structure a4FreshUnit_a4unPart (k R : ℕ) (S : Set (Fin k → ℤ))
    (f : (Fin k → ℤ) → Fin k → ℤ) where
  r : ℕ
  L : Fin r → Finset ((Fin k → ℤ) × ℤ)
  A : Fin r → Matrix (Fin k) (Fin k) ℤ
  c : Fin r → Fin k → ℤ
  nr : r ≤ R
  card : ∀ i, (L i).card ≤ R
  norm : ∀ i p, p ∈ L i → ∑ s, |p.1 s| ≤ (R : ℤ)
  det : ∀ i, (A i).det = 1 ∨ (A i).det = -1
  mat : ∀ i s t, |A i s t| ≤ (R : ℤ)
  sub : ∀ i, polyPZ k (L i) ⊆ S
  dis : ∀ i j, i ≠ j → Disjoint (polyPZ k (L i)) (polyPZ k (L j))
  cover : ∀ x ∈ S, ∃ i, x ∈ polyPZ k (L i)
  affine : ∀ i x, x ∈ polyPZ k (L i) → f x = A i *ᵥ x + c i

private def a4FreshUnit_a4unPart_congr {k R} {S : Set (Fin k → ℤ)}
    {f g : (Fin k → ℤ) → Fin k → ℤ} (p : a4FreshUnit_a4unPart k R S f)
    (h : ∀ x ∈ S, f x = g x) : a4FreshUnit_a4unPart k R S g :=
  { p with affine := fun i x hx => (h x (p.sub i hx)).symm.trans (p.affine i x hx) }

private lemma a4FreshUnit_a4unPart_pull_norm (k R T : ℕ)
    (A : Matrix (Fin k) (Fin k) ℤ) (hA : ∀ i j, |A i j| ≤ (R : ℤ))
    (v : Fin k → ℤ) (hv : ∑ j, |v j| ≤ (T : ℤ)) :
    (∑ j, |(Aᵀ *ᵥ v) j|) ≤ ((k*R*T : ℕ) : ℤ) := by
  have hb (j : Fin k) : |(Aᵀ *ᵥ v) j| ≤ (R : ℤ)*T := by
    change |∑ i, A i j*v i| ≤ _
    calc
      _ ≤ ∑ i, |A i j*v i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (R : ℤ)*|v i| := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hA i j) (abs_nonneg _))
      _ = (R : ℤ)*∑ i, |v i| := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
  exact (Finset.sum_le_sum (fun j _ => hb j)).trans_eq (by simp [Nat.cast_mul,mul_assoc])

set_option maxHeartbeats 2000000 in
private noncomputable def a4FreshUnit_a4unPart_comp2 {k R T} {S V : Set (Fin k → ℤ)}
    {f g : (Fin k → ℤ) → Fin k → ℤ}
    (p : a4FreshUnit_a4unPart k R S f) (q : a4FreshUnit_a4unPart k T V g) (hf : Set.MapsTo f S V) :
    a4FreshUnit_a4unPart k (R*T+R+T+k*R*T+1) S (g ∘ f) := by
  classical
  let e : Fin (p.r*q.r) ≃ Fin p.r × Fin q.r := finProdFinEquiv.symm
  let L (i : Fin (p.r*q.r)) := p.L (e i).1 ∪
    shiftPullbackConstraints k (p.A (e i).1) (p.c (e i).1) (q.L (e i).2)
  have hmem (i : Fin (p.r*q.r)) (x : Fin k → ℤ) :
      x ∈ polyPZ k (L i) ↔ x ∈ polyPZ k (p.L (e i).1) ∧ f x ∈ polyPZ k (q.L (e i).2) := by
    simp only [polyPZ,L,Set.mem_setOf_eq,Finset.forall_mem_union]
    change (x ∈ polyPZ k (p.L (e i).1) ∧
      x ∈ polyPZ k (shiftPullbackConstraints k (p.A (e i).1) (p.c (e i).1) (q.L (e i).2))) ↔ _
    rw [polyPZ_shiftPullbackConstraints]
    constructor
    · rintro ⟨hx,hy⟩
      exact ⟨hx,by rwa [p.affine _ x hx,add_comm]⟩
    · rintro ⟨hx,hy⟩
      exact ⟨hx,by rwa [p.affine _ x hx,add_comm] at hy⟩
  refine ⟨p.r*q.r,L,(fun i => q.A (e i).2*p.A (e i).1),
    (fun i => q.A (e i).2 *ᵥ p.c (e i).1 + q.c (e i).2),?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (Nat.mul_le_mul p.nr q.nr).trans (by omega)
  · intro i
    have hc := Finset.card_union_le (p.L (e i).1)
      (shiftPullbackConstraints k (p.A (e i).1) (p.c (e i).1) (q.L (e i).2))
    have hi : (shiftPullbackConstraints k (p.A (e i).1) (p.c (e i).1) (q.L (e i).2)).card ≤ T :=
      Finset.card_image_le.trans (q.card _)
    exact hc.trans (by have := p.card (e i).1; omega)
  · intro i z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (p.norm _ z hz).trans (by omega)
    · change z ∈ (q.L (e i).2).image
        (fun v => ((p.A (e i).1)ᵀ *ᵥ v.1, v.2 + ∑ s, v.1 s * p.c (e i).1 s)) at hz
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
      exact (a4FreshUnit_a4unPart_pull_norm k R T _ (p.mat _) v.1 (q.norm _ v hv)).trans (by omega)
  · intro i
    rw [Matrix.det_mul]
    rcases q.det (e i).2 with h | h <;> rcases p.det (e i).1 with h' | h' <;>
      rw [h,h'] <;> norm_num
  · intro i s t
    have hs := transitionSize_mul_le (q.A (e i).2) (p.A (e i).1)
    have hqa : transitionSize (q.A (e i).2) ≤ T := (matInftyNorm_le_iff _ _).2 (q.mat _)
    have hpa : transitionSize (p.A (e i).1) ≤ R := (matInftyNorm_le_iff _ _).2 (p.mat _)
    apply (matInftyNorm_le_iff _ _).1 (hs.trans ?_) s t
    have hb := Nat.mul_le_mul (Nat.mul_le_mul_left k hqa) hpa
    nlinarith
  · intro i x hx
    exact p.sub _ ((hmem i x).1 hx).1
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hx,hxf⟩ := (hmem i x).1 hx
    obtain ⟨hy,hyf⟩ := (hmem j x).1 hy
    by_cases he : (e i).1=(e j).1
    · have hne : (e i).2 ≠ (e j).2 := by
        intro h; exact hij (e.injective (Prod.ext he h))
      exact Set.disjoint_left.mp (q.dis _ _ hne) hxf hyf
    · exact Set.disjoint_left.mp (p.dis _ _ he) hx hy
  · intro x hx
    obtain ⟨i,hi⟩ := p.cover x hx
    obtain ⟨j,hj⟩ := q.cover (f x) (hf hx)
    refine ⟨e.symm (i,j),?_⟩
    rw [hmem]
    simpa using And.intro hi hj
  · intro i x hx
    obtain ⟨hx,hfx⟩ := (hmem i x).1 hx
    change g (f x) = _
    rw [q.affine _ _ hfx,p.affine _ _ hx,Matrix.mulVec_add,Matrix.mulVec_mulVec,add_assoc]

private lemma a4FreshUnit_a4un_box_succ_bij (n N : ℕ) (l : Fin (n+2) → ℕ) :
    l ∈ boxB (n+2) N ↔ l 0 ≤ N/(n+2) ∧ Fin.tail l ∈ boxB (n+1) N := by
  simp [boxB, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff,
    Fin.forall_fin_succ, Fin.tail_def]

private lemma a4FreshUnit_a4un_bij8 (k N : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N)
    (hl : lcmUpTo k ∣ N) :
    Set.BijOn (foldUN k N) (simplexS k N : Set _) (boxB k N : Set _) := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk1 : k=1
    · subst k
      have he : (simplexS 1 N : Set (Fin 1 → ℕ)) = (boxB 1 N : Set (Fin 1 → ℕ)) := by
        ext x
        simp [onb_mem_simplex, boxB, Fintype.mem_piFinset, Finset.mem_range,
          Fin.forall_fin_one, Nat.lt_succ_iff]
      change Set.BijOn id (simplexS 1 N : Set _) (boxB 1 N : Set (Fin 1 → ℕ))
      rw [he]
      exact Set.bijOn_id _
    obtain ⟨n,rfl⟩ : ∃ n, k=n+2 := ⟨k-2,by omega⟩
    obtain ⟨hdiv,hprev⟩ := a4un_lcm (n+2) N (by omega) hl
    have hprev' : lcmUpTo (n+1) ∣ N := by simpa using hprev
    have hi := ih (n+1) (by omega) (by omega) hprev'
    let T : (Fin (n+2) → ℤ) → (Fin (n+1) → ℕ) :=
      fun y => Fin.tail (fun t => (y t).toNat)
    let G : (Fin (n+2) → ℤ) → (Fin (n+2) → ℕ) :=
      fun y => Fin.cons (y 0).toNat (foldUN (n+1) N (T y))
    have hT (y : Fin (n+2) → ℤ) (hy : y ∈ foldTargetBase (n+2) N) :
        T y ∈ simplexS (n+1) N := by
      apply (onb_mem_simplex _ _ _).2
      have ht := (onb_mem_simplex _ _ _).1 (a4un_tail (n+2) N (by omega) y hy)
      convert ht using 1
      apply Finset.sum_congr rfl
      intro i hi
      rfl
    have hG : Set.BijOn G (foldTargetBase (n+2) N) (boxB (n+2) N : Set _) := by
      refine ⟨?_,?_,?_⟩
      · intro y hy
        apply (a4FreshUnit_a4un_box_succ_bij n N _).2
        refine ⟨?_,by simpa [G] using hi.mapsTo (hT y hy)⟩
        have hb := (a4f_base_formula2 (n+2) N (by omega) y).1 hy
        dsimp [G]
        simp only [Fin.cons_zero]
        have h := Int.toNat_le_toNat hb.2.1
        simpa only [Int.toNat_natCast, Fin.zero_eta] using h
      · intro y hy z hz he
        have hh := congrArg (fun l : Fin (n+2) → ℕ => l 0) he
        have ht := congrArg (Fin.tail (α := fun _ : Fin (n+2) => ℕ)) he
        simp only [G, Fin.cons_zero] at hh
        simp only [G, Fin.tail_cons] at ht
        have htail := hi.injOn (hT y hy) (hT z hz) ht
        funext t
        refine Fin.cases ?_ (fun i => ?_) t
        · have hy0 := Int.toNat_of_nonneg (hy.1 (0 : Fin (n+2)))
          have hz0 := Int.toNat_of_nonneg (hz.1 (0 : Fin (n+2)))
          omega
        · have hc := congrArg (fun a : ℕ => (a : ℤ)) (congrFun htail i)
          simpa [T, Fin.tail_def, Int.toNat_of_nonneg (hy.1 _),
            Int.toNat_of_nonneg (hz.1 _)] using hc
      · intro l hl
        obtain ⟨hl0,hlt⟩ := (a4FreshUnit_a4un_box_succ_bij n N l).1 hl
        obtain ⟨z,hz,hzl⟩ := hi.surjOn hlt
        let Y : Fin (n+2) → ℤ := Fin.cons (l 0 : ℤ) (fun i => (z i : ℤ))
        have hY : Y ∈ foldTargetBase (n+2) N := by
          apply (a4f_base_formula2 (n+2) N (by omega) Y).2
          refine ⟨?_,?_,?_⟩
          · intro t
            refine Fin.cases (by simp [Y]) (fun i => by simp [Y]) t
          · simpa [Y] using (show (l 0 : ℤ) ≤ (N/(n+2) : ℕ) by exact_mod_cast hl0)
          · have hzs := (onb_mem_simplex (n+1) N z).1 hz
            have hzsi : (∑ i : Fin (n+1), (z i : ℤ)) ≤ (N : ℤ) := by exact_mod_cast hzs
            simpa [Y, Finset.sum_filter, Fin.sum_univ_succ] using hzsi
        refine ⟨Y,hY,?_⟩
        have hTY : T Y=z := by funext i; simp [T,Y,Fin.tail_def]
        dsimp [G]
        rw [hTY,hzl]
        simpa [Y] using Fin.cons_self_tail l
    obtain ⟨_,_,_,_,_,_,_,_,hfold,_⟩ := prop_fold (n+2) N (by omega) hN hdiv
    apply (hG.comp hfold).congr
    intro x hx
    change G (foldMapGlobal (n+2) N x) = foldUN (n+2) N x
    simp only [foldUN, if_neg (by omega : N ≠ 0)]
    rfl

private def a4FreshUnit_a4UN_liftEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

private lemma a4FreshUnit_a4UN_liftEquiv_zero (n : ℕ) :
    a4FreshUnit_a4UN_liftEquiv n (Sum.inl 0) = 0 := by
  apply Fin.ext
  simp [a4FreshUnit_a4UN_liftEquiv, finSumFinEquiv_apply_left]

private lemma a4FreshUnit_a4UN_liftEquiv_succ (n : ℕ) (j : Fin n) :
    a4FreshUnit_a4UN_liftEquiv n (Sum.inr j) = j.succ := by
  apply Fin.ext
  simp [a4FreshUnit_a4UN_liftEquiv, finSumFinEquiv_apply_right]

private def a4FreshUnit_a4UN_liftMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.reindex (a4FreshUnit_a4UN_liftEquiv n) (a4FreshUnit_a4UN_liftEquiv n)
    (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 0 A)

private lemma a4FreshUnit_a4UN_liftMatrix_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    (a4FreshUnit_a4UN_liftMatrix A).det = A.det := by
  rw [a4FreshUnit_a4UN_liftMatrix, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂]
  simp

private lemma a4FreshUnit_a4UN_liftMatrix_bound {n R : ℕ} (hR : 1 ≤ R)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : ∀ i j, |A i j| ≤ (R : ℤ)) :
    ∀ i j, |a4FreshUnit_a4UN_liftMatrix A i j| ≤ (R : ℤ) := by
  intro i j
  obtain ⟨i, rfl⟩ := (a4FreshUnit_a4UN_liftEquiv n).surjective i
  obtain ⟨j, rfl⟩ := (a4FreshUnit_a4UN_liftEquiv n).surjective j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i
      subst j
      simpa [a4FreshUnit_a4UN_liftMatrix, Matrix.reindex_apply, Matrix.submatrix_apply] using
        (show (1 : ℤ) ≤ R by exact_mod_cast hR)
    | inr j => simp [a4FreshUnit_a4UN_liftMatrix, Matrix.reindex_apply, Matrix.submatrix_apply]
  | inr i =>
    cases j with
    | inl j => simp [a4FreshUnit_a4UN_liftMatrix, Matrix.reindex_apply, Matrix.submatrix_apply]
    | inr j => simpa [a4FreshUnit_a4UN_liftMatrix, Matrix.reindex_apply, Matrix.submatrix_apply] using hA i j

private lemma a4FreshUnit_a4UN_liftMatrix_mulVec3 {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin (n + 1) → ℤ) :
    a4FreshUnit_a4UN_liftMatrix A *ᵥ x = Fin.cons (α := fun _ => ℤ) (x 0) (A *ᵥ Fin.tail x) := by
  classical
  have hrow (s : Fin 1 ⊕ Fin n) :
      (a4FreshUnit_a4UN_liftMatrix A *ᵥ x) (a4FreshUnit_a4UN_liftEquiv n s) =
        (Fin.cons (α := fun _ => ℤ) (x 0) (A *ᵥ Fin.tail x)) (a4FreshUnit_a4UN_liftEquiv n s) := by
    change (∑ j, a4FreshUnit_a4UN_liftMatrix A (a4FreshUnit_a4UN_liftEquiv n s) j * x j) = _
    rw [← (a4FreshUnit_a4UN_liftEquiv n).sum_comp
      (fun j => a4FreshUnit_a4UN_liftMatrix A (a4FreshUnit_a4UN_liftEquiv n s) j * x j)]
    simp only [a4FreshUnit_a4UN_liftMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply]
    cases s with
    | inl i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [a4FreshUnit_a4UN_liftMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
        Fintype.sum_sum_type, a4FreshUnit_a4UN_liftEquiv_zero]
    | inr i =>
      simp [a4FreshUnit_a4UN_liftMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
        Fintype.sum_sum_type, a4FreshUnit_a4UN_liftEquiv_succ, Matrix.mulVec, dotProduct, Fin.tail_def]
  funext t
  obtain ⟨s, rfl⟩ := (a4FreshUnit_a4UN_liftEquiv n).surjective t
  exact hrow s

private noncomputable def a4FreshUnit_a4UN_liftConstraints {n : ℕ}
    (L : Finset ((Fin n → ℤ) × ℤ)) : Finset ((Fin (n + 1) → ℤ) × ℤ) := by
  classical
  exact L.image (fun p => (Fin.cons 0 p.1, p.2))

private lemma a4FreshUnit_a4UN_liftConstraints_mem2 {n : ℕ}
    (L : Finset ((Fin n → ℤ) × ℤ)) (x : Fin (n + 1) → ℤ) :
    x ∈ polyPZ (n + 1) (a4FreshUnit_a4UN_liftConstraints L) ↔ Fin.tail x ∈ polyPZ n L := by
  classical
  change (∀ p ∈ L.image (fun p => (Fin.cons 0 p.1,p.2)), 0 ≤ (∑ s, p.1 s*x s)+p.2) ↔ _
  rw [Finset.forall_mem_image]
  simp [polyPZ,Fin.sum_univ_succ,Fin.tail_def]

private noncomputable def a4FreshUnit_a4unPart_lift3 {n R} {S : Set (Fin n → ℤ)}
    {f : (Fin n → ℤ) → Fin n → ℤ} (hR : 1 ≤ R) (p : a4FreshUnit_a4unPart n R S f) :
    a4FreshUnit_a4unPart (n+1) R {x | Fin.tail x ∈ S}
      (fun x => Fin.cons (x 0) (f (Fin.tail x))) := by
  classical
  refine ⟨p.r,(fun i => a4FreshUnit_a4UN_liftConstraints (p.L i)),
    (fun i => a4FreshUnit_a4UN_liftMatrix (p.A i)),(fun i => Fin.cons 0 (p.c i)),p.nr,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact Finset.card_image_le.trans (p.card i)
  · intro i z hz
    change z ∈ (p.L i).image (fun z => (Fin.cons 0 z.1,z.2)) at hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    simpa [Fin.sum_univ_succ] using p.norm i v hv
  · intro i
    rw [a4FreshUnit_a4UN_liftMatrix_det]
    exact p.det i
  · exact fun i => a4FreshUnit_a4UN_liftMatrix_bound hR _ (p.mat i)
  · intro i x hx
    exact p.sub i ((a4FreshUnit_a4UN_liftConstraints_mem2 _ _).1 hx)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (p.dis i j hij)
      ((a4FreshUnit_a4UN_liftConstraints_mem2 _ _).1 hx) ((a4FreshUnit_a4UN_liftConstraints_mem2 _ _).1 hy)
  · intro x hx
    obtain ⟨i,hi⟩ := p.cover (Fin.tail x) hx
    exact ⟨i,(a4FreshUnit_a4UN_liftConstraints_mem2 _ _).2 hi⟩
  · intro i x hx
    rw [a4FreshUnit_a4UN_liftMatrix_mulVec3,p.affine i _ ((a4FreshUnit_a4UN_liftConstraints_mem2 _ _).1 hx)]
    funext t
    refine Fin.cases ?_ (fun j => ?_) t <;> simp

private def a4FreshUnit_a4UNS (k N : ℕ) : Set (Fin k → ℤ) :=
  {x | (∀ s, 0 ≤ x s) ∧ ∑ s, x s ≤ (N : ℤ)}

private noncomputable def a4FreshUnit_a4UNU (k N : ℕ) (x : Fin k → ℤ) : Fin k → ℤ :=
  fun s => (foldUN k N (fun t => (x t).toNat) s : ℤ)

private lemma a4FreshUnit_a4UNS_cast2 (k N : ℕ) (y : Fin k → ℤ) :
    y ∈ a4FreshUnit_a4UNS k N ↔ ∃ x : Fin k → ℕ, x ∈ simplexS k N ∧ (fun s => (x s : ℤ)) = y := by
  constructor
  · rintro ⟨hn,hs⟩
    let x : Fin k → ℕ := fun s => (y s).toNat
    have he : (fun s => (x s : ℤ)) = y := by
      funext s; exact Int.toNat_of_nonneg (hn s)
    refine ⟨x,(onb_mem_simplex _ _ _).2 ?_,he⟩
    have hcast : ((∑ s, x s : ℕ) : ℤ) = ∑ s, y s := by rw [Nat.cast_sum,he]
    exact_mod_cast (show ((∑ s,x s : ℕ) : ℤ) ≤ (N : ℤ) by rwa [hcast])
  · rintro ⟨x,hx,rfl⟩
    refine ⟨fun s => Nat.cast_nonneg _,?_⟩
    dsimp only
    exact_mod_cast (onb_mem_simplex _ _ _).1 hx

private noncomputable def a4FreshUnit_a4UN_foldPart2 (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N)
    (hkN : k ∣ N) : a4FreshUnit_a4unPart k (2*k+1) (a4FreshUnit_a4UNS k N)
      (fun y => foldMapGlobal k N (fun s => (y s).toNat)) := by
  classical
  obtain ⟨_,_,_,_,_,_,_,_,hbij,hdata⟩ := prop_fold k N hk hN hkN
  have hL (i : Fin k) := (hdata (i.val+1) (by omega) (by have := i.isLt; omega)).1
  choose L hpoly hcard hnorm using hL
  have hA (i : Fin k) := (hdata (i.val+1) (by omega) (by have := i.isLt; omega)).2.2
  choose A c hdet hentries haff using hA
  have hmem (i : Fin k) (y : Fin k → ℤ) : y ∈ polyPZ k (L i) ↔
      ∃ x : Fin k → ℕ, x ∈ foldSourcePiece k N (i.val+1) ∧ (fun s => (x s : ℤ))=y := by
    rw [← hpoly i]
    rfl
  refine ⟨k,L,A,c,by omega,hcard,?_,hdet,?_,?_,?_,?_,?_⟩
  · intro i p hp
    exact (hnorm i p hp).trans (by omega)
  · intro i s t
    rcases hentries i s t with h | h <;> rw [h] <;> norm_num <;> omega
  · intro i y hy
    obtain ⟨x,hx,rfl⟩ := (hmem i y).1 hy
    exact (a4FreshUnit_a4UNS_cast2 k N _).2 ⟨x,
      ((foldSourcePiece_partition k N hk hkN).1 _ (by omega) (by have := i.isLt; omega)).1 hx,rfl⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro y hy hz
    obtain ⟨x,hx,rfl⟩ := (hmem i y).1 hy
    obtain ⟨z,hz,he⟩ := (hmem j _).1 hz
    have hez : z=x := by
      funext s
      exact_mod_cast congrFun he s
    subst z
    obtain ⟨m,hm,hu⟩ := (foldSourcePiece_partition k N hk hkN).2 x |>.1
      (((foldSourcePiece_partition k N hk hkN).1 _ (by omega) (by have := i.isLt; omega)).1 hx)
    have hh := (hu _ ⟨by omega,by have := i.isLt; omega,hx⟩).trans
      (hu _ ⟨by omega,by have := j.isLt; omega,hz⟩).symm
    apply hij
    apply Fin.ext
    omega
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := (a4FreshUnit_a4UNS_cast2 k N y).1 hy
    obtain ⟨m,hm,hu⟩ := (foldSourcePiece_partition k N hk hkN).2 x |>.1 hx
    let i : Fin k := ⟨m-1,by omega⟩
    refine ⟨i,(hmem i _).2 ⟨x,?_,rfl⟩⟩
    have he : i.val+1=m := by dsimp [i]; omega
    rw [he]
    exact hm.2.2
  · intro i y hy
    obtain ⟨x,hx,rfl⟩ := (hmem i y).1 hy
    simp only [Int.toNat_natCast]
    rw [a4recordFold20261014_fm3_global_piece k N hk hkN _
      (by omega) (by have := i.isLt; omega) x hx]
    exact haff i _

private noncomputable def a4FreshUnit_a4UN_boxPart (k : ℕ) (lo hi : Fin k → ℤ) :
    a4FreshUnit_a4unPart k (2*k+1) (boxZ k lo hi : Set _) id := by
  classical
  refine ⟨1,(fun _ => boxConstraints k lo hi),(fun _ => 1),(fun _ => 0),by omega,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact (card_boxConstraints_le k lo hi).trans (by omega)
  · intro i p hp
    rw [sum_abs_boxConstraints k lo hi p hp]
    omega
  · intro i; left; simp
  · intro i s t
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num <;> omega
  · intro i
    rw [polyPZ_boxConstraints]
  · intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  · intro x hx
    refine ⟨0,?_⟩
    rwa [polyPZ_boxConstraints]
  · intro i x hx
    simp

private noncomputable def a4FreshUnit_a4UN_onePart3 (N : ℕ) :
    a4FreshUnit_a4unPart 1 3 (a4FreshUnit_a4UNS 1 N) (a4FreshUnit_a4UNU 1 N) := by
  classical
  have he : (boxZ 1 (fun _ => 0) (fun _ => (N : ℤ)) : Set _) = a4FreshUnit_a4UNS 1 N := by
    ext x
    simp only [boxZ,Finset.mem_coe,Fintype.mem_piFinset,Finset.mem_Icc,a4FreshUnit_a4UNS,Set.mem_setOf_eq]
    change (∀ s, 0 ≤ x s ∧ x s ≤ (N : ℤ)) ↔ (∀ s, 0 ≤ x s) ∧ ∑ s,x s ≤ (N : ℤ)
    simp only [Fin.forall_fin_one,Fin.sum_univ_one]
  have p := a4FreshUnit_a4UN_boxPart 1 (fun _ => 0) (fun _ => (N : ℤ))
  rw [he] at p
  apply a4FreshUnit_a4unPart_congr p
  intro x hx
  funext s
  exact (Int.toNat_of_nonneg (hx.1 s)).symm

private lemma a4FreshUnit_a4UN_fold_maps (n N : ℕ) (hN : 1 ≤ N) (hl : lcmUpTo (n+2) ∣ N) :
    Set.MapsTo (fun y : Fin (n+2) → ℤ => foldMapGlobal (n+2) N (fun s => (y s).toNat))
      (a4FreshUnit_a4UNS (n+2) N) {y | Fin.tail y ∈ a4FreshUnit_a4UNS (n+1) N} := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := (a4FreshUnit_a4UNS_cast2 _ _ _).1 hy
  simp only [Int.toNat_natCast]
  have hkN := (a4un_lcm (n+2) N (by omega) hl).1
  have hb := (foldMap_spec (n+2) N (by omega) hkN).1 x hx
  refine ⟨fun s => hb.1 _,?_⟩
  have ht := hb.2.2
  rw [a4f_tail_sum] at ht
  change (∑ s, Fin.tail (foldMapGlobal (n+2) N x) s) ≤ (N : ℤ)
  convert ht using 1
  simp only [Finset.sum_filter,Fin.sum_univ_succ,Fin.tail_def]
  simp

private lemma a4FreshUnit_a4UN_step_eq (n N : ℕ) (hN : 1 ≤ N) (hl : lcmUpTo (n+2) ∣ N)
    (y : Fin (n+2) → ℤ) (hy : y ∈ a4FreshUnit_a4UNS (n+2) N) :
    Fin.cons (foldMapGlobal (n+2) N (fun s => (y s).toNat) 0)
      (a4FreshUnit_a4UNU (n+1) N (Fin.tail (foldMapGlobal (n+2) N (fun s => (y s).toNat)))) =
        a4FreshUnit_a4UNU (n+2) N y := by
  obtain ⟨x,hx,rfl⟩ := (a4FreshUnit_a4UNS_cast2 _ _ _).1 hy
  simp only [Int.toNat_natCast]
  have hkN := (a4un_lcm (n+2) N (by omega) hl).1
  have hb := (foldMap_spec (n+2) N (by omega) hkN).1 x hx
  funext s
  refine Fin.cases ?_ (fun t => ?_) s
  · simp [a4FreshUnit_a4UNU,foldUN,show N ≠ 0 by omega,Int.toNat_of_nonneg (hb.1 _)]
  · simp [a4FreshUnit_a4UNU,foldUN,show N ≠ 0 by omega,Fin.tail_def]

private theorem a4FreshUnit_a4UN_parts3 (k : ℕ) (hk : 1 ≤ k) :
    ∃ R : ℕ, 1 ≤ R ∧ ∀ N : ℕ, 1 ≤ N → lcmUpTo k ∣ N →
      Nonempty (a4FreshUnit_a4unPart k R (a4FreshUnit_a4UNS k N) (a4FreshUnit_a4UNU k N)) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk1 : k=1
    · subst k
      exact ⟨3,by omega,fun N _ _ => ⟨a4FreshUnit_a4UN_onePart3 N⟩⟩
    obtain ⟨n,rfl⟩ : ∃ n, k=n+2 := ⟨k-2,by omega⟩
    obtain ⟨R,hR,hparts⟩ := ih (n+1) (by omega) (by omega)
    let T := 2*(n+2)+1
    refine ⟨T*R+T+R+(n+2)*T*R+1,by omega,?_⟩
    intro N hN hl
    have hdiv := a4un_lcm (n+2) N (by omega) hl
    have hp := (hparts N hN (by simpa using hdiv.2)).some
    let q := a4FreshUnit_a4unPart_lift3 hR hp
    let p := a4FreshUnit_a4UN_foldPart2 (n+2) N (by omega) hN hdiv.1
    let z := a4FreshUnit_a4unPart_comp2 p q (a4FreshUnit_a4UN_fold_maps n N hN hl)
    exact ⟨a4FreshUnit_a4unPart_congr z (a4FreshUnit_a4UN_step_eq n N hN hl)⟩

private def a4FreshUnit_a4UNPart_mono {k R T} {S : Set (Fin k → ℤ)}
    {f : (Fin k → ℤ) → Fin k → ℤ} (p : a4FreshUnit_a4unPart k R S f) (h : R ≤ T) :
    a4FreshUnit_a4unPart k T S f :=
  { p with nr := p.nr.trans h
           card := fun i => (p.card i).trans h
           norm := fun i z hz => (p.norm i z hz).trans (by exact_mod_cast h)
           mat := fun i s t => (p.mat i s t).trans (by exact_mod_cast h) }

private lemma a4FreshUnit_a4UNS_zero2 (k : ℕ) : a4FreshUnit_a4UNS k 0 = {0} := by
  ext x
  constructor
  · rintro ⟨hn,hs⟩
    apply Set.mem_singleton_iff.mpr
    funext s
    have hh := Finset.single_le_sum (fun t _ => hn t) (Finset.mem_univ s)
    change x s = 0
    norm_num at hs
    have hn' := hn s
    omega
  · rintro rfl
    simp [a4FreshUnit_a4UNS]

private noncomputable def a4FreshUnit_a4UN_zeroPart2 (k : ℕ) :
    a4FreshUnit_a4unPart k (2*k+1) (a4FreshUnit_a4UNS k 0) (a4FreshUnit_a4UNU k 0) := by
  have he : (boxZ k (fun _ => 0) (fun _ => 0) : Set _) = a4FreshUnit_a4UNS k 0 := by
    rw [a4FreshUnit_a4UNS_zero2]
    ext x
    simp only [boxZ,Finset.mem_coe,Fintype.mem_piFinset,Finset.mem_Icc,Set.mem_singleton_iff]
    constructor
    · intro hx
      funext s
      change x s=0
      have := hx s
      omega
    · rintro rfl
      simp
  have p := a4FreshUnit_a4UN_boxPart k (fun _ => 0) (fun _ => 0)
  rw [he] at p
  apply a4FreshUnit_a4unPart_congr p
  intro x hx
  rw [a4FreshUnit_a4UNS_zero2] at hx
  have hx0 := Set.mem_singleton_iff.mp hx
  subst x
  funext s
  change 0 = (foldUN k 0 0 s : ℤ)
  rw [foldUN_zero]
  rfl

private def a4FreshUnit_a4UNB (k N : ℕ) : Set (Fin k → ℤ) :=
  {l | ∀ s, 0 ≤ l s ∧ l s ≤ ((N / (k-s.val) : ℕ) : ℤ)}

private lemma a4FreshUnit_a4UNB_cast (k N : ℕ) (y : Fin k → ℤ) :
    y ∈ a4FreshUnit_a4UNB k N ↔ ∃ x : Fin k → ℕ, x ∈ boxB k N ∧ (fun s => (x s : ℤ))=y := by
  constructor
  · intro hy
    let x : Fin k → ℕ := fun s => (y s).toNat
    have hc : (fun s => (x s : ℤ))=y := by
      funext s
      exact Int.toNat_of_nonneg (hy s).1
    refine ⟨x,?_,hc⟩
    apply Fintype.mem_piFinset.mpr
    intro s
    apply Finset.mem_range.mpr
    have ht : (x s : ℤ) ≤ ((N / (k-s.val) : ℕ) : ℤ) := by
      rw [congrFun hc s]
      exact (hy s).2
    have ht' : x s ≤ N / (k-s.val) := by exact_mod_cast ht
    omega
  · rintro ⟨x,hx,rfl⟩
    intro s
    refine ⟨Nat.cast_nonneg _,?_⟩
    have ht := Finset.mem_range.mp (Fintype.mem_piFinset.mp hx s)
    dsimp only
    exact_mod_cast (show x s ≤ N / (k-s.val) by omega)

private lemma a4FreshUnit_a4UN_bijZ3 (k N : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N) (hl : lcmUpTo k ∣ N) :
    Set.BijOn (a4FreshUnit_a4UNU k N) (a4FreshUnit_a4UNS k N) (a4FreshUnit_a4UNB k N) := by
  have hu (x : Fin k → ℕ) : a4FreshUnit_a4UNU k N (fun s => (x s : ℤ)) =
      (fun s => (foldUN k N x s : ℤ)) := by
    funext s
    dsimp only [a4FreshUnit_a4UNU]
    simp only [Int.toNat_natCast]
  have hb := a4FreshUnit_a4un_bij8 k N hk hN hl
  refine ⟨?_,?_,?_⟩
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := (a4FreshUnit_a4UNS_cast2 _ _ _).1 hy
    apply (a4FreshUnit_a4UNB_cast _ _ _).2
    exact ⟨foldUN k N x,hb.mapsTo hx,by rw [hu]⟩
  · intro y hy z hz he
    obtain ⟨x,hx,rfl⟩ := (a4FreshUnit_a4UNS_cast2 _ _ _).1 hy
    obtain ⟨t,ht,rfl⟩ := (a4FreshUnit_a4UNS_cast2 _ _ _).1 hz
    have he' : foldUN k N x=foldUN k N t := by
      funext s
      have hs := congrFun he s
      rw [hu,hu] at hs
      dsimp only at hs
      exact_mod_cast hs
    rw [hb.injOn hx ht he']
  · intro y hy
    obtain ⟨l,hl,rfl⟩ := (a4FreshUnit_a4UNB_cast _ _ _).1 hy
    obtain ⟨x,hx,he⟩ := hb.surjOn hl
    refine ⟨(fun s => (x s : ℤ)),(a4FreshUnit_a4UNS_cast2 _ _ _).2 ⟨x,hx,rfl⟩,?_⟩
    rw [hu,he]

private lemma a4FreshUnit_a4UN_bijZ2_zero (k : ℕ) :
    Set.BijOn (a4FreshUnit_a4UNU k 0) (a4FreshUnit_a4UNS k 0) (a4FreshUnit_a4UNB k 0) := by
  have he : a4FreshUnit_a4UNB k 0 = {0} := by
    ext x
    simp only [a4FreshUnit_a4UNB,Set.mem_setOf_eq,Nat.zero_div,Nat.cast_zero,Set.mem_singleton_iff]
    constructor
    · intro hx
      funext s
      change x s=0
      have := hx s
      omega
    · rintro rfl
      simp
  rw [a4FreshUnit_a4UNS_zero2,he]
  have hu : a4FreshUnit_a4UNU k 0 0=0 := by
    funext s
    change (foldUN k 0 0 s : ℤ)=0
    rw [foldUN_zero]
    rfl
  refine ⟨?_,?_,?_⟩
  · intro x hx
    rw [Set.mem_singleton_iff.mp hx,hu]
    exact Set.mem_singleton _
  · intro x hx y hy _
    exact (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm
  · intro y hy
    exact ⟨0,Set.mem_singleton _,hu.trans (Set.mem_singleton_iff.mp hy).symm⟩

private theorem a4FreshUnit_a4UN_all (k : ℕ) (hk : 1 ≤ k) :
    ∃ R : ℕ, ∀ N : ℕ, lcmUpTo k ∣ N →
      Nonempty (a4FreshUnit_a4unPart k R (a4FreshUnit_a4UNS k N) (a4FreshUnit_a4UNU k N)) ∧
        Set.BijOn (a4FreshUnit_a4UNU k N) (a4FreshUnit_a4UNS k N) (a4FreshUnit_a4UNB k N) := by
  classical
  obtain ⟨R,hR,hparts⟩ := a4FreshUnit_a4UN_parts3 k hk
  refine ⟨max R (2*k+1),?_⟩
  intro N hl
  by_cases hN : N=0
  · subst N
    exact ⟨⟨a4FreshUnit_a4UNPart_mono (a4FreshUnit_a4UN_zeroPart2 k) (le_max_right _ _)⟩,
      a4FreshUnit_a4UN_bijZ2_zero k⟩
  · exact ⟨⟨a4FreshUnit_a4UNPart_mono (hparts N (by omega) hl).some (le_max_left _ _)⟩,
      a4FreshUnit_a4UN_bijZ3 k N hk (by omega) hl⟩

theorem prop_UNmap_explicit :
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
                U N x = Matrix.mulVec (A i) x + c i := by
  classical
  intro k hk
  obtain ⟨R,hR⟩ := a4FreshUnit_a4UN_all k hk
  refine ⟨R,a4FreshUnit_a4UNU k,?_⟩
  intro N hN
  obtain ⟨hp,hbij⟩ := hR N hN
  let p := hp.some
  refine ⟨hbij,p.r,p.L,p.A,p.c,p.nr,p.card,p.norm,p.det,p.mat,p.sub,?_,?_,p.affine⟩
  · intro i j hij x hx
    exact Set.disjoint_left.mp (p.dis i j hij) hx.1 hx.2
  · intro x hx hs
    exact p.cover x ⟨hx,hs⟩
/-- The real simplex `S = {x ∈ ℝ_{≥0}^k : x₁ + ⋯ + x_k ≤ lcm(1,…,k)}`. -/
def ehrhartSimplexReal (k : ℕ) : Set (Fin k → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ (lcmUpTo k : ℝ)}

/-- The real box `B = ∏_{s=1}^k [0, lcm(1,…,k)/(k+1-s)]`, indexed by `s : Fin k`
(so `k + 1 - (s+1) = k - s.val`). -/
def ehrhartBoxReal (k : ℕ) : Set (Fin k → ℝ) :=
  {x | ∀ s : Fin k, 0 ≤ x s ∧ x s ≤ (lcmUpTo k : ℝ) / ((k - s.val : ℕ) : ℝ)}

/-- The lattice points `P ∩ ℤ^k` of a set `P ⊆ ℝ^k`. -/
def latticePointsOf (k : ℕ) (P : Set (Fin k → ℝ)) : Set (Fin k → ℤ) :=
  {z | (fun i => (z i : ℝ)) ∈ P}

private lemma a4ehrFresh6_simplex_card (k N : ℕ) :
    (simplexS k N).card = (N+k).choose k := by
  rw [← Fintype.card_coe,
    ← Fintype.card_congr (onb_degEquiv_final k N), onb_card]

private lemma a4ehrFresh6_lcmdiv (k : ℕ) (s : Fin k) :
    k-s.val ∣ lcmUpTo k := by
  apply Finset.dvd_lcm (f := id)
  apply Finset.mem_Icc.mpr
  have := s.isLt
  omega

open scoped Pointwise in
private lemma a4ehrFresh6_simplex_mem (k t : ℕ) (ht : 1 ≤ t)
    (z : Fin k → ℤ) :
    z ∈ latticePointsOf k ((t : ℝ) • ehrhartSimplexReal k) ↔
      (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ ((t*lcmUpTo k : ℕ) : ℤ) := by
  have hp : (0 : ℝ) < t := by
    exact_mod_cast (show 0 < t by omega)
  change (fun i => (z i : ℝ)) ∈ (t : ℝ) • ehrhartSimplexReal k ↔ _
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨x, ⟨hx, hs⟩, he⟩
    have hz (i) : (z i : ℝ) = (t : ℝ)*x i := by
      have h := congrFun he i
      simpa using h.symm
    refine ⟨fun i => by
      exact_mod_cast (hz i ▸ mul_nonneg hp.le (hx i)), ?_⟩
    have hsum : (∑ i, (z i : ℝ)) ≤
        (t : ℝ)*(lcmUpTo k : ℝ) := by
      simp_rw [hz]
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hs hp.le
    exact_mod_cast hsum
  · rintro ⟨hz, hs⟩
    refine ⟨fun i => (z i : ℝ)/(t : ℝ), ⟨?_, ?_⟩, ?_⟩
    · intro i
      exact div_nonneg (by exact_mod_cast hz i) hp.le
    · rw [← Finset.sum_div]
      apply (div_le_iff₀ hp).2
      have h : (∑ i, (z i : ℝ)) ≤
          (t : ℝ)*(lcmUpTo k : ℝ) := by
        exact_mod_cast hs
      simpa [mul_comm] using h
    · funext i
      change (t : ℝ) * ((z i : ℝ)/(t : ℝ)) = (z i : ℝ)
      field_simp

open scoped Pointwise in
private lemma a4ehrFresh6_box_mem (k t : ℕ) (ht : 1 ≤ t)
    (z : Fin k → ℤ) :
    z ∈ latticePointsOf k ((t : ℝ) • ehrhartBoxReal k) ↔
      ∀ i, 0 ≤ z i ∧
        z i ≤ ((t*lcmUpTo k / (k-i.val) : ℕ) : ℤ) := by
  have hp : (0 : ℝ) < t := by
    exact_mod_cast (show 0 < t by omega)
  have hd (i : Fin k) : (0 : ℝ) < ((k-i.val : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k-i.val by have := i.isLt; omega)
  have hdiv (i : Fin k) : k-i.val ∣ t*lcmUpTo k :=
    dvd_mul_of_dvd_right (a4ehrFresh6_lcmdiv k i) t
  have hcast (i : Fin k) :
      ((t*lcmUpTo k / (k-i.val) : ℕ) : ℝ) =
        (t : ℝ)*(lcmUpTo k : ℝ)/((k-i.val : ℕ) : ℝ) := by
    rw [Nat.cast_div_charZero (hdiv i), Nat.cast_mul]
  change (fun i => (z i : ℝ)) ∈ (t : ℝ) • ehrhartBoxReal k ↔ _
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨x, hx, he⟩ i
    have hz : (z i : ℝ) = (t : ℝ)*x i := by
      simpa using (congrFun he i).symm
    refine ⟨by
      exact_mod_cast (hz ▸ mul_nonneg hp.le (hx i).1), ?_⟩
    have hb : (z i : ℝ) ≤
        ((t*lcmUpTo k / (k-i.val) : ℕ) : ℝ) := by
      rw [hz, hcast]
      simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_left (hx i).2 hp.le
    exact (Int.cast_le (R := ℝ)).mp
      (by simpa only [Int.cast_natCast] using hb)
  · intro hz
    refine ⟨fun i => (z i : ℝ)/(t : ℝ), ?_, ?_⟩
    · intro i
      refine ⟨div_nonneg (by exact_mod_cast (hz i).1) hp.le, ?_⟩
      apply (div_le_iff₀ hp).2
      have h : (z i : ℝ) ≤
          ((t*lcmUpTo k / (k-i.val) : ℕ) : ℝ) := by
        simpa only [Int.cast_natCast] using
          (Int.cast_le (R := ℝ)).mpr (hz i).2
      rw [hcast] at h
      simpa [mul_div_assoc, mul_comm] using h
    · funext i
      change (t : ℝ) * ((z i : ℝ)/(t : ℝ)) = (z i : ℝ)
      field_simp

private lemma a4ehrFresh6_countS (k N : ℕ) :
    (a4FreshUnit_a4UNS k N).ncard = (N+k).choose k := by
  have he : a4FreshUnit_a4UNS k N =
      (fun x : Fin k → ℕ => fun i => (x i : ℤ)) ''
        (simplexS k N : Set _) := by
    ext z
    exact a4FreshUnit_a4UNS_cast2 k N z
  rw [he, Set.ncard_image_of_injective, Set.ncard_coe_finset,
    a4ehrFresh6_simplex_card]
  intro x y he
  funext i
  have h : (x i : ℤ) = (y i : ℤ) := congrFun he i
  exact_mod_cast h

private lemma a4ehrFresh6_choose_prod (N k : ℕ) :
    ((N + k).choose k : ℚ) =
      ∏ s : Fin k, ((N + k - s.val : ℕ) : ℚ) /
        ((k - s.val : ℕ) : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.prod_univ_succ]
      have he (s : Fin k) :
          ((N + (k + 1) - s.succ.val : ℕ) : ℚ) /
              ((k + 1 - s.succ.val : ℕ) : ℚ) =
            ((N + k - s.val : ℕ) : ℚ) /
              ((k - s.val : ℕ) : ℚ) := by
        have hs := s.isLt
        have hn : N + (k + 1) - s.succ.val = N + k - s.val := by
          simp only [Fin.val_succ]
          omega
        have hd : k + 1 - s.succ.val = k - s.val := by
          simp only [Fin.val_succ]
          omega
        rw [hn, hd]
      simp_rw [he]
      rw [← ih]
      simp only [Fin.val_zero, Nat.sub_zero]
      have hr :
          ((N + k + 1 : ℕ) : ℚ) * ((N + k).choose k : ℚ) =
            ((N + k + 1).choose (k + 1) : ℚ) *
              ((k + 1 : ℕ) : ℚ) := by
        exact_mod_cast Nat.add_one_mul_choose_eq (N + k) k
      have hn : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      rw [show N + (k + 1) = N + k + 1 by omega,
        div_mul_eq_mul_div]
      exact (eq_div_iff hn).2 hr.symm

private lemma a4ehrFresh6_nat_counts (k N : ℕ) (hk : 1 ≤ k)
    (hd : lcmUpTo k ∣ N) :
    (simplexS k N).card = (boxB k N).card := by
  classical
  have hf (s : Fin k) :
      ((N+k-s.val : ℕ) : ℚ) / ((k-s.val : ℕ) : ℚ) =
        ((N / (k-s.val) + 1 : ℕ) : ℚ) := by
    have hs := s.isLt
    have hdn : k-s.val ∣ N := (a4ehrFresh6_lcmdiv k s).trans hd
    have hn : ((k-s.val : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (show k-s.val ≠ 0 by omega)
    rw [show N+k-s.val=N+(k-s.val) by omega, Nat.cast_add,
      Nat.cast_add, Nat.cast_one, Nat.cast_div_charZero hdn]
    field_simp
  have hc : ((N+k).choose k : ℚ) = ((boxB k N).card : ℚ) := by
    rw [a4ehrFresh6_choose_prod]
    simp_rw [hf]
    simp [boxB, Fintype.card_piFinset, Nat.cast_prod]
  rw [a4ehrFresh6_simplex_card]
  exact_mod_cast hc

private lemma a4ehrFresh6_countB (k N : ℕ) (hk : 1 ≤ k)
    (hd : lcmUpTo k ∣ N) :
    (a4FreshUnit_a4UNB k N).ncard = (N+k).choose k := by
  have he : a4FreshUnit_a4UNB k N =
      (fun x : Fin k → ℕ => fun i => (x i : ℤ)) ''
        (boxB k N : Set _) := by
    ext z
    exact a4FreshUnit_a4UNB_cast k N z
  rw [he, Set.ncard_image_of_injective, Set.ncard_coe_finset,
    ← a4ehrFresh6_nat_counts k N hk hd, a4ehrFresh6_simplex_card]
  intro x y he
  funext i
  have h : (x i : ℤ) = (y i : ℤ) := congrFun he i
  exact_mod_cast h

open scoped Pointwise in
theorem ehrhart_simplex_eq_box (k : ℕ) (hk : 1 ≤ k) :
    (∀ t : ℕ, 1 ≤ t →
      Set.ncard (latticePointsOf k ((t : ℝ) • ehrhartSimplexReal k)) =
          (t * lcmUpTo k + k).choose k ∧
        (((t * lcmUpTo k + k).choose k : ℕ) : ℚ) =
          ∏ s : Fin k, ((t * lcmUpTo k + k - s.val : ℕ) : ℚ) / ((k - s.val : ℕ) : ℚ) ∧
        (∏ s : Fin k, ((t * lcmUpTo k + k - s.val : ℕ) : ℚ) / ((k - s.val : ℕ) : ℚ)) =
          (Set.ncard (latticePointsOf k ((t : ℝ) • ehrhartBoxReal k)) : ℚ) ∧
        Set.ncard (latticePointsOf k ((t : ℝ) • ehrhartSimplexReal k)) =
          Set.ncard (latticePointsOf k ((t : ℝ) • ehrhartBoxReal k))) ∧
    ∀ N : ℕ, lcmUpTo k ∣ N → (simplexS k N).card = (boxB k N).card := by
  refine ⟨?_, fun N hd => a4ehrFresh6_nat_counts k N hk hd⟩
  intro t ht
  have hs : latticePointsOf k ((t : ℝ) • ehrhartSimplexReal k) =
      a4FreshUnit_a4UNS k (t*lcmUpTo k) := by
    ext z
    exact a4ehrFresh6_simplex_mem k t ht z
  have hb : latticePointsOf k ((t : ℝ) • ehrhartBoxReal k) =
      a4FreshUnit_a4UNB k (t*lcmUpTo k) := by
    ext z
    exact a4ehrFresh6_box_mem k t ht z
  have hsc := a4ehrFresh6_countS k (t*lcmUpTo k)
  have hbc := a4ehrFresh6_countB k (t*lcmUpTo k) hk (dvd_mul_left _ _)
  rw [hs, hb]
  refine ⟨hsc, a4ehrFresh6_choose_prod _ _, ?_, hsc.trans hbc.symm⟩
  rw [hbc, ← a4ehrFresh6_choose_prod]
private lemma agent4_onb_box_bridge : UniformBoundUnit.ThmBox := by
  classical
  intro k r V h hk hV hh a ha
  obtain ⟨C, hC, hb⟩ := thm_box k r V h a hk hV hh ha
  refine ⟨C, hC, ?_⟩
  intro α hα c hc lo hi L hL hLV θ
  by_cases hlo : ∀ j, lo j ≤ hi j
  · simpa only [UniformBoundUnit.latticePtsZ, UniformBoundUnit.boxVolZ,
      UniformBoundUnit.boxSectZ, UniformBoundUnit.boxLenZ, expTwoPiI] using
      hb α hα.1 hα.2 c (fun j => (hc j).1) (fun j => (hc j).2)
        lo hi hlo L hL hLV θ
  · have hempty : UniformBoundUnit.latticePtsZ k L lo hi = ∅ := by
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

private lemma agent4_onb_UN_bridge (k : ℕ) (hk : 1 ≤ k) :
    UniformBoundUnit.PropUNmap k := by
  classical
  obtain ⟨R, hR⟩ := a4FreshUnit_a4UN_all k hk
  refine ⟨R, ?_⟩
  intro N hN hdiv
  let p := (hR N hdiv).1.some
  refine ⟨foldUN k N, a4FreshUnit_a4un_bij8 k N hk hN hdiv,
    p.r, p.L, p.A, p.c, p.nr, p.card, p.norm, p.det, p.mat, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hxZ : (fun s => (x s : ℤ)) ∈ a4FreshUnit_a4UNS k N :=
        (a4FreshUnit_a4UNS_cast2 k N _).2 ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := p.cover _ hxZ
      refine ⟨i, hi, ?_⟩
      intro j hj
      by_contra hji
      exact Set.disjoint_left.mp (p.dis j i hji) hj hi
    · rintro ⟨i, hi, _⟩
      obtain ⟨y, hy, he⟩ := (a4FreshUnit_a4UNS_cast2 k N _).1 (p.sub i hi)
      have hxy : y = x := by
        funext s
        exact_mod_cast congrFun he s
      rwa [hxy] at hy
  · intro i x hx s
    have he := congrFun (p.affine i (fun t => (x t : ℤ)) hx) s
    simpa only [a4FreshUnit_a4UNU, Int.toNat_natCast, Pi.add_apply] using he

theorem thm_onb (K : ℕ) (hK : 2 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ,
        ∃ φ : Module.Basis (Fin (Module.finrank ℂ (PolySpaceH K N))) ℂ (PolySpaceH K N),
          (∀ i j, polyInner K N (φ i) (φ j) = if i = j then 1 else 0) ∧
          ∀ i, ∀ z : Fin K → ℂ, ∑ s, ‖z s‖ ^ 2 < 1 →
            ‖polyEval K N (φ i) z‖ ≤ C := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  obtain ⟨C, hC, hbasis⟩ := UniformBoundUnit.thm_onbexplicit_allDegrees
    k (by omega) 2 (by norm_num) agent4_onb_box_bridge
    (fun j hj _ => agent4_onb_UN_bridge j hj)
  refine ⟨C, hC, ?_⟩
  intro N
  obtain ⟨ψ, horth, hbound⟩ := hbasis (Real.sqrt 2) bddPartQuot_two_sqrtTwo N
  have hdim : (N + k).choose k = Module.finrank ℂ (PolySpaceH (k + 1) N) := by
    rw [Module.finrank_fintype_fun_eq_card, onb_card]
  let e : Fin ((N + k).choose k) ≃ Fin (Module.finrank ℂ (PolySpaceH (k + 1) N)) :=
    finCongr hdim
  refine ⟨ψ.reindex e, ?_, ?_⟩
  · intro i j
    simpa only [Module.Basis.reindex_apply, e.symm.injective.eq_iff] using
      horth (e.symm i) (e.symm j)
  · intro i z hz
    rw [Module.Basis.reindex_apply]
    have hb := allDegreesProof_hom_bound (k + 1) N (by omega) (ψ (e.symm i)) C
      (hbound (e.symm i)) z
    have hr : Real.sqrt (∑ s, ‖z s‖ ^ 2) ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hz.le
    exact hb.trans (mul_le_of_le_one_right hC.le
      (pow_le_one₀ (Real.sqrt_nonneg _) hr))
