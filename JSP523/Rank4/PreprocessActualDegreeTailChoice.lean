import JSP523.Rank4.PreprocessActualGeometricRegularization

/-! # Choosing the actual uniform degree tail after τ -/

namespace JSP523.Rank4

noncomputable def actualRegularizationLevel (τ : ℝ) : ℕ := max 256 ⌈2048 / τ⌉₊

noncomputable def actualDegreeTailThreshold (τ : ℝ) : ℕ := 2 * actualRegularizationLevel τ ^ 8

/-- The fixed threshold depends only on τ.  The subfamily and the actual
edge loss are constructed by geometric regularization. -/
theorem exists_actual_degree_tail_cleanup
    {n : ℕ} (F : Family (Fin n)) (q : ℕ) (τ : ℝ) (hτ : 0 < τ)
    (hn : q ^ 11 ≤ n) (hAdm : Admissible F) (hUniform : Uniform 4 F)
    (hVertex : ∀ v, (F.filter fun E => v ∈ E).card ≤ q ^ 8 * n ^ 2)
    (hPair : ∀ P : Edge (Fin n), P.card = 2 → rankFourPairDegree F P ≤ q ^ 8 * n)
    (hFacet : ∀ Q : Edge (Fin n), Q.card = 3 → (facetCompletions F Finset.univ Q).card ≤ q ^ 8) :
    1 ≤ actualDegreeTailThreshold τ ∧
    ∃ B₁ : Family (Fin n), B₁ ⊆ F ∧
      (8 * ((F \ B₁).card : ℝ) ≤ τ * (n : ℝ) ^ 3) ∧
      (∀ Q : Edge (Fin n), Q.card = 3 →
        2 * (facetCompletions B₁ Finset.univ Q).card ≤ actualDegreeTailThreshold τ) := by
  let L := actualRegularizationLevel τ
  have hL : 256 ≤ L := Nat.le_max_left _ _
  have hLPos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hLReal : 2048 ≤ τ * (L : ℝ) := by
    have hc : 2048 / τ ≤ (L : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_max_right 256 ⌈2048 / τ⌉₊))
    have hh := (div_le_iff₀ hτ).1 hc
    linarith
  obtain ⟨B₁, hBF, hLoss, _, _, hCap⟩ := exists_actual_bounded_degree_regularization
    F q L hL hn hAdm hUniform hVertex hPair hFacet
  have hLossReal : (L : ℝ) * ((F \ B₁).card : ℝ) ≤ 256 * (n : ℝ) ^ 3 := by exact_mod_cast hLoss
  have hScaled : (L : ℝ) * (8 * ((F \ B₁).card : ℝ)) ≤ (L : ℝ) * (τ * (n : ℝ) ^ 3) := by
    have hh := mul_le_mul_of_nonneg_right hLReal (by positivity : 0 ≤ (n : ℝ) ^ 3)
    nlinarith
  have hDegree : 1 ≤ actualDegreeTailThreshold τ := by
    have hOne : 1 ≤ L ^ 8 := one_le_pow₀ (by omega : 1 ≤ L)
    change 1 ≤ 2 * L ^ 8
    omega
  refine ⟨hDegree, B₁, hBF, (mul_le_mul_iff_right₀ hLPos).1 ?_, ?_⟩
  · simpa only [mul_comm] using hScaled
  · intro Q hQ
    exact Nat.mul_le_mul_left 2 (hCap Q hQ)

end JSP523.Rank4
