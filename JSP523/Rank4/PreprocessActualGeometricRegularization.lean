import JSP523.Rank4.PreprocessContractionScalar

/-! # Actual dyadic regularization with arbitrarily small edge loss -/

namespace JSP523.Rank4

private theorem sixth_power_le_half_eighth (q : ℕ) (hq : 256 ≤ q) :
    q ^ 6 ≤ (q / 2) ^ 8 := by
  have hHalf : 27 ≤ q / 2 := by omega
  have hqHalf : q ≤ 3 * (q / 2) := by omega
  have hSq : 729 ≤ (q / 2) ^ 2 := by nlinarith
  calc
    _ ≤ (3 * (q / 2)) ^ 6 := Nat.pow_le_pow_left hqHalf 6
    _ = 729 * (q / 2) ^ 6 := by ring
    _ ≤ (q / 2) ^ 2 * (q / 2) ^ 6 := Nat.mul_le_mul_right _ hSq
    _ = (q / 2) ^ 8 := by ring

/-- The reserve term makes the geometric loss summation division-free. -/
private theorem actual_dyadic_regularization_aux
    {n : ℕ} (L : ℕ) (hL : 256 ≤ L) (q : ℕ)
    (F : Family (Fin n)) (hRange : L ≤ 2 * q) (hn : q ^ 11 ≤ n)
    (hAdm : Admissible F) (hUniform : Uniform 4 F)
    (hVertex : ∀ v, (F.filter fun E => v ∈ E).card ≤ q ^ 8 * n ^ 2)
    (hPair : ∀ P : Edge (Fin n), P.card = 2 → rankFourPairDegree F P ≤ q ^ 8 * n)
    (hFacet : ∀ Q : Edge (Fin n), Q.card = 3 → (facetCompletions F Finset.univ Q).card ≤ q ^ 8) :
    ∃ K : Family (Fin n), K ⊆ F ∧
      L * q * (F \ K).card + 128 * L * n ^ 3 ≤ 256 * q * n ^ 3 ∧
      (∀ v, (K.filter fun E => v ∈ E).card ≤ L ^ 8 * n ^ 2) ∧
      (∀ P : Edge (Fin n), P.card = 2 → rankFourPairDegree K P ≤ L ^ 8 * n) ∧
      (∀ Q : Edge (Fin n), Q.card = 3 → (facetCompletions K Finset.univ Q).card ≤ L ^ 8) := by
  induction q using Nat.strong_induction_on generalizing F with
  | h q ih =>
    by_cases hStop : q ≤ L
    · have hPow := Nat.pow_le_pow_left hStop 8
      refine ⟨F, Finset.Subset.refl _, ?_, ?_, ?_, ?_⟩
      · simp only [Finset.sdiff_self, Finset.card_empty, mul_zero, zero_add]
        nlinarith [Nat.mul_le_mul_right (128 * n ^ 3) hRange]
      · intro v
        exact (hVertex v).trans (Nat.mul_le_mul_right _ hPow)
      · intro P hP
        exact (hPair P hP).trans (Nat.mul_le_mul_right n hPow)
      · intro Q hQ
        exact (hFacet Q hQ).trans hPow
    · have hq : 256 ≤ q := by omega
      have hq2 : 2 ≤ q := by omega
      obtain ⟨F₁, hF₁F, hLoss₁, hV₁, hP₁, hQ₁⟩ :=
        exists_actual_eighth_power_contraction F q hq2 hn hAdm hUniform hVertex hPair hFacet
      let p := q / 2
      have hpLt : p < q := Nat.div_lt_self (by omega) (by omega)
      have hpRange : L ≤ 2 * p := by dsimp [p]; omega
      have hpPos : 0 < p := by omega
      have hpLe : p ≤ q := Nat.div_le_self q 2
      have hpN : p ^ 11 ≤ n := (Nat.pow_le_pow_left hpLe 11).trans hn
      have hPower : q ^ 6 ≤ p ^ 8 := sixth_power_le_half_eighth q hq
      obtain ⟨K, hKF₁, hLossK, hVK, hPK, hQK⟩ := ih p hpLt F₁ hpRange hpN
        (admissible_mono hF₁F hAdm) (fun _ hE => hUniform (hF₁F hE))
        (fun v => (hV₁ v).trans (Nat.mul_le_mul_right _ hPower))
        (fun P hP => (hP₁ P hP).trans (Nat.mul_le_mul_right _ hPower))
        (fun Q hQ => (hQ₁ Q hQ).trans hPower)
      refine ⟨K, hKF₁.trans hF₁F, ?_, hVK, hPK, hQK⟩
      have h0 := Finset.card_sdiff_add_card_eq_card hF₁F
      have h1 := Finset.card_sdiff_add_card_eq_card hKF₁
      have h2 := Finset.card_sdiff_add_card_eq_card (hKF₁.trans hF₁F)
      have hAdd : (F \ K).card = (F \ F₁).card + (F₁ \ K).card := by omega
      have hTwop : 2 * p ≤ q := by dsimp [p]; omega
      have hScaled₁ := Nat.mul_le_mul_left (L * p) hLoss₁
      have hScaledK := Nat.mul_le_mul_left q hLossK
      have hReserve := Nat.mul_le_mul_left (128 * L * n ^ 3) hTwop
      have hTotal : p * (L * q * (F \ K).card + 128 * L * n ^ 3) ≤
          p * (256 * q * n ^ 3) := by
        rw [hAdd]
        nlinarith only [hScaled₁, hScaledK, hReserve]
      exact Nat.le_of_mul_le_mul_left hTotal hpPos

/-- Given the initial admissible range `q^11 ≤ n`, actual deletion reduces
all degree factors to the fixed `L^8`, at cost at most `256 n³/L`.
The output is a real subfamily of F, not a scalar regularization premise. -/
theorem exists_actual_bounded_degree_regularization
    {n : ℕ} (F : Family (Fin n)) (q L : ℕ)
    (hL : 256 ≤ L) (hn : q ^ 11 ≤ n)
    (hAdm : Admissible F) (hUniform : Uniform 4 F)
    (hVertex : ∀ v, (F.filter fun E => v ∈ E).card ≤ q ^ 8 * n ^ 2)
    (hPair : ∀ P : Edge (Fin n), P.card = 2 → rankFourPairDegree F P ≤ q ^ 8 * n)
    (hFacet : ∀ Q : Edge (Fin n), Q.card = 3 → (facetCompletions F Finset.univ Q).card ≤ q ^ 8) :
    ∃ K : Family (Fin n), K ⊆ F ∧ L * (F \ K).card ≤ 256 * n ^ 3 ∧
      (∀ v, (K.filter fun E => v ∈ E).card ≤ L ^ 8 * n ^ 2) ∧
      (∀ P : Edge (Fin n), P.card = 2 → rankFourPairDegree K P ≤ L ^ 8 * n) ∧
      (∀ Q : Edge (Fin n), Q.card = 3 → (facetCompletions K Finset.univ Q).card ≤ L ^ 8) := by
  by_cases hStop : q ≤ L
  · have hPow := Nat.pow_le_pow_left hStop 8
    exact ⟨F, Finset.Subset.refl _, by simp,
      fun v => (hVertex v).trans (Nat.mul_le_mul_right _ hPow),
      fun P hP => (hPair P hP).trans (Nat.mul_le_mul_right _ hPow),
      fun Q hQ => (hFacet Q hQ).trans hPow⟩
  · obtain ⟨K, hKF, hLoss, hV, hP, hQ⟩ := actual_dyadic_regularization_aux L hL q F
      (by omega) hn hAdm hUniform hVertex hPair hFacet
    refine ⟨K, hKF, ?_, hV, hP, hQ⟩
    have hMul : q * (L * (F \ K).card) ≤ q * (256 * n ^ 3) := by nlinarith only [hLoss, Nat.zero_le (128 * L * n ^ 3)]
    exact Nat.le_of_mul_le_mul_left hMul (by omega)

end JSP523.Rank4
