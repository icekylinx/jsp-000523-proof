import JSP523.Rank5.OutsideTotalErrorPower
import JSP523.Rank5.LocalExactPowerClose

/-!
# Quantitative local theorem for a fixed rank

This instantiates the finite local close with the explicit total error
coefficients from §IV.2.
-/

namespace JSP523

/-- An explicit ground-set threshold dominating all three required scales. -/
def localExactGroundThreshold (r : ℕ) : ℕ :=
  max (4 * r) (max (r * (r - 3) * (2 * r - 1))
    (4 * outsideTotalErrorLinearCoefficient r))

/-- The real density constant used for the quadratic error term. -/
noncomputable def localExactDensity (r : ℕ) : ℝ :=
  1 / (4 * outsideTotalErrorQuadraticCoefficient r : ℕ)

/-- The explicit quadratic coefficient is positive for every rank in the
range of the local theorem. -/
theorem outsideTotalErrorQuadraticCoefficient_pos
    (r : ℕ) (hr : 5 ≤ r) : 0 < outsideTotalErrorQuadraticCoefficient r := by
  have hK : 0 < 2 * (4 * r) ^ (r - 1) * (r - 1) := by
    apply Nat.mul_pos
    · positivity
    · omega
  have hFactor : 0 < 1 + 3 * r ^ r := by omega
  have hOther : 0 < 2 * r + r * (r - 1) := by omega
  have hTerm : 0 < (2 * (4 * r) ^ (r - 1) * (r - 1)) ^ 2 *
      (1 + 3 * r ^ r) := Nat.mul_pos (pow_pos hK 2) hFactor
  unfold outsideTotalErrorQuadraticCoefficient
  exact add_pos_of_nonneg_of_pos (Nat.zero_le _) (Nat.mul_pos hOther hTerm)


/-- The explicit real density constant is positive for every rank in the
range of the theorem. -/
theorem localExactDensity_pos (r : ℕ) (hr : 5 ≤ r) :
    0 < localExactDensity r := by
  unfold localExactDensity
  have hB : 0 < outsideTotalErrorQuadraticCoefficient r :=
    outsideTotalErrorQuadraticCoefficient_pos r hr
  have hDen : (0 : ℝ) <
      (4 * outsideTotalErrorQuadraticCoefficient r : ℕ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < 4) hB
  exact one_div_pos.mpr hDen

/-- For fixed `r ≥ 5`, the explicit density condition forces the local
near-star upper bound as soon as the ground set exceeds the explicit
rank-only threshold `w₀(r)`. -/
theorem quantitative_near_star_exact
    {α : Type*} [DecidableEq α]
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) (hr : 5 ≤ r)
    (hw₀ : localExactGroundThreshold r ≤ W.card)
    (hDensity : ((missingStarFacets H W v r).card : ℝ) ≤
      localExactDensity r * (W.card : ℝ) ^ (r - 1)) :
    H.card ≤ W.card.choose (r - 1) + W.card / r := by
  let A := outsideTotalErrorLinearCoefficient r
  let B := outsideTotalErrorQuadraticCoefficient r
  have hOuter : max (r * (r - 3) * (2 * r - 1))
      (4 * outsideTotalErrorLinearCoefficient r) ≤ W.card := by
    dsimp [localExactGroundThreshold] at hw₀
    exact le_trans (Nat.le_max_right (4 * r) _) hw₀
  have hW0 : 4 * r ≤ W.card := by
    dsimp [localExactGroundThreshold] at hw₀
    exact le_trans (Nat.le_max_left _ _) hw₀
  have hMargin : r * (r - 3) * (2 * r - 1) ≤ W.card :=
    le_trans (Nat.le_max_left _ _) hOuter
  have hA : 4 * A ≤ W.card := by
    dsimp [A]
    exact le_trans (Nat.le_max_right _ _) hOuter
  have hBpos : 0 < B := by
    dsimp [B]
    exact outsideTotalErrorQuadraticCoefficient_pos r hr
  have hSmallNat : 4 * B * (missingStarFacets H W v r).card ≤
      W.card ^ (r - 1) := by
    apply Counting.real_density_implies_power_small
      W.card (missingStarFacets H W v r).card B (r - 1) hBpos
    simpa [localExactDensity, B, div_eq_mul_inv, mul_comm] using hDensity
  have hPower := outside_total_error_power_bound H W v r
    hAdm hUniform hr hvW hW0
  have hBudget : W.card ^ (r - 1) * actualOutsideContractionError H W v r ≤
      A * (missingStarFacets H W v r).card * W.card ^ (r - 2) +
        B * (missingStarFacets H W v r).card ^ 2 := by
    simpa [A, B, actualOutsideContractionError, Nat.add_assoc,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hPower
  exact near_star_exact_of_actual_power_error H W v r A B
    hAdm hUniform hSupport hvW hr hMargin hA hSmallNat hBudget


/-- Existence form of the quantitative first conclusion in Theorem IV.2.1:
for each fixed rank, there are explicit positive density and ground-set
constants that imply the local near-star upper bound. -/
theorem exists_quantitative_near_star_exact (r : ℕ) (hr : 5 ≤ r) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ w₀ : ℕ,
      ∀ {α : Type*} [DecidableEq α] (H : Family α) (W : Edge α)
        (v : α),
        Admissible H → Uniform r H →
        (∀ E ∈ H, E ⊆ insert v W) → v ∉ W →
        w₀ ≤ W.card →
        ((missingStarFacets H W v r).card : ℝ) ≤
          δ * (W.card : ℝ) ^ (r - 1) →
        H.card ≤ W.card.choose (r - 1) + W.card / r := by
  refine ⟨localExactDensity r, localExactDensity_pos r hr,
    localExactGroundThreshold r, ?_⟩
  intro α _ H W v hAdm hUniform hSupport hvW hw₀ hDensity
  exact quantitative_near_star_exact H W v r hAdm hUniform hSupport hvW hr
    hw₀ hDensity

/-- The second assertion of Theorem IV.2.1 under the same explicit power
budget: if the family reaches the star baseline, its actual outside family
is linear and satisfies the sharp incidence bound. -/
theorem outside_linear_incidence_of_quantitative_baseline
    {α : Type*} [DecidableEq α]
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) (hr : 5 ≤ r)
    (hw₀ : localExactGroundThreshold r ≤ W.card)
    (hDensity : ((missingStarFacets H W v r).card : ℝ) ≤
      localExactDensity r * (W.card : ℝ) ^ (r - 1))
    (hBaseline : W.card.choose (r - 1) ≤ H.card) :
    LinearFamily (outsideFamily H W) ∧
      r * (outsideFamily H W).card ≤
        W.card + (missingStarFacets H W v r).card := by
  let A := outsideTotalErrorLinearCoefficient r
  let B := outsideTotalErrorQuadraticCoefficient r
  let q := (missingStarFacets H W v r).card
  let b := (outsideFamily H W).card
  have hOuter : max (r * (r - 3) * (2 * r - 1))
      (4 * outsideTotalErrorLinearCoefficient r) ≤ W.card := by
    dsimp [localExactGroundThreshold] at hw₀
    exact le_trans (Nat.le_max_right (4 * r) _) hw₀
  have hMargin : r * (r - 3) * (2 * r - 1) ≤ W.card :=
    le_trans (Nat.le_max_left _ _) hOuter
  have hW0 : 4 * r ≤ W.card := by
    dsimp [localExactGroundThreshold] at hw₀
    exact le_trans (Nat.le_max_left _ _) hw₀
  have hBpos : 0 < B := by
    dsimp [B]
    exact outsideTotalErrorQuadraticCoefficient_pos r hr
  have hSmallNat : 4 * B * q ≤ W.card ^ (r - 1) := by
    apply Counting.real_density_implies_power_small
      W.card q B (r - 1) hBpos
    simpa [localExactDensity, B, div_eq_mul_inv, mul_comm] using hDensity
  have hPower := outside_total_error_power_bound H W v r
    hAdm hUniform hr hvW hW0
  have hBudget : W.card ^ (r - 1) * actualOutsideContractionError H W v r ≤
      A * q * W.card ^ (r - 2) + B * q ^ 2 := by
    simpa [A, B, actualOutsideContractionError, Nat.add_assoc,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hPower
  have hwPos : 0 < W.card := by omega
  have hexp : r - 2 + 1 = r - 1 := by omega
  have hAbsorb := Counting.absorb_linear_quadratic_power_error
    W.card q (actualOutsideContractionError H W v r) A B (r - 2)
      hwPos (by
        dsimp [A]
        exact le_trans (Nat.le_max_right _ _) hOuter)
      (by simpa [hexp] using hSmallNat) (by simpa [hexp] using hBudget)
  have hFinite := outside_finite_contraction_main_terms H W v r
    hAdm hUniform hr hvW
  have hFinite' : r * (r - 1) * b ≤
      2 * r * q + (r - 1) * W.card + actualOutsideContractionError H W v r := by
    simpa [q, b, actualOutsideContractionError, Nat.add_assoc,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hFinite
  have hCoeff : 1 ≤ r * (r - 3) := by
    have hr3 : 0 < r - 3 := by omega
    nlinarith
  have hErr : 2 * actualOutsideContractionError H W v r ≤
      r * (r - 3) * q := by
    calc
      2 * actualOutsideContractionError H W v r =
          1 * (2 * actualOutsideContractionError H W v r) := by omega
      _ ≤ (r * (r - 3)) *
          (2 * actualOutsideContractionError H W v r) :=
        Nat.mul_le_mul_right _ hCoeff
      _ ≤ (r * (r - 3)) * q :=
        Nat.mul_le_mul_left _ hAbsorb
      _ = r * (r - 3) * q := rfl
  have hContract := scaled_contraction_of_error_bound r W.card q b
    (actualOutsideContractionError H W v r) (by omega : 3 ≤ r) hFinite' hErr
  have hId := near_star_card_identity hUniform hSupport hvW
  change H.card = W.card.choose (r - 1) - q + b at hId
  have hQle : q ≤ W.card.choose (r - 1) := by
    have hFacets := present_add_missing_star_facets H W v r
    change (presentStarFacets H W v r).card + q = W.card.choose (r - 1) at hFacets
    omega
  have hqb : q ≤ b := by rw [hId] at hBaseline; omega
  have hSmallGap := missing_below_local_gap_of_scaled_contraction
    r W.card q b hr hMargin hqb hContract
  have h2r : 2 * r ≤ W.card := by
    have hCoeff' : 2 ≤ r - 3 := by omega
    have hMul := Nat.mul_le_mul_left r hCoeff'
    have hFactor : 1 ≤ 2 * r - 1 := by omega
    have hMul' := Nat.mul_le_mul_left (r * (r - 3)) hFactor
    omega
  have hLin := outside_linear_of_missing_below_local_gap
    hAdm hUniform hvW (by omega : 3 ≤ r) h2r hSmallGap
  let Bfam := outsideFamily H W
  have hBH : Bfam ⊆ H := Finset.filter_subset _ _
  have hBU : Uniform r Bfam := fun E hE => hUniform (hBH hE)
  have hBW : ∀ E ∈ Bfam, E ⊆ W := by
    intro E hE
    exact (Finset.mem_filter.mp hE).2
  have hInc := linear_near_star_incidence_bound hAdm hBH hBU hLin
    (by omega : 3 ≤ r) hBW hvW
  exact ⟨hLin, by simpa [Bfam] using hInc⟩

end JSP523
