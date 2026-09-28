import JSP523.Rank5.ExceptionalOutsideContraction
import JSP523.Counting.LocalErrorAbsorption

/-!
# Exact local close from an actual polynomial error budget

The error below is the concrete dirty / exceptional-pair / singleton-
threshold / all-exceptional expression in the finite contraction theorem.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- The actual finite error appearing in the right side of the main-term
outside contraction. -/
noncomputable def actualOutsideContractionError
    (H : Family α) (W : Edge α) (v : α) (r : ℕ) : ℕ :=
  let D := badSingletonVertices H W v r
  let J := D.card.choose 2 * (W.card - 2).choose (r - 3)
  let Δ := W.card.choose (r - 2) - (W.card - r - 1).choose (r - 2)
  let dirty := (actualDirtyOutsideEdges H W v r).card
  let bᵣ := (outsideFamily H D).card
  r * (r - 1) * dirty + r * (2 * J + D.card * Δ) +
    r * (r - 1) * J + r * (r - 1) * bᵣ

/-- Actual near-star exactness from a polynomially bounded concrete finite
error. The coefficients `A,B` remain generic for later instantiation by the
explicit Part IV power estimates. We split according to whether the number
of outside edges is at least the missing-facet count. -/
theorem near_star_exact_of_actual_power_error
    (H : Family α) (W : Edge α) (v : α) (r A B : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) (hr : 5 ≤ r)
    (hw : r * (r - 3) * (2 * r - 1) ≤ W.card)
    (hLarge : 4 * A ≤ W.card)
    (hSmall : 4 * B * (missingStarFacets H W v r).card ≤
      W.card ^ (r - 1))
    (hPower : W.card ^ (r - 1) * actualOutsideContractionError H W v r ≤
      A * (missingStarFacets H W v r).card * W.card ^ (r - 2) +
        B * (missingStarFacets H W v r).card ^ 2) :
    H.card ≤ W.card.choose (r - 1) + W.card / r := by
  let q := (missingStarFacets H W v r).card
  let b := (outsideFamily H W).card
  let err := actualOutsideContractionError H W v r
  have hwPos : 0 < W.card := by
    have hr3 : 0 < r - 3 := by omega
    have hr2 : 0 < 2 * r - 1 := by omega
    have hprod : 0 < r * (r - 3) * (2 * r - 1) := by positivity
    omega
  have hexp : r - 2 + 1 = r - 1 := by omega
  have hAbsorb := Counting.absorb_linear_quadratic_power_error
    W.card q err A B (r - 2) hwPos hLarge
      (by simpa [q, hexp] using hSmall)
      (by simpa [q, err, hexp] using hPower)
  have hFinite := outside_finite_contraction_main_terms H W v r
    hAdm hUniform hr hvW
  have hFinite' : r * (r - 1) * b ≤
      2 * r * q + (r - 1) * W.card + err := by
    simpa [q, b, err, actualOutsideContractionError, Nat.add_assoc,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hFinite
  have hCoeff : 1 ≤ r * (r - 3) := by
    have hr3 : 0 < r - 3 := by omega
    nlinarith
  have hErr : 2 * err ≤ r * (r - 3) * q := by
    calc
      2 * err = 1 * (2 * err) := by omega
      _ ≤ (r * (r - 3)) * (2 * err) :=
        Nat.mul_le_mul_right (2 * err) hCoeff
      _ ≤ (r * (r - 3)) * q :=
        Nat.mul_le_mul_left (r * (r - 3)) hAbsorb
      _ = r * (r - 3) * q := rfl
  have hContract := scaled_contraction_of_error_bound
    r W.card q b err (by omega : 3 ≤ r) hFinite' hErr
  by_cases hqb : q ≤ b
  · exact near_star_exact_of_scaled_contraction
      hAdm hUniform hSupport hvW hr hw hqb hContract
  · have hId := near_star_card_identity hUniform hSupport hvW
    have hLess : b < q := by omega
    have hFacets := present_add_missing_star_facets H W v r
    have hQle : q ≤ W.card.choose (r - 1) := by
      change (presentStarFacets H W v r).card + q = W.card.choose (r - 1) at hFacets
      omega
    change H.card = W.card.choose (r - 1) - q + b at hId
    have hBase : W.card.choose (r - 1) - q + b ≤ W.card.choose (r - 1) := by
      calc
        W.card.choose (r - 1) - q + b ≤
            W.card.choose (r - 1) - q + q :=
          Nat.add_le_add_left (Nat.le_of_lt hLess) _
        _ = W.card.choose (r - 1) := Nat.sub_add_cancel hQle
    rw [hId]
    exact hBase.trans (Nat.le_add_right _ _)

end JSP523
