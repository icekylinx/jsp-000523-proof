import JSP523.Rank5.ExceptionalErrorPowerBounds
import JSP523.Rank5.DeltaErrorPower
import JSP523.Rank5.ExceptionalOutsideContraction
import JSP523.Rank5.DirtyOutsideErrorPower
import Mathlib.Tactic.Ring

/-!
# Explicit power budget for the finite outside-contraction error

The error is exactly the one in `outside_finite_contraction_main_terms` and
`near_star_exact_of_explicit_outside_error`. The coefficients are rank-only
natural numbers; the resulting estimate has no division or asymptotic terms.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

def outsideDirtyLinearCoefficient (r : ℕ) : ℕ :=
  2 * (4 * r) ^ (r - 1) * (r - 1).choose 2 +
    ∑ k ∈ Finset.Icc 3 (r - 2),
      2 * (4 * r) ^ (r - 1) * (r - 1).choose k

def outsideDirtyQuadraticCoefficient (r : ℕ) : ℕ :=
  2 * (2 * (4 * r) ^ (r - 1) * (r - 1).choose 2) ^ 2

def outsideTotalErrorLinearCoefficient (r : ℕ) : ℕ :=
  r * (r - 1) * outsideDirtyLinearCoefficient r +
    r * (2 * (4 * r) ^ (r - 1) * (r - 1)) * (r + 1)

def outsideTotalErrorQuadraticCoefficient (r : ℕ) : ℕ :=
  r * (r - 1) * outsideDirtyQuadraticCoefficient r + (2 * r + r * (r - 1)) *
    ((2 * (4 * r) ^ (r - 1) * (r - 1)) ^ 2 * (1 + 3 * r ^ r))

/-- The exact error in the finite outside contraction obeys an explicit
linear-plus-quadratic power budget. -/
theorem outside_total_error_power_bound
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 5 ≤ r) (hvW : v ∉ W) (hw : 4 * r ≤ W.card) :
    let D := badSingletonVertices H W v r
    let Δ := W.card.choose (r - 2) - (W.card - r - 1).choose (r - 2)
    let J := D.card.choose 2 * (W.card - 2).choose (r - 3)
    let bᵣ := (outsideFamily H D).card
    let q := (missingStarFacets H W v r).card
    let err := r * (r - 1) * (actualDirtyOutsideEdges H W v r).card +
      r * (2 * J + D.card * Δ) +
      r * (r - 1) * J + r * (r - 1) * bᵣ
    W.card ^ (r - 1) * err ≤
      outsideTotalErrorLinearCoefficient r * q * W.card ^ (r - 2) +
        outsideTotalErrorQuadraticCoefficient r * q ^ 2 := by
  classical
  let D := badSingletonVertices H W v r
  let w := W.card
  let q := (missingStarFacets H W v r).card
  let Δ := w.choose (r - 2) - (w - r - 1).choose (r - 2)
  let J := D.card.choose 2 * (w - 2).choose (r - 3)
  let bᵣ := (outsideFamily H D).card
  let dirty := (actualDirtyOutsideEdges H W v r).card
  let K := 2 * (4 * r) ^ (r - 1) * (r - 1)
  let C := K ^ 2 * (1 + 3 * r ^ r)
  let R := r * (r - 1)
  let err := R * dirty + r * (2 * J + D.card * Δ) + R * J + R * bᵣ
  let Cpair := 2 * (4 * r) ^ (r - 1) * (r - 1).choose 2
  let Chigh := ∑ k ∈ Finset.Icc 3 (r - 2),
    2 * (4 * r) ^ (r - 1) * (r - 1).choose k
  let ADirty := Cpair + Chigh
  let BDirty := 2 * Cpair ^ 2
  have hDelta := actual_singleton_delta_error_power_bound H W v r hr hw
  change w * D.card * Δ ≤ K * (r + 1) * q at hDelta
  have hExceptional := exceptional_pair_and_all_bad_power_bound
    H W v r hr hAdm hUniform hw
  change w ^ (r - 1) * (J + bᵣ) ≤ C * q ^ 2 at hExceptional
  have hCoef : R ≤ 2 * r + R := Nat.le_add_left R (2 * r)
  have hJBcoef : (2 * r + R) * J + R * bᵣ ≤
      (2 * r + R) * (J + bᵣ) := by nlinarith
  have hJandB : w ^ (r - 1) * ((2 * r + R) * J + R * bᵣ) ≤
      (2 * r + R) * C * q ^ 2 := by
    calc
      w ^ (r - 1) * ((2 * r + R) * J + R * bᵣ) ≤
          w ^ (r - 1) * ((2 * r + R) * (J + bᵣ)) :=
        Nat.mul_le_mul_left _ hJBcoef
      _ = (2 * r + R) * (w ^ (r - 1) * (J + bᵣ)) := by ac_rfl
      _ ≤ (2 * r + R) * (C * q ^ 2) :=
        Nat.mul_le_mul_left _ hExceptional
      _ = (2 * r + R) * C * q ^ 2 := by ac_rfl
  have hDeltaReorder : w * (D.card * Δ) ≤ K * (r + 1) * q := by
    simpa [Nat.mul_assoc] using hDelta
  have hDeltaScaled : w ^ (r - 1) * (r * (D.card * Δ)) ≤
      (r * K * (r + 1)) * q * w ^ (r - 2) := by
    have hexp : r - 1 = (r - 2) + 1 := by omega
    have hBase : w ^ (r - 1) * (D.card * Δ) ≤
        K * (r + 1) * q * w ^ (r - 2) := by
      rw [hexp, pow_succ]
      calc
        w ^ (r - 2) * w * (D.card * Δ) =
            w ^ (r - 2) * (w * (D.card * Δ)) := by ac_rfl
        _ ≤
            w ^ (r - 2) * (K * (r + 1) * q) :=
          Nat.mul_le_mul_left _ hDeltaReorder
        _ = K * (r + 1) * q * w ^ (r - 2) := by ac_rfl
    calc
      w ^ (r - 1) * (r * (D.card * Δ)) =
          r * (w ^ (r - 1) * (D.card * Δ)) := by ac_rfl
      _ ≤ r * (K * (r + 1) * q * w ^ (r - 2)) :=
        Nat.mul_le_mul_left r hBase
      _ = (r * K * (r + 1)) * q * w ^ (r - 2) := by ac_rfl
  have hDirty := actual_dirty_outside_error_power_bound H W v r
    hAdm hUniform hr hvW hw
  change w ^ (r - 1) * dirty ≤
    ADirty * q * w ^ (r - 2) + BDirty * q ^ 2 at hDirty
  have hDirtyScaled : w ^ (r - 1) * (R * dirty) ≤
      (R * ADirty) * q * w ^ (r - 2) + (R * BDirty) * q ^ 2 := by
    calc
      w ^ (r - 1) * (R * dirty) = R * (w ^ (r - 1) * dirty) := by ac_rfl
      _ ≤ R * (ADirty * q * w ^ (r - 2) + BDirty * q ^ 2) :=
        Nat.mul_le_mul_left R hDirty
      _ = (R * ADirty) * q * w ^ (r - 2) +
          (R * BDirty) * q ^ 2 := by ring
  have hErrEq : err = R * dirty + r * (D.card * Δ) +
      ((2 * r + R) * J + R * bᵣ) := by
    dsimp [err, R]
    ring
  have hWhole : w ^ (r - 1) * err ≤
      ((R * ADirty) * q * w ^ (r - 2) +
        (r * K * (r + 1)) * q * w ^ (r - 2)) +
        ((R * BDirty) * q ^ 2 + (2 * r + R) * C * q ^ 2) := by
    calc
      w ^ (r - 1) * err =
          w ^ (r - 1) *
            (R * dirty + r * (D.card * Δ) +
              ((2 * r + R) * J + R * bᵣ)) := by rw [hErrEq]
      _ = w ^ (r - 1) * (R * dirty) +
          (w ^ (r - 1) * (r * (D.card * Δ)) +
            w ^ (r - 1) * ((2 * r + R) * J + R * bᵣ)) := by ring
      _ ≤ (R * ADirty * q * w ^ (r - 2) + R * BDirty * q ^ 2) +
          (r * K * (r + 1) * q * w ^ (r - 2) +
            (2 * r + R) * C * q ^ 2) :=
        Nat.add_le_add hDirtyScaled
          (Nat.add_le_add hDeltaScaled hJandB)
      _ = _ := by ac_rfl
  change w ^ (r - 1) * err ≤
    outsideTotalErrorLinearCoefficient r * q * w ^ (r - 2) +
      outsideTotalErrorQuadraticCoefficient r * q ^ 2
  calc
    w ^ (r - 1) * err ≤
        ((R * ADirty) * q * w ^ (r - 2) +
          (r * K * (r + 1)) * q * w ^ (r - 2)) +
          ((R * BDirty) * q ^ 2 + (2 * r + R) * C * q ^ 2) := hWhole
    _ = outsideTotalErrorLinearCoefficient r * q * w ^ (r - 2) +
        outsideTotalErrorQuadraticCoefficient r * q ^ 2 := by
      dsimp [outsideTotalErrorLinearCoefficient,
        outsideTotalErrorQuadraticCoefficient, outsideDirtyLinearCoefficient,
        outsideDirtyQuadraticCoefficient, K, C, R, ADirty, BDirty,
        Cpair, Chigh]
      ring

end JSP523
