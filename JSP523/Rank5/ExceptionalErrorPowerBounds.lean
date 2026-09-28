import JSP523.Rank5.BadRootPowerBounds
import JSP523.Rank5.ExceptionalMultiVertex
import Mathlib.Tactic.Ring

/-!
# Explicit polynomial bounds for the exceptional error terms

This module bounds the pair budget `J` and the actual all-bad layer `bᵣ`
using the denominator-free bad-singleton estimate and the coarse ground-set
bound. No asymptotic notation occurs in the statements.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

private theorem exceptional_square_scale
    (d w r K q : ℕ)
    (hScale : d * w ^ (r - 2) ≤ K * q) :
    d ^ 2 * w ^ (2 * r - 4) ≤ K ^ 2 * q ^ 2 := by
  have hExp : (r - 2) * 2 = 2 * r - 4 := by omega
  have hEq : (d * w ^ (r - 2)) ^ 2 = d ^ 2 * w ^ (2 * r - 4) := by
    calc
      (d * w ^ (r - 2)) ^ 2 = d ^ 2 * (w ^ (r - 2)) ^ 2 := by ring
      _ = d ^ 2 * w ^ (2 * r - 4) := by
        rw [pow_two, ← pow_mul, hExp]
  have hSq := Nat.mul_le_mul hScale hScale
  have hSq' : (d * w ^ (r - 2)) ^ 2 ≤ (K * q) ^ 2 := by
    simpa [pow_two] using hSq
  have hCoeff : (K * q) ^ 2 = K ^ 2 * q ^ 2 := by ring
  calc
    d ^ 2 * w ^ (2 * r - 4) = (d * w ^ (r - 2)) ^ 2 := hEq.symm
    _ ≤ (K * q) ^ 2 := hSq'
    _ = K ^ 2 * q ^ 2 := hCoeff

/-- The `J` and all-exceptional error terms have an explicit quadratic
bound after multiplication by `w^(r-1)`. The rank constant is
`K^2 * (1 + 3*r^r)`, where `K = 2*(4*r)^(r-1)*(r-1)` is exactly the
constant in the singleton power bound. -/
theorem exceptional_pair_and_all_bad_power_bound
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hr : 5 ≤ r) (hAdm : Admissible H) (hUniform : Uniform r H)
    (hw : 4 * r ≤ W.card) :
    let D := badSingletonVertices H W v r
    let d := D.card
    let q := (missingStarFacets H W v r).card
    let J := d.choose 2 * (W.card - 2).choose (r - 3)
    let bᵣ := (outsideFamily H D).card
    let K := 2 * (4 * r) ^ (r - 1) * (r - 1)
    W.card ^ (r - 1) * (J + bᵣ) ≤
      (K ^ 2 * (1 + 3 * r ^ r)) * q ^ 2 := by
  classical
  let D := badSingletonVertices H W v r
  let d := D.card
  let w := W.card
  let q := (missingStarFacets H W v r).card
  let J := d.choose 2 * (w - 2).choose (r - 3)
  let bᵣ := (outsideFamily H D).card
  let K := 2 * (4 * r) ^ (r - 1) * (r - 1)
  have hr₃ : 3 ≤ r := by omega
  have hdw : d ≤ w := Finset.card_le_card (Finset.filter_subset _ _)
  have hSingleton := actual_bad_singleton_power_bound H W v r hr₃ hw
  change d * w ^ (r - 2) ≤ K * q at hSingleton
  have hSquare := exceptional_square_scale d w r K q hSingleton
  have hChooseD : d.choose 2 ≤ d ^ 2 := Nat.choose_le_pow d 2
  have hChooseW : (w - 2).choose (r - 3) ≤ w ^ (r - 3) := by
    exact (Nat.choose_le_choose (r - 3) (Nat.sub_le w 2)).trans
      (Nat.choose_le_pow w (r - 3))
  have hJ : J ≤ d ^ 2 * w ^ (r - 3) := by
    dsimp [J]
    exact Nat.mul_le_mul hChooseD hChooseW
  have hExp₂ : (r - 3) + (r - 1) = 2 * r - 4 := by omega
  have hJScaled : w ^ (r - 1) * J ≤ d ^ 2 * w ^ (2 * r - 4) := by
    calc
      w ^ (r - 1) * J ≤ w ^ (r - 1) * (d ^ 2 * w ^ (r - 3)) :=
        Nat.mul_le_mul_left _ hJ
      _ = d ^ 2 * (w ^ (r - 1) * w ^ (r - 3)) := by ac_rfl
      _ = d ^ 2 * w ^ (2 * r - 4) := by
        calc
          d ^ 2 * (w ^ (r - 1) * w ^ (r - 3)) =
              d ^ 2 * w ^ ((r - 1) + (r - 3)) := by rw [← pow_add]
          _ = d ^ 2 * w ^ (2 * r - 4) := by
            rw [Nat.add_comm (r - 1) (r - 3), hExp₂]
  have hAll := outside_all_bad_coarse_bound H W v r hr hUniform hAdm
  change r.factorial * bᵣ ≤ 3 * r ^ r * d ^ (r - 1) at hAll
  have hFact : 1 ≤ r.factorial := Nat.factorial_pos r
  have hAllWeak : bᵣ ≤ 3 * r ^ r * d ^ (r - 1) := by
    calc
      bᵣ = 1 * bᵣ := by simp
      _ ≤ r.factorial * bᵣ := Nat.mul_le_mul_right bᵣ hFact
      _ ≤ 3 * r ^ r * d ^ (r - 1) := hAll
  have hExp₁ : r - 1 = 2 + (r - 3) := by omega
  have hExp₂ : (r - 3) + (r - 1) = 2 * r - 4 := by omega
  have hDpow : d ^ (r - 1) * w ^ (r - 1) ≤
      d ^ 2 * w ^ (2 * r - 4) := by
    have hdPow : d ^ (r - 1) = d ^ 2 * d ^ (r - 3) := by
      rw [hExp₁, pow_add]
    rw [hdPow]
    calc
      d ^ 2 * d ^ (r - 3) * w ^ (r - 1) ≤
          d ^ 2 * w ^ (r - 3) * w ^ (r - 1) := by
        exact Nat.mul_le_mul_right (w ^ (r - 1))
          (Nat.mul_le_mul_left (d ^ 2)
            (pow_le_pow_left' (by omega : d ≤ w) (r - 3)))
      _ = d ^ 2 * w ^ (2 * r - 4) := by
        calc
          d ^ 2 * w ^ (r - 3) * w ^ (r - 1) =
              d ^ 2 * (w ^ (r - 3) * w ^ (r - 1)) := by ac_rfl
          _ = d ^ 2 * w ^ ((r - 3) + (r - 1)) := by rw [← pow_add]
          _ = d ^ 2 * w ^ (2 * r - 4) := by rw [hExp₂]
  have hAllScaled : w ^ (r - 1) * bᵣ ≤
      3 * r ^ r * (d ^ 2 * w ^ (2 * r - 4)) := by
    calc
      w ^ (r - 1) * bᵣ ≤
          w ^ (r - 1) * (3 * r ^ r * d ^ (r - 1)) :=
        Nat.mul_le_mul_left _ hAllWeak
      _ = 3 * r ^ r * (d ^ (r - 1) * w ^ (r - 1)) := by ac_rfl
      _ ≤ 3 * r ^ r * (d ^ 2 * w ^ (2 * r - 4)) :=
        Nat.mul_le_mul_left _ hDpow
  have hSum : w ^ (r - 1) * (J + bᵣ) ≤
      d ^ 2 * w ^ (2 * r - 4) +
        3 * r ^ r * (d ^ 2 * w ^ (2 * r - 4)) := by
    rw [Nat.mul_add]
    exact Nat.add_le_add hJScaled hAllScaled
  have hCoeff : d ^ 2 * w ^ (2 * r - 4) +
      3 * r ^ r * (d ^ 2 * w ^ (2 * r - 4)) ≤
      (K ^ 2 * (1 + 3 * r ^ r)) * q ^ 2 := by
    calc
      d ^ 2 * w ^ (2 * r - 4) +
          3 * r ^ r * (d ^ 2 * w ^ (2 * r - 4)) =
          (1 + 3 * r ^ r) * (d ^ 2 * w ^ (2 * r - 4)) := by ring
      _ ≤ (1 + 3 * r ^ r) * (K ^ 2 * q ^ 2) :=
        Nat.mul_le_mul_left _ hSquare
      _ = (K ^ 2 * (1 + 3 * r ^ r)) * q ^ 2 := by ring
  change w ^ (r - 1) * (J + bᵣ) ≤
    (K ^ 2 * (1 + 3 * r ^ r)) * q ^ 2
  exact hSum.trans hCoeff

end JSP523
