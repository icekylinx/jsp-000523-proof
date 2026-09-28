import JSP523.Counting.LocalLinearity
import Mathlib.Tactic.Ring

/-!
# From a small missing-star budget to exact local linearity

The final arithmetic step of Theorem IV.2.1 compares each overlap
threshold (IV.2.2) with `w - 2r + 2`.  This module records that finite
binomial comparison and applies the existing trade and incidence theorems.
The quantitative contraction (IV.2.10) that forces such a small budget is
a separate geometric obligation.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

private theorem succ_le_choose_add (a j : ℕ) (hj : 1 ≤ j) :
    a + 1 ≤ (a + j).choose j := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hRec : (a + 1 + j).choose j =
        (a + j).choose (j - 1) + (a + j).choose j := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.choose_succ_left (a + j) j hj
    have hPos : 0 < (a + j).choose (j - 1) :=
      Nat.choose_pos (by omega)
    rw [hRec]
    omega

/-- Every overlap threshold for a difference of size `1,…,r-2` is at
least `w - 2r + 2` once `w ≥ 2r`. This is the binomial comparison used at
the end of §IV.2.3. -/
theorem overlap_threshold_ge_local_gap
    (w r k : ℕ) (hr : 3 ≤ r) (hw : 2 * r ≤ w)
    (_hk₁ : 1 ≤ k) (hk₂ : k ≤ r - 2) :
    w - (2 * r - 2) ≤
      (w - r - k).choose (r - 1 - k) := by
  let a := w - (2 * r - 2) - 1
  let j := r - 1 - k
  have hj : 1 ≤ j := by dsimp [j]; omega
  have ha : a + 1 = w - (2 * r - 2) := by dsimp [a]; omega
  have hn : a + j = w - r - k := by dsimp [a, j]; omega
  simpa only [← ha, ← hn, j] using succ_le_choose_add a j hj

/-- The small-gap numerical condition excludes every two-vertex overlap
in the outside family. -/
theorem outside_linear_of_missing_below_local_gap
    {H : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hU : Uniform r H)
    (hvW : v ∉ W) (hr : 3 ≤ r)
    (hw : 2 * r ≤ W.card)
    (hSmall : (missingStarFacets H W v r).card <
      W.card - (2 * r - 2)) :
    LinearFamily (outsideFamily H W) := by
  let B := outsideFamily H W
  have hBH : B ⊆ H := Finset.filter_subset _ _
  have hBU : Uniform r B := by
    intro E hE
    exact hU (hBH hE)
  have hBW : ∀ E ∈ B, E ⊆ W := by
    intro E hE
    exact (Finset.mem_filter.mp hE).2
  apply outside_linear_of_small_missing hH hBH hBU hBW hvW
  intro k hk₁ hk₂
  exact hSmall.trans_le
    (overlap_threshold_ge_local_gap W.card r k hr hw hk₁ hk₂)

/-- The exact bound (IV.2.11) follows as soon as the missing-star budget
falls below the local gap. -/
theorem near_star_exact_of_missing_below_local_gap
    {H : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hU : Uniform r H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) (hr : 3 ≤ r)
    (hw : 2 * r ≤ W.card)
    (hSmall : (missingStarFacets H W v r).card <
      W.card - (2 * r - 2)) :
    H.card ≤ W.card.choose (r - 1) + W.card / r := by
  exact near_star_upper_of_linear_outside hH hU hSupport hvW hr
    (outside_linear_of_missing_below_local_gap hH hU
      hvW hr hw hSmall)

/-- The absorbed form of the contraction (IV.2.10) forces the missing
budget below the overlap gap when the ground set is sufficiently large.
The explicit lower bound on `w` is convenient rather than optimized. -/
theorem missing_below_local_gap_of_absorbed_contraction
    (r w q b : ℕ) (hr : 5 ≤ r)
    (hw : r * (r - 3) * (2 * r - 1) ≤ w)
    (hqb : q ≤ b)
    (hContract :
      2 * (r - 1) * b ≤
        (r + 1) * q + 2 * (r - 1) * (w / r)) :
    q < w - (2 * r - 2) := by
  have hr₁ : r - 1 + 1 = r := by omega
  have hr₃ : r - 3 + 3 = r := by omega
  have hCoeff : 2 * (r - 1) + 1 ≤ r * (r - 3) := by
    have hMul := Nat.mul_le_mul_left r hr
    nlinarith
  have hCoeffPos : 0 < r * (r - 3) := by omega
  have hGapQ : (r - 3) * q ≤ 2 * (r - 1) * (w / r) := by
    have hLeft := Nat.mul_le_mul_left (2 * (r - 1)) hqb
    nlinarith [hContract]
  have hFloor : r * (w / r) ≤ w := Nat.mul_div_le w r
  have hScaled : r * (r - 3) * q ≤ 2 * (r - 1) * w := by
    calc
      r * (r - 3) * q = r * ((r - 3) * q) := by ring
      _ ≤ r * (2 * (r - 1) * (w / r)) :=
        Nat.mul_le_mul_left r hGapQ
      _ = 2 * (r - 1) * (r * (w / r)) := by ring
      _ ≤ 2 * (r - 1) * w :=
        Nat.mul_le_mul_left (2 * (r - 1)) hFloor
  have hMargin :
      2 * (r - 1) * w + r * (r - 3) * (2 * r - 1) ≤
        r * (r - 3) * w := by
    have hMul := Nat.mul_le_mul_right w hCoeff
    nlinarith [hw]
  have hScaledGap :
      r * (r - 3) * (q + (2 * r - 1)) ≤
        r * (r - 3) * w := by
    calc
      r * (r - 3) * (q + (2 * r - 1)) =
          r * (r - 3) * q + r * (r - 3) * (2 * r - 1) := by ring
      _ ≤ 2 * (r - 1) * w + r * (r - 3) * (2 * r - 1) :=
        Nat.add_le_add_right hScaled _
      _ ≤ r * (r - 3) * w := hMargin
  have hGap : q + (2 * r - 1) ≤ w :=
    Nat.le_of_mul_le_mul_left hScaledGap hCoeffPos
  omega

/-- Finite exactness from the absorbed contraction and the genuine
near-star hypotheses. This is the numerical close in §IV.2.3, with the
derivation of the contraction from (IV.2.5)–(IV.2.9) left explicit. -/
theorem near_star_exact_of_absorbed_contraction
    {H : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hU : Uniform r H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) (hr : 5 ≤ r)
    (hw : r * (r - 3) * (2 * r - 1) ≤ W.card)
    (hqb : (missingStarFacets H W v r).card ≤
      (outsideFamily H W).card)
    (hContract :
      2 * (r - 1) * (outsideFamily H W).card ≤
        (r + 1) * (missingStarFacets H W v r).card +
          2 * (r - 1) * (W.card / r)) :
    H.card ≤ W.card.choose (r - 1) + W.card / r := by
  have hSmall := missing_below_local_gap_of_absorbed_contraction
    r W.card (missingStarFacets H W v r).card
    (outsideFamily H W).card hr hw hqb hContract
  have hLarge : 2 * r ≤ W.card := by
    have hr₃ : r - 3 + 3 = r := by omega
    have hCoeff : 2 * r ≤ r * (r - 3) := by
      have hMul := Nat.mul_le_mul_left r hr
      nlinarith
    have hFactor : 1 ≤ 2 * r - 1 := by omega
    have hMul := Nat.mul_le_mul_left (r * (r - 3)) hFactor
    calc
      2 * r ≤ r * (r - 3) := hCoeff
      _ ≤ r * (r - 3) * (2 * r - 1) := by simpa using hMul
      _ ≤ W.card := hw
  apply near_star_exact_of_missing_below_local_gap
    hH hU hSupport hvW (by omega) hLarge hSmall

/-- An integer-scaled version of the manuscript's real absorbed
contraction. It keeps the term `w/r` as `w` after clearing denominators,
so no floor correction is built into the hypothesis. -/
theorem missing_below_local_gap_of_scaled_contraction
    (r w q b : ℕ) (hr : 5 ≤ r)
    (hw : r * (r - 3) * (2 * r - 1) ≤ w)
    (hqb : q ≤ b)
    (hContract :
      2 * r * (r - 1) * b ≤
        r * (r + 1) * q + 2 * (r - 1) * w) :
    q < w - (2 * r - 2) := by
  have hr₁ : r - 1 + 1 = r := by omega
  have hr₃ : r - 3 + 3 = r := by omega
  have hCoeff : 2 * (r - 1) + 1 ≤ r * (r - 3) := by
    have hMul := Nat.mul_le_mul_left r hr
    nlinarith
  have hCoeffPos : 0 < r * (r - 3) := by omega
  have hScaled : r * (r - 3) * q ≤ 2 * (r - 1) * w := by
    have hLeft := Nat.mul_le_mul_left (2 * r * (r - 1)) hqb
    have hSum : 2 * r * (r - 1) * q ≤
        r * (r + 1) * q + 2 * (r - 1) * w :=
      hLeft.trans hContract
    have hCoeffEq : 2 * r * (r - 1) =
        r * (r + 1) + r * (r - 3) := by
      calc
        2 * r * (r - 1) = r * (2 * (r - 1)) := by ring
        _ = r * ((r + 1) + (r - 3)) := by congr 1; omega
        _ = r * (r + 1) + r * (r - 3) := by ring
    rw [hCoeffEq, Nat.add_mul] at hSum
    omega
  have hMargin :
      2 * (r - 1) * w + r * (r - 3) * (2 * r - 1) ≤
        r * (r - 3) * w := by
    have hMul := Nat.mul_le_mul_right w hCoeff
    nlinarith [hw]
  have hScaledGap :
      r * (r - 3) * (q + (2 * r - 1)) ≤
        r * (r - 3) * w := by
    calc
      r * (r - 3) * (q + (2 * r - 1)) =
          r * (r - 3) * q + r * (r - 3) * (2 * r - 1) := by ring
      _ ≤ 2 * (r - 1) * w + r * (r - 3) * (2 * r - 1) :=
        Nat.add_le_add_right hScaled _
      _ ≤ r * (r - 3) * w := hMargin
  have hGap : q + (2 * r - 1) ≤ w :=
    Nat.le_of_mul_le_mul_left hScaledGap hCoeffPos
  omega

/-- The exact local theorem under the integer-scaled absorbed
contraction. This is the natural target for the finite counting chain,
after its error terms are bounded using `q ≤ δ_r w^(r-1)`. -/
theorem near_star_exact_of_scaled_contraction
    {H : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hU : Uniform r H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) (hr : 5 ≤ r)
    (hw : r * (r - 3) * (2 * r - 1) ≤ W.card)
    (hqb : (missingStarFacets H W v r).card ≤
      (outsideFamily H W).card)
    (hContract :
      2 * r * (r - 1) * (outsideFamily H W).card ≤
        r * (r + 1) * (missingStarFacets H W v r).card +
          2 * (r - 1) * W.card) :
    H.card ≤ W.card.choose (r - 1) + W.card / r := by
  have hSmall := missing_below_local_gap_of_scaled_contraction
    r W.card (missingStarFacets H W v r).card
    (outsideFamily H W).card hr hw hqb hContract
  have hLarge : 2 * r ≤ W.card := by
    have hr₃ : r - 3 + 3 = r := by omega
    have hCoeff : 2 * r ≤ r * (r - 3) := by
      have hMul := Nat.mul_le_mul_left r hr
      nlinarith
    have hFactor : 1 ≤ 2 * r - 1 := by omega
    have hMul := Nat.mul_le_mul_left (r * (r - 3)) hFactor
    calc
      2 * r ≤ r * (r - 3) := hCoeff
      _ ≤ r * (r - 3) * (2 * r - 1) := by simpa using hMul
      _ ≤ W.card := hw
  exact near_star_exact_of_missing_below_local_gap
    hH hU hSupport hvW (by omega) hLarge hSmall

/-- The arithmetic absorption step behind (IV.2.10). If the finite
counting chain has principal coefficient `2/(r-1)` and the remaining
error is at most half the available coefficient gap, it gives the
scaled contraction used above. -/
theorem scaled_contraction_of_error_bound
    (r w q b err : ℕ) (hr : 3 ≤ r)
    (hFinite : r * (r - 1) * b ≤
      2 * r * q + (r - 1) * w + err)
    (hError : 2 * err ≤ r * (r - 3) * q) :
    2 * r * (r - 1) * b ≤
      r * (r + 1) * q + 2 * (r - 1) * w := by
  have hCoeff : 4 * r + r * (r - 3) = r * (r + 1) := by
    calc
      4 * r + r * (r - 3) = r * (4 + (r - 3)) := by ring
      _ = r * (r + 1) := by congr 1; omega
  calc
    2 * r * (r - 1) * b = 2 * (r * (r - 1) * b) := by ring
    _ ≤ 2 * (2 * r * q + (r - 1) * w + err) :=
      Nat.mul_le_mul_left 2 hFinite
    _ = 4 * r * q + 2 * (r - 1) * w + 2 * err := by ring
    _ ≤ 4 * r * q + 2 * (r - 1) * w + r * (r - 3) * q :=
      Nat.add_le_add_left hError _
    _ = r * (r + 1) * q + 2 * (r - 1) * w := by
      calc
        4 * r * q + 2 * (r - 1) * w + r * (r - 3) * q =
            (4 * r + r * (r - 3)) * q + 2 * (r - 1) * w := by ring
        _ = _ := by rw [hCoeff]

end JSP523
