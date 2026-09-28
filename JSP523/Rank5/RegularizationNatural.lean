import JSP523.Rank5.RegularizationFinite
import JSP523.Rank5.RegularizationNaturalScale

set_option linter.style.haveILetI false

/-!
# A completely specified finite natural-scale round

All rounding, heavy-root gap, cover-size, shadow-radius, and collision
budget choices are made here.  The loss is an explicit integer expression.
This file does not assert that its expression has already been converted
into the uniform real-power/O-bound in Theorem IV.4.1.
-/

namespace JSP523.Rank5

open Finset
open scoped BigOperators
open JSP523.Rank5

/-- Floor of the manuscript's intermediate scale. -/
def discreteRoundRoot (R : ℕ) : ℕ := Nat.nthRoot 8 (R ^ 5)

/-- Floor of the target scale. -/
def discreteRoundTarget (R : ℕ) : ℕ := Nat.nthRoot 4 (R ^ 3)

def discreteRoundMultiplier (n R : ℕ) : ℕ := 2 * n / discreteRoundRoot R + 1

def discreteRoundCoverSize (n r R : ℕ) : ℕ :=
  ∑ s ∈ Finset.Icc 1 (r - 2), s * (discreteRoundMultiplier n R - 1)

/-- Integer radius for every star link in the original parent. -/
def discreteRoundRadius (n r R : ℕ) : ℕ :=
  Nat.nthRoot (r - 1) ((r - 1).factorial * (R * n ^ (r - 2))) + 1

def discreteRoundCollision (n r R : ℕ) : ℕ :=
  let h := discreteRoundCoverSize n r R
  n.choose (r - 2) * (h * (h - 1) *
    ((r - 1) * (r - 1) * (R * n ^ (r - 3)) +
      n * (n - 1) * (r - 2) * (R * n ^ (r - 4))))

/-- The actual removed-cover layer budget, with no real-number rounding. -/
def discreteRoundLayerBudget (n r R : ℕ) : ℕ :=
  Nat.nthRoot 2 (discreteRoundCollision n r R) + 1 +
    ((discreteRoundRadius n r R + (r - 1)) * n.choose (r - 2)) / (r - 1) +
      (discreteRoundCoverSize n r R).choose 2 * (R * n ^ (r - 3))

theorem discrete_round_root_le_target (R : ℕ) (hR : 1 ≤ R) :
    discreteRoundRoot R ≤ discreteRoundTarget R := by
  have hLo : (discreteRoundRoot R) ^ 8 ≤ R ^ 5 :=
    Nat.pow_nthRoot_le (Or.inl (by norm_num))
  have hRpow : R ^ 5 ≤ R ^ 6 := by
    calc
      R ^ 5 = R ^ 5 * 1 := by simp
      _ ≤ R ^ 5 * R := Nat.mul_le_mul_left _ hR
      _ = R ^ 6 := by ring
  have hPower : (discreteRoundRoot R) ^ 4 ≤ R ^ 3 := by
    by_contra h
    have hlt : R ^ 3 < (discreteRoundRoot R) ^ 4 := by omega
    have hltSq := Nat.pow_lt_pow_left hlt (by norm_num : 2 ≠ 0)
    have hleft : (R ^ 3) ^ 2 = R ^ 6 := by ring
    have hright : ((discreteRoundRoot R) ^ 4) ^ 2 = (discreteRoundRoot R) ^ 8 := by ring
    rw [hleft, hright] at hltSq
    omega
  exact (Nat.le_nthRoot_iff (by norm_num : 4 ≠ 0)).2 hPower

/-- Natural-scale finite regularization for every rank at least four.
Only admissibility, uniformity, the natural parent codegrees, and explicit
rank/scale restrictions are assumed. The family and all auxiliary choices
are constructed from the existing finite counting APIs. -/
theorem natural_scale_finite_regularization
    {n r R : ℕ} (H : Family (Fin n))
    (hr : 4 ≤ r) (hn : 1 ≤ n)
    (hR23 : R ^ 3 ≤ n ^ 2)
    (hLarge : (16 * (36 * r) ^ 3) ^ 8 ≤ R ^ 5)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hCaps : ∀ j, 1 ≤ j → j ≤ r - 1 →
      ∀ S : Edge (Fin n), S.card = j →
        (H.filter (fun E => S ⊆ E)).card ≤ R * n ^ (r - j - 1)) :
    ∃ K : Family (Fin n), K ⊆ H ∧ Admissible K ∧ Uniform r K ∧
      (∀ j, 1 ≤ j → j ≤ r - 1 →
        ∀ S : Edge (Fin n), S.card = j →
          (K.filter (fun E => S ⊆ E)).card ≤
            discreteRoundTarget R * n ^ (r - j - 1)) ∧
      (discreteRoundTarget R - 1) * (H.card - K.card) ≤
        (discreteRoundTarget R - 1) * discreteRoundLayerBudget n r R +
          2 * (n.choose 2 * ((r - 1) * (discreteRoundRoot R * n ^ (r - 3)))) := by
  classical
  letI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
  let V : Edge (Fin n) := Finset.univ
  let T := discreteRoundRoot R
  let a := discreteRoundMultiplier n R
  let h := discreteRoundCoverSize n r R
  let d : ℕ → ℕ := fun s => T * n ^ (r - s - 1)
  let D : ℕ → ℕ := fun s => R * n ^ (r - s - 2)
  let L := discreteRoundRadius n r R
  let b := Nat.nthRoot 2 (discreteRoundCollision n r R) + 1
  obtain ⟨hLo, hHi, hTR, hTLarge⟩ := natural_root_rounding R r (by omega) hLarge
  have hTpos : 0 < T := by
    have hrpos : 0 < r := by omega
    have hThreshold : 0 < 16 * (36 * r) ^ 3 := by positivity
    change 0 < Nat.nthRoot 8 (R ^ 5)
    omega
  have hRpos : 1 ≤ R := by
    change Nat.nthRoot 8 (R ^ 5) ≤ R at hTR
    change 0 < Nat.nthRoot 8 (R ^ 5) at hTpos
    omega
  have haLo : 2 * n ≤ a * T := by
    have hDiv := Nat.mod_add_div (2 * n) T
    have hMod := Nat.mod_lt (2 * n) hTpos
    dsimp [a, discreteRoundMultiplier]
    change 2 * n ≤ (2 * n / T + 1) * T
    rw [Nat.add_mul, Nat.one_mul]
    rw [Nat.mul_comm T (2 * n / T)] at hDiv
    omega
  have haHi : a * T ≤ 2 * n + T := by
    have hDiv := Nat.mod_add_div (2 * n) T
    dsimp [a, discreteRoundMultiplier]
    change (2 * n / T + 1) * T ≤ 2 * n + T
    rw [Nat.add_mul, Nat.one_mul]
    rw [Nat.mul_comm T (2 * n / T)] at hDiv
    omega
  have hOff : ∀ s, 1 ≤ s → s ≤ r - 2 →
      ∀ P ∈ V.powersetCard s, ∀ x : Fin n, x ∉ P →
        (H.filter (fun E => P ∪ {x} ⊆ E)).card ≤ D s := by
    intro s hs hsr P hP x hx
    have hPc := (Finset.mem_powersetCard.mp hP).2
    have hSize : (P ∪ {x}).card = s + 1 := by
      rw [Finset.union_singleton, Finset.card_insert_of_notMem hx, hPc]
    have hc := hCaps (s + 1) (by omega) (by omega) _ hSize
    have he : r - (s + 1) - 1 = r - s - 2 := by omega
    simpa only [he, D] using hc
  have hGap : ∀ s, 1 ≤ s → s ≤ r - 2 →
      (V.powersetCard (r - s)).card +
        a * a * ((r - s) * D s) < a * d s := by
    intro s hs hsr
    have hThresh : 16 * (36 * (r - s)) ^ 3 ≤ T := by
      have hm := Nat.mul_le_mul_left 16
        (Nat.pow_le_pow_left (Nat.mul_le_mul_left 36 (Nat.sub_le r s)) 3)
      exact hm.trans hTLarge
    have hg := heavy_root_gap_at_rounded_scale n (r - s) R T a (d s) (D s)
      (by omega) hn hR23 hLo hHi hTR haLo haHi hThresh (le_rfl) (le_rfl)
    simpa only [V, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, Nat.mul_assoc] using hg
  have hD₁ : ∀ z : Fin n,
      (H.filter (fun E => z ∈ E)).card ≤ R * n ^ (r - 2) := by
    intro z
    have hc := hCaps 1 (by omega) (by omega) ({z} : Edge (Fin n)) (by simp)
    have he : r - 1 - 1 = r - 2 := by omega
    simpa only [Finset.singleton_subset_iff, he] using hc
  have hD₂ : ∀ S : Edge (Fin n), S.card = 2 →
      (H.filter (fun E => S ⊆ E)).card ≤ R * n ^ (r - 3) := by
    intro S hS
    have he : r - 2 - 1 = r - 3 := by omega
    simpa only [he] using hCaps 2 (by omega) (by omega) S hS
  have hD₃ : ∀ S : Edge (Fin n), S.card = 3 →
      (H.filter (fun E => S ⊆ E)).card ≤ R * n ^ (r - 4) := by
    intro S hS
    have he : r - 3 - 1 = r - 4 := by omega
    simpa only [he] using hCaps 3 (by omega) (by omega) S hS
  have hRadius : (r - 1).factorial * (R * n ^ (r - 2)) ≤ L ^ (r - 1) :=
    Nat.le_of_lt (Nat.lt_pow_nthRoot_add_one (by omega : r - 1 ≠ 0) _)
  have hCollision : discreteRoundCollision n r R ≤ b ^ 2 :=
    Nat.le_of_lt (Nat.lt_pow_nthRoot_add_one (by norm_num : 2 ≠ 0) _)
  obtain ⟨K, hKH, hAdmK, hUniformK, hSmall, hFacet, hLoss⟩ :=
    regularization_explicit_finite_round H V r (discreteRoundTarget R) h
      (R * n ^ (r - 2)) (R * n ^ (r - 3)) (R * n ^ (r - 4)) L b
      d D (fun _ => a) hAdm hUniform (by intro E hE; exact Finset.subset_univ _)
      hr hOff hGap (le_rfl) hD₁ hD₂ hD₃ hRadius hCollision
  refine ⟨K, hKH, hAdmK, hUniformK, ?_, ?_⟩
  · intro j hj hjr S hS
    by_cases hLast : j = r - 1
    · have hScard : S.card = r - 1 := by omega
      have hSPow : S ∈ V.powersetCard (r - 1) :=
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hScard⟩
      subst j
      have he : r - (r - 1) - 1 = 0 := by omega
      simpa only [hScard, he, pow_zero, Nat.mul_one] using hFacet S hSPow
    · have hjSmall : j ≤ r - 2 := by omega
      have hSPow : S ∈ V.powersetCard j :=
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩
      exact (hSmall j hj hjSmall S hSPow).trans
        (Nat.mul_le_mul_right _ (discrete_round_root_le_target R hRpos))
  · have he : r - 2 - 1 = r - 3 := by omega
    simpa only [V, Finset.card_univ, Fintype.card_fin, d, he,
      discreteRoundLayerBudget, b, L, h, T] using hLoss

end JSP523.Rank5
