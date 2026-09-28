import JSP523.Rank5.RegularizationFinite
import JSP523.Rank5.RegularizationNaturalScale
import JSP523.Rank5.FarStarTail

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

/-- The weighted finite-round ledger also gives a directly additive loss
bound once the natural target has reached the nontrivial range. -/
theorem natural_scale_finite_regularization_additive_loss
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
      H.card ≤ K.card + discreteRoundLayerBudget n r R +
        2 * (n.choose 2 * ((r - 1) *
          (discreteRoundRoot R * n ^ (r - 3)))) /
            (discreteRoundTarget R - 1) := by
  obtain ⟨K, hKH, hAdmK, hUniformK, hCapsK, hWeighted⟩ :=
    natural_scale_finite_regularization H hr hn hR23 hLarge hAdm hUniform hCaps
  have hRootLarge : 16 * (36 * r) ^ 3 ≤ discreteRoundRoot R :=
    (natural_root_rounding R r (by omega) hLarge).2.2.2
  have hBase : 1 ≤ 36 * r := by omega
  have hCube : 1 ≤ (36 * r) ^ 3 :=
    Nat.one_le_pow _ _ hBase
  have hThreshold : 2 ≤ 16 * (36 * r) ^ 3 := by nlinarith
  have hRpos : 1 ≤ R := by
    have hRootPos : 0 < discreteRoundRoot R := by omega
    by_contra h
    have hRzero : R = 0 := by omega
    simp [hRzero, discreteRoundRoot] at hRootPos
  have hTarget : 2 ≤ discreteRoundTarget R := by
    have hRT := discrete_round_root_le_target R hRpos
    omega
  let c := discreteRoundTarget R - 1
  let d := H.card - K.card
  let b := discreteRoundLayerBudget n r R
  let e := 2 * (n.choose 2 * ((r - 1) *
    (discreteRoundRoot R * n ^ (r - 3))))
  have hc : 1 ≤ c := by dsimp [c]; omega
  have hBasic : d ≤ b + e / c := by
    by_contra h
    have hStrict : b + e / c + 1 ≤ d := by omega
    have hMult := Nat.mul_le_mul_left c hStrict
    change c * d ≤ c * b + e at hWeighted
    have hRem : e % c < c := Nat.mod_lt e (by omega)
    have hDecomp := Nat.mod_add_div e c
    nlinarith [hMult, hRem, hDecomp]
  have hCard := Finset.card_le_card hKH
  dsimp [c, d, b, e] at hBasic
  refine ⟨K, hKH, hAdmK, hUniformK, hCapsK, ?_⟩
  omega

/-- The exact integer scale after a specified number of natural rounds. -/
def discreteRoundIterate (R : ℕ) : ℕ → ℕ
  | 0 => R
  | t + 1 => discreteRoundTarget (discreteRoundIterate R t)

/-- A coarse additive ledger for one natural round. -/
def discreteRoundAdditiveLoss (n r R : ℕ) : ℕ :=
  discreteRoundLayerBudget n r R +
    2 * (n.choose 2 * ((r - 1) *
      (discreteRoundRoot R * n ^ (r - 3)))) /
        (discreteRoundTarget R - 1)

theorem discrete_round_target_le_self (R : ℕ) :
    discreteRoundTarget R ≤ R := by
  by_cases hR : R = 0
  · simp [hR, discreteRoundTarget]
  · have hRpos : 1 ≤ R := by omega
    have hPow : (discreteRoundTarget R) ^ 4 ≤ R ^ 3 :=
      Nat.pow_nthRoot_le (Or.inl (by norm_num))
    have hRpow : R ^ 3 ≤ R ^ 4 := by
      calc
        R ^ 3 = R ^ 3 * 1 := by simp
        _ ≤ R ^ 3 * R := Nat.mul_le_mul_left _ hRpos
        _ = R ^ 4 := by ring
    by_contra h
    have hlt : R < discreteRoundTarget R := by omega
    have hltPow := Nat.pow_lt_pow_left hlt (by norm_num : 4 ≠ 0)
    omega

/-- The target scale beats the intermediate root by every fixed integer
factor once `R` exceeds the eighth power of that factor. -/
theorem discrete_round_root_ratio_bound (R m : ℕ)
    (hmR : m ^ 8 ≤ R) :
    m * discreteRoundRoot R ≤ discreteRoundTarget R := by
  have hRoot : (discreteRoundRoot R) ^ 8 ≤ R ^ 5 :=
    Nat.pow_nthRoot_le (Or.inl (by norm_num))
  have hProduct := Nat.mul_le_mul hmR hRoot
  have hEighth : (m * discreteRoundRoot R) ^ 8 ≤ (R ^ 3) ^ 2 := by
    calc
      (m * discreteRoundRoot R) ^ 8 =
          m ^ 8 * (discreteRoundRoot R) ^ 8 := by ring
      _ ≤ R * R ^ 5 := hProduct
      _ = (R ^ 3) ^ 2 := by ring
  have hFourth : (m * discreteRoundRoot R) ^ 4 ≤ R ^ 3 := by
    by_contra h
    have hlt : R ^ 3 < (m * discreteRoundRoot R) ^ 4 := by omega
    have hltSq := Nat.pow_lt_pow_left hlt (by norm_num : 2 ≠ 0)
    nlinarith [hEighth]
  exact (Nat.le_nthRoot_iff (by norm_num : 4 ≠ 0)).2 hFourth

/-- The square of the intermediate root eventually beats `R` by every
fixed factor, up to a harmless factor four from flooring. -/
theorem discrete_round_root_square_ratio_bound (R m : ℕ)
    (hR : 1 ≤ R) (hmR : m ^ 4 ≤ R) :
    m * R ≤ 4 * (discreteRoundRoot R) ^ 2 := by
  let T := discreteRoundRoot R
  have hTpos : 1 ≤ T := by
    dsimp [T, discreteRoundRoot]
    apply (Nat.le_nthRoot_iff (by norm_num : 8 ≠ 0)).2
    simpa using (Nat.one_le_pow 5 R hR)
  have hRootHi : R ^ 5 < (T + 1) ^ 8 :=
    Nat.lt_pow_nthRoot_add_one (by norm_num : 8 ≠ 0) _
  have hFourth : (m * R) ^ 4 ≤ R ^ 5 := by
    calc
      (m * R) ^ 4 = m ^ 4 * R ^ 4 := by ring
      _ ≤ R * R ^ 4 := Nat.mul_le_mul_right _ hmR
      _ = R ^ 5 := by ring
  have hSquare : m * R ≤ (T + 1) ^ 2 := by
    by_contra h
    have hlt : (T + 1) ^ 2 < m * R := by omega
    have hltPow := Nat.pow_lt_pow_left hlt (by norm_num : 4 ≠ 0)
    have hPower : ((T + 1) ^ 2) ^ 4 = (T + 1) ^ 8 := by ring
    rw [hPower] at hltPow
    omega
  have hFloor : (T + 1) ^ 2 ≤ 4 * T ^ 2 := by
    nlinarith [hTpos]
  exact hSquare.trans hFloor

/-- An explicit arbitrary-factor saving for the facet part of one round's
additive ledger. It is the finite form of the `R^{-1/8}` saving. -/
theorem discrete_round_facet_quotient_bound
    (n r R m : ℕ) (hm : 1 ≤ m) (hmR : (2 * m) ^ 8 ≤ R) :
    m * (2 * (n.choose 2 * ((r - 1) *
      (discreteRoundRoot R * n ^ (r - 3)))) /
        (discreteRoundTarget R - 1)) ≤
      2 * (n.choose 2 * ((r - 1) * n ^ (r - 3))) := by
  let T := discreteRoundRoot R
  let c := discreteRoundTarget R - 1
  let A := 2 * (n.choose 2 * ((r - 1) * n ^ (r - 3)))
  let e := 2 * (n.choose 2 * ((r - 1) * (T * n ^ (r - 3))))
  have hRpos : 1 ≤ R := by
    have hm2 : 1 ≤ 2 * m := by omega
    have hPow : 1 ≤ (2 * m) ^ 8 := Nat.one_le_pow _ _ hm2
    omega
  have hTpos : 1 ≤ T := by
    dsimp [T, discreteRoundRoot]
    apply (Nat.le_nthRoot_iff (by norm_num : 8 ≠ 0)).2
    have hPow : 1 ≤ R ^ 5 := Nat.one_le_pow _ _ hRpos
    simpa using hPow
  have hRatio := discrete_round_root_ratio_bound R (2 * m) hmR
  have hSave : m * T ≤ c := by
    dsimp [T, c] at *
    have hProd : 1 ≤ m * discreteRoundRoot R := by nlinarith [hm, hTpos]
    have hRatio' : 2 * (m * discreteRoundRoot R) ≤
        discreteRoundTarget R := by
      calc
        _ = (2 * m) * discreteRoundRoot R := by ring
        _ ≤ _ := hRatio
    omega
  have hc : 0 < c := by
    have hProd : 0 < m * T := Nat.mul_pos (by omega) (by omega)
    omega
  have he : e = A * T := by dsimp [e, A]; ring
  have hBound : m * e ≤ c * A := by
    calc
      m * e = (m * T) * A := by rw [he]; ring
      _ ≤ c * A := Nat.mul_le_mul_right A hSave
  have hDiv : (e / c) * c ≤ e := Nat.div_mul_le_self e c
  have hScaled := Nat.mul_le_mul_left m hDiv
  have hCancel : m * (e / c) ≤ A := by
    have hScaled' : c * (m * (e / c)) ≤ c * A := by
      nlinarith [hScaled, hBound]
    exact Nat.le_of_mul_le_mul_left hScaled' hc
  simpa only [e, c, A, T] using hCancel

/-- For a fixed number of rounds, the entire facet quotient has an
arbitrarily small explicit coefficient once every current scale is large. -/
theorem discrete_round_facet_sum_bound
    (n r R steps m : ℕ) (hm : 1 ≤ m)
    (hLarge : ∀ i < steps,
      (2 * m) ^ 8 ≤ discreteRoundIterate R i) :
    m * (∑ i ∈ Finset.range steps,
      2 * (n.choose 2 * ((r - 1) *
        (discreteRoundRoot (discreteRoundIterate R i) * n ^ (r - 3)))) /
          (discreteRoundTarget (discreteRoundIterate R i) - 1)) ≤
      steps * (2 * (n.choose 2 * ((r - 1) * n ^ (r - 3)))) := by
  rw [Finset.mul_sum]
  calc
    (∑ i ∈ Finset.range steps,
      m * (2 * (n.choose 2 * ((r - 1) *
        (discreteRoundRoot (discreteRoundIterate R i) * n ^ (r - 3)))) /
          (discreteRoundTarget (discreteRoundIterate R i) - 1))) ≤
      ∑ _i ∈ Finset.range steps,
        2 * (n.choose 2 * ((r - 1) * n ^ (r - 3))) := by
          apply Finset.sum_le_sum
          intro i hi
          exact discrete_round_facet_quotient_bound n r
            (discreteRoundIterate R i) m hm
              (hLarge i (Finset.mem_range.mp hi))
    _ = steps * (2 * (n.choose 2 * ((r - 1) * n ^ (r - 3)))) := by simp

/-- The facet quotient in any fixed finite iteration has an explicit
arbitrarily small coefficient against the extremal star size. -/
theorem discrete_round_facet_sum_star_bound
    (n r R steps m : ℕ) (hr : 4 ≤ r)
    (hn : 2 * (r - 1) + 1 ≤ n) (hm : 1 ≤ m)
    (hLarge : ∀ i < steps,
      (2 * m) ^ 8 ≤ discreteRoundIterate R i) :
    m * (∑ i ∈ Finset.range steps,
      2 * (n.choose 2 * ((r - 1) *
        (discreteRoundRoot (discreteRoundIterate R i) * n ^ (r - 3)))) /
          (discreteRoundTarget (discreteRoundIterate R i) - 1)) ≤
      steps * (2 * (r - 1) *
        (2 ^ (r - 1) * (r - 1).factorial)) *
          (n - 1).choose (r - 1) := by
  have hFacet := discrete_round_facet_sum_bound n r R steps m hm hLarge
  have hChoose : n.choose 2 ≤ n ^ 2 := Nat.choose_le_pow n 2
  have hExp : 2 + (r - 3) = r - 1 := by omega
  have hPower : n ^ 2 * n ^ (r - 3) = n ^ (r - 1) := by
    rw [← pow_add, hExp]
  have hOne : 2 * (n.choose 2 * ((r - 1) * n ^ (r - 3))) ≤
      2 * (r - 1) * n ^ (r - 1) := by
    calc
      _ = 2 * (r - 1) * (n.choose 2 * n ^ (r - 3)) := by ring
      _ ≤ 2 * (r - 1) * (n ^ 2 * n ^ (r - 3)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hChoose)
      _ = 2 * (r - 1) * n ^ (r - 1) := by rw [hPower]
  have hStar := far_star_power_le_choose_multiple n (r - 1) hn
  calc
    _ ≤ steps * (2 * (n.choose 2 * ((r - 1) * n ^ (r - 3)))) := hFacet
    _ ≤ steps * (2 * (r - 1) * n ^ (r - 1)) :=
      Nat.mul_le_mul_left steps hOne
    _ ≤ steps * (2 * (r - 1) *
          (2 ^ (r - 1) * (r - 1).factorial)) *
          (n - 1).choose (r - 1) := by
      have hMul := Nat.mul_le_mul_left (steps * (2 * (r - 1))) hStar
      nlinarith [hMul]

theorem discrete_round_iterate_le_start (R t : ℕ) :
    discreteRoundIterate R t ≤ R := by
  induction t with
  | zero => simp [discreteRoundIterate]
  | succ t ih =>
      exact (discrete_round_target_le_self _).trans ih

/-- Iterate the actual finite regularization while retaining the total
deletion ledger. All later parent codegree caps come from the previous
round; the only remaining input is the explicit size threshold at each
chosen integer scale. -/
theorem natural_scale_finite_regularization_iterate
    {n r R : ℕ} (steps : ℕ) (H : Family (Fin n))
    (hr : 4 ≤ r) (hn : 1 ≤ n) (hR23 : R ^ 3 ≤ n ^ 2)
    (hLarge : ∀ i < steps,
      (16 * (36 * r) ^ 3) ^ 8 ≤
        (discreteRoundIterate R i) ^ 5)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hCaps : ∀ j, 1 ≤ j → j ≤ r - 1 →
      ∀ S : Edge (Fin n), S.card = j →
        (H.filter (fun E => S ⊆ E)).card ≤ R * n ^ (r - j - 1)) :
    ∃ K : Family (Fin n), K ⊆ H ∧ Admissible K ∧ Uniform r K ∧
      (∀ j, 1 ≤ j → j ≤ r - 1 →
        ∀ S : Edge (Fin n), S.card = j →
          (K.filter (fun E => S ⊆ E)).card ≤
            discreteRoundIterate R steps * n ^ (r - j - 1)) ∧
      H.card ≤ K.card +
        ∑ i ∈ Finset.range steps,
          discreteRoundAdditiveLoss n r (discreteRoundIterate R i) := by
  induction steps generalizing H with
  | zero =>
      refine ⟨H, Finset.Subset.rfl, hAdm, hUniform, ?_, ?_⟩
      · simpa only [discreteRoundIterate] using hCaps
      · simp
  | succ t ih =>
      have hLargeT : ∀ i < t,
          (16 * (36 * r) ^ 3) ^ 8 ≤
            (discreteRoundIterate R i) ^ 5 := by
        intro i hi
        exact hLarge i (by omega)
      obtain ⟨K, hKH, hAdmK, hUniformK, hCapsK, hLossK⟩ :=
        ih H hLargeT hAdm hUniform hCaps
      have hCurrent23 : (discreteRoundIterate R t) ^ 3 ≤ n ^ 2 :=
        (Nat.pow_le_pow_left (discrete_round_iterate_le_start R t) 3).trans hR23
      obtain ⟨K', hK'K, hAdmK', hUniformK', hCapsK', hRoundLoss⟩ :=
        natural_scale_finite_regularization_additive_loss K hr hn
          hCurrent23 (hLarge t (by omega)) hAdmK hUniformK hCapsK
      refine ⟨K', hK'K.trans hKH, hAdmK', hUniformK', ?_, ?_⟩
      · simpa only [discreteRoundIterate] using hCapsK'
      · rw [Finset.sum_range_succ]
        have hRoundLoss' : K.card ≤ K'.card +
            discreteRoundAdditiveLoss n r (discreteRoundIterate R t) := by
          simpa only [discreteRoundAdditiveLoss, Nat.add_assoc] using hRoundLoss
        omega

end JSP523.Rank5
