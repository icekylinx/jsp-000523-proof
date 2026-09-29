import JSP523.Rank5.ColorQuantitativeFixedPaletteDegree

/-! # Actual fixed-rank multilevel deletion with majority labels

The label and the deletion set are constructed from the parent family.
The remaining uncolored and bicolored totals are actual finite sets.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α] [Nonempty α]

omit [Nonempty α] in
theorem total_fixed_palette_core_degrees_eq_edges
    (H : Family α) (V : Edge α) (r k : ℕ)
    (hUniform : Uniform r H)
    (hAmbient : ∀ E ∈ H, E ⊆ V) :
    (∑ B ∈ V.powersetCard k,
        (H.filter fun E => B ⊆ E).card) = r.choose k * H.card := by
  classical
  calc
    (∑ B ∈ V.powersetCard k,
        (H.filter fun E => B ⊆ E).card) =
        ∑ B ∈ V.powersetCard k,
          ∑ E ∈ H, if B ⊆ E then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro B hB
      exact Finset.card_filter (fun E : Edge α => B ⊆ E) H
    _ = ∑ E ∈ H, ∑ B ∈ V.powersetCard k,
          if B ⊆ E then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ E ∈ H, (E.powersetCard k).card := by
      apply Finset.sum_congr rfl
      intro E hE
      calc
        (∑ B ∈ V.powersetCard k,
            if B ⊆ E then (1 : ℕ) else 0) =
            ((V.powersetCard k).filter fun B => B ⊆ E).card :=
          (Finset.card_filter (fun B : Edge α => B ⊆ E) _).symm
        _ = (E.powersetCard k).card := by
          congr 1
          ext B
          simp only [Finset.mem_filter, Finset.mem_powersetCard]
          constructor
          · rintro ⟨⟨_, hCard⟩, hBE⟩
            exact ⟨hBE, hCard⟩
          · rintro ⟨hBE, hCard⟩
            exact ⟨⟨hBE.trans (hAmbient E hE), hCard⟩, hBE⟩
    _ = ∑ _E ∈ H, r.choose k := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [Finset.card_powersetCard, hUniform hE]

    _ = r.choose k * H.card := by simp [mul_comm]

omit [Nonempty α] in
theorem total_fixed_palette_core_links_le_edges
    (H : Family α) (V : Edge α) (r s k : ℕ)
    (hUniform : Uniform r H) (hAmbient : ∀ E ∈ H, E ⊆ V) :
    (∑ B ∈ V.powersetCard k, (actualCoreLink H V B s).card) ≤
      r.choose k * H.card := by
  classical
  calc
    _ ≤ ∑ B ∈ V.powersetCard k, (H.filter fun E => B ⊆ E).card := by
      apply Finset.sum_le_sum
      intro B _
      apply Finset.card_le_card_of_injOn (fun P => B ∪ P)
      · intro P hP
        exact Finset.mem_filter.mpr ⟨(mem_actual_core_link.mp hP).2.2.2, Finset.subset_union_left⟩
      · intro P hP Q hQ hEq
        have hp := (mem_actual_core_link.mp hP).2.2.1
        have hq := (mem_actual_core_link.mp hQ).2.2.1
        have h := congrArg (fun E : Edge α => E \ B) hEq
        simpa only [Finset.union_sdiff_cancel_left hp.symm,
          Finset.union_sdiff_cancel_left hq.symm] using h
    _ = _ := total_fixed_palette_core_degrees_eq_edges H V r k hUniform hAmbient

noncomputable def fixedPaletteMajorityLabel
    (H : Family α) (V : Edge α) (s k t : ℕ) (B : Edge α) : α := by
  classical
  exact if h : 2 ≤ k ∧ B.card = k ∧ 2 * fixedPaletteSampleSize k ≤ (actualCoreLink H V B s).card then
    Classical.choose (exists_fixed_palette_core_label_exception_degree_bound H V B s k t h.1 h.2.1 h.2.2)
  else Classical.choice inferInstance

theorem fixed_palette_majority_cleanup_core_budget
    (H : Family α) (V B : Edge α) (s k t u q : ℕ)
    (hk : 2 ≤ k) (hBc : B.card = k) (hu : 2 * fixedPaletteSampleSize k ≤ u) :
    (q : ℝ) * ((cleanupTails H V B s u q
      (fun A P Q => ¬ ActualStrongPartner H V P Q s k t
        (fixedPaletteMajorityLabel H V s k t A))).card : ℝ) ≤
      (q : ℝ) * u + ((actualCoreLink H V B s).card : ℝ) + (4 * (fixedPaletteMajorityConstant (fixedPaletteSampleSize k) : ℝ)) *
        ((uncoloredEdgeSupports (actualCoreLink H V B s)
          (fixedPaletteCoreSupportColor H V B s k t)).card +
        (bicoloredTriangleSupports (actualCoreLink H V B s)
          (fixedPaletteCoreSupportColor H V B s k t)).card / (u : ℝ)) := by
  classical
  let bad := fun A P Q => ¬ ActualStrongPartner H V P Q s k t (fixedPaletteMajorityLabel H V s k t A)
  have hSample : 4 ≤ fixedPaletteSampleSize k := le_max_left _ _
  have hupos : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  by_cases hLow : (actualCoreLink H V B s).card < u
  · have hNat : q * (cleanupTails H V B s u q bad).card ≤ q * u := by
      simpa only [cleanupTails, dite_eq_left hLow] using
        Nat.mul_le_mul_left q hLow.le
    have hReal : (q : ℝ) * (cleanupTails H V B s u q bad).card ≤ (q : ℝ) * u := by
      exact_mod_cast hNat
    have hExtra : (0 : ℝ) ≤ ((actualCoreLink H V B s).card : ℝ) + (4 * (fixedPaletteMajorityConstant (fixedPaletteSampleSize k) : ℝ)) *
        ((uncoloredEdgeSupports (actualCoreLink H V B s)
          (fixedPaletteCoreSupportColor H V B s k t)).card +
        (bicoloredTriangleSupports (actualCoreLink H V B s)
          (fixedPaletteCoreSupportColor H V B s k t)).card / (u : ℝ)) := by positivity
    dsimp [bad] at hReal
    nlinarith [Nat.cast_nonneg (α := ℝ) (fixedPaletteMajorityConstant (fixedPaletteSampleSize k))]
  · have hLarge : u ≤ (actualCoreLink H V B s).card := by omega
    have hEight : 2 * fixedPaletteSampleSize k ≤ (actualCoreLink H V B s).card := hu.trans hLarge
    have hChoice := (Classical.choose_spec
      (exists_fixed_palette_core_label_exception_degree_bound H V B s k t hk hBc hEight)).2
    have hChosen : fixedPaletteMajorityLabel H V s k t B =
        Classical.choose (exists_fixed_palette_core_label_exception_degree_bound H V B s k t hk hBc hEight) := by
      simp only [fixedPaletteMajorityLabel, dite_eq_left (And.intro hk (And.intro hBc hEight))]
    rw [← hChosen] at hChoice
    have hNatural := high_fiber_sum_bound (actualCoreLink H V B s)
      (fun P => actualBadPartnerDegree H V B s bad P) q
    have hNat : q * (cleanupTails H V B s u q bad).card ≤
        ∑ P ∈ actualCoreLink H V B s, actualBadPartnerDegree H V B s bad P := by
      simpa only [cleanupTails, dite_eq_right hLow] using hNatural
    have hReal : (q : ℝ) * (cleanupTails H V B s u q bad).card ≤
        ((∑ P ∈ actualCoreLink H V B s, actualBadPartnerDegree H V B s bad P) : ℝ) := by
      exact_mod_cast hNat
    have hDeg : (u : ℝ) ≤ (actualCoreLink H V B s).card := by exact_mod_cast hLarge
    have hDiv := div_le_div_of_nonneg_left
      (Nat.cast_nonneg (bicoloredTriangleSupports (actualCoreLink H V B s)
        (fixedPaletteCoreSupportColor H V B s k t)).card) hupos hDeg
    dsimp [bad] at hReal
    have hBadEq : (∑ P ∈ actualCoreLink H V B s,
        actualBadPartnerDegree H V B s
          (fun A R T => ¬ ActualStrongPartner H V R T s k t (fixedPaletteMajorityLabel H V s k t A)) P) =
      ∑ P ∈ actualCoreLink H V B s,
        actualBadPartnerDegree H V B s
          (fun _ R T => ¬ ActualStrongPartner H V R T s k t (fixedPaletteMajorityLabel H V s k t B)) P := by
      rfl
    have hBadEqReal := congrArg (fun n : ℕ => (n : ℝ)) hBadEq
    push_cast at hBadEqReal
    rw [hBadEqReal] at hReal
    have hqNon : (0 : ℝ) ≤ (q : ℝ) * u := by positivity
    nlinarith [Nat.cast_nonneg (α := ℝ) (fixedPaletteMajorityConstant (fixedPaletteSampleSize k))]

/-- The actual majority-label deletion budget, with no assumed aggregate
    exception hypothesis. Its two color totals are the actual parent-link
    uncolored and bicolored support counts. -/
theorem fixed_palette_majority_multilevel_cleanup_budget
    (H : Family α) (V : Edge α) (r s k t u q : ℕ)
    (hk : 2 ≤ k) (hUniform : Uniform r H) (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hu : 2 * fixedPaletteSampleSize k ≤ u) :
    (q : ℝ) * ((multilevelDeletedEdges H V (V.powersetCard k) s u q
      (fun B P Q => ¬ ActualStrongPartner H V P Q s k t
        (fixedPaletteMajorityLabel H V s k t B))).card : ℝ) ≤
      (q : ℝ) * V.card.choose k * u + (r.choose k : ℝ) * (H.card : ℝ) + (4 * (fixedPaletteMajorityConstant (fixedPaletteSampleSize k) : ℝ)) *
        ((∑ B ∈ V.powersetCard k,
          ((uncoloredEdgeSupports (actualCoreLink H V B s)
            (fixedPaletteCoreSupportColor H V B s k t)).card : ℝ)) +
        (∑ B ∈ V.powersetCard k,
          ((bicoloredTriangleSupports (actualCoreLink H V B s)
            (fixedPaletteCoreSupportColor H V B s k t)).card : ℝ)) / (u : ℝ)) := by
  classical
  let bad := fun B P Q => ¬ ActualStrongPartner H V P Q s k t (fixedPaletteMajorityLabel H V s k t B)
  let tails := fun B => cleanupTails H V B s u q bad
  have hCard : (multilevelDeletedEdges H V (V.powersetCard k) s u q bad).card ≤
      ∑ B ∈ V.powersetCard k, (tails B).card := by
    calc
      _ ≤ ∑ B ∈ V.powersetCard k, ((tails B).image fun P => B ∪ P).card := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum (fun B hB => Finset.card_image_le)
  have hReal : ((multilevelDeletedEdges H V (V.powersetCard k) s u q bad).card : ℝ) ≤
      ∑ B ∈ V.powersetCard k, ((tails B).card : ℝ) := by exact_mod_cast hCard
  have hScaled := mul_le_mul_of_nonneg_left hReal (Nat.cast_nonneg q)
  rw [Finset.mul_sum] at hScaled
  have hSum := Finset.sum_le_sum (fun B (hB : B ∈ V.powersetCard k) =>
    fixed_palette_majority_cleanup_core_budget H V B s k t u q hk (Finset.mem_powersetCard.mp hB).2 hu)
  have hDegreesNat := total_fixed_palette_core_links_le_edges H V r s k hUniform hAmbient
  have hDegrees : (∑ B ∈ V.powersetCard k, ((actualCoreLink H V B s).card : ℝ)) ≤
      (r.choose k : ℝ) * (H.card : ℝ) := by exact_mod_cast hDegreesNat
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
    Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard] at hSum
  dsimp [tails,bad] at hScaled
  rw [← Finset.mul_sum] at hScaled
  nlinarith only [hScaled, hSum, hDegrees]

end JSP523.Rank5
