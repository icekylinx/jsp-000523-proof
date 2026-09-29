import JSP523.Rank5.LowerCoreExceptionDegree

/-! # Actual rank-five multilevel deletion with majority labels

The label and the deletion set are constructed from the parent family.
The remaining uncolored and bicolored totals are actual finite sets.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α] [Nonempty α]

noncomputable def lowerMajorityLabel
    (H : Family α) (V : Edge α) (t : ℕ) (B : Edge α) : α := by
  classical
  exact if h : B.card = 3 ∧ 8 ≤ (actualCoreLink H V B 2).card then
    Classical.choose (exists_lower_core_label_exception_degree_bound H V B t h.1 h.2)
  else Classical.choice inferInstance

theorem lower_majority_cleanup_core_budget
    (H : Family α) (V B : Edge α) (t u q : ℕ)
    (hBc : B.card = 3) (hu : 8 ≤ u) :
    (q : ℝ) * ((cleanupTails H V B 2 u q
      (fun A P Q => ¬ ActualStrongPartner H V P Q 2 3 t
        (lowerMajorityLabel H V t A))).card : ℝ) ≤
      (q : ℝ) * u + ((actualCoreLink H V B 2).card : ℝ) + 3200 *
        ((uncoloredEdgeSupports (actualCoreLink H V B 2)
          (lowerCoreSupportColor H V B t)).card +
        (bicoloredTriangleSupports (actualCoreLink H V B 2)
          (lowerCoreSupportColor H V B t)).card / (u : ℝ)) := by
  classical
  let bad := fun A P Q => ¬ ActualStrongPartner H V P Q 2 3 t (lowerMajorityLabel H V t A)
  have hupos : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  by_cases hLow : (actualCoreLink H V B 2).card < u
  · have hNat : q * (cleanupTails H V B 2 u q bad).card ≤ q * u := by
      simpa only [cleanupTails, dite_eq_left hLow] using
        Nat.mul_le_mul_left q hLow.le
    have hReal : (q : ℝ) * (cleanupTails H V B 2 u q bad).card ≤ (q : ℝ) * u := by
      exact_mod_cast hNat
    have hExtra : (0 : ℝ) ≤ ((actualCoreLink H V B 2).card : ℝ) + 3200 *
        ((uncoloredEdgeSupports (actualCoreLink H V B 2)
          (lowerCoreSupportColor H V B t)).card +
        (bicoloredTriangleSupports (actualCoreLink H V B 2)
          (lowerCoreSupportColor H V B t)).card / (u : ℝ)) := by positivity
    dsimp [bad] at hReal
    linarith
  · have hLarge : u ≤ (actualCoreLink H V B 2).card := by omega
    have hEight : 8 ≤ (actualCoreLink H V B 2).card := hu.trans hLarge
    have hChoice := (Classical.choose_spec
      (exists_lower_core_label_exception_degree_bound H V B t hBc hEight)).2
    have hChosen : lowerMajorityLabel H V t B =
        Classical.choose (exists_lower_core_label_exception_degree_bound H V B t hBc hEight) := by
      simp only [lowerMajorityLabel, dite_eq_left (And.intro hBc hEight)]
    rw [← hChosen] at hChoice
    have hNatural := high_fiber_sum_bound (actualCoreLink H V B 2)
      (fun P => actualBadPartnerDegree H V B 2 bad P) q
    have hNat : q * (cleanupTails H V B 2 u q bad).card ≤
        ∑ P ∈ actualCoreLink H V B 2, actualBadPartnerDegree H V B 2 bad P := by
      simpa only [cleanupTails, dite_eq_right hLow] using hNatural
    have hReal : (q : ℝ) * (cleanupTails H V B 2 u q bad).card ≤
        ((∑ P ∈ actualCoreLink H V B 2, actualBadPartnerDegree H V B 2 bad P) : ℝ) := by
      exact_mod_cast hNat
    have hDeg : (u : ℝ) ≤ (actualCoreLink H V B 2).card := by exact_mod_cast hLarge
    have hDiv := div_le_div_of_nonneg_left
      (Nat.cast_nonneg (bicoloredTriangleSupports (actualCoreLink H V B 2)
        (lowerCoreSupportColor H V B t)).card) hupos hDeg
    dsimp [bad] at hReal
    have hBadEq : (∑ P ∈ actualCoreLink H V B 2,
        actualBadPartnerDegree H V B 2
          (fun A R T => ¬ ActualStrongPartner H V R T 2 3 t (lowerMajorityLabel H V t A)) P) =
      ∑ P ∈ actualCoreLink H V B 2,
        actualBadPartnerDegree H V B 2
          (fun _ R T => ¬ ActualStrongPartner H V R T 2 3 t (lowerMajorityLabel H V t B)) P := by
      rfl
    have hBadEqReal := congrArg (fun n : ℕ => (n : ℝ)) hBadEq
    push_cast at hBadEqReal
    rw [hBadEqReal] at hReal
    have hqNon : (0 : ℝ) ≤ (q : ℝ) * u := by positivity
    linarith

/-- The actual majority-label deletion budget, with no assumed aggregate
    exception hypothesis. Its two color totals are the actual parent-link
    uncolored and bicolored support counts. -/
theorem lower_majority_multilevel_cleanup_budget
    (H : Family α) (V : Edge α) (t u q : ℕ)
    (hUniform : Uniform 5 H) (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hu : 8 ≤ u) :
    (q : ℝ) * ((multilevelDeletedEdges H V (V.powersetCard 3) 2 u q
      (fun B P Q => ¬ ActualStrongPartner H V P Q 2 3 t
        (lowerMajorityLabel H V t B))).card : ℝ) ≤
      (q : ℝ) * V.card.choose 3 * u + 10 * (H.card : ℝ) + 3200 *
        ((∑ B ∈ V.powersetCard 3,
          ((uncoloredEdgeSupports (actualCoreLink H V B 2)
            (lowerCoreSupportColor H V B t)).card : ℝ)) +
        (∑ B ∈ V.powersetCard 3,
          ((bicoloredTriangleSupports (actualCoreLink H V B 2)
            (lowerCoreSupportColor H V B t)).card : ℝ)) / (u : ℝ)) := by
  classical
  let bad := fun B P Q => ¬ ActualStrongPartner H V P Q 2 3 t (lowerMajorityLabel H V t B)
  let tails := fun B => cleanupTails H V B 2 u q bad
  have hCard : (multilevelDeletedEdges H V (V.powersetCard 3) 2 u q bad).card ≤
      ∑ B ∈ V.powersetCard 3, (tails B).card := by
    calc
      _ ≤ ∑ B ∈ V.powersetCard 3, ((tails B).image fun P => B ∪ P).card := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum (fun B hB => Finset.card_image_le)
  have hReal : ((multilevelDeletedEdges H V (V.powersetCard 3) 2 u q bad).card : ℝ) ≤
      ∑ B ∈ V.powersetCard 3, ((tails B).card : ℝ) := by exact_mod_cast hCard
  have hScaled := mul_le_mul_of_nonneg_left hReal (Nat.cast_nonneg q)
  rw [Finset.mul_sum] at hScaled
  have hSum := Finset.sum_le_sum (fun B (hB : B ∈ V.powersetCard 3) =>
    lower_majority_cleanup_core_budget H V B t u q (Finset.mem_powersetCard.mp hB).2 hu)
  have hDegreesNat := total_three_core_parent_pair_links_le_ten_edges H V hUniform hAmbient
  have hDegrees : (∑ B ∈ V.powersetCard 3, ((actualCoreLink H V B 2).card : ℝ)) ≤
      10 * (H.card : ℝ) := by
    simp only [actual_core_link_two_eq_parent_pair_link]
    exact_mod_cast hDegreesNat
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
    Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard] at hSum
  dsimp [tails,bad] at hScaled
  nlinarith [hScaled, hSum, hDegrees]

end JSP523.Rank5
