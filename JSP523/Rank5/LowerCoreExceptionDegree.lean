import JSP523.Rank5.LowerCoreColoring

/-! # Ordered exceptional degrees from actual lower-core colors

The multilevel deletion tests ordered root partners and includes the
self-pair. Their total is paid by the parent degree and four copies of
the exceptional unordered support count.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

theorem lower_exception_degree_sum_le_supports
    (H : Family α) (V B : Edge α) (t : ℕ) (z : α) :
    (∑ P ∈ actualCoreLink H V B 2,
      actualBadPartnerDegree H V B 2
        (fun _ R T => ¬ ActualStrongPartner H V R T 2 3 t z) P) ≤
      (actualCoreLink H V B 2).card + 4 * (lowerExceptionalSupports H V B t z).card := by
  classical
  let S := actualCoreLink H V B 2
  let X := lowerExceptionalSupports H V B t z
  let D := (S ×ˢ S).filter fun p => ¬ ActualStrongPartner H V p.1 p.2 2 3 t z
  have hCover : D ⊆ (S.image fun P => (P,P)) ∪ X.biUnion (fun e => e ×ˢ e) := by
    intro p hp
    have hParts := Finset.mem_filter.mp hp
    have hPair := Finset.mem_product.mp hParts.1
    by_cases hEq : p.1 = p.2
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨p.1,hPair.1,by ext <;> simp [hEq]⟩)
    · have hX : ({p.1,p.2} : Finset (Edge α)) ∈ X := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair hEq⟩, ?_⟩
        · exact Finset.insert_subset_iff.mpr ⟨hPair.1,Finset.singleton_subset_iff.mpr hPair.2⟩
        · intro hStrong
          exact hParts.2 (hStrong p.1 (by simp) p.2 (by simp) hEq)
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨{p.1,p.2},hX,Finset.mem_product.mpr ⟨by simp,by simp⟩⟩)
  have hCells : ∀ e ∈ X, (e ×ˢ e).card ≤ 4 := by
    intro e he
    have hEc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
    simp only [Finset.card_product, hEc]
    omega
  have hCount : (∑ P ∈ S,
      actualBadPartnerDegree H V B 2
        (fun _ R T => ¬ ActualStrongPartner H V R T 2 3 t z) P) = D.card := by
    simp only [actualBadPartnerDegree, D, S, Finset.card_eq_sum_ones,
      Finset.sum_filter, Finset.sum_product]
  change (∑ P ∈ S, actualBadPartnerDegree H V B 2
    (fun _ R T => ¬ ActualStrongPartner H V R T 2 3 t z) P) ≤ S.card + 4 * X.card
  rw [hCount]
  have hUnion := Finset.card_union_le (S.image fun P => (P,P))
    (X.biUnion fun e => e ×ˢ e)
  have hDiag := Finset.card_image_le (s := S) (f := fun P => (P,P))
  have hOff := Finset.card_biUnion_le_card_mul X (fun e => e ×ˢ e) 4 hCells
  have hSub := Finset.card_le_card hCover
  nlinarith

/-- The actual three-color majority center controls the full ordered
    exception-degree sum used to delete parent edges. -/
theorem exists_lower_core_label_exception_degree_bound
    (H : Family α) (V B : Edge α) (t : ℕ)
    (hBc : B.card = 3) (hDegree : 8 ≤ (actualCoreLink H V B 2).card) :
    ∃ z ∈ B,
      ((∑ P ∈ actualCoreLink H V B 2,
        actualBadPartnerDegree H V B 2
          (fun _ R T => ¬ ActualStrongPartner H V R T 2 3 t z) P) : ℝ) ≤
      ((actualCoreLink H V B 2).card : ℝ) + 3200 *
        ((uncoloredEdgeSupports (actualCoreLink H V B 2)
          (lowerCoreSupportColor H V B t)).card +
        (bicoloredTriangleSupports (actualCoreLink H V B 2)
          (lowerCoreSupportColor H V B t)).card /
            ((actualCoreLink H V B 2).card : ℝ)) := by
  obtain ⟨z,hz,hBound⟩ := exists_lower_core_majority_label H V B t hBc hDegree
  refine ⟨z,hz,?_⟩
  have hNat := lower_exception_degree_sum_le_supports H V B t z
  have hReal :
      ((∑ P ∈ actualCoreLink H V B 2,
        actualBadPartnerDegree H V B 2
          (fun _ R T => ¬ ActualStrongPartner H V R T 2 3 t z) P) : ℝ) ≤
      ((actualCoreLink H V B 2).card : ℝ) +
        4 * ((lowerExceptionalSupports H V B t z).card : ℝ) := by exact_mod_cast hNat
  linarith

end JSP523.Rank5
