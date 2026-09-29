import JSP523.Rank5.ColorQuantitativeFixedPaletteCleanup
import JSP523.Rank5.InheritanceLowRetention

/-! # Actual fixed-rank lower uncolored-cell budget

Disjoint nonstrong pair roots have at most `t + 9 D₄` common triple cores.
This is the disjoint contribution to IV.7.3 with ordinary parent extended core
codegrees; overlapping roots are counted separately by OverlapPartnerBudget.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

theorem fixed_palette_nonstrong_cell_bound
    (H : Family α) (V P Q : Edge α) (s k t D₄ : ℕ)
    (hs : 1 ≤ s) (hk : 2 ≤ k) (hAdm : Admissible H)
    (hP : P ∈ V.powersetCard s) (hQ : Q ∈ V.powersetCard s)
    (hPQ : Disjoint P Q)
    (hNoStrong : ∀ z, ¬ ActualStrongPartner H V P Q s k t z)
    (hD₄ : ∀ S : Edge α, S.card = s + 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    (commonPrefixTails H V P Q k).card ≤ t + k * k * D₄ := by
  classical
  let cell := commonPrefixTails H V P Q k
  have hPc := (Finset.mem_powersetCard.mp hP).2
  have hQc := (Finset.mem_powersetCard.mp hQ).2
  have hPnon : P.Nonempty := Finset.card_pos.mp (by omega)
  have hQnon : Q.Nonempty := Finset.card_pos.mp (by omega)
  have hCellCap : ∀ S : Edge α, S.card = 2 →
      (cell.filter fun A => S ⊆ A).card ≤ D₄ := by
    intro S hSc
    by_cases hDisj : Disjoint P S
    · have hUnion : (P ∪ S).card = s + 2 := by
        rw [Finset.card_union_of_disjoint hDisj, hPc, hSc]
      exact (JSP523.common_prefix_tails_fiber_le_parent_degree
        (H := H) (W := V) (Y := P) (Z := Q) (S := S) (t := k)).trans (hD₄ _ hUnion)
    · have hEmpty : (cell.filter fun A => S ⊆ A) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro A hA
        have hParts := Finset.mem_filter.mp hA
        have hDisjA := (Finset.disjoint_union_right.mp
          (mem_common_prefix_tails.mp hParts.1).2.2.1).1.symm
        exact hDisj (hDisjA.mono_right hParts.2)
      simp [hEmpty]
  by_cases hSmall : cell.card < t
  · change cell.card ≤ _
    omega
  have hLarge : t ≤ cell.card := by omega
  have hNoUnique : ∀ z, ¬ UniqueCellCenter cell z := by
    intro z hz
    exact hNoStrong z ⟨hQ, hPQ, hLarge, hz⟩
  by_cases hEmpty : cell = ∅
  · change cell.card ≤ _
    simp [hEmpty]
  obtain ⟨A,hA⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  by_cases hNoCenter : NoGlobalCenter cell
  · have hBound := JSP523.intersecting_card_le_pair_cap
      (fun T hT => (mem_common_prefix_tails.mp hT).2.1)
      (JSP523.common_prefix_tails_intersecting hAdm hPnon hQnon hPQ (by omega : 1 ≤ k))
      hNoCenter hA (by omega) hCellCap
    change cell.card ≤ k * k * D₄ at hBound
    change cell.card ≤ _
    omega
  · have hCenter : ∃ z, ∀ A ∈ cell, z ∈ A := by
      by_contra h
      exact hNoCenter (by
        intro z
        by_contra hz
        exact h ⟨z, by intro B hB; by_contra hzB; exact hz ⟨B,hB,hzB⟩⟩)
    obtain ⟨z,hz⟩ := hCenter
    have hAnother : ∃ w, w ≠ z ∧ ∀ A ∈ cell, w ∈ A := by
      by_contra h
      apply hNoUnique z
      exact ⟨hz, by intro w hw; by_contra hwz; exact h ⟨w,hwz,hw⟩⟩
    obtain ⟨w,hwz,hw⟩ := hAnother
    have hBound := JSP523.intersecting_card_le_common_pair_cap hwz.symm hz hw hCellCap
    change cell.card ≤ _
    nlinarith [Nat.mul_le_mul_left D₄ (show 1 ≤ k * k by nlinarith)]

/-- Ordered disjoint pair roots lacking a strong common-cell label. -/
noncomputable def fixedPaletteUncoloredRootPairs
    (H : Family α) (V : Edge α) (s k t : ℕ) : Finset (Edge α × Edge α) := by
  classical
  exact (V.powersetCard s ×ˢ V.powersetCard s).filter fun p =>
    Disjoint p.1 p.2 ∧ ∀ z, ¬ ActualStrongPartner H V p.1 p.2 s k t z

/-- The disjoint uncolored incidence term in IV.7.3, on actual parent cells. -/
theorem fixed_palette_uncolored_cell_incidence_budget
    (H : Family α) (V : Edge α) (s k t D₄ : ℕ)
    (hs : 1 ≤ s) (hk : 2 ≤ k) (hAdm : Admissible H)
    (hD₄ : ∀ S : Edge α, S.card = s + 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    (∑ p ∈ fixedPaletteUncoloredRootPairs H V s k t,
      (commonPrefixTails H V p.1 p.2 k).card) ≤
      (V.powersetCard s).card ^ 2 * (t + k * k * D₄) := by
  classical
  have hBound : ∀ p ∈ fixedPaletteUncoloredRootPairs H V s k t,
      (commonPrefixTails H V p.1 p.2 k).card ≤ t + k * k * D₄ := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    have hRoots := Finset.mem_product.mp h.1
    exact fixed_palette_nonstrong_cell_bound H V p.1 p.2 s k t D₄
      hs hk hAdm hRoots.1 hRoots.2 h.2.1 h.2.2 hD₄
  have hPairs : (fixedPaletteUncoloredRootPairs H V s k t).card ≤ (V.powersetCard s).card ^ 2 := by
    have h := Finset.card_le_card
      (Finset.filter_subset (fun p : Edge α × Edge α =>
        Disjoint p.1 p.2 ∧ ∀ z, ¬ ActualStrongPartner H V p.1 p.2 s k t z)
        (V.powersetCard s ×ˢ V.powersetCard s))
    simpa only [fixedPaletteUncoloredRootPairs, Finset.card_product, pow_two] using h
  calc
    _ ≤ ∑ _p ∈ fixedPaletteUncoloredRootPairs H V s k t, (t + k * k * D₄) := Finset.sum_le_sum hBound
    _ = (fixedPaletteUncoloredRootPairs H V s k t).card * (t + k * k * D₄) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hPairs

end JSP523.Rank5
