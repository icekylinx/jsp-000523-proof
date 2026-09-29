import JSP523.Rank5.LowerUncoloredReindex

/-! # Pinned actual lower bicolored-triangle budget

An orientation with repeated label at the first root is counted directly.
The repeated-center degree pays for its third root, and a four-codegree
pays for the supporting triple core.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

def LowerRepeatedTriangle (H : Family α) (V : Edge α) (t : ℕ)
    (P Q R : Edge α) : Prop :=
  ∃ z w, z ≠ w ∧ ActualStrongPartner H V P Q 2 3 t z ∧
    ActualStrongPartner H V P R 2 3 t z ∧ ActualStrongPartner H V Q R 2 3 t w

noncomputable def lowerBicoloredFirstTriples
    (H : Family α) (V : Edge α) (t : ℕ) : Finset ((Edge α × Edge α) × Edge α) := by
  classical
  exact ((V.powersetCard 2 ×ˢ V.powersetCard 2) ×ˢ V.powersetCard 2).filter fun p =>
    LowerRepeatedTriangle H V t p.1.1 p.1.2 p.2

noncomputable def lowerTriangleCoreCell
    (H : Family α) (V : Edge α) (p : (Edge α × Edge α) × Edge α) : Family α := by
  classical
  exact (V.powersetCard 3).filter fun B =>
    p.1.1 ∈ actualCoreLink H V B 2 ∧ p.1.2 ∈ actualCoreLink H V B 2 ∧
      p.2 ∈ actualCoreLink H V B 2

theorem strong_center_not_mem_first_root
    (H : Family α) (V P Q : Edge α) (t : ℕ) (ht : 1 ≤ t)
    {z : α} (hz : ActualStrongPartner H V P Q 2 3 t z) : z ∉ P := by
  obtain ⟨B,hB⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < t) hz.2.2.1)
  have hzB := hz.2.2.2.1 B hB
  have hDisj := (Finset.disjoint_union_right.mp (mem_common_prefix_tails.mp hB).2.2.1).1
  exact fun hzP => Finset.disjoint_left.mp hDisj hzB hzP

/-- A bicolored orientation pins its first root and two distinct labels,
    so at most `D₄` actual triple cores support it. -/
theorem lower_repeated_triangle_core_cell_le_four_codegree
    (H : Family α) (V : Edge α) (t D₄ : ℕ)
    (hD₄ : ∀ S : Edge α, S.card = 4 → (H.filter fun E => S ⊆ E).card ≤ D₄)
    {p : (Edge α × Edge α) × Edge α}
    (hp : p ∈ lowerBicoloredFirstTriples H V t) :
    (lowerTriangleCoreCell H V p).card ≤ D₄ := by
  classical
  obtain ⟨z,w,hzw,hPQ,hPR,hQR⟩ := (Finset.mem_filter.mp hp).2
  let C := lowerTriangleCoreCell H V p
  by_cases hEmpty : C = ∅
  · change C.card ≤ D₄
    simp [hEmpty]
  obtain ⟨B₀,hB₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have h₀ := Finset.mem_filter.mp hB₀
  have h₀Core := Finset.mem_powersetCard.mp h₀.1
  have hz₀ := lower_strong_label_mem_actual_core H V B₀ p.1.1 p.1.2 t
    h₀Core.1 h₀Core.2 h₀.2.1 h₀.2.2.1 hPQ
  have hw₀ := lower_strong_label_mem_actual_core H V B₀ p.1.2 p.2 t
    h₀Core.1 h₀Core.2 h₀.2.2.1 h₀.2.2.2 hQR
  have hP₀ := mem_actual_core_link.mp h₀.2.1
  have hPinDisj : Disjoint p.1.1 ({z,w} : Edge α) := by
    apply hP₀.2.2.1.mono_right
    exact Finset.insert_subset_iff.mpr ⟨hz₀,Finset.singleton_subset_iff.mpr hw₀⟩
  have hPinCard : (p.1.1 ∪ {z,w}).card = 4 := by
    rw [Finset.card_union_of_disjoint hPinDisj, hP₀.2.1, Finset.card_pair hzw]
  have hCount : C.card ≤ (H.filter fun E => p.1.1 ∪ {z,w} ⊆ E).card := by
    apply Finset.card_le_card_of_injOn (fun B => B ∪ p.1.1)
    · intro B hB
      have h := Finset.mem_filter.mp hB
      have hc := Finset.mem_powersetCard.mp h.1
      have hz := lower_strong_label_mem_actual_core H V B p.1.1 p.1.2 t
        hc.1 hc.2 h.2.1 h.2.2.1 hPQ
      have hw := lower_strong_label_mem_actual_core H V B p.1.2 p.2 t
        hc.1 hc.2 h.2.2.1 h.2.2.2 hQR
      have hParent := (mem_actual_core_link.mp h.2.1).2.2.2
      refine Finset.mem_filter.mpr ⟨hParent, ?_⟩
      apply Finset.union_subset Finset.subset_union_right
      exact (Finset.insert_subset_iff.mpr ⟨hz,Finset.singleton_subset_iff.mpr hw⟩).trans
        Finset.subset_union_left
    · intro B hB A hA hEq
      have hBP := (mem_actual_core_link.mp (Finset.mem_filter.mp hB).2.1).2.2.1.symm
      have hAP := (mem_actual_core_link.mp (Finset.mem_filter.mp hA).2.1).2.2.1.symm
      have h := congrArg (fun E => E \ p.1.1) hEq
      simpa only [Finset.union_sdiff_cancel_right hBP, Finset.union_sdiff_cancel_right hAP] using h
  exact hCount.trans (hD₄ _ hPinCard)

/-- The full repeated-root orientation sum satisfies the IV.7.4 pinned
    budget. Every unordered bicolored triangle has such an orientation. -/
theorem lower_bicolored_first_triangle_weighted_budget
    (H : Family α) (V : Edge α) (t D₃ D₄ : ℕ) (ht : 1 ≤ t)
    (hD₃ : ∀ S : Edge α, S.card = 3 → (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 → (H.filter fun E => S ⊆ E).card ≤ D₄) :
    t * (∑ p ∈ lowerBicoloredFirstTriples H V t, (lowerTriangleCoreCell H V p).card) ≤
      (V.powersetCard 2).card ^ 2 * D₃ * D₃ * D₄ := by
  classical
  let T := lowerBicoloredFirstTriples H V t
  let pairs := V.powersetCard 2 ×ˢ V.powersetCard 2
  have hMap : ∀ p ∈ T, p.1 ∈ pairs := by
    intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hOne : ∀ pq ∈ pairs,
      t * (∑ p ∈ T.filter fun p => p.1 = pq, (lowerTriangleCoreCell H V p).card) ≤
        D₃ * D₃ * D₄ := by
    intro pq hpq
    let F := T.filter fun p => p.1 = pq
    by_cases hEmpty : F = ∅
    · change t * (∑ p ∈ F, (lowerTriangleCoreCell H V p).card) ≤ _
      simp [hEmpty]
    obtain ⟨p₀,hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
    have h₀ := Finset.mem_filter.mp hp₀
    obtain ⟨z,w,hzw,hPQ,hPR,hQR⟩ := (Finset.mem_filter.mp h₀.1).2
    have hPQ' : ActualStrongPartner H V pq.1 pq.2 2 3 t z := by simpa only [h₀.2] using hPQ
    have hzP := strong_center_not_mem_first_root H V pq.1 pq.2 t ht hPQ'
    have hSub : F.card ≤ (actualCenterPartners H V pq.1 2 3 t z ∅).card := by
      apply Finset.card_le_card_of_injOn (fun p => p.2)
      · intro p hp
        have h := Finset.mem_filter.mp hp
        obtain ⟨z',w',hne,hPQ₂,hPR₂,hQR₂⟩ := (Finset.mem_filter.mp h.1).2
        have hPQ₂' : ActualStrongPartner H V pq.1 pq.2 2 3 t z' := by simpa only [h.2] using hPQ₂
        have hzz := actual_strong_partner_center_unique H V pq.1 pq.2 2 3 t hPQ₂' hPQ'
        have hPR' : ActualStrongPartner H V pq.1 p.2 2 3 t z := by simpa only [h.2,hzz] using hPR₂
        exact Finset.mem_filter.mpr ⟨hPR'.1,hPR',Finset.empty_subset _⟩
      · intro p hp q hq heq
        exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) heq
    have hPin := repeated_center_partner_bound_from_codegrees H V pq.1 2 3 t z ∅ 0 D₃ D₃
      (Finset.mem_powersetCard.mp (Finset.mem_product.mp hpq).1).2 hzP (by simp) hD₃ hD₃
    have hWeighted := (Nat.mul_le_mul_left t hSub).trans hPin
    have hCells : (∑ p ∈ F, (lowerTriangleCoreCell H V p).card) ≤ F.card * D₄ := by
      calc
        _ ≤ ∑ _p ∈ F, D₄ := Finset.sum_le_sum (fun p hp =>
          lower_repeated_triangle_core_cell_le_four_codegree H V t D₄ hD₄ (Finset.mem_filter.mp hp).1)
        _ = _ := by simp
    exact (Nat.mul_le_mul_left t hCells).trans (by nlinarith [Nat.mul_le_mul_right D₄ hWeighted])
  have hReindex := Finset.sum_fiberwise_of_maps_to (s := T) (t := pairs) hMap
    (fun p => (lowerTriangleCoreCell H V p).card)
  calc
    _ = ∑ pq ∈ pairs, t * (∑ p ∈ T.filter fun p => p.1 = pq,
        (lowerTriangleCoreCell H V p).card) := by rw [← hReindex, Finset.mul_sum]
    _ ≤ ∑ _pq ∈ pairs, D₃ * D₃ * D₄ := Finset.sum_le_sum hOne
    _ = _ := by simp [pairs, Finset.card_product, pow_two, mul_assoc]

end JSP523.Rank5
