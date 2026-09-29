import JSP523.Rank5.HigherRankFacetRetention

/-! # Full arbitrary-rank shared-facet inheritance deletion budget

This is IV.9.1–IV.9.3 for s=2, with the upper colors and lower
partner guarantees supplied by their actual deletion sets.
-/
namespace JSP523.Rank5.HigherRankUpper
variable {α : Type*} [DecidableEq α] [Nonempty α]

theorem facet_incidence_budget_of_actual_cleanups
    (K H : Family α) (V : Edge α) (n P Q L tLower tUpper u q D₃ D₄ Dₙ : ℕ)
    (lower : Edge α → α)
    (hKH : K ⊆ H) (hUniformK : Uniform (n + 2) K)
    (hUniformH : Uniform (n + 2) H) (hAmbientH : ∀ E ∈ H, E ⊆ V)
    (hUpper : Disjoint K (upperFacetColorCleanupEdges (n + 1) H V tUpper))
    (hLower : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard n) 2 u q
        (fun B R T => ¬ ActualStrongPartner H V R T 2 n tLower (lower B))))
    (hQ : 0 < Q) (hScale : Q * L ≤ P * u) (hq : 4 * q ≤ L)
    (hqu : q < u) (ht : 1 ≤ tLower)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hDₙ : ∀ S : Edge α, S.card = n + 1 →
      (H.filter fun E => S ⊆ E).card ≤ Dₙ)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    Q * (tLower * (2 * L) *
      (facetBadIncidences K V (n + 1)
        (facetColorCenter K H V (n + 1) tUpper hKH hUpper) lower).card) ≤
      tLower * (2 * L) * (lowFacetIncidenceConstant n * P * H.card) +
        Q * (8 * (V.powersetCard 2).card ^ 2 * D₃ * Dₙ * D₄) := by
  let center := facetColorCenter K H V (n + 1) tUpper hKH hUpper
  let I := highRetentionBadIncidences n K H V P Q center lower
  let bad := fun B R T => ¬ ActualStrongPartner H V R T 2 n tLower (lower B)
  have hAmbientK : ∀ E ∈ K, E ⊆ V := fun E hE => hAmbientH E (hKH hE)
  have hI : I ⊆ facetBadIncidences K V (n + 1) center lower := Finset.sdiff_subset
  have hMin : ∀ i ∈ I,
      Q * L ≤ P * (H.filter fun E => facetWitnessCore i ⊆ E).card := by
    intro i hi
    have hC := facet_bad_incidence_core_mem_powerset n K V center lower (hI hi)
    have hR := facet_bad_incidence_first_root_mem_pair_link n K V center lower
      hUniformK hAmbientK (hI hi)
    have hDegree := retained_pair_root_parent_degree_ge K H V
      (V.powersetCard n) u q bad hKH hLower hC hR
    rw [actual_core_link_two_eq_parent_pair_link] at hDegree
    exact hScale.trans (Nat.mul_le_mul_left P (hDegree.trans
      (JSP523.Counting.parent_pair_link_card_le_codegree H V (facetWitnessCore i))))
  have hRetained := (high_retention_bad_incidence_degrees n K H V P Q 0 L
    center lower hQ hUniformK hAmbientK (by intro i hi; simp) hMin).2
  have hFacet : ∀ i ∈ I, 2 ≤ (facetParents K i.1.2).card := by
    intro i hi
    have hShared := (Finset.mem_filter.mp (hI hi)).2.2.1
    have hAc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hShared).1).2
    rw [← facet_completion_vertices_card_eq_parent_degree n K V i.1.2
      hUniformK hAmbientK hAc]
    exact (Finset.mem_filter.mp hShared).2
  have hWeighted := facet_weighted_bound_of_actual_cleanups n I K H V
    tLower tUpper u q D₃ D₄ Dₙ lower hKH hUniformK hAmbientK hUpper hI hLower
    hqu ht (fun i hi => hq.trans (hRetained i hi)) hD₃ hDₙ hD₄
  exact facet_bad_incidence_combined_budget n K H V P Q tLower 2 L
    (8 * (V.powersetCard 2).card ^ 2 * D₃ * Dₙ * D₄) center lower
    hUniformK hUniformH hAmbientK hAmbientH hFacet hRetained hWeighted

/-- The same explicit budget controls the actual number of deleted edges. -/
theorem facet_repair_loss_budget_of_actual_cleanups
    (K H : Family α) (V : Edge α) (n P Q L tLower tUpper u q D₃ D₄ Dₙ : ℕ)
    (lower : Edge α → α)
    (hKH : K ⊆ H) (hUniformK : Uniform (n + 2) K)
    (hUniformH : Uniform (n + 2) H) (hAmbientH : ∀ E ∈ H, E ⊆ V)
    (hUpper : Disjoint K (upperFacetColorCleanupEdges (n + 1) H V tUpper))
    (hLower : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard n) 2 u q
        (fun B R T => ¬ ActualStrongPartner H V R T 2 n tLower (lower B))))
    (hQ : 0 < Q) (hScale : Q * L ≤ P * u) (hq : 4 * q ≤ L)
    (hqu : q < u) (ht : 1 ≤ tLower)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hDₙ : ∀ S : Edge α, S.card = n + 1 →
      (H.filter fun E => S ⊆ E).card ≤ Dₙ)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    Q * (tLower * (2 * L) *
      (K.card - (repairSharedFacet K V (n + 1)
        (facetColorCenter K H V (n + 1) tUpper hKH hUpper) lower).card)) ≤
      tLower * (2 * L) * (lowFacetIncidenceConstant n * P * H.card) +
        Q * (8 * (V.powersetCard 2).card ^ 2 * D₃ * Dₙ * D₄) := by
  have hLoss := shared_facet_repair_loss_le_bad_incidences K V (n + 1)
    (facetColorCenter K H V (n + 1) tUpper hKH hUpper) lower
  exact (Nat.mul_le_mul_left Q (Nat.mul_le_mul_left (tLower * (2 * L)) hLoss)).trans
    (facet_incidence_budget_of_actual_cleanups K H V n P Q L tLower tUpper
      u q D₃ D₄ Dₙ lower hKH hUniformK hUniformH hAmbientH hUpper hLower
      hQ hScale hq hqu ht hD₃ hDₙ hD₄)

end JSP523.Rank5.HigherRankUpper
