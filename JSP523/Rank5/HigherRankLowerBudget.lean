import JSP523.Rank5.HigherRankLowerRetention

/-! # Full s=3 lower-inheritance deletion budget

This bound is derived from actual parent partners and retained roots.
The two thresholds correspond to cores of sizes n+1 and n in an
(n+3)-uniform family.
-/
namespace JSP523.Rank5.HigherRankLower
variable {α : Type*} [DecidableEq α]

theorem lower_incidence_budget_of_actual_cleanups
    (K H : Family α) (V : Edge α)
    (n P Q LUpper LLower tLower tUpper uLower qLower uUpper qUpper D₄ D₅ Dₙ : ℕ)
    (upper lower : Edge α → α)
    (hKH : K ⊆ H) (hUniformK : Uniform (n + 3) K)
    (hUniformH : Uniform (n + 3) H) (hAmbientH : ∀ E ∈ H, E ⊆ V)
    (hUpper : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard (n + 1)) 2 uUpper qUpper
        (fun A R T => ¬ ActualStrongPartner H V R T 2 (n + 1) tUpper (upper A))))
    (hLower : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard n) 3 uLower qLower
        (fun B R T => ¬ ActualStrongPartner H V R T 3 n tLower (lower B))))
    (hQ : 0 < Q)
    (hScaleUpper : Q * LUpper ≤ P * uUpper)
    (hScaleLower : Q * LLower ≤ P * uLower)
    (hqUpper : 2 * qUpper ≤ LUpper) (hqLower : 4 * qLower ≤ LLower)
    (hGapUpper : qUpper < uUpper) (hGapLower : qLower < uLower)
    (ht : 1 ≤ tLower)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄)
    (hDₙ : ∀ S : Edge α, S.card = n + 1 →
      (H.filter fun E => S ⊆ E).card ≤ Dₙ)
    (hD₅ : ∀ S : Edge α, S.card = 5 →
      (H.filter fun E => S ⊆ E).card ≤ D₅) :
    Q * (tLower * (LUpper * LLower) *
      (badIncidences K V (n + 1) upper lower).card) ≤
      tLower * (LUpper * LLower) * (lowFacetIncidenceConstant n * P * H.card) +
        Q * (12 * (V.powersetCard 3).card ^ 2 * D₄ * Dₙ * D₅) := by
  classical
  let I := highRetentionBadIncidences n K H V P Q upper lower
  have hI : I ⊆ badIncidences K V (n + 1) upper lower := Finset.sdiff_subset
  have hAmbientK : ∀ E ∈ K, E ⊆ V := fun E hE => hAmbientH E (hKH hE)
  have hMinUpper : ∀ i ∈ I,
      Q * LUpper ≤ P * (facetParents H i.1.2).card := by
    intro i hi
    have hAc := (Finset.mem_filter.mp (hI hi)).2.2.1
    have hRoot := bad_incidence_upper_root_mem_pair_link K V n upper lower
      hUniformK hAmbientK (hI hi)
    have hDegree := retained_pair_root_parent_degree_ge K H V
      (V.powersetCard (n + 1)) uUpper qUpper
      (fun A R T => ¬ ActualStrongPartner H V R T 2 (n + 1) tUpper (upper A))
      hKH hUpper hAc hRoot
    rw [actual_core_link_two_eq_parent_pair_link] at hDegree
    exact hScaleUpper.trans (Nat.mul_le_mul_left P (hDegree.trans
      (JSP523.Counting.parent_pair_link_card_le_codegree H V i.1.2)))
  have hMinLower : ∀ i ∈ I,
      Q * LLower ≤ P * (H.filter fun E => lowerWitnessCore i ⊆ E).card := by
    intro i hi
    have hBC := bad_incidence_core_mem_powerset K V n upper lower (hI hi)
    have hRoot := bad_incidence_first_root_mem_triple_link K V n upper lower
      hUniformK hAmbientK (hI hi)
    have hDegree := retained_core_root_parent_degree_ge K H V
      (V.powersetCard n) 3 uLower qLower
      (fun B R T => ¬ ActualStrongPartner H V R T 3 n tLower (lower B))
      hKH hLower hBC hRoot
    change uLower ≤ (parentTripleLink H V (lowerWitnessCore i)).card at hDegree
    rw [parent_triple_link_card_eq_codegree n H V (lowerWitnessCore i)
      hUniformH hAmbientH (Finset.mem_powersetCard.mp hBC).2] at hDegree
    exact hScaleLower.trans (Nat.mul_le_mul_left P hDegree)
  have hRetained := high_retention_bad_incidence_degrees n K H V P Q LUpper LLower
    upper lower hQ hUniformK hAmbientK hMinUpper hMinLower
  have hWeighted := lower_weighted_bound_of_actual_cleanups I K H V
    n tLower tUpper uLower qLower uUpper qUpper D₄ D₅ Dₙ upper lower
    hI hKH hUniformK hAmbientK hUpper hLower hGapUpper hGapLower
    (fun i hi => hqUpper.trans (hRetained.1 i hi))
    (fun i hi => hqLower.trans (hRetained.2 i hi)) ht hD₄ hDₙ hD₅
  exact facet_bad_incidence_combined_budget n K H V P Q tLower LUpper LLower
    (12 * (V.powersetCard 3).card ^ 2 * D₄ * Dₙ * D₅) upper lower
    hUniformK hUniformH hAmbientK hAmbientH hRetained.1 hRetained.2 hWeighted

/-- Reindex the original cleanup's sigma witnesses into the actual
    parent/core/deleted-vertex incidences used in the s=3 bound. -/
theorem bad_rank_deletion_incidences_card_le
    (K : Family α) (V : Edge α) (m : ℕ) (z : Edge α → α)
    (hAmbient : ∀ E ∈ K, E ⊆ V) :
    (badRankDeletionIncidences K m z).card ≤ (badIncidences K V m z z).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun w : (_E : Edge α) × Edge α × α => ((w.1, w.2.1), w.2.2))
  · intro w hw
    have hParts := Finset.mem_sigma.mp hw
    have hW := Finset.mem_filter.mp hParts.2
    have hProd := Finset.mem_product.mp hW.1
    have hCore := Finset.mem_powersetCard.mp hProd.1
    have hPow : w.2.1 ∈ V.powersetCard m :=
      Finset.mem_powersetCard.mpr ⟨hCore.1.trans (hAmbient _ hParts.1), hCore.2⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hParts.1, hPow⟩, hAmbient _ hParts.1 hProd.2⟩,
        hCore.1, hPow, hW.2⟩
  · rintro ⟨E, A, a⟩ _ ⟨F, B, b⟩ _ hEq
    change ((E, A), a) = ((F, B), b) at hEq
    simp only [Prod.mk.injEq] at hEq
    rcases hEq with ⟨⟨rfl, rfl⟩, rfl⟩
    rfl

/-- The concrete rank-inheritance repair loss is bounded by this same
    actual incidence set. -/
theorem rank_repair_loss_le_lower_bad_incidences [Nonempty α]
    (K : Family α) (V : Edge α) (m : ℕ) (z : Edge α → α)
    (hAmbient : ∀ E ∈ K, E ⊆ V) :
    K.card - (repairRankInheritance K m z).card ≤
      (badIncidences K V m z z).card :=
  (repair_rank_inheritance_loss_le_bad_incidences K m z).trans
    (bad_rank_deletion_incidences_card_le K V m z hAmbient)

end JSP523.Rank5.HigherRankLower
