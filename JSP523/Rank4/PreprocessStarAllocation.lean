import JSP523.Rank4.PreprocessStarLayers
import JSP523.Rank5.ShadowAllocationDiscrete

/-! # Allocation for the actual separated rank-four star links -/

namespace JSP523.Rank4

variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Every ordinary shadow pair lies in the actual pair shadow. -/
theorem shadow_subset_star_link_pair_shadow
    (L : ι → Family α) (V : Edge α) (i : ι)
    (hGround : ∀ T ∈ L i, T ∈ V.powersetCard 3) :
    Finset.shadow (L i) ⊆ starLinkPairShadow L V i := by
  intro P hP
  obtain ⟨T, hT, x, hx, hErase⟩ := Finset.mem_shadow_iff.mp hP
  have hTG := Finset.mem_powersetCard.mp (hGround T hT)
  have hSub : P ⊆ T := by rw [← hErase]; exact Finset.erase_subset x T
  have hCard : P.card = 2 := by rw [← hErase, Finset.card_erase_of_mem hx, hTG.2]
  exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hSub.trans hTG.1, hCard⟩, T, hT, hSub⟩

omit [DecidableEq α] in
theorem pair_owner_cleaned_link_subset
    (L : ι → Family α) (owner : Edge α → ι) (i : ι) :
    pairOwnerCleanedLink L owner i ⊆ L i := Finset.filter_subset _ _

/-- Integer shadow allocation suffices for both the regularization step
and the subsequent single-center extraction; the additive radius error is three. -/
theorem actual_cleaned_star_allocation
    {n : ℕ} (V : Edge (Fin n)) (I : Finset ι) (L : ι → Family (Fin n))
    (owner : Edge (Fin n) → ι) (radius : ℕ)
    (hGround : ∀ i ∈ I, ∀ T ∈ L i, T ∈ V.powersetCard 3)
    (hSize : ∀ i ∈ I, 6 * (L i).card ≤ radius ^ 3) :
    3 * (∑ i ∈ I, (pairOwnerCleanedLink L owner i).card) ≤
      (radius + 3) * V.card.choose 2 := by
  classical
  have hClean : ∀ i ∈ I, ∀ T ∈ pairOwnerCleanedLink L owner i, T ∈ V.powersetCard 3 := by
    intro i hi T hT
    exact hGround i hi T (pair_owner_cleaned_link_subset L owner i hT)
  apply JSP523.Rank5.disjoint_shadow_radius_allocation_on_ground V I
    (pairOwnerCleanedLink L owner) (by norm_num : 2 ≤ 3)
  · intro i hi T hT
    exact (Finset.mem_powersetCard.mp (hClean i hi T hT)).2
  · exact hClean
  · intro i hi
    have hSub := pair_owner_cleaned_link_subset L owner i
    simpa [Nat.factorial] using (Nat.mul_le_mul_left 6 (Finset.card_le_card hSub)).trans (hSize i hi)
  · intro i hi j hj hij
    exact (pair_owner_cleaning_shadows_disjoint L owner V i j hij).mono
      (shadow_subset_star_link_pair_shadow _ V i (hClean i hi))
      (shadow_subset_star_link_pair_shadow _ V j (hClean j hj))

end JSP523.Rank4
