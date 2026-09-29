import JSP523.Rank4.GlobalActualEndToEndError
import JSP523.Rank4.PreprocessInitialOuterCoverBudget
import JSP523.Rank4.PreprocessInitialOuterBudgetScale
import JSP523.Rank4.GlobalActualOuterOverlapScale

namespace JSP523.Rank4

def endToEndGround {n : ℕ} (Z X : Edge (Fin n)) : Edge (Fin n) := Finset.univ \ (Z ∪ X)

def endToEndOverlap {n : ℕ} (H : Family (Fin n)) (Z X : Edge (Fin n)) : ℕ :=
  ((Z.biUnion fun c => rankFourStarLink H (endToEndGround Z X) c) ∩
    rankFourFacetShadow (fixedDecompositionCore H (endToEndGround Z X)) (endToEndGround Z X)).card

structure ActualOuterMasterPacket {n : ℕ} (H : Family (Fin n)) (Z X : Edge (Fin n)) (level : ℕ) (a : ℝ) where
  owner : Edge (Fin n) → Fin n
  outerLoss : ℕ
  original_mass : H.card ≤
    (Z.biUnion (pairOwnerCleanedLink (fun c => rankFourStarLink H (endToEndGround Z X) c) owner)).card +
      (fixedDecompositionCore H (endToEndGround Z X)).card + outerLoss
  outer_bound : outerLoss ≤ initial_outer_polynomial_budget n Z.card X.card (initial_outer_radius n)
  preprocessing : ActualEndToEndData H (endToEndGround Z X) level a (endToEndOverlap H Z X) outerLoss

/-- The actual initial cover, actual owner cleaning, and actual regularization
construct the entire master packet. No outer-loss or master premise is supplied. -/
theorem eventually_exists_actual_outer_master_packet
    (H : (n : ℕ) → Family (Fin n)) (Z X : (n : ℕ) → Edge (Fin n))
    (hAdm : ∀ n, Admissible (H n)) (hUniform : ∀ n, Uniform 4 (H n))
    (hData : ∀ᶠ n in Filter.atTop, initial_outer_overlap_cover_data (H n) (Z n) (X n))
    (level : ℕ) (hLevel : 256 ≤ level) (a : ℝ) (ha : 0 < a) :
    ∀ᶠ n in Filter.atTop, Nonempty (ActualOuterMasterPacket (H n) (Z n) (X n) level a) := by
  filter_upwards [hData, eventually_initial_outer_ground_at_least_six,
    eventually_actual_end_to_end_data level hLevel a ha, Filter.eventually_ge_atTop (1 : ℕ)] with n hd hg hm hn
  rcases hd with ⟨hX, _, _, hCount, hVertex, hCoreVertex, hTriple⟩
  let U := endToEndGround (Z n) (X n)
  let L := fun c => rankFourStarLink (H n) U c
  have hU : 6 ≤ U.card := hg U hCount
  have hSize : ∀ c ∈ X n, 6 * ((fixedDecompositionCore (H n) (Finset.univ \ Z n)).filter fun E => c ∈ E).card ≤
      initial_outer_radius n ^ 3 := by
    intro c _
    have h := (mul_le_mul_of_nonneg_left (hVertex c) (by norm_num : (0 : ℝ) ≤ 6)).trans
      (initial_outer_radius_cube_lower n)
    exact_mod_cast h
  let fallback : Fin n := ⟨0, hn⟩
  obtain ⟨owner, loss, hOriginal, hLoss⟩ := exists_initial_outer_original_budget
    (H n) (Z n) (X n) fallback (initial_outer_radius n) (hAdm n) (hUniform n) hX hU hSize
  have hOutside : ∀ c ∈ Z n, c ∉ U := by
    intro c hc hIn
    exact (Finset.mem_sdiff.mp hIn).2 (Finset.mem_union_left _ hc)
  have hEdges : ∀ c ∈ Z n, ∀ Q ∈ L c, insert c Q ∈ H n := by
    intro c _ Q hQ
    exact (Finset.mem_filter.mp hQ).2
  have hGround : ∀ c ∈ Z n, ∀ Q ∈ L c, Q ∈ U.powersetCard 3 := by
    intro c _ Q hQ
    exact (Finset.mem_filter.mp hQ).1
  have hOverlap : ((Z n).biUnion (pairOwnerCleanedLink L owner) ∩
      rankFourFacetShadow (fixedDecompositionCore (H n) U) U).card ≤ endToEndOverlap (H n) (Z n) (X n) := by
    apply Finset.card_le_card
    intro Q hQ
    obtain ⟨hc, hShadow⟩ := Finset.mem_inter.mp hQ
    obtain ⟨c, hcZ, hQc⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨c, hcZ, pair_owner_cleaned_link_subset L owner c hQc⟩, hShadow⟩
  obtain ⟨A⟩ := hm (H n) U Finset.univ fallback L (Z n) owner (endToEndOverlap (H n) (Z n) (X n)) loss
    (hAdm n) (hUniform n) (Finset.subset_univ U) hCoreVertex hTriple (fun c _ => Finset.mem_univ c)
    hOutside hEdges hGround (by omega) hOverlap hOriginal
  exact ⟨⟨owner, loss, hOriginal, hLoss, A⟩⟩

end JSP523.Rank4
