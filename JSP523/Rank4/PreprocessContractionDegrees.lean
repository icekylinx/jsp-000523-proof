import JSP523.Rank4.PreprocessQuantitativePairCover
import JSP523.Rank4.PreprocessCollisionMoment

/-! # Degree inheritance for the actual contraction step -/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

theorem rank_four_vertex_degree_le_ground_mul_pair_cap
    (F : Family α) (U : Edge α) (M : ℕ)
    (hUniform : Uniform 4 F) (hGround : ∀ E ∈ F, E ⊆ U)
    (hPair : ∀ P : Edge α, P.card = 2 → rankFourPairDegree F P ≤ M) (v : α) :
    (F.filter fun E => v ∈ E).card ≤ U.card * M := by
  classical
  have hSub : (F.filter fun E => v ∈ E) ⊆
      (U.erase v).biUnion fun w => F.filter fun E => ({v, w} : Edge α) ⊆ E := by
    intro E hE
    have hEF := (Finset.mem_filter.mp hE).1
    have hvE := (Finset.mem_filter.mp hE).2
    have hErase : (E.erase v).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hvE, hUniform hEF]
      norm_num
    obtain ⟨w, hw⟩ := hErase
    have hwE := (Finset.mem_erase.mp hw).2
    have hwv := (Finset.mem_erase.mp hw).1
    refine Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨hwv, hGround E hEF hwE⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨hEF, by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hvE hwE⟩
  calc
    _ ≤ ((U.erase v).biUnion fun w => F.filter fun E => ({v, w} : Edge α) ⊆ E).card := Finset.card_le_card hSub
    _ ≤ ∑ w ∈ U.erase v, (F.filter fun E => ({v, w} : Edge α) ⊆ E).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ U.erase v, M := by
      apply Finset.sum_le_sum
      intro w hw
      exact hPair {v, w} (Finset.card_pair (Ne.symm (Finset.mem_erase.mp hw).1))
    _ = (U.erase v).card * M := by simp
    _ ≤ U.card * M := Nat.mul_le_mul_right M Finset.card_erase_le

theorem fixed_core_sdiff_eq_disjoint_filter
    (F : Family α) (U X : Edge α) (hGround : ∀ E ∈ F, E ⊆ U) :
    fixedDecompositionCore F (U \ X) = F.filter fun E => Disjoint E X := by
  ext E
  simp only [fixedDecompositionCore, Finset.mem_filter]
  constructor
  · rintro ⟨hEF, hSub⟩
    refine ⟨hEF, Finset.disjoint_left.mpr ?_⟩
    intro x hx hxX
    exact (Finset.mem_sdiff.mp (hSub hx)).2 hxX
  · rintro ⟨hEF, hEX⟩
    refine ⟨hEF, ?_⟩
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hGround E hEF hx, fun hxX => Finset.disjoint_left.mp hEX hx hxX⟩

end JSP523.Rank4
