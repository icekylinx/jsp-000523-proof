import JSP523.Rank4.PreprocessInitialOuterCoverTriples
import JSP523.Rank4.PreprocessTouchingLoss
import JSP523.Rank5.InitialCodegreeCleanup
import JSP523.Coarse.AllRank

/-! # Actual initial outer cover and induced rank-four core

High vertex degrees are removed first. A maximal matching then covers
all heavy triples in the remaining actual parent family.
-/

namespace JSP523.Rank4

noncomputable def initialOuterHighVertices {n : ℕ}
    (H : Family (Fin n)) (D : ℝ) : Edge (Fin n) := by
  classical
  exact Finset.univ.filter fun z => D < ((H.filter fun E => z ∈ E).card : ℝ)

theorem initial_outer_high_vertices_mass_bound {n : ℕ}
    (H : Family (Fin n)) (D : ℝ) (hUniform : Uniform 4 H) :
    D * (initialOuterHighVertices H D).card ≤ 4 * (H.card : ℝ) := by
  classical
  have hSum := JSP523.Rank5.sum_vertex_degrees_eq_rank_mul_card H hUniform
  have hSumR : (∑ z : Fin n, ((H.filter fun E => z ∈ E).card : ℝ)) =
      4 * (H.card : ℝ) := by exact_mod_cast hSum
  calc
    _ = ∑ _z ∈ initialOuterHighVertices H D, D := by simp [mul_comm]
    _ ≤ ∑ z ∈ initialOuterHighVertices H D, ((H.filter fun E => z ∈ E).card : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      exact (Finset.mem_filter.mp hz).2.le
    _ ≤ ∑ z : Fin n, ((H.filter fun E => z ∈ E).card : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro z _ _
      exact Nat.cast_nonneg _
    _ = _ := hSumR

theorem initial_outer_vertex_degree_cap {n : ℕ}
    (H : Family (Fin n)) (D : ℝ) (hD : 0 ≤ D) (z : Fin n) :
    (((fixedDecompositionCore H (Finset.univ \ initialOuterHighVertices H D)).filter
      fun E => z ∈ E).card : ℝ) ≤ D := by
  classical
  by_cases hz : z ∈ initialOuterHighVertices H D
  · have hEmpty : (fixedDecompositionCore H (Finset.univ \ initialOuterHighVertices H D)).filter
        (fun E => z ∈ E) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro E hE
      have hParts := Finset.mem_filter.mp hE
      exact (Finset.mem_sdiff.mp ((Finset.mem_filter.mp hParts.1).2 hParts.2)).2 hz
    simpa only [hEmpty, Finset.card_empty, Nat.cast_zero] using hD
  · have hCap : ((H.filter fun E => z ∈ E).card : ℝ) ≤ D := by
      by_contra h
      exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ z, by linarith⟩)
    apply le_trans _ hCap
    exact_mod_cast Finset.card_le_card (show
      (fixedDecompositionCore H (Finset.univ \ initialOuterHighVertices H D)).filter (fun E => z ∈ E) ⊆
        H.filter (fun E => z ∈ E) from fun E hE =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).1,
            (Finset.mem_filter.mp hE).2⟩)

/-- A fully actual finite initial decomposition. The high-vertex and
heavy-triple sets satisfy the budgets needed by III.A.3. -/
theorem exists_initial_outer_cover {n : ℕ}
    (H : Family (Fin n)) (D : ℝ) (t : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform 4 H)
    (hD : 0 ≤ D) (ht : 0 < t) (hGap : 2 * n ≤ t ^ 2) :
    ∃ Z X : Edge (Fin n),
      X ⊆ Finset.univ \ Z ∧
      D * (Z.card : ℝ) ≤ 128 * (n : ℝ) ^ 3 ∧ X.card * t ≤ 6 * n ∧
      n ≤ (Finset.univ \ (Z ∪ X)).card + Z.card + X.card ∧
      (∀ z : Fin n, (((fixedDecompositionCore H (Finset.univ \ Z)).filter
        fun E => z ∈ E).card : ℝ) ≤ D) ∧
      (∀ z : Fin n, (((fixedDecompositionCore H (Finset.univ \ (Z ∪ X))).filter
        fun E => z ∈ E).card : ℝ) ≤ D) ∧
      (∀ T : Edge (Fin n), T.card = 3 →
        (rankFourFacetParents (fixedDecompositionCore H (Finset.univ \ (Z ∪ X))) T).card < t) := by
  classical
  let Z := initialOuterHighVertices H D
  let W : Edge (Fin n) := Finset.univ \ Z
  let H₀ := fixedDecompositionCore H W
  have hH₀H : H₀ ⊆ H := Finset.filter_subset _ _
  have hAdm₀ : Admissible H₀ := admissible_mono hH₀H hAdm
  have hUniform₀ : Uniform 4 H₀ := fun E hE => hUniform (hH₀H hE)
  have hWn : W.card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (show W ⊆ Finset.univ from Finset.subset_univ _)
  obtain ⟨X, hXW, hXCard, hTriple⟩ := exists_initial_heavy_triple_cover H₀ W t
    hAdm₀ hUniform₀ ht ((Nat.mul_le_mul_left 2 hWn).trans hGap)
  let U : Edge (Fin n) := Finset.univ \ (Z ∪ X)
  let B := fixedDecompositionCore H U
  have hUW : U ⊆ W := by
    intro z hz
    have h := Finset.mem_sdiff.mp hz
    exact Finset.mem_sdiff.mpr ⟨h.1, fun hzZ => h.2 (Finset.mem_union_left _ hzZ)⟩
  have hB₀ : B ⊆ H₀ := by
    intro E hE
    have h := Finset.mem_filter.mp hE
    exact Finset.mem_filter.mpr ⟨h.1, h.2.trans hUW⟩
  have hUniB : Uniform 4 B := fun E hE => hUniform₀ (hB₀ hE)
  have hGroundB : ∀ E ∈ B, E ⊆ U := fun E hE => (Finset.mem_filter.mp hE).2
  have hCap₀ (z : Fin n) : ((H₀.filter fun E => z ∈ E).card : ℝ) ≤ D :=
    initial_outer_vertex_degree_cap H D hD z
  have hMassZ := initial_outer_high_vertices_mass_bound H D hUniform
  have hCoarse : (H.card : ℝ) ≤ 32 * (n : ℝ) ^ 3 := by
    exact_mod_cast (by simpa only [Fintype.card_fin] using Coarse.coarse_rank_four H hUniform hAdm)
  refine ⟨Z, X, hXW, by dsimp [Z]; nlinarith only [hMassZ, hCoarse],
    hXCard.trans (Nat.mul_le_mul_left 6 hWn), ?_, hCap₀, ?_, ?_⟩
  · have hCount := Finset.card_sdiff_add_card_eq_card
      (show Z ∪ X ⊆ Finset.univ from Finset.subset_univ _)
    have hUnion := Finset.card_union_le Z X
    simp only [Finset.card_univ, Fintype.card_fin] at hCount
    omega
  · intro z
    apply le_trans _ (hCap₀ z)
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter (fun E => z ∈ E) hB₀)
  · intro T hT
    change (rankFourFacetParents B T).card < t
    by_cases hNonempty : (rankFourFacetParents B T).Nonempty
    · obtain ⟨E,hE⟩ := hNonempty
      have hParts := Finset.mem_filter.mp hE
      have hTU : T ⊆ U := hParts.2.trans (hGroundB E hParts.1)
      have hTW : T ∈ W.powersetCard 3 := Finset.mem_powersetCard.mpr ⟨hTU.trans hUW,hT⟩
      have hTX : Disjoint T X := by
        apply Finset.disjoint_left.mpr
        intro x hxT hxX
        exact (Finset.mem_sdiff.mp (hTU hxT)).2 (Finset.mem_union_right _ hxX)
      have hLow := hTriple T hTW hTX
      rw [← facet_completions_card_eq_parent_edges B U T hUniB hGroundB hT]
      apply lt_of_le_of_lt _ hLow
      apply Finset.card_le_card
      intro z hz
      have h := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hUW h.1, hB₀ h.2⟩
    · simpa only [Finset.not_nonempty_iff_eq_empty.mp hNonempty, Finset.card_empty] using ht

end JSP523.Rank4
