import JSP523.Rank4.PreprocessCellMoment
import JSP523.Rank4.GlobalDegreeTail

/-! # The improved cross moment for geometric regularization -/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- A facet cap bounds the star alternative in each distinct-completion
graph by that same cap, independently of the number of vertices. -/
theorem cross_completion_pair_graph_card_le_facet_cap
    {H : Family α} {V W : Edge α} {c d x y : α} {R : ℕ}
    (hH : Admissible H) (hUniform : Uniform 4 H)
    (hGround : ∀ E ∈ H, E ⊆ W)
    (hCap : ∀ T : Edge α, T.card = 3 → (facetCompletions H W T).card ≤ R)
    (hcd : c ≠ d) (hcV : c ∉ V) (hdV : d ∉ V)
    (hxV : x ∈ V) (hyV : y ∈ V) (hxy : x ≠ y) :
    (crossCompletionPairGraph H V c d x y).card ≤ max R 3 := by
  classical
  rcases cross_completion_pair_graph_star_or_small hH hcd hcV hdV hxV hyV hxy with
    ⟨z, hz⟩ | hSmall
  · let G := crossCompletionPairGraph H V c d x y
    by_cases hG : G.Nonempty
    · obtain ⟨P, hP⟩ := hG
      have hPspec := Finset.mem_filter.mp hP
      have hzV : z ∈ V := (Finset.mem_powersetCard.mp hPspec.1).1 (hz P hP)
      have hcx : c ≠ x := fun h => hcV (h ▸ hxV)
      have hcz : c ≠ z := fun h => hcV (h ▸ hzV)
      have hOut (Q : Edge α) (hQ : Q ∈ G) : x ∉ Q := by
        have hs := Finset.mem_filter.mp hQ
        have h2 := (Finset.mem_powersetCard.mp hs.1).2
        have h3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs.2.1).1).2
        intro hxQ
        rw [Finset.insert_eq_of_mem hxQ] at h3
        omega
      have hxz : x ≠ z := fun h => hOut P hP (h ▸ hz P hP)
      have hTriple : ({c, x, z} : Edge α).card = 3 := by simp [hcx, hcz, hxz]
      have hMap : Set.MapsTo (fun Q => insert c (insert x Q)) (↑G : Set (Edge α))
          (↑(rankFourFacetParents H {c, x, z}) : Set (Edge α)) := by
        intro Q hQ
        have hs := Finset.mem_filter.mp hQ
        refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs.2.1).2, ?_⟩
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · simp
        · simp
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hz Q hQ))
      have hInj : (↑G : Set (Edge α)).InjOn (fun Q => insert c (insert x Q)) := by
        intro Q hQ S hS hEq
        have hRecover (A : Edge α) (hA : A ∈ G) :
            ((insert c (insert x A)).erase c).erase x = A := by
          have hs := Finset.mem_filter.mp hA
          have hcA : c ∉ A := fun hc => hcV ((Finset.mem_powersetCard.mp hs.1).1 hc)
          rw [Finset.erase_insert (by simp [hcx, hcA]), Finset.erase_insert (hOut A hA)]
        have he := congrArg (fun E : Edge α => (E.erase c).erase x) hEq
        simpa only [hRecover Q hQ, hRecover S hS] using he
      have hCount := Finset.card_le_card_of_injOn _ hMap hInj
      have hParents : (rankFourFacetParents H {c, x, z}).card ≤ R := by
        rw [← facet_completions_card_eq_parent_edges H W {c, x, z} hUniform hGround hTriple]
        exact hCap _ hTriple
      exact (hCount.trans hParents).trans (Nat.le_max_left _ _)
    · have hEmpty : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hG
      change G.card ≤ _
      simp [hEmpty]
  · exact hSmall.trans (Nat.le_max_right _ _)

/-- The cross moment used in the contraction step: with pair cap `M`
and facet cap `R`, its two parts cost `3 max(M,9R)` and `max(R,3)|V|²`.
Thus `M = R|W|` gives `O(R|W|²)`, the improvement needed in III.A.20. -/
theorem rank_four_star_cross_moment_le_degree_caps
    {H : Family α} {V W : Edge α} {c d : α} {M R : ℕ}
    (hH : Admissible H) (hUniform : Uniform 4 H)
    (hGround : ∀ E ∈ H, E ⊆ W) (hVW : V ⊆ W)
    (hPair : ∀ P : Edge α, P.card = 2 → rankFourPairDegree H P ≤ M)
    (hCap : ∀ T : Edge α, T.card = 3 → (facetCompletions H W T).card ≤ R)
    (hcd : c ≠ d) (hcV : c ∉ V) (hdV : d ∉ V) :
    (∑ P ∈ V.powersetCard 2,
      linkPairDegree (rankFourStarLink H V c) P *
        linkPairDegree (rankFourStarLink H V d) P) ≤
      3 * max M (9 * R) + max R 3 * V.card ^ 2 := by
  have hFacetV : ∀ T : Edge α, T.card = 3 → (facetCompletions H V T).card ≤ R := by
    intro T hT
    apply (Finset.card_le_card ?_).trans (hCap T hT)
    intro x hx
    exact Finset.mem_filter.mpr ⟨hVW (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
  have hCommon : rankFourStarLink H V c ∩ rankFourStarLink H V d ⊆
      commonTripleCell H V c d := by
    intro T hT
    have hc := Finset.mem_filter.mp (Finset.mem_inter.mp hT).1
    have hd := Finset.mem_filter.mp (Finset.mem_inter.mp hT).2
    have hTG := Finset.mem_powersetCard.mp hc.1
    apply mem_common_triple_cell.mpr
    refine ⟨hTG.1, hTG.2, ?_, hc.2, hd.2⟩
    apply Finset.disjoint_left.mpr
    intro z hz hzcd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzcd
    rcases hzcd with rfl | rfl
    · exact hcV (hTG.1 hz)
    · exact hdV (hTG.1 hz)
  have hJ := (Finset.card_le_card hCommon).trans
    (common_triple_cell_card_le_of_degree_caps hH hcd hPair hFacetV)
  have hDistinct : (∑ x ∈ V, ∑ y ∈ V.erase x,
      (crossCompletionPairGraph H V c d x y).card) ≤ max R 3 * V.card ^ 2 := by
    calc
      _ ≤ ∑ x ∈ V, ∑ _y ∈ V.erase x, max R 3 := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro y hy
        exact cross_completion_pair_graph_card_le_facet_cap hH hUniform hGround hCap
          hcd hcV hdV hx (Finset.mem_erase.mp hy).2 (Ne.symm (Finset.mem_erase.mp hy).1)
      _ ≤ ∑ _x ∈ V, V.card * max R 3 := by
        apply Finset.sum_le_sum
        intro x _
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact Nat.mul_le_mul_right _ (Finset.card_erase_le (s := V) (a := x))
      _ = max R 3 * V.card ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
        ring
  rw [rank_four_star_cross_moment_exact]
  exact Nat.add_le_add (Nat.mul_le_mul_left 3 hJ) hDistinct

/-- The actual owner-cleaning loss with the improved uniform cross moment. -/
theorem rank_four_star_owner_cleaning_loss_sq_bound_degree_caps
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {H : Family α} {V W : Edge α} (centers : ι → α) (M R : ℕ)
    (hH : Admissible H) (hUniform : Uniform 4 H)
    (hGround : ∀ E ∈ H, E ⊆ W) (hVW : V ⊆ W)
    (hPair : ∀ P : Edge α, P.card = 2 → rankFourPairDegree H P ≤ M)
    (hCap : ∀ T : Edge α, T.card = 3 → (facetCompletions H W T).card ≤ R)
    (hInjective : Function.Injective centers) (hOutside : ∀ i, centers i ∉ V) :
    (∑ i : ι,
      (rankFourStarLink H V (centers i) \ pairOwnerCleanedLink
        (fun j => rankFourStarLink H V (centers j))
        (maximumDegreePairOwner (fun j => rankFourStarLink H V (centers j))) i).card) ^ 2 ≤
      (V.powersetCard 2).card *
        ((Fintype.card ι * (Fintype.card ι - 1)) *
          (3 * max M (9 * R) + max R 3 * V.card ^ 2)) := by
  let L : ι → Family α := fun i => rankFourStarLink H V (centers i)
  have hLG : ∀ i T, T ∈ L i → T ∈ V.powersetCard 3 := by
    intro i T hT
    exact (Finset.mem_filter.mp hT).1
  have hOwner : ∀ P ∈ V.powersetCard 2, ∀ i,
      starLinkPairDegree L i P ≤ starLinkPairDegree L (maximumDegreePairOwner L P) P := by
    intro P _ i
    exact maximum_degree_pair_owner_spec L P i
  have hMoment : ∀ i j, i ≠ j →
      (∑ P ∈ V.powersetCard 2, starLinkPairDegree L i P * starLinkPairDegree L j P) ≤
        3 * max M (9 * R) + max R 3 * V.card ^ 2 := by
    intro i j hij
    have hcd : centers i ≠ centers j := fun h => hij (hInjective h)
    simpa [L, starLinkPairDegree, linkPairDegree] using
      rank_four_star_cross_moment_le_degree_caps hH hUniform hGround hVW hPair hCap
        hcd (hOutside i) (hOutside j)
  simpa [L] using maximum_pair_owner_cleaning_loss_sq_le_uniform_pair_moment
    L (maximumDegreePairOwner L) V hLG hOwner
      (3 * max M (9 * R) + max R 3 * V.card ^ 2) hMoment

end JSP523.Rank4
