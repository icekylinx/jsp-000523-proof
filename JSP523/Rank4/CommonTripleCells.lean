import JSP523.Counting.IntersectingTripleCenter
import JSP523.Counting.PrefixCommonSystem
import JSP523.Counting.ThreeDisjointTails

/-!
# Common triple cells at rank four

These are the cells `J_{ab}` in `paper/proof.pdf`, §III.A.1.
The forbidden switch and the nine-pair covering lemma provide a center
for every sufficiently large cell.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- The actual common triples completing both distinct vertices to edges. -/
def commonTripleCell (H : Family α) (V : Edge α) (a b : α) : Family α :=
  (V.powersetCard 3).filter fun T =>
    Disjoint T ({a, b} : Edge α) ∧ insert a T ∈ H ∧ insert b T ∈ H

/-- The manuscript's `J_{ab}` has no explicit tail-disjointness condition. -/
def rawCommonTripleCell (H : Family α) (V : Edge α) (a b : α) : Family α :=
  (V.powersetCard 3).filter fun T => insert a T ∈ H ∧ insert b T ∈ H

theorem mem_commonTripleCell
    {H : Family α} {V T : Edge α} {a b : α} :
    T ∈ commonTripleCell H V a b ↔
      T ⊆ V ∧ T.card = 3 ∧ Disjoint T ({a, b} : Edge α) ∧
        insert a T ∈ H ∧ insert b T ∈ H := by
  simp only [commonTripleCell, Finset.mem_filter, Finset.mem_powersetCard]
  tauto

/-- In a uniform four-family, the two completions force the tail to avoid
both completion vertices, so the explicit and raw cells agree. -/
theorem rawCommonTripleCell_eq_commonTripleCell
    {H : Family α} {V : Edge α} {a b : α}
    (hU : Uniform 4 H) :
    rawCommonTripleCell H V a b = commonTripleCell H V a b := by
  ext T
  constructor
  · intro hT
    have hTraw := Finset.mem_filter.mp hT
    have hTcard : T.card = 3 := (Finset.mem_powersetCard.mp hTraw.1).2
    have hAcard : (insert a T).card = 4 := hU hTraw.2.1
    have hBcard : (insert b T).card = 4 := hU hTraw.2.2
    have ha : a ∉ T := by
      intro ha
      simp [Finset.insert_eq_of_mem ha, hTcard] at hAcard
    have hb : b ∉ T := by
      intro hb
      simp [Finset.insert_eq_of_mem hb, hTcard] at hBcard
    apply Finset.mem_filter.mpr
    refine ⟨hTraw.1, ?_, hTraw.2.1, hTraw.2.2⟩
    apply Finset.disjoint_left.mpr
    intro x hxT hxAB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxAB
    rcases hxAB with rfl | rfl
    · exact ha hxT
    · exact hb hxT
  · intro hT
    have h := Finset.mem_filter.mp hT
    exact Finset.mem_filter.mpr ⟨h.1, h.2.2⟩

/-- The rank-four common cell is the general disjoint-prefix system
specialized to singleton prefixes. -/
theorem commonTripleCell_eq_commonPrefixTriples
    (H : Family α) (V : Edge α) (a b : α) :
    commonTripleCell H V a b =
      commonPrefixTriples H V ({a} : Edge α) ({b} : Edge α) := by
  ext T
  simp [mem_commonTripleCell, mem_commonPrefixTriples, Finset.singleton_union]

theorem commonTripleCell_intersecting
    {H : Family α} {V : Edge α} {a b : α}
    (hH : Admissible H) (hab : a ≠ b) :
    PairwiseIntersecting (commonTripleCell H V a b) := by
  rw [commonTripleCell_eq_commonPrefixTriples]
  apply common_prefix_triples_intersecting hH
  · simp
  · simp
  · simpa using (Finset.disjoint_singleton.mpr (by simpa using hab))

/-- Actual completions of a facet inside the specified ground set. -/
def facetCompletions (H : Family α) (V T : Edge α) : Finset α :=
  V.filter fun x => insert x T ∈ H

/-- Pair degree in `J_{ab}` is bounded by the degree of the actual facet
`aP`.  The map removes the fixed pair `P` from each common triple; its
singleton remainder records a different completion of `aP`. -/
theorem commonTripleCell_pairDegree_le_facetCompletions
    (H : Family α) (V : Edge α) (a b : α) (P : Edge α)
    (hPcard : P.card = 2) :
    triplePairDegree (commonTripleCell H V a b) P ≤
      (facetCompletions H V (insert a P)).card := by
  classical
  let C := (commonTripleCell H V a b).filter fun T => P ⊆ T
  let f : Edge α → Edge α := fun T => T \ P
  let W := (facetCompletions H V (insert a P)).image
    (fun x => ({x} : Edge α))
  have hmap : ∀ T ∈ C, f T ∈ W := by
    intro T hTC
    have hTC' := Finset.mem_filter.mp hTC
    have hT := (mem_commonTripleCell.mp hTC'.1)
    have hPT : P ⊆ T := hTC'.2
    have hdiffCard : (T \ P).card = 1 := by
      rw [Finset.card_sdiff_of_subset hPT]
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hdiffCard
    have hxDiff : x ∈ T \ P := by simp [hx]
    have hxV : x ∈ V := hT.1 (Finset.mem_sdiff.mp hxDiff).1
    have hTeq : T = insert x P := by
      have hUnion := Finset.union_sdiff_of_subset hPT
      rw [hx] at hUnion
      rw [Finset.union_singleton] at hUnion
      exact hUnion.symm
    have hEdge : insert x (insert a P) ∈ H := by
      rw [hTeq] at hT
      simpa only [Finset.insert_comm] using hT.2.2.2.1
    change T \ P ∈ W
    rw [hx]
    exact Finset.mem_image.mpr
      ⟨x, Finset.mem_filter.mpr ⟨hxV, hEdge⟩, rfl⟩
  have hinj : Set.InjOn f (↑C : Set (Edge α)) := by
    intro T hT U hU hEq
    have hPT : P ⊆ T := (Finset.mem_filter.mp hT).2
    have hPU : P ⊆ U := (Finset.mem_filter.mp hU).2
    have hTunion := Finset.union_sdiff_of_subset hPT
    have hUunion := Finset.union_sdiff_of_subset hPU
    change T \ P = U \ P at hEq
    calc
      T = P ∪ (T \ P) := hTunion.symm
      _ = P ∪ (U \ P) := by rw [hEq]
      _ = U := hUunion
  have hcard : C.card ≤ W.card :=
    Finset.card_le_card_of_injOn f hmap hinj
  have hW : W.card ≤ (facetCompletions H V (insert a P)).card :=
    Finset.card_image_le
  exact hcard.trans hW

/-- A uniform bound on actual facet completions supplies the pair-degree
assumption in the nine-pair lemma. -/
theorem commonTripleCell_pairDegree_le_of_facet_cap
    {H : Family α} {V : Edge α} {a b : α} {D : ℕ}
    (hCap : ∀ T : Edge α, T.card = 3 →
      (facetCompletions H V T).card ≤ D)
    (P : Edge α) (hPcard : P.card = 2) :
    triplePairDegree (commonTripleCell H V a b) P ≤ D := by
  by_cases haP : a ∈ P
  · have hzero : triplePairDegree (commonTripleCell H V a b) P = 0 := by
      apply Finset.card_eq_zero.mpr
      ext T
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hT, hPT⟩
        have hcell := (mem_commonTripleCell.mp hT)
        have haT : a ∈ T := hPT haP
        exact False.elim
          ((Finset.disjoint_left.mp hcell.2.2.1) haT (by simp))
      · simp
    omega
  · have hFacetCard : (insert a P).card = 3 := by
      rw [Finset.card_insert_of_notMem haP, hPcard]
    exact (commonTripleCell_pairDegree_le_facetCompletions
      H V a b P hPcard).trans (hCap (insert a P) hFacetCard)

/-- The large rank-four common cell has a center under the manuscript's
actual maximum facet-degree hypothesis. -/
theorem commonTripleCell_large_has_center_of_facet_cap
    {H : Family α} {V : Edge α} {a b : α} {D : ℕ}
    (hH : Admissible H) (hab : a ≠ b)
    (hCap : ∀ T : Edge α, T.card = 3 →
      (facetCompletions H V T).card ≤ D)
    (hLarge : 9 * D < (commonTripleCell H V a b).card) :
    ∃ z : α, ∀ ⦃T : Edge α⦄,
      T ∈ commonTripleCell H V a b → z ∈ T := by
  apply intersecting_triples_large_has_center
  · intro T hT
    exact (mem_commonTripleCell.mp hT).2.1
  · exact commonTripleCell_intersecting hH hab
  · exact commonTripleCell_pairDegree_le_of_facet_cap hCap
  · exact hLarge

/-- A bounded pair degree forces a common center after the weak cells
have been cleared. -/
theorem commonTripleCell_large_has_center
    {H : Family α} {V : Edge α} {a b : α} {D : ℕ}
    (hH : Admissible H) (hab : a ≠ b)
    (hD : ∀ P : Edge α, P.card = 2 →
      triplePairDegree (commonTripleCell H V a b) P ≤ D)
    (hLarge : 9 * D < (commonTripleCell H V a b).card) :
    ∃ z : α, ∀ ⦃T : Edge α⦄,
      T ∈ commonTripleCell H V a b → z ∈ T := by
  apply intersecting_triples_large_has_center
  · intro T hT
    exact (mem_commonTripleCell.mp hT).2.1
  · exact commonTripleCell_intersecting hH hab
  · exact hD
  · exact hLarge

/-- Once a cell is larger than its pair-degree cap, its center is unique. -/
theorem commonTripleCell_center_unique
    {H : Family α} {V : Edge α} {a b x y : α} {D : ℕ}
    (hD : ∀ P : Edge α, P.card = 2 →
      triplePairDegree (commonTripleCell H V a b) P ≤ D)
    (hLarge : D < (commonTripleCell H V a b).card)
    (hx : ∀ ⦃T : Edge α⦄,
      T ∈ commonTripleCell H V a b → x ∈ T)
    (hy : ∀ ⦃T : Edge α⦄,
      T ∈ commonTripleCell H V a b → y ∈ T) : x = y := by
  by_contra hxy
  have hpair : ({x, y} : Edge α).card = 2 := Finset.card_pair hxy
  have hsub : commonTripleCell H V a b ⊆
      (commonTripleCell H V a b).filter
        (fun T => ({x, y} : Edge α) ⊆ T) := by
    intro T hT
    apply Finset.mem_filter.mpr
    refine ⟨hT, ?_⟩
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx hT
    · exact hy hT
  have hcard := Finset.card_le_card hsub
  have hbound := hD {x, y} hpair
  unfold triplePairDegree at hbound
  omega

/-- The three parent matching witnesses in §III.B.4 force the label of a
used completion pair into a star-layer pair.  Witnesses live in the parent
family `H`; no assertion about later retained subfamilies is needed. -/
theorem three_parent_tails_force_label_in_pair
    {H : Family α} {V P R S T : Edge α}
    {a b c z : α}
    (hH : Admissible H) (hab : a ≠ b) (hcz : c ≠ z)
    (hPcard : P.card = 2)
    (hRS : Disjoint R S) (hRT : Disjoint R T)
    (hST : Disjoint S T)
    (hcR : c ∉ R) (hcS : c ∉ S) (hcT : c ∉ T)
    (hStar : insert c P ∈ commonTripleCell H V a b)
    (hR : insert z R ∈ commonTripleCell H V a b)
    (hS : insert z S ∈ commonTripleCell H V a b)
    (hT : insert z T ∈ commonTripleCell H V a b) :
    z ∈ P := by
  by_contra hzP
  have hI := commonTripleCell_intersecting (V := V) hH hab
  have hContradict (Q : Edge α)
      (hcQ : c ∉ Q)
      (hPQ : Disjoint P Q)
      (hQ : insert z Q ∈ commonTripleCell H V a b) : False := by
    have hDisj : Disjoint (insert c P) (insert z Q) := by
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      rcases Finset.mem_insert.mp hx with rfl | hxP
      · rcases Finset.mem_insert.mp hx' with hEq | hcQmem
        · exact hcz hEq
        · exact hcQ hcQmem
      · rcases Finset.mem_insert.mp hx' with hEq | hxQ
        · exact hzP (hEq ▸ hxP)
        · exact (Finset.disjoint_left.mp hPQ) hxP hxQ
    have hNe : insert c P ≠ insert z Q := by
      intro hEq
      have hc : c ∈ insert z Q := hEq ▸ (Finset.mem_insert_self c P)
      rcases Finset.mem_insert.mp hc with hEqCZ | hcQmem
      · exact hcz hEqCZ
      · exact hcQ hcQmem
    have hMeet := hI hStar hQ hNe
    have hEmpty := Finset.disjoint_iff_inter_eq_empty.mp hDisj
    rw [hEmpty] at hMeet
    simp at hMeet
  rcases three_disjoint_tails_one_avoids_pair hPcard hRS hRT hST with
    hPR | hPS | hPT
  · exact hContradict R hcR hPR hR
  · exact hContradict S hcS hPS hS
  · exact hContradict T hcT hPT hT

end JSP523.Rank4
