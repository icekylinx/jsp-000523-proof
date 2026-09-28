import JSP523.Rank3.CommonLinkIntersecting
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# The actual rank-three common-link incidence count

For a base pair `p`, the completion vertices are precisely the points of the
ambient set outside `p` whose singleton extensions belong to `H`.  A pair of
such vertices is a cell of the actual common link.  Counting incidences by
cells and by base pairs gives an exact identity, without a structural payment
assumption or a free cardinal parameter.
-/

namespace JSP523.Rank3

section Incidence

variable {α : Type*} [DecidableEq α]

/-- The actual set of vertices extending `p` to an edge of `H`. -/
def completionVertices (H : Family α) (V p : Edge α) : Edge α := by
  exact V.filter (fun x => x ∉ p ∧ p ∪ {x} ∈ H)

/-- Unordered cells formed by two distinct completion vertices of `p`. -/
def completionCells (H : Family α) (V p : Edge α) : Family α :=
  (completionVertices H V p).powersetCard 2

theorem completion_vertices_subset_ground (H : Family α) (V p : Edge α) :
    completionVertices H V p ⊆ V := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

theorem completion_cells_subset_ground (H : Family α) (V p : Edge α) :
    completionCells H V p ⊆ V.powersetCard 2 := by
  intro q hq
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hq
  exact Finset.mem_powersetCard.mpr
    ⟨hsub.trans (completion_vertices_subset_ground H V p), hcard⟩

/-- A cell and a base pair are incident exactly when the cell consists of
    two actual completion vertices for that base pair. -/
theorem mem_common_link_iff_mem_completion_cells
    (H : Family α) (V q p : Edge α)
    (hq : q ∈ V.powersetCard 2)
    (hp : p ∈ V.powersetCard 2) :
    p ∈ commonLink H V q ↔ q ∈ completionCells H V p := by
  constructor
  · intro hlink
    obtain ⟨_, x, hx, y, hy, hxy, hdis, hpx, hpy⟩ :=
      Finset.mem_filter.mp hlink
    have hqcard : q.card = 2 := (Finset.mem_powersetCard.mp hq).2
    have hqsub : q ⊆ V := (Finset.mem_powersetCard.mp hq).1
    have hpair : ({x, y} : Edge α) = q := by
      apply Finset.eq_of_subset_of_card_le
      · intro t ht
        rcases Finset.mem_insert.mp ht with htx | hty
        · exact htx ▸ hx
        · exact (Finset.mem_singleton.mp hty) ▸ hy
      · rw [Finset.card_pair hxy, hqcard]
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro t ht
      have ht' : t ∈ ({x, y} : Edge α) := hpair.symm ▸ ht
      rcases Finset.mem_insert.mp ht' with htx | hty
      · subst t
        apply Finset.mem_filter.mpr
        refine ⟨hqsub hx, ?_, hpx⟩
        intro hxp
        exact (Finset.disjoint_left.mp hdis) hxp hx
      · have hty' : t = y := Finset.mem_singleton.mp hty
        subst t
        apply Finset.mem_filter.mpr
        refine ⟨hqsub hy, ?_, hpy⟩
        intro hyp
        exact (Finset.disjoint_left.mp hdis) hyp hy
    · exact hqcard
  · intro hcell
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hcell
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    have hx := Finset.mem_filter.mp (hsub (by simp : x ∈ ({x, y} : Edge α)))
    have hy := Finset.mem_filter.mp (hsub (by simp : y ∈ ({x, y} : Edge α)))
    obtain ⟨_, hxp, hpx⟩ := hx
    obtain ⟨_, hyp, hpy⟩ := hy
    have hdis : Disjoint p ({x, y} : Edge α) := by
      apply Finset.disjoint_left.mpr
      intro t htp htq
      rcases Finset.mem_insert.mp htq with htx | hty
      · exact hxp (htx ▸ htp)
      · exact hyp ((Finset.mem_singleton.mp hty) ▸ htp)
    exact Finset.mem_filter.mpr
      ⟨hp, ⟨x, by simp, y, by simp, hxy, hdis, hpx, hpy⟩⟩

/-- Every base pair in an actual common link belongs to the actual pair
    support, since at least one of its extensions is an edge. -/
theorem common_link_subset_used_pairs
    (H : Family α) (V q : Edge α) :
    commonLink H V q ⊆ usedPairs H V := by
  intro p hp
  obtain ⟨hpV, x, _, _, _, _, _, hpx, _⟩ :=
    Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨hpV, ⟨p ∪ {x}, hpx, ?_⟩⟩
  intro t ht
  exact Finset.mem_union.mpr (Or.inl ht)

/-- An actual completion cell has a nonempty common link and hence lies in
    the cell support used in the finite rank-three ledger. -/
theorem completion_cells_subset_used_cells
    (H : Family α) (V p : Edge α)
    (hp : p ∈ V.powersetCard 2) :
    completionCells H V p ⊆ usedCells H V := by
  intro q hq
  have hqV := completion_cells_subset_ground H V p hq
  have hpLink :=
    (mem_common_link_iff_mem_completion_cells H V q p hqV hp).mpr hq
  exact (mem_used_cells_iff_common_link_nonempty H V q).mpr
    ⟨hqV, ⟨p, hpLink⟩⟩

/-- A common link indexed by any ambient cell is intersecting when `H` is
    admissible.  This removes the `{x,y}` presentation from the local result. -/
theorem common_link_intersecting_of_ground_cell
    {H : Family α} {V q p t : Edge α}
    (hH : Admissible H)
    (hq : q ∈ V.powersetCard 2)
    (hp : p ∈ commonLink H V q)
    (ht : t ∈ commonLink H V q) :
    ¬ Disjoint p t := by
  obtain ⟨x, y, hxy, rfl⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hq).2
  exact common_link_pair_intersecting hH hxy hp ht

/-- A subset of a finite index set can be counted by its membership
    indicators.  This local elementary lemma supplies both sides of the
    incidence count with the same normalization. -/
private theorem card_subset_as_indicator_sum
    {β : Type*} [DecidableEq β] (s t : Finset β) (hsub : t ⊆ s) :
    t.card = ∑ x ∈ s, if x ∈ t then (1 : ℕ) else 0 := by
  have hfilter : s.filter (fun x => x ∈ t) = t := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).2
    · intro hx
      exact Finset.mem_filter.mpr ⟨hsub hx, hx⟩
  calc
    t.card = (s.filter (fun x => x ∈ t)).card :=
      congrArg Finset.card hfilter.symm
    _ = ∑ x ∈ s, if x ∈ t then (1 : ℕ) else 0 :=
      Finset.card_filter (fun x => x ∈ t) s

/-- Exact finite double count of common-link incidences.  Its right side
    uses the real extension degrees of base pairs, with no abstract incidence
    cardinal standing in for the family. -/
theorem actual_common_link_double_count
    (H : Family α) (V : Edge α) :
    (∑ q ∈ V.powersetCard 2, (commonLink H V q).card) =
      ∑ p ∈ V.powersetCard 2,
        (completionVertices H V p).card.choose 2 := by
  classical
  let P : Family α := V.powersetCard 2
  calc
    (∑ q ∈ P, (commonLink H V q).card) =
        ∑ q ∈ P, ∑ p ∈ P,
          if p ∈ commonLink H V q then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      exact card_subset_as_indicator_sum P (commonLink H V q)
        (fun p hp => (Finset.mem_filter.mp hp).1)
    _ = ∑ p ∈ P, ∑ q ∈ P,
          if p ∈ commonLink H V q then (1 : ℕ) else 0 :=
      Finset.sum_comm
    _ = ∑ p ∈ P, ∑ q ∈ P,
          if q ∈ completionCells H V p then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      exact if_congr
        (mem_common_link_iff_mem_completion_cells H V q p hq hp) rfl rfl
    _ = ∑ p ∈ P, (completionCells H V p).card := by
      apply Finset.sum_congr rfl
      intro p _
      exact (card_subset_as_indicator_sum P (completionCells H V p)
        (completion_cells_subset_ground H V p)).symm
    _ = ∑ p ∈ P,
          (completionVertices H V p).card.choose 2 := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.card_powersetCard 2 (completionVertices H V p)

/-- The actual cell support is the union of completion-cell families over
    all ambient base pairs. -/
theorem used_cells_eq_bi_union_completion_cells
    (H : Family α) (V : Edge α) :
    usedCells H V =
      (V.powersetCard 2).biUnion (fun p => completionCells H V p) := by
  ext q
  constructor
  · intro hq
    obtain ⟨hqV, ⟨p, hpLink⟩⟩ :=
      (mem_used_cells_iff_common_link_nonempty H V q).mp hq
    have hpV : p ∈ V.powersetCard 2 :=
      (Finset.mem_filter.mp hpLink).1
    exact Finset.mem_biUnion.mpr
      ⟨p, hpV,
        (mem_common_link_iff_mem_completion_cells H V q p hqV hpV).mp hpLink⟩
  · intro hq
    obtain ⟨p, hpV, hcell⟩ := Finset.mem_biUnion.mp hq
    exact completion_cells_subset_used_cells H V p hpV hcell

/-- The size of the actual cell support is bounded by the true total number
    of common-link incidences.  Cells with several base completions may be
    counted more than once on the right. -/
theorem used_cells_card_le_common_link_incidence_count
    (H : Family α) (V : Edge α) :
    (usedCells H V).card ≤
      ∑ q ∈ V.powersetCard 2, (commonLink H V q).card := by
  calc
    (usedCells H V).card =
        ((V.powersetCard 2).biUnion
          (fun p => completionCells H V p)).card := by
      rw [used_cells_eq_bi_union_completion_cells]
    _ ≤ ∑ p ∈ V.powersetCard 2, (completionCells H V p).card :=
      Finset.card_biUnion_le
    _ = ∑ q ∈ V.powersetCard 2, (commonLink H V q).card := by
      rw [actual_common_link_double_count]
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.card_powersetCard 2 (completionVertices H V p)

/-- Each individual common link is contained in the actual pair support. -/
theorem common_link_card_le_used_pairs_card
    (H : Family α) (V q : Edge α) :
    (commonLink H V q).card ≤ (usedPairs H V).card :=
  Finset.card_le_card (common_link_subset_used_pairs H V q)

end Incidence

end JSP523.Rank3
