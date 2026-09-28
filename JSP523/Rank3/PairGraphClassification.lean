import JSP523.Rank3.IncidenceDoubleCount
import Lean.Elab.Tactic.Omega

/-!
# Classification of the pair graphs occurring as common links

An intersecting family of two-element edges is a star or is contained in
one triangle.  The proof uses only the two-point cardinality of each edge
and the impossibility of disjoint edges.  Thus a common link with at least
four members has a unique center.
-/

namespace JSP523.Rank3

section PairGraphs

variable {α : Type*} [DecidableEq α]

/-- Two distinct points in a two-element finset determine it. -/
private theorem pair_eq_of_two_members
    {p : Edge α} {a b : α}
    (hp : p.card = 2) (ha : a ∈ p) (hb : b ∈ p)
    (hab : a ≠ b) : p = {a, b} := by
  have hsub : ({a, b} : Edge α) ⊆ p := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hxa | hxb
    · exact hxa ▸ ha
    · exact (Finset.mem_singleton.mp hxb) ▸ hb
  have hcard : p.card ≤ ({a, b} : Edge α).card := by
    rw [hp, Finset.card_pair hab]
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- Any edge meeting `{a,b}` contains one of its two vertices. -/
private theorem mem_of_meets_pair
    {W : Edge α} {a b : α}
    (hmeet : ¬ Disjoint W ({a, b} : Edge α)) :
    a ∈ W ∨ b ∈ W := by
  by_cases ha : a ∈ W
  · exact Or.inl ha
  · right
    by_contra hb
    apply hmeet
    apply Finset.disjoint_left.mpr
    intro x hxW hxpair
    rcases Finset.mem_insert.mp hxpair with hxa | hxb
    · exact ha (hxa ▸ hxW)
    · exact hb ((Finset.mem_singleton.mp hxb) ▸ hxW)

/-- A nonempty intersecting pair graph without a global center is contained
    in the three edges of a triangle. -/
theorem pair_graph_triangle_of_no_center
    (G : Family α)
    (hG : G.Nonempty)
    (hpair : ∀ p ∈ G, p.card = 2)
    (hmeet : ∀ p ∈ G, ∀ q ∈ G, ¬ Disjoint p q)
    (hnocenter : ¬ ∃ x : α, ∀ p ∈ G, x ∈ p) :
    ∃ a b c : α, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      G ⊆ ({({a, b} : Edge α), ({b, c} : Edge α),
        ({a, c} : Edge α)} : Family α) := by
  obtain ⟨E, hE⟩ := hG
  obtain ⟨a, b, hab, hEpair⟩ := Finset.card_eq_two.mp (hpair E hE)
  have habG : ({a, b} : Edge α) ∈ G := hEpair ▸ hE
  have hFexists : ∃ F ∈ G, a ∉ F := by
    by_contra h
    apply hnocenter
    refine ⟨a, ?_⟩
    intro F hFG
    by_contra haF
    exact h ⟨F, hFG, haF⟩
  obtain ⟨F, hFG, haF⟩ := hFexists
  have hbF : b ∈ F := by
    rcases mem_of_meets_pair (hmeet F hFG _ habG) with haF' | hbF'
    · exact False.elim (haF haF')
    · exact hbF'
  have hFcard : F.card = 2 := hpair F hFG
  have hFrest : (F.erase b).Nonempty := by
    apply Finset.card_pos.mp
    have hcardErase := Finset.card_erase_add_one hbF
    omega
  obtain ⟨c, hcErase⟩ := hFrest
  have hcb : c ≠ b := (Finset.mem_erase.mp hcErase).1
  have hcF : c ∈ F := (Finset.mem_erase.mp hcErase).2
  have hca : c ≠ a := by
    intro hca
    exact haF (hca ▸ hcF)
  have hbc : b ≠ c := Ne.symm hcb
  have hac : a ≠ c := Ne.symm hca
  have hFpair : F = {b, c} :=
    pair_eq_of_two_members hFcard hbF hcF hbc
  have hbcG : ({b, c} : Edge α) ∈ G := hFpair ▸ hFG
  have hTexists : ∃ T ∈ G, b ∉ T := by
    by_contra h
    apply hnocenter
    refine ⟨b, ?_⟩
    intro T hTG
    by_contra hbT
    exact h ⟨T, hTG, hbT⟩
  obtain ⟨T, hTG, hbT⟩ := hTexists
  have haT : a ∈ T := by
    rcases mem_of_meets_pair (hmeet T hTG _ habG) with haT' | hbT'
    · exact haT'
    · exact False.elim (hbT hbT')
  have hcT : c ∈ T := by
    rcases mem_of_meets_pair (hmeet T hTG _ hbcG) with hbT' | hcT'
    · exact False.elim (hbT hbT')
    · exact hcT'
  have hTpair : T = {a, c} :=
    pair_eq_of_two_members (hpair T hTG) haT hcT hac
  have hacG : ({a, c} : Edge α) ∈ G := hTpair ▸ hTG
  refine ⟨a, b, c, hab, hbc, hac, ?_⟩
  intro W hWG
  have hWcard : W.card = 2 := hpair W hWG
  have hWab : a ∈ W ∨ b ∈ W :=
    mem_of_meets_pair (hmeet W hWG _ habG)
  have hWbc : b ∈ W ∨ c ∈ W :=
    mem_of_meets_pair (hmeet W hWG _ hbcG)
  have hWac : a ∈ W ∨ c ∈ W :=
    mem_of_meets_pair (hmeet W hWG _ hacG)
  rcases hWab with haW | hbW
  · rcases hWbc with hbW | hcW
    · have heq : W = {a, b} :=
        pair_eq_of_two_members hWcard haW hbW hab
      simp [heq]
    · have heq : W = {a, c} :=
        pair_eq_of_two_members hWcard haW hcW hac
      simp [heq]
  · rcases hWac with haW | hcW
    · have heq : W = {a, b} :=
        pair_eq_of_two_members hWcard haW hbW hab
      simp [heq]
    · have heq : W = {b, c} :=
        pair_eq_of_two_members hWcard hbW hcW hbc
      simp [heq]

/-- The finite graph classification, including the empty family. -/
theorem intersecting_pair_graph_star_or_small
    (G : Family α)
    (hpair : ∀ p ∈ G, p.card = 2)
    (hmeet : ∀ p ∈ G, ∀ q ∈ G, ¬ Disjoint p q) :
    (∃ x : α, ∀ p ∈ G, x ∈ p) ∨ G.card ≤ 3 := by
  by_cases hG : G.Nonempty
  · by_cases hcenter : ∃ x : α, ∀ p ∈ G, x ∈ p
    · exact Or.inl hcenter
    · right
      obtain ⟨a, b, c, _, _, _, hsub⟩ :=
        pair_graph_triangle_of_no_center G hG hpair hmeet hcenter
      exact (Finset.card_le_card hsub).trans (Finset.card_le_three)
  · right
    have hEmpty : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hG
    simp [hEmpty]

/-- Two distinct universal vertices would force every two-element edge
    to be the same pair. -/
theorem pair_graph_center_unique_of_two_edges
    (G : Family α)
    (hpair : ∀ p ∈ G, p.card = 2)
    (hlarge : 1 < G.card)
    {a b : α}
    (ha : ∀ p ∈ G, a ∈ p)
    (hb : ∀ p ∈ G, b ∈ p) :
    a = b := by
  by_contra hab
  have hsub : G ⊆ ({({a, b} : Edge α)} : Family α) := by
    intro p hp
    have heq : p = {a, b} :=
      pair_eq_of_two_members (hpair p hp) (ha p hp) (hb p hp) hab
    exact Finset.mem_singleton.mpr heq
  have hbound := Finset.card_le_card hsub
  have hsingle : ({({a, b} : Edge α)} : Family α).card = 1 := by simp
  omega

/-- Every actual common link of an admissible triple family is a star or
    has at most three pair edges. -/
theorem actual_common_link_star_or_small
    {H : Family α} {V q : Edge α}
    (hH : Admissible H)
    (hq : q ∈ V.powersetCard 2) :
    (∃ x : α, ∀ p ∈ commonLink H V q, x ∈ p) ∨
      (commonLink H V q).card ≤ 3 := by
  apply intersecting_pair_graph_star_or_small (commonLink H V q)
  · intro p hp
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp t ht
    exact common_link_intersecting_of_ground_cell hH hq hp ht

/-- A common link with at least four edges has a unique star center. -/
theorem actual_common_link_unique_center_of_large
    {H : Family α} {V q : Edge α}
    (hH : Admissible H)
    (hq : q ∈ V.powersetCard 2)
    (hlarge : 3 < (commonLink H V q).card) :
    ∃ x : α, (∀ p ∈ commonLink H V q, x ∈ p) ∧
      ∀ y : α, (∀ p ∈ commonLink H V q, y ∈ p) → y = x := by
  rcases actual_common_link_star_or_small hH hq with ⟨x, hx⟩ | hsmall
  · refine ⟨x, hx, ?_⟩
    intro y hy
    have hpair : ∀ p ∈ commonLink H V q, p.card = 2 := by
      intro p hp
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
    have htwo : 1 < (commonLink H V q).card := by omega
    exact (pair_graph_center_unique_of_two_edges
      (commonLink H V q) hpair htwo hx hy).symm
  · omega

end PairGraphs

end JSP523.Rank3
