import JSP523.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-!
# Linear intersecting triple systems

This module formalizes the finite `<= 7` lemma used in the non-star branch of
JSP-000523's common-prefix argument.

The proof is organized for reuse:

1. in a non-star linear intersecting 3-graph every vertex has degree at most 3;
2. after fixing one edge `E`, every other edge has a unique one-point
   intersection with `E`;
3. every such one-point fiber has size at most 2;
4. the bounded-fiber cardinality lemma gives `|H \ {E}| <= 2 * 3`.
-/

namespace JSP523

section LinearTriple

variable {α : Type*} [DecidableEq α]

/-- Distinct edges of `H` meet. -/
def PairwiseIntersecting (H : Family α) : Prop :=
  ∀ ⦃E F : Edge α⦄, E ∈ H → F ∈ H → E ≠ F → (E ∩ F).Nonempty

/-- Distinct edges of `H` meet in at most one vertex. -/
def LinearFamily (H : Family α) : Prop :=
  ∀ ⦃E F : Edge α⦄, E ∈ H → F ∈ H → E ≠ F → (E ∩ F).card ≤ 1

/-- No vertex belongs to every edge of `H`. -/
def NoGlobalCenter (H : Family α) : Prop :=
  ∀ x : α, ∃ E : Edge α, E ∈ H ∧ x ∉ E

/-- The member edges of `H` containing `x`. -/
def vertexEdges (H : Family α) (x : α) : Family α :=
  H.filter (fun E => x ∈ E)

@[simp] theorem mem_vertex_edges {H : Family α} {x : α} {E : Edge α} :
    E ∈ vertexEdges H x ↔ E ∈ H ∧ x ∈ E := by
  simp [vertexEdges]

/-- In a linear intersecting family, two distinct edges meet in exactly one point. -/
theorem intersection_card_eq_one
    {H : Family α} {E F : Edge α}
    (hI : PairwiseIntersecting H)
    (hL : LinearFamily H)
    (hE : E ∈ H) (hF : F ∈ H) (hne : E ≠ F) :
    (E ∩ F).card = 1 := by
  apply Nat.le_antisymm
  · exact hL hE hF hne
  · exact Finset.one_le_card.mpr (hI hE hF hne)

/--
In a non-star linear intersecting 3-graph, every vertex belongs to at most
three edges.
-/
theorem vertex_degree_le_three
    {H : Family α}
    (hU : Uniform 3 H)
    (hI : PairwiseIntersecting H)
    (hL : LinearFamily H)
    (hN : NoGlobalCenter H)
    (x : α) :
    (vertexEdges H x).card ≤ 3 := by
  obtain ⟨W, hWH, hxW⟩ := hN x
  let f : Edge α → Edge α := fun F => F ∩ W
  have hmap : Set.MapsTo f (↑(vertexEdges H x) : Set (Edge α))
      (↑(W.powersetCard 1) : Set (Edge α)) := by
    intro F hF
    have hFH : F ∈ H := (mem_vertex_edges.mp hF).1
    have hxF : x ∈ F := (mem_vertex_edges.mp hF).2
    have hFW : F ≠ W := by
      intro hEq
      apply hxW
      rw [← hEq]
      exact hxF
    have hcard : (F ∩ W).card = 1 :=
      intersection_card_eq_one hI hL hFH hWH hFW
    exact Finset.mem_powersetCard.mpr ⟨by
      intro y hy
      exact (Finset.mem_inter.mp hy).2, hcard⟩
  have hinj : Set.InjOn f (↑(vertexEdges H x) : Set (Edge α)) := by
    intro F hF G hG hEq
    by_contra hFG
    have hFH : F ∈ H := (mem_vertex_edges.mp hF).1
    have hGH : G ∈ H := (mem_vertex_edges.mp hG).1
    have hxF : x ∈ F := (mem_vertex_edges.mp hF).2
    have hxG : x ∈ G := (mem_vertex_edges.mp hG).2
    have hFW : F ≠ W := by
      intro hEqFW
      apply hxW
      rw [← hEqFW]
      exact hxF
    have hFWnon : (F ∩ W).Nonempty := hI hFH hWH hFW
    obtain ⟨y, hyFW⟩ := hFWnon
    have hEqInter : F ∩ W = G ∩ W := by
      simpa [f] using hEq
    have hyGW : y ∈ G ∩ W := by
      rw [← hEqInter]
      exact hyFW
    have hyF : y ∈ F := (Finset.mem_inter.mp hyFW).1
    have hyW : y ∈ W := (Finset.mem_inter.mp hyFW).2
    have hyG : y ∈ G := (Finset.mem_inter.mp hyGW).1
    have hxy : x ≠ y := by
      intro hxy
      apply hxW
      rw [hxy]
      exact hyW
    have hpair : {x, y} ⊆ F ∩ G := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz
      · subst z
        exact Finset.mem_inter.mpr ⟨hxF, hxG⟩
      · subst z
        exact Finset.mem_inter.mpr ⟨hyF, hyG⟩
    have htwo : 2 ≤ (F ∩ G).card := by
      have hc := Finset.card_le_card hpair
      rw [Finset.card_pair hxy] at hc
      exact hc
    have hone : (F ∩ G).card ≤ 1 := hL hFH hGH hFG
    omega
  have hdeg : (vertexEdges H x).card ≤ (W.powersetCard 1).card :=
    Finset.card_le_card_of_injOn f hmap hinj
  calc
    (vertexEdges H x).card ≤ (W.powersetCard 1).card := hdeg
    _ = W.card.choose 1 := Finset.card_powersetCard 1 W
    _ = W.card := Nat.choose_one_right W.card
    _ = 3 := hU hWH

/--
The non-star linear intersecting triple-system bound.  This is the finite
`<= 7` statement used by the common-prefix theorem in the `r >= 5` closure.
-/
theorem linear_intersecting_triples_card_le_seven
    {H : Family α}
    (hU : Uniform 3 H)
    (hI : PairwiseIntersecting H)
    (hL : LinearFamily H)
    (hN : NoGlobalCenter H) :
    H.card ≤ 7 := by
  by_cases hH : H.Nonempty
  · obtain ⟨E, hEH⟩ := hH
    let g : Edge α → Edge α := fun F => F ∩ E
    have hmap : ∀ F ∈ H.erase E, g F ∈ E.powersetCard 1 := by
      intro F hFS
      have hFH : F ∈ H := Finset.mem_of_mem_erase hFS
      have hFE : F ≠ E := Finset.ne_of_mem_erase hFS
      have hcard : (F ∩ E).card = 1 :=
        intersection_card_eq_one hI hL hFH hEH hFE
      exact Finset.mem_powersetCard.mpr ⟨by
        intro y hy
        exact (Finset.mem_inter.mp hy).2, hcard⟩
    have hfiber : ∀ b ∈ E.powersetCard 1,
        {F ∈ H.erase E | g F = b}.card ≤ 2 := by
      intro b hb
      have hbsub : b ⊆ E := (Finset.mem_powersetCard.mp hb).1
      have hbcard : b.card = 1 := (Finset.mem_powersetCard.mp hb).2
      obtain ⟨x, hbEq⟩ := Finset.card_eq_one.mp hbcard
      have hxb : x ∈ b := by simp [hbEq]
      have hxE : x ∈ E := hbsub hxb
      have hEvert : E ∈ vertexEdges H x := mem_vertex_edges.mpr ⟨hEH, hxE⟩
      have hdeg : (vertexEdges H x).card ≤ 3 :=
        vertex_degree_le_three hU hI hL hN x
      have herase : ((vertexEdges H x).erase E).card ≤ 2 := by
        have hadd := Finset.card_erase_add_one hEvert
        omega
      have hsub : {F ∈ H.erase E | g F = b} ⊆ (vertexEdges H x).erase E := by
        intro F hF
        have hfilter := Finset.mem_filter.mp hF
        have hFS : F ∈ H.erase E := hfilter.1
        have hg : g F = b := hfilter.2
        have hFH : F ∈ H := Finset.mem_of_mem_erase hFS
        have hFne : F ≠ E := Finset.ne_of_mem_erase hFS
        have hxInter : x ∈ F ∩ E := by
          change x ∈ g F
          rw [hg]
          exact hxb
        have hxF : x ∈ F := (Finset.mem_inter.mp hxInter).1
        exact Finset.mem_erase.mpr ⟨hFne, mem_vertex_edges.mpr ⟨hFH, hxF⟩⟩
      exact (Finset.card_le_card hsub).trans herase
    have hSix : (H.erase E).card ≤ 6 := by
      have hBound :
          (H.erase E).card ≤ 2 * (E.powersetCard 1).card :=
        Finset.card_le_mul_card_image_of_maps_to hmap 2 hfiber
      have hEcard : E.card = 3 := hU hEH
      calc
        (H.erase E).card ≤ 2 * (E.powersetCard 1).card := hBound
        _ = 2 * E.card.choose 1 := by rw [Finset.card_powersetCard]
        _ = 2 * E.card := by rw [Nat.choose_one_right]
        _ = 6 := by rw [hEcard]
    have hadd := Finset.card_erase_add_one hEH
    omega
  · have hEmpty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    simp [hEmpty]

/-- Every linear intersecting triple system is either a star or has at most seven edges. -/
theorem linear_intersecting_triples_star_or_small
    {H : Family α}
    (hU : Uniform 3 H)
    (hI : PairwiseIntersecting H)
    (hL : LinearFamily H) :
    (∃ x : α, ∀ ⦃E : Edge α⦄, E ∈ H → x ∈ E) ∨ H.card ≤ 7 := by
  classical
  by_cases hStar : ∃ x : α, ∀ ⦃E : Edge α⦄, E ∈ H → x ∈ E
  · exact Or.inl hStar
  · right
    apply linear_intersecting_triples_card_le_seven hU hI hL
    intro x
    by_contra hx
    have hall : ∀ ⦃E : Edge α⦄, E ∈ H → x ∈ E := by
      intro E hEH
      by_contra hxE
      exact hx ⟨E, hEH, hxE⟩
    exact hStar ⟨x, hall⟩

end LinearTriple

end JSP523
