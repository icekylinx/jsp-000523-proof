import JSP523.Rank3.ActualSupports
import Lean.Elab.Tactic.Omega

/-!
# Admissibility forces each common pair-link to be intersecting

For distinct `x,y`, an oriented common link consists of pairs `p` disjoint
from `{x,y}` for which both `p ∪ {x}` and `p ∪ {y}` are edges.  Two disjoint
pairs in this link give the forbidden four-edge repeated-union rectangle.
No uniformity hypothesis is needed for this local implication.
-/

namespace JSP523.Rank3

section CommonLink

variable {α : Type*} [DecidableEq α]

/-- Adjoining distinct new vertices to disjoint pairs preserves
    disjointness of the two resulting edges. -/
private theorem disjoint_cross_edges
    {p q : Edge α} {u v : α}
    (hpq : Disjoint p q)
    (huq : u ∉ q) (hvp : v ∉ p) (huv : u ≠ v) :
    Disjoint (p ∪ {u}) (q ∪ {v}) := by
  apply Finset.disjoint_left.mpr
  intro t htL htR
  rcases Finset.mem_union.mp htL with htp | htu
  · rcases Finset.mem_union.mp htR with htq | htv
    · exact (Finset.disjoint_left.mp hpq) htp htq
    · have htv' : t = v := Finset.mem_singleton.mp htv
      exact hvp (htv' ▸ htp)
  · have htu' : t = u := Finset.mem_singleton.mp htu
    rcases Finset.mem_union.mp htR with htq | htv
    · exact huq (htu' ▸ htq)
    · have htv' : t = v := Finset.mem_singleton.mp htv
      exact huv (htu'.symm.trans htv')

/-- A point present on the left but absent from the right separates the
    two singleton extensions. -/
private theorem singleton_extension_ne
    {p q : Edge α} {u v : α}
    (huq : u ∉ q) (huv : u ≠ v) :
    p ∪ {u} ≠ q ∪ {v} := by
  intro heq
  have huL : u ∈ p ∪ {u} := by simp
  have huR : u ∈ q ∪ {v} := heq ▸ huL
  rcases Finset.mem_union.mp huR with huq' | huv'
  · exact huq huq'
  · exact huv (Finset.mem_singleton.mp huv')

/-- A witness in one base pair and absent from the other extended edge
    separates extensions even when both use the same added point. -/
private theorem extension_ne_of_witness
    {p q : Edge α} {u v t : α}
    (htp : t ∈ p) (htq : t ∉ q) (htv : t ≠ v) :
    p ∪ {u} ≠ q ∪ {v} := by
  intro heq
  have htL : t ∈ p ∪ {u} := Finset.mem_union.mpr (Or.inl htp)
  have htR : t ∈ q ∪ {v} := heq ▸ htL
  rcases Finset.mem_union.mp htR with htq' | htv'
  · exact htq htq'
  · exact htv (Finset.mem_singleton.mp htv')

/-- The four cross edges of two disjoint common-link pairs form a
    forbidden configuration. -/
theorem common_link_rectangle_forbidden
    {H : Family α} {p q : Edge α} {x y : α}
    (hH : Admissible H)
    (hxy : x ≠ y)
    (hpq : Disjoint p q)
    (hpNonempty : p.Nonempty) (hqNonempty : q.Nonempty)
    (hxp : x ∉ p) (hyp : y ∉ p)
    (hxq : x ∉ q) (hyq : y ∉ q)
    (hpx : p ∪ {x} ∈ H) (hpy : p ∪ {y} ∈ H)
    (hqx : q ∪ {x} ∈ H) (hqy : q ∪ {y} ∈ H) :
    False := by
  obtain ⟨t, htp⟩ := hpNonempty
  obtain ⟨s, hsq⟩ := hqNonempty
  have htq : t ∉ q := by
    intro htq
    exact (Finset.disjoint_left.mp hpq) htp htq
  have hsp : s ∉ p := by
    intro hsp
    exact (Finset.disjoint_left.mp hpq) hsp hsq
  have htx : t ≠ x := by
    intro heq
    exact hxp (heq ▸ htp)
  have hsy : s ≠ y := by
    intro heq
    exact hyq (heq ▸ hsq)
  have hdistinct : FourDistinct
      (p ∪ {x}) (q ∪ {y}) (p ∪ {y}) (q ∪ {x}) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact singleton_extension_ne hxq hxy
    · exact singleton_extension_ne hxp hxy
    · exact extension_ne_of_witness htp htq htx
    · exact extension_ne_of_witness hsq hsp hsy
    · exact singleton_extension_ne hyq (Ne.symm hxy)
    · exact singleton_extension_ne hyq (Ne.symm hxy)
  have hAB : Disjoint (p ∪ {x}) (q ∪ {y}) :=
    disjoint_cross_edges hpq hxq hyp hxy
  have hCD : Disjoint (p ∪ {y}) (q ∪ {x}) :=
    disjoint_cross_edges hpq hyq hxp (Ne.symm hxy)
  have hunion : (p ∪ {x}) ∪ (q ∪ {y}) =
      (p ∪ {y}) ∪ (q ∪ {x}) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro h
      rcases h with (hpz | hzx) | (hqz | hzy)
      · exact Or.inl (Or.inl hpz)
      · exact Or.inr (Or.inr hzx)
      · exact Or.inr (Or.inl hqz)
      · exact Or.inl (Or.inr hzy)
    · intro h
      rcases h with (hpz | hzy) | (hqz | hzx)
      · exact Or.inl (Or.inl hpz)
      · exact Or.inr (Or.inr hzy)
      · exact Or.inr (Or.inl hqz)
      · exact Or.inl (Or.inr hzx)
  exact hH hpx hqy hpy hqx ⟨hdistinct, hAB, hCD, hunion⟩

/-- The oriented common link of `x,y` on the ambient vertex set. -/
def orientedCommonLink
    (H : Family α) (V : Edge α) (x y : α) : Family α := by
  exact (V.powersetCard 2).filter (fun p =>
    Disjoint p ({x, y} : Edge α) ∧
      p ∪ {x} ∈ H ∧ p ∪ {y} ∈ H)

/-- A disjoint pair of edges in one oriented common link would produce
    the forbidden rectangle above. -/
theorem oriented_common_link_intersecting
    {H : Family α} {V : Edge α} {x y : α}
    (hH : Admissible H) (hxy : x ≠ y)
    {p q : Edge α}
    (hp : p ∈ orientedCommonLink H V x y)
    (hq : q ∈ orientedCommonLink H V x y) :
    ¬ Disjoint p q := by
  intro hpq
  obtain ⟨hpV, hpOut, hpx, hpy⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqV, hqOut, hqx, hqy⟩ := Finset.mem_filter.mp hq
  have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp hpV).2
  have hq2 : q.card = 2 := (Finset.mem_powersetCard.mp hqV).2
  have hpNonempty : p.Nonempty := Finset.card_pos.mp (by omega)
  have hqNonempty : q.Nonempty := Finset.card_pos.mp (by omega)
  have hxp : x ∉ p := by
    intro hx
    exact (Finset.disjoint_left.mp hpOut) hx (by simp)
  have hyp : y ∉ p := by
    intro hy
    exact (Finset.disjoint_left.mp hpOut) hy (by simp)
  have hxq : x ∉ q := by
    intro hx
    exact (Finset.disjoint_left.mp hqOut) hx (by simp)
  have hyq : y ∉ q := by
    intro hy
    exact (Finset.disjoint_left.mp hqOut) hy (by simp)
  exact common_link_rectangle_forbidden hH hxy hpq
    hpNonempty hqNonempty hxp hyp hxq hyq hpx hpy hqx hqy

/-- The unordered common-link definition on `{x,y}` agrees with the
    oriented definition: reversing the witnesses only swaps the two
    required edge-membership facts. -/
theorem mem_commonLink_pair_iff_oriented
    (H : Family α) (V : Edge α) {x y : α}
    (hxy : x ≠ y) (p : Edge α) :
    p ∈ commonLink H V ({x, y} : Edge α) ↔
      p ∈ orientedCommonLink H V x y := by
  constructor
  · intro hp
    obtain ⟨hpV, u, hu, v, hv, huv, hout, hpu, hpv⟩ :=
      Finset.mem_filter.mp hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    have hedges : p ∪ {x} ∈ H ∧ p ∪ {y} ∈ H := by
      rcases hu with hux | huy
      · rcases hv with hvx | hvy
        · exact False.elim (huv (hux.trans hvx.symm))
        · constructor
          · simpa only [hux] using hpu
          · simpa only [hvy] using hpv
      · rcases hv with hvx | hvy
        · constructor
          · simpa only [hvx] using hpv
          · simpa only [huy] using hpu
        · exact False.elim (huv (huy.trans hvy.symm))
    exact Finset.mem_filter.mpr ⟨hpV, hout, hedges.1, hedges.2⟩
  · intro hp
    obtain ⟨hpV, hout, hpx, hpy⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨hpV, ⟨x, by simp, y, by simp, hxy, hout, hpx, hpy⟩⟩

/-- The actual common link of a two-point cell is intersecting for every
    admissible family. -/
theorem common_link_pair_intersecting
    {H : Family α} {V : Edge α} {x y : α}
    (hH : Admissible H) (hxy : x ≠ y)
    {p q : Edge α}
    (hp : p ∈ commonLink H V ({x, y} : Edge α))
    (hq : q ∈ commonLink H V ({x, y} : Edge α)) :
    ¬ Disjoint p q := by
  have hp' := (mem_commonLink_pair_iff_oriented H V hxy p).mp hp
  have hq' := (mem_commonLink_pair_iff_oriented H V hxy q).mp hq
  exact oriented_common_link_intersecting hH hxy hp' hq'

end CommonLink

end JSP523.Rank3
