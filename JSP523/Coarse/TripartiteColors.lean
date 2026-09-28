import JSP523.Coarse.TripleCommon
import Mathlib.Tactic.FinCases

/-!
# Color facts for the three-partite step of Part I

The manuscript phrases Lemma I.3 with three disjoint vertex classes.  A
three-color map with one vertex of each color in every triple is equivalent
after tagging the classes.  This file isolates the finite color facts used
to assign link diagonals to a unique vertex link.
-/

namespace JSP523.Coarse

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every member has three vertices with pairwise distinct colors. -/
def RainbowTripleSystem (T : Family α) (color : α → Fin 3) : Prop :=
  ∀ E ∈ T, E.card = 3 ∧
    ∀ x ∈ E, ∀ y ∈ E, x ≠ y → color x ≠ color y

omit [Fintype α] [DecidableEq α] in
theorem RainbowTripleSystem.uniform
    {T : Family α} {color : α → Fin 3}
    (h : RainbowTripleSystem T color) : Uniform 3 T := by
  intro E hE
  exact (h E hE).1

private theorem fin_three_unique_missing
    (a b c d : Fin 3)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hda : d ≠ a) (hdb : d ≠ b) : c = d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp_all

private theorem fin_three_no_four_distinct
    (a b c d : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : False := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp_all

omit [Fintype α] in
/-- Two vertices completing the same pair in a rainbow triple system
have the same color. -/
theorem rainbow_same_color_of_common_pair
    {T : Family α} {color : α → Fin 3}
    (h : RainbowTripleSystem T color)
    {z w x y : α} (hzw : z ≠ w)
    (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w)
    (hx : ({z, w, x} : Edge α) ∈ T)
    (hy : ({z, w, y} : Edge α) ∈ T) :
    color x = color y := by
  have hzx : z ∈ ({z, w, x} : Edge α) := by simp
  have hwx : w ∈ ({z, w, x} : Edge α) := by simp
  have hxx : x ∈ ({z, w, x} : Edge α) := by simp
  have hzy : z ∈ ({z, w, y} : Edge α) := by simp
  have hwy : w ∈ ({z, w, y} : Edge α) := by simp
  have hyy : y ∈ ({z, w, y} : Edge α) := by simp
  have hab := (h _ hx).2 z hzx w hwx hzw
  have hca := (h _ hx).2 x hxx z hzx hxz
  have hcb := (h _ hx).2 x hxx w hwx hxw
  have hda := (h _ hy).2 y hyy z hzy hyz
  have hdb := (h _ hy).2 y hyy w hwy hyw
  exact fin_three_unique_missing
    (color z) (color w) (color x) (color y)
    hab hca hcb hda hdb

omit [Fintype α] in
private theorem pair_union_singleton_eq_triple (a b c : α) :
    ({a, b} : Edge α) ∪ {c} = {a, b, c} := by
  ext x
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem rainbow_common_pair_colors
    {T : Family α} {color : α → Fin 3}
    (h : RainbowTripleSystem T color)
    {x y a b : α}
    (hp : ({a, b} : Edge α) ∈
      Rank3.orientedCommonLink T Finset.univ x y) :
    color a ≠ color b ∧
      color x ≠ color a ∧ color x ≠ color b := by
  obtain ⟨_, _, hpx, _⟩ := Finset.mem_filter.mp hp
  have hE : ({a, b, x} : Edge α) ∈ T := by
    simpa only [pair_union_singleton_eq_triple] using hpx
  have hcard : ({a, b, x} : Edge α).card = 3 := (h _ hE).1
  obtain ⟨hab, hax, hbx⟩ := Finset.card_triple_eq_three_iff.mp hcard
  have ha : a ∈ ({a, b, x} : Edge α) := by simp
  have hb : b ∈ ({a, b, x} : Edge α) := by simp
  have hx : x ∈ ({a, b, x} : Edge α) := by simp
  exact ⟨(h _ hE).2 a ha b hb hab,
    (h _ hE).2 x hx a ha hax.symm,
    (h _ hE).2 x hx b hb hbx.symm⟩

theorem rainbow_common_link_no_triangle
    {T : Family α} {color : α → Fin 3}
    (h : RainbowTripleSystem T color)
    {x y z u v : α}
    (hzu : ({z, u} : Edge α) ∈
      Rank3.orientedCommonLink T Finset.univ x y)
    (hzv : ({z, v} : Edge α) ∈
      Rank3.orientedCommonLink T Finset.univ x y)
    (huv : ({u, v} : Edge α) ∈
      Rank3.orientedCommonLink T Finset.univ x y) : False := by
  obtain ⟨hzuColor, hxz, hxu⟩ := rainbow_common_pair_colors h hzu
  obtain ⟨hzvColor, _, hxv⟩ := rainbow_common_pair_colors h hzv
  have huvColor := (rainbow_common_pair_colors h huv).1
  exact fin_three_no_four_distinct
    (color x) (color z) (color u) (color v)
    hxz hxu hxv hzuColor hzvColor huvColor

/-- In a rainbow admissible triple system, two distinct common-link
pairs through `z` force every common-link pair through `z`.  This is the
bipartite-star argument in the first half of Lemma I.3. -/
theorem rainbow_common_link_center_of_two
    {T : Family α} {color : α → Fin 3}
    (hT : Admissible T) (h : RainbowTripleSystem T color)
    {x y z u v : α} (hxy : x ≠ y) (huv : u ≠ v)
    (hzu : ({z, u} : Edge α) ∈
      Rank3.orientedCommonLink T Finset.univ x y)
    (hzv : ({z, v} : Edge α) ∈
      Rank3.orientedCommonLink T Finset.univ x y) :
    ∀ p ∈ Rank3.orientedCommonLink T Finset.univ x y,
      z ∈ p := by
  intro p hp
  by_contra hz
  have hmeetU : ¬ Disjoint p ({z, u} : Edge α) :=
    Rank3.oriented_common_link_intersecting hT hxy hp hzu
  have hmeetV : ¬ Disjoint p ({z, v} : Edge α) :=
    Rank3.oriented_common_link_intersecting hT hxy hp hzv
  have hu : u ∈ p := by
    by_contra hu
    apply hmeetU
    apply Finset.disjoint_left.mpr
    intro t ht hpPair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpPair
    rcases hpPair with rfl | rfl
    · exact hz ht
    · exact hu ht
  have hv : v ∈ p := by
    by_contra hv
    apply hmeetV
    apply Finset.disjoint_left.mpr
    intro t ht hpPair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpPair
    rcases hpPair with rfl | rfl
    · exact hz ht
    · exact hv ht
  have hp2 : p.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
  have hsub : ({u, v} : Edge α) ⊆ p := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hu
    · exact hv
  have hpeq : p = {u, v} := by
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [hp2, Finset.card_pair huv]
  exact rainbow_common_link_no_triangle h hzu hzv (hpeq ▸ hp)

theorem link_common_neighbor_to_common_link
    {T : Family α} (hU : Uniform 3 T)
    {x y z w : α} (hxy : x ≠ y)
    (hw : w ∈ (tripleLinkGraph T z).neighborFinset x ∩
      (tripleLinkGraph T z).neighborFinset y) :
    ({z, w} : Edge α) ∈
      Rank3.orientedCommonLink T Finset.univ x y := by
  have hxw : (tripleLinkGraph T z).Adj x w := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hw).1
  have hyw : (tripleLinkGraph T z).Adj y w := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hw).2
  have hzxw : ({z, x, w} : Edge α).card = 3 := hU hxw.2
  have hzyw : ({z, y, w} : Edge α).card = 3 := hU hyw.2
  obtain ⟨hzx, hzw, _⟩ := Finset.card_triple_eq_three_iff.mp hzxw
  obtain ⟨hzy, _, _⟩ := Finset.card_triple_eq_three_iff.mp hzyw
  have hpV : ({z, w} : Edge α) ∈
      (Finset.univ : Finset α).powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, Finset.card_pair hzw⟩
  have hdisj : Disjoint ({z, w} : Edge α) ({x, y} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro a ha hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hp
    rcases ha with rfl | rfl <;> rcases hp with rfl | rfl
    · exact hzx rfl
    · exact hzy rfl
    · exact hxw.1 rfl
    · exact hyw.1 rfl
  have hxEdge : ({z, w} : Edge α) ∪ {x} ∈ T := by
    rw [pair_union_singleton_eq_triple]
    simpa only [Finset.pair_comm w x] using hxw.2
  have hyEdge : ({z, w} : Edge α) ∪ {y} ∈ T := by
    rw [pair_union_singleton_eq_triple]
    simpa only [Finset.pair_comm w y] using hyw.2
  exact Finset.mem_filter.mpr ⟨hpV, hdisj, hxEdge, hyEdge⟩

theorem link_diagonal_common_link_two_edges
    {T : Family α} (hU : Uniform 3 T)
    {x y z : α} (hxy : x ≠ y)
    (hdiag : s(x, y) ∈ graphDiagonals (tripleLinkGraph T z)) :
    ∃ u v : α, u ≠ v ∧
      ({z, u} : Edge α) ∈
        Rank3.orientedCommonLink T Finset.univ x y ∧
      ({z, v} : Edge α) ∈
        Rank3.orientedCommonLink T Finset.univ x y := by
  have htwo := (mem_graph_diagonals_iff
    (tripleLinkGraph T z) hxy).mp hdiag
  have hone : 1 < ((tripleLinkGraph T z).neighborFinset x ∩
      (tripleLinkGraph T z).neighborFinset y).card := by
    dsimp [graphCodegree] at htwo
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hone
  exact ⟨u, v, huv,
    link_common_neighbor_to_common_link hU hxy hu,
    link_common_neighbor_to_common_link hU hxy hv⟩

/-- Equation (I.4)'s uniqueness assertion: a given unordered pair can
be a diagonal in at most one original vertex link of a rainbow admissible
triple system. -/
theorem rainbow_diagonal_unique_link
    {T : Family α} {color : α → Fin 3}
    (hT : Admissible T) (h : RainbowTripleSystem T color)
    {x y z w : α} (hxy : x ≠ y)
    (hz : s(x, y) ∈ graphDiagonals (tripleLinkGraph T z))
    (hw : s(x, y) ∈ graphDiagonals (tripleLinkGraph T w)) :
    z = w := by
  have hU := h.uniform
  obtain ⟨u, v, huv, hzu, hzv⟩ :=
    link_diagonal_common_link_two_edges hU hxy hz
  obtain ⟨a, b, hab, hwa, hwb⟩ :=
    link_diagonal_common_link_two_edges hU hxy hw
  have hcenter := rainbow_common_link_center_of_two
    hT h hxy huv hzu hzv
  have hza : z ∈ ({w, a} : Edge α) := hcenter _ hwa
  have hzb : z ∈ ({w, b} : Edge α) := hcenter _ hwb
  by_contra hzw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hza hzb
  rcases hza with hzw' | hza
  · exact hzw hzw'
  rcases hzb with hzw' | hzb
  · exact hzw hzw'
  exact hab (hza.symm.trans hzb)

theorem rainbow_common_link_same_completion_color
    {T : Family α} {color : α → Fin 3}
    (h : RainbowTripleSystem T color)
    {x y z w : α}
    (hp : ({z, w} : Edge α) ∈
      Rank3.orientedCommonLink T Finset.univ x y) :
    color x = color y := by
  obtain ⟨hpV, hpDisj, hpX, hpY⟩ := Finset.mem_filter.mp hp
  have hzw : z ≠ w := by
    have hcard := (Finset.mem_powersetCard.mp hpV).2
    by_contra h
    subst w
    simp at hcard
  have hxz : x ≠ z := by
    intro h
    apply (Finset.disjoint_left.mp hpDisj) (by simp : z ∈ ({z, w} : Edge α))
    simp [h]
  have hxw : x ≠ w := by
    intro h
    apply (Finset.disjoint_left.mp hpDisj) (by simp : w ∈ ({z, w} : Edge α))
    simp [h]
  have hyz : y ≠ z := by
    intro h
    apply (Finset.disjoint_left.mp hpDisj) (by simp : z ∈ ({z, w} : Edge α))
    simp [h]
  have hyw : y ≠ w := by
    intro h
    apply (Finset.disjoint_left.mp hpDisj) (by simp : w ∈ ({z, w} : Edge α))
    simp [h]
  have hX : ({z, w, x} : Edge α) ∈ T := by
    simpa only [pair_union_singleton_eq_triple] using hpX
  have hY : ({z, w, y} : Edge α) ∈ T := by
    simpa only [pair_union_singleton_eq_triple] using hpY
  exact rainbow_same_color_of_common_pair h hzw hxz hxw hyz hyw hX hY

theorem rainbow_link_diagonal_same_color
    {T : Family α} {color : α → Fin 3}
    (h : RainbowTripleSystem T color)
    {x y z : α} (hxy : x ≠ y)
    (hdiag : s(x, y) ∈ graphDiagonals (tripleLinkGraph T z)) :
    color x = color y := by
  obtain ⟨u, v, huv, hzu, hzv⟩ :=
    link_diagonal_common_link_two_edges h.uniform hxy hdiag
  exact rainbow_common_link_same_completion_color h hzu

/-- The unordered within-class vertex pairs for a three-coloring. -/
def sameColorPairs (color : α → Fin 3) : Finset (Sym2 α) :=
  Finset.univ.filter fun p =>
    ∃ x y : α, x ≠ y ∧ p = s(x, y) ∧ color x = color y

theorem graph_diagonals_subset_same_color_pairs
    {T : Family α} {color : α → Fin 3}
    (h : RainbowTripleSystem T color) (z : α) :
    graphDiagonals (tripleLinkGraph T z) ⊆
      sameColorPairs color := by
  intro p hp
  obtain ⟨x, y, hxy, rfl, _⟩ := (Finset.mem_filter.mp hp).2
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,
    ⟨x, y, hxy, rfl, rainbow_link_diagonal_same_color h hxy hp⟩⟩

/-- Equation (I.4), with `S` represented by the exact finite set of
within-class unordered pairs. -/
theorem sum_link_diagonals_le_same_color_pairs
    {T : Family α} {color : α → Fin 3}
    (hT : Admissible T) (h : RainbowTripleSystem T color) :
    (∑ z : α, (graphDiagonals (tripleLinkGraph T z)).card) ≤
      (sameColorPairs color).card := by
  classical
  let D : α → Finset (Sym2 α) := fun z =>
    graphDiagonals (tripleLinkGraph T z)
  have hpairwise : ((Finset.univ : Finset α) : Set α).PairwiseDisjoint D := by
    intro z _ w _ hzw
    apply Finset.disjoint_left.mpr
    intro p hpz hpw
    obtain ⟨x, y, hxy, rfl, _⟩ := (Finset.mem_filter.mp hpz).2
    exact hzw (rainbow_diagonal_unique_link hT h hxy hpz hpw)
  have hsub : (Finset.univ : Finset α).biUnion D ⊆
      sameColorPairs color := by
    intro p hp
    obtain ⟨z, _, hpz⟩ := Finset.mem_biUnion.mp hp
    exact graph_diagonals_subset_same_color_pairs h z hpz
  calc
    (∑ z : α, (graphDiagonals (tripleLinkGraph T z)).card) =
        ((Finset.univ : Finset α).biUnion D).card := by
      exact (Finset.card_biUnion hpairwise).symm
    _ ≤ (sameColorPairs color).card := Finset.card_le_card hsub

omit [Fintype α] in
theorem sym2_to_finset_injective :
    Function.Injective (Sym2.toFinset : Sym2 α → Finset α) := by
  intro p q
  refine Sym2.inductionOn₂ p q ?_
  intro a b c d h
  simp only [Sym2.toFinset_mk_eq] at h
  have hs : ({a, b} : Set α) = {c, d} := by
    simpa using congrArg (fun F : Finset α => (F : Set α)) h
  rcases Set.pair_eq_pair_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Sym2.eq_swap

/-- Within-class unordered pairs, represented by two-element finsets. -/
def sameColorSetPairs (color : α → Fin 3) : Family α :=
  (Finset.univ : Finset α).powersetCard 2 |>.filter fun p =>
    ∃ x y : α, x ≠ y ∧ p = {x, y} ∧ color x = color y

/-- Across-class unordered pairs, represented by two-element finsets. -/
def crossColorSetPairs (color : α → Fin 3) : Family α :=
  (Finset.univ : Finset α).powersetCard 2 |>.filter fun p =>
    ∃ x y : α, x ≠ y ∧ p = {x, y} ∧ color x ≠ color y

theorem same_color_pairs_card_le_same_color_set_pairs
    (color : α → Fin 3) :
    (sameColorPairs color).card ≤ (sameColorSetPairs color).card := by
  apply Finset.card_le_card_of_injOn Sym2.toFinset
  · intro p hp
    obtain ⟨x, y, hxy, rfl, hcol⟩ := (Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ?_, ⟨x, y, hxy, ?_, hcol⟩⟩
    · exact ⟨Finset.subset_univ _, by
        simpa only [Sym2.toFinset_mk_eq] using Finset.card_pair hxy⟩
    · exact Sym2.toFinset_mk_eq
  · intro p _ q _ hpq
    exact sym2_to_finset_injective hpq

theorem sum_link_diagonals_le_same_color_set_pairs
    {T : Family α} {color : α → Fin 3}
    (hT : Admissible T) (h : RainbowTripleSystem T color) :
    (∑ z : α, (graphDiagonals (tripleLinkGraph T z)).card) ≤
      (sameColorSetPairs color).card :=
  (sum_link_diagonals_le_same_color_pairs hT h).trans
    (same_color_pairs_card_le_same_color_set_pairs color)

omit [Fintype α] [DecidableEq α] in
theorem RainbowTripleSystem.mono
    {S T : Family α} {color : α → Fin 3}
    (hST : S ⊆ T) (hT : RainbowTripleSystem T color) :
    RainbowTripleSystem S color := by
  intro E hE
  exact hT E (hST hE)

/-- Used pairs of a rainbow triple system cross two different classes. -/
theorem used_pairs_subset_cross_color_set_pairs
    {T : Family α} {color : α → Fin 3}
    (h : RainbowTripleSystem T color) :
    Rank3.usedPairs T Finset.univ ⊆
      crossColorSetPairs color := by
  intro p hp
  obtain ⟨hpV, E, hET, hpE⟩ := Finset.mem_filter.mp hp
  obtain ⟨x, y, hxy, rfl⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hpV).2
  have hxE : x ∈ E := hpE (by simp)
  have hyE : y ∈ E := hpE (by simp)
  have hxyColor : color x ≠ color y :=
    (h E hET).2 x hxE y hyE hxy
  exact Finset.mem_filter.mpr
    ⟨hpV, ⟨x, y, hxy, rfl, hxyColor⟩⟩

/-- Supported common-link cells of a rainbow triple system are
within one color class. -/
theorem used_cells_subset_same_color_set_pairs
    {T : Family α} {color : α → Fin 3}
    (h : RainbowTripleSystem T color) :
    Rank3.usedCells T Finset.univ ⊆
      sameColorSetPairs color := by
  intro q hq
  obtain ⟨hqV, p, hpV, x, hx, y, hy, hxy,
    hpq, hpx, hpy⟩ := Finset.mem_filter.mp hq
  have hq2 : q.card = 2 := (Finset.mem_powersetCard.mp hqV).2
  have hsub : ({x, y} : Edge α) ⊆ q := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hqeq : q = {x, y} := by
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [hq2, Finset.card_pair hxy]
  have hpJ : p ∈ Rank3.orientedCommonLink T Finset.univ x y := by
    apply Finset.mem_filter.mpr
    exact ⟨hpV, hqeq ▸ hpq, hpx, hpy⟩
  obtain ⟨z, w, hzw, hpEq⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hpV).2
  have hpJpair : ({z, w} : Edge α) ∈
      Rank3.orientedCommonLink T Finset.univ x y := hpEq ▸ hpJ
  exact Finset.mem_filter.mpr
    ⟨hqV, ⟨x, y, hxy, hqeq,
      rainbow_common_link_same_completion_color h hpJpair⟩⟩

/-- Lemma I.3 in its exact finite color form: `P` counts across-class
pairs and `S` counts within-class pairs. -/
theorem rainbow_triple_count
    {T : Family α} {color : α → Fin 3}
    (hT : Admissible T) (h : RainbowTripleSystem T color) :
    3 * T.card ≤ (crossColorSetPairs color).card +
      4 * (sameColorSetPairs color).card := by
  let T₀ := cleanTripleSystem T
  have hBudget : T.card ≤ T₀.card +
      ∑ z : α, (graphDiagonals (tripleLinkGraph T z)).card :=
    clean_triple_system_card_budget T
  have hD : (∑ z : α,
      (graphDiagonals (tripleLinkGraph T z)).card) ≤
      (sameColorSetPairs color).card :=
    sum_link_diagonals_le_same_color_set_pairs hT h
  have hSupport : 3 * T₀.card ≤
      (Rank3.usedPairs T₀ Finset.univ).card +
        (Rank3.usedCells T₀ Finset.univ).card :=
    clean_triple_system_support_bound T hT h.uniform
  have hRainbowClean : RainbowTripleSystem T₀ color :=
    h.mono Finset.sdiff_subset
  have hPairs : (Rank3.usedPairs T₀ Finset.univ).card ≤
      (crossColorSetPairs color).card :=
    Finset.card_le_card (used_pairs_subset_cross_color_set_pairs hRainbowClean)
  have hCells : (Rank3.usedCells T₀ Finset.univ).card ≤
      (sameColorSetPairs color).card :=
    Finset.card_le_card (used_cells_subset_same_color_set_pairs hRainbowClean)
  omega

/-- A color class in the finite ambient vertex type. -/
def colorClass (color : α → Fin 3) (i : Fin 3) : Finset α :=
  Finset.univ.filter fun x => color x = i

theorem same_color_set_pairs_subset_class_pairs
    (color : α → Fin 3) :
    sameColorSetPairs color ⊆
      (Finset.univ : Finset (Fin 3)).biUnion
        (fun i => (colorClass color i).powersetCard 2) := by
  intro p hp
  obtain ⟨hp2, x, y, hxy, rfl, hcol⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_biUnion.mpr
  refine ⟨color x, Finset.mem_univ _, Finset.mem_powersetCard.mpr ?_⟩
  constructor
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · simp [colorClass]
    · simp [colorClass, hcol.symm]
  · exact (Finset.mem_powersetCard.mp hp2).2

theorem same_color_set_pairs_card_le_three_choose_two
    (color : α → Fin 3) (n : ℕ)
    (hclass : ∀ i : Fin 3, (colorClass color i).card ≤ n) :
    (sameColorSetPairs color).card ≤ 3 * n.choose 2 := by
  calc
    (sameColorSetPairs color).card ≤
        ((Finset.univ : Finset (Fin 3)).biUnion
          (fun i => (colorClass color i).powersetCard 2)).card :=
      Finset.card_le_card (same_color_set_pairs_subset_class_pairs color)
    _ ≤ ∑ i : Fin 3, ((colorClass color i).powersetCard 2).card :=
      Finset.card_biUnion_le
    _ = ∑ i : Fin 3, (colorClass color i).card.choose 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.card_powersetCard 2 (colorClass color i)
    _ ≤ ∑ _i : Fin 3, n.choose 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.choose_le_choose 2 (hclass i)
    _ = 3 * n.choose 2 := by simp

private def orderedColorPairs : Finset (Fin 3 × Fin 3) :=
  Finset.univ.filter fun ij => ij.1 < ij.2

private theorem ordered_color_pairs_card : orderedColorPairs.card = 3 := by
  decide

private def crossPairFamily (color : α → Fin 3)
    (i j : Fin 3) : Family α :=
  ((colorClass color i).product (colorClass color j)).image
    (fun xy => ({xy.1, xy.2} : Edge α))

theorem cross_color_set_pairs_subset_class_products
    (color : α → Fin 3) :
    crossColorSetPairs color ⊆
      orderedColorPairs.biUnion
        (fun ij => crossPairFamily color ij.1 ij.2) := by
  intro p hp
  obtain ⟨_, x, y, hxy, rfl, hcol⟩ := Finset.mem_filter.mp hp
  rcases lt_or_gt_of_ne hcol with hlt | hgt
  · apply Finset.mem_biUnion.mpr
    refine ⟨(color x, color y), ?_, ?_⟩
    · simp [orderedColorPairs, hlt]
    · apply Finset.mem_image.mpr
      refine ⟨(x, y), ?_, rfl⟩
      exact Finset.mem_product.mpr
        ⟨by simp [colorClass], by simp [colorClass]⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨(color y, color x), ?_, ?_⟩
    · simp [orderedColorPairs, hgt]
    · apply Finset.mem_image.mpr
      refine ⟨(y, x), ?_, ?_⟩
      · exact Finset.mem_product.mpr
          ⟨by simp [colorClass], by simp [colorClass]⟩
      · exact Finset.pair_comm y x

theorem cross_color_set_pairs_card_le_three_square
    (color : α → Fin 3) (n : ℕ)
    (hclass : ∀ i : Fin 3, (colorClass color i).card ≤ n) :
    (crossColorSetPairs color).card ≤ 3 * n ^ 2 := by
  have hEach : ∀ ij ∈ orderedColorPairs,
      (crossPairFamily color ij.1 ij.2).card ≤ n ^ 2 := by
    intro ij _
    calc
      (crossPairFamily color ij.1 ij.2).card ≤
          ((colorClass color ij.1).product
            (colorClass color ij.2)).card := Finset.card_image_le
      _ = (colorClass color ij.1).card *
            (colorClass color ij.2).card := Finset.card_product _ _
      _ ≤ n * n := Nat.mul_le_mul (hclass ij.1) (hclass ij.2)
      _ = n ^ 2 := by simp [pow_two]
  calc
    (crossColorSetPairs color).card ≤
        (orderedColorPairs.biUnion
          (fun ij => crossPairFamily color ij.1 ij.2)).card :=
      Finset.card_le_card (cross_color_set_pairs_subset_class_products color)
    _ ≤ ∑ ij ∈ orderedColorPairs,
          (crossPairFamily color ij.1 ij.2).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _ij ∈ orderedColorPairs, n ^ 2 :=
      Finset.sum_le_sum hEach
    _ = 3 * n ^ 2 := by simp [ordered_color_pairs_card]

private theorem two_mul_choose_two_le_square (n : ℕ) :
    2 * n.choose 2 ≤ n ^ 2 := by
  rw [Nat.choose_two_right, pow_two]
  have hsub : n * (n - 1) ≤ n * n :=
    Nat.mul_le_mul_left n (Nat.sub_le n 1)
  omega

/-- The final numeric consequence of Lemma I.3: if all three color
classes have at most `n` vertices, an admissible rainbow triple system
has at most `3n²` triples. -/
theorem rainbow_triple_card_le_three_square
    {T : Family α} {color : α → Fin 3}
    (hT : Admissible T) (h : RainbowTripleSystem T color)
    (n : ℕ)
    (hclass : ∀ i : Fin 3, (colorClass color i).card ≤ n) :
    T.card ≤ 3 * n ^ 2 := by
  have hMain := rainbow_triple_count hT h
  have hCross := cross_color_set_pairs_card_le_three_square
    color n hclass
  have hSame := same_color_set_pairs_card_le_three_choose_two
    color n hclass
  have hChoose := two_mul_choose_two_le_square n
  omega

end JSP523.Coarse
