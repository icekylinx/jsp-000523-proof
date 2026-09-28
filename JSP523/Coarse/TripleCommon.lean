import JSP523.Coarse.TripleLinks

/-!
# Common-link cells after removing link four-cycles

The key step after the simultaneous graph deletion in Lemma I.3 is valid
for any admissible triple system: if every ordinary vertex link is
four-cycle-free, then every common link of two vertices has at most one
pair.  The tripartite hypothesis enters only in the earlier accounting of
how many link diagonals can occur.
-/

namespace JSP523.Coarse

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
private theorem pair_eq_of_member
    {p : Edge α} {z : α} (hp : p.card = 2) (hz : z ∈ p) :
    ∃ w : α, w ≠ z ∧ p = {z, w} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with hza | hzb
  · subst z
    exact ⟨b, hab.symm, rfl⟩
  · subst z
    exact ⟨a, hab, Finset.pair_comm a b⟩

omit [Fintype α] in
private theorem link_edges_from_common_pair
    (T : Family α) {x y z w : α}
    (hxw : x ≠ w) (hyw : y ≠ w)
    (hpX : ({z, w} : Edge α) ∪ {x} ∈ T)
    (hpY : ({z, w} : Edge α) ∪ {y} ∈ T) :
    (tripleLinkGraph T z).Adj x w ∧
      (tripleLinkGraph T z).Adj y w := by
  have hperm (t : α) :
      ({z, w} : Edge α) ∪ {t} = ({z, t, w} : Edge α) := by
    ext a
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  constructor
  · exact (tripleLinkGraph_adj T z x w).2
      ⟨hxw, by simpa only [hperm] using hpX⟩
  · exact (tripleLinkGraph_adj T z y w).2
      ⟨hyw, by simpa only [hperm] using hpY⟩

/-- Once all ordinary vertex links are four-cycle-free, every actual
common link contains at most one pair.  This is the step immediately
before equation (I.5) in the manuscript. -/
theorem common_link_card_le_one_of_link_free
    (T : Family α) (hT : Admissible T)
    (hfree : ∀ z : α, FourCycleFree (tripleLinkGraph T z))
    (q : Edge α) (hq : q ∈ (Finset.univ : Finset α).powersetCard 2) :
    (Rank3.commonLink T Finset.univ q).card ≤ 1 := by
  classical
  obtain ⟨x, y, hxy, rfl⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hq).2
  apply Finset.card_le_one.mpr
  intro p hp r hr
  by_contra hpr
  have hpNotDisj : ¬ Disjoint p r :=
    Rank3.common_link_pair_intersecting hT hxy hp hr
  have hmeet : (p ∩ r).Nonempty := by
    by_contra hEmpty
    exact hpNotDisj (Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hEmpty))
  obtain ⟨z, hz⟩ := hmeet
  have hpOr := (Rank3.mem_common_link_pair_iff_oriented
    T Finset.univ hxy p).mp hp
  have hrOr := (Rank3.mem_common_link_pair_iff_oriented
    T Finset.univ hxy r).mp hr
  obtain ⟨hpV, hpDisj, hpX, hpY⟩ := Finset.mem_filter.mp hpOr
  obtain ⟨hrV, hrDisj, hrX, hrY⟩ := Finset.mem_filter.mp hrOr
  have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp hpV).2
  have hr2 : r.card = 2 := (Finset.mem_powersetCard.mp hrV).2
  obtain ⟨w, hwz, hpEq⟩ := pair_eq_of_member hp2 (Finset.mem_inter.mp hz).1
  obtain ⟨t, htz, hrEq⟩ := pair_eq_of_member hr2 (Finset.mem_inter.mp hz).2
  have hwt : w ≠ t := by
    intro h
    exact hpr (hpEq.trans (h ▸ hrEq.symm))
  have hxw : x ≠ w := by
    intro h
    apply (Finset.disjoint_left.mp hpDisj) (hpEq ▸ (by simp : w ∈ ({z, w} : Edge α)))
    simp [h]
  have hyw : y ≠ w := by
    intro h
    apply (Finset.disjoint_left.mp hpDisj) (hpEq ▸ (by simp : w ∈ ({z, w} : Edge α)))
    simp [h]
  have hxt : x ≠ t := by
    intro h
    apply (Finset.disjoint_left.mp hrDisj) (hrEq ▸ (by simp : t ∈ ({z, t} : Edge α)))
    simp [h]
  have hyt : y ≠ t := by
    intro h
    apply (Finset.disjoint_left.mp hrDisj) (hrEq ▸ (by simp : t ∈ ({z, t} : Edge α)))
    simp [h]
  have hpAdj := link_edges_from_common_pair T hxw hyw
    (hpEq ▸ hpX) (hpEq ▸ hpY)
  have hrAdj := link_edges_from_common_pair T hxt hyt
    (hrEq ▸ hrX) (hrEq ▸ hrY)
  have htwo : 2 ≤ graphCodegree (tripleLinkGraph T z) x y :=
    two_le_graph_codegree_of_common (tripleLinkGraph T z)
      hwt hpAdj.1 hpAdj.2 hrAdj.1 hrAdj.2
  have hone := hfree z x y hxy
  omega

theorem clean_triple_system_common_link_card_le_one
    (T : Family α) (hT : Admissible T)
    (q : Edge α) (hq : q ∈ (Finset.univ : Finset α).powersetCard 2) :
    (Rank3.commonLink (cleanTripleSystem T) Finset.univ q).card ≤ 1 := by
  apply common_link_card_le_one_of_link_free
  · exact admissible_mono (Finset.sdiff_subset) hT
  · exact clean_triple_system_link_four_cycle_free T
  · exact hq

private theorem sub_one_le_choose_two (d : ℕ) :
    d - 1 ≤ d.choose 2 := by
  cases d with
  | zero => decide
  | succ d =>
    cases d with
    | zero => decide
    | succ d =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      omega

omit [Fintype α] in
/-- The first and second actual completion moments give a general
three-edge incidence upper bound.  This is the arithmetic used in the
last paragraph of Lemma I.3. -/
theorem triple_card_le_pairs_plus_common_incidence
    (T : Family α) (V : Edge α)
    (hU : Uniform 3 T) (hV : ∀ E ∈ T, E ⊆ V) :
    3 * T.card ≤ (Rank3.usedPairs T V).card +
      ∑ q ∈ V.powersetCard 2, (Rank3.commonLink T V q).card := by
  classical
  have hExcess : Rank3.pairDegreeExcess T V ≤
      ∑ p ∈ V.powersetCard 2,
        (Rank3.completionVertices T V p).card.choose 2 := by
    calc
      Rank3.pairDegreeExcess T V ≤
          ∑ p ∈ Rank3.usedPairs T V,
            (Rank3.completionVertices T V p).card.choose 2 := by
        unfold Rank3.pairDegreeExcess
        apply Finset.sum_le_sum
        intro p _
        exact sub_one_le_choose_two _
      _ ≤ ∑ p ∈ V.powersetCard 2,
            (Rank3.completionVertices T V p).card.choose 2 :=
        Finset.sum_le_sum_of_subset (Rank3.used_pairs_subset T V)
  have hfirst := Rank3.used_pairs_completion_excess_ledger T V hU hV
  have hsecond := Rank3.actual_common_link_double_count T V
  omega

omit [Fintype α] in
/-- When every common link has at most one member, its total incidence
count is at most the number of supported common-link cells. -/
theorem common_link_incidence_le_used_cells
    (T : Family α) (V : Edge α)
    (hJ : ∀ q ∈ V.powersetCard 2,
      (Rank3.commonLink T V q).card ≤ 1) :
    (∑ q ∈ V.powersetCard 2,
      (Rank3.commonLink T V q).card) ≤
        (Rank3.usedCells T V).card := by
  classical
  have hsupport := Rank3.used_cells_common_link_double_count T V
  have hdouble := Rank3.actual_common_link_double_count T V
  have heq : (∑ q ∈ V.powersetCard 2,
      (Rank3.commonLink T V q).card) =
      ∑ q ∈ Rank3.usedCells T V,
        (Rank3.commonLink T V q).card := by
    omega
  rw [heq]
  calc
    (∑ q ∈ Rank3.usedCells T V,
      (Rank3.commonLink T V q).card) ≤
        ∑ _q ∈ Rank3.usedCells T V, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact hJ q ((Rank3.used_cells_subset T V) hq)
    _ = (Rank3.usedCells T V).card := by simp

/-- The cleaned admissible triple system satisfies the support inequality
`3|T₀| ≤ |P(T₀)|+|C(T₀)|` without any rank-three signed payment theorem. -/
theorem clean_triple_system_support_bound
    (T : Family α) (hT : Admissible T)
    (hU : Uniform 3 T) :
    3 * (cleanTripleSystem T).card ≤
      (Rank3.usedPairs (cleanTripleSystem T) Finset.univ).card +
        (Rank3.usedCells (cleanTripleSystem T) Finset.univ).card := by
  have hUclean : Uniform 3 (cleanTripleSystem T) := by
    intro E hE
    exact hU (Finset.mem_sdiff.mp hE).1
  have hground : ∀ E ∈ cleanTripleSystem T, E ⊆ (Finset.univ : Edge α) :=
    fun _ _ => Finset.subset_univ _
  have hfirst := triple_card_le_pairs_plus_common_incidence
    (cleanTripleSystem T) Finset.univ hUclean hground
  have hsecond := common_link_incidence_le_used_cells
    (cleanTripleSystem T) Finset.univ
    (clean_triple_system_common_link_card_le_one T hT)
  omega

end JSP523.Coarse
