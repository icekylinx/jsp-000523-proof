import JSP523.Rank4.NativeFacetDoubleCount

/-!
# Pair-link common neighbors and native tail degrees

Before the selected-slot restriction is imposed, a common neighbor in
the ordinary pair link at the pair of tail vertices is exactly a
neighbor of that tail vertex in the native graph of the completion pair.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The ordinary pair link of an actual four-uniform family, on vertices
outside the base pair and inside the finite ground set. -/
def rawPairLinkGraph
    (K : Family α) (U Q : Edge α) : SimpleGraph α where
  Adj a b := a ∉ Q ∧ b ∉ Q ∧ a ∈ U ∧ b ∈ U ∧
    a ≠ b ∧ insert a (insert b Q) ∈ K
  symm := ⟨by
    intro a b h
    rcases h with ⟨haQ, hbQ, haU, hbU, hab, hE⟩
    exact ⟨hbQ, haQ, hbU, haU, hab.symm, by
      simpa only [Finset.insert_comm] using hE⟩⟩
  loopless := ⟨by
    intro a h
    exact h.2.2.2.2.1 rfl⟩

instance rawPairLinkGraphDecidableRel
    (K : Family α) (U Q : Edge α) :
    DecidableRel (rawPairLinkGraph K U Q).Adj :=
  inferInstanceAs (DecidableRel (fun a b : α =>
    a ∉ Q ∧ b ∉ Q ∧ a ∈ U ∧ b ∈ U ∧
      a ≠ b ∧ insert a (insert b Q) ∈ K))

omit [Fintype α] in
@[simp] theorem raw_pair_link_graph_adj
    (K : Family α) (U Q : Edge α) (a b : α) :
    (rawPairLinkGraph K U Q).Adj a b ↔
      a ∉ Q ∧ b ∉ Q ∧ a ∈ U ∧ b ∈ U ∧
        a ≠ b ∧ insert a (insert b Q) ∈ K :=
  Iff.rfl

omit [Fintype α] in
/-- A completion of a three-element facet in a uniform four-family is
outside that facet. -/
theorem four_facet_completion_not_in_facet
    (K : Family α) (hUniform : Uniform 4 K)
    (T : Edge α) (hTcard : T.card = 3)
    (a : α) (hEdge : insert a T ∈ K) :
    a ∉ T := by
  intro haT
  have hFour : (insert a T).card = 4 := hUniform hEdge
  rw [Finset.insert_eq_of_mem haT, hTcard] at hFour
  omega

omit [Fintype α] in
/-- A common neighbor in the raw pair link at the tail pair corresponds
exactly to a native graph neighbor of its second tail vertex. -/
theorem raw_pair_common_neighbor_iff_native_neighbor
    (K : Family α) (U : Edge α)
    (hUniform : Uniform 4 K)
    (a b z w x : α)
    (haU : a ∈ U) (hbU : b ∈ U)
    (hzU : z ∈ U) (hwU : w ∈ U)
    (hab : a ≠ b) (hzw : z ≠ w)
    (haQ : a ∉ ({z, w} : Edge α))
    (hbQ : b ∉ ({z, w} : Edge α)) :
    ((rawPairLinkGraph K U ({z, w} : Edge α)).Adj a x ∧
      (rawPairLinkGraph K U ({z, w} : Edge α)).Adj b x) ↔
        (nativeTailGraph K U ({a, b} : Edge α) z).Adj w x := by
  classical
  let P : Edge α := {a, b}
  let Q : Edge α := {z, w}
  let T : Edge α := {z, w, x}
  have hPmem : P ∈ U.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair hab⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact haU
    · exact (Finset.mem_singleton.mp ht) ▸ hbU
  have hTQ : T = insert x Q := by
    ext t
    simp only [T, Q, Finset.mem_insert, Finset.mem_singleton]
    tauto
  constructor
  · rintro ⟨hax, hbx⟩
    have hax' := (raw_pair_link_graph_adj K U Q a x).mp hax
    have hbx' := (raw_pair_link_graph_adj K U Q b x).mp hbx
    obtain ⟨_, hxQ, _, hxU, _, hEa⟩ := hax'
    obtain ⟨_, _, _, _, _, hEb⟩ := hbx'
    have hzx : z ≠ x := by
      intro h
      exact hxQ (by simp [Q, h])
    have hwx : w ≠ x := by
      intro h
      exact hxQ (by simp [Q, h])
    have hTmem : T ∈ U.powersetCard 3 := by
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro t ht
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact hzU
        · exact hwU
        · exact hxU
      · exact Finset.card_triple_eq_three_iff.mpr
          ⟨hzw, hzx, hwx⟩
    have hSub : P ⊆ facetCompletions K U T := by
      intro t ht
      simp only [P, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨haU, by simpa [hTQ] using hEa⟩
      · exact Finset.mem_filter.mpr ⟨hbU, by simpa [hTQ] using hEb⟩
    have hCell : T ∈ commonRootCell K U P :=
      (common_root_cell_iff_pair_of_facet_completions
        K U P T hUniform hPmem hTmem).2 hSub
    exact ⟨hwx, hCell⟩
  · intro hNative
    have hwx : w ≠ x := hNative.1
    have hCell : T ∈ commonRootCell K U P := hNative.2
    have hPcard : P.card = 2 := Finset.card_pair hab
    have hCell' : T ∈ commonTripleCell K U
        (pairRootRep P hPcard).1 (pairRootRep P hPcard).2 := by
      simpa only [commonRootCell, dite_eq_left hPcard] using hCell
    have hData := mem_common_triple_cell.mp hCell'
    have hTmem : T ∈ U.powersetCard 3 :=
      Finset.mem_powersetCard.mpr ⟨hData.1, hData.2.1⟩
    have hTcard : T.card = 3 := hData.2.1
    have hzx : z ≠ x :=
      (Finset.card_triple_eq_three_iff.mp hTcard).2.1
    have hxT : x ∈ T := by simp [T]
    have hxU : x ∈ U := hData.1 hxT
    have hxQ : x ∉ Q := by
      intro hxQ
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hxQ
      rcases hxQ with hxz | hxw
      · exact hzx hxz.symm
      · exact hwx hxw.symm
    have hSub : P ⊆ facetCompletions K U T :=
      (common_root_cell_iff_pair_of_facet_completions
        K U P T hUniform hPmem hTmem).1 hCell
    have haC : a ∈ facetCompletions K U T :=
      hSub (by simp [P])
    have hbC : b ∈ facetCompletions K U T :=
      hSub (by simp [P])
    have hEa : insert a T ∈ K := (Finset.mem_filter.mp haC).2
    have hEb : insert b T ∈ K := (Finset.mem_filter.mp hbC).2
    have hax : a ≠ x := by
      intro h
      exact (four_facet_completion_not_in_facet K hUniform T hTcard a hEa)
        (h.symm ▸ hxT)
    have hbx : b ≠ x := by
      intro h
      exact (four_facet_completion_not_in_facet K hUniform T hTcard b hEb)
        (h.symm ▸ hxT)
    constructor
    · exact (raw_pair_link_graph_adj K U Q a x).2
        ⟨haQ, hxQ, haU, hxU, hax, by simpa [hTQ] using hEa⟩
    · exact (raw_pair_link_graph_adj K U Q b x).2
        ⟨hbQ, hxQ, hbU, hxU, hbx, by simpa [hTQ] using hEb⟩

/-- The raw pair-link common-neighbor multiplicity is exactly the degree
of the corresponding native tail vertex. -/
theorem raw_pair_common_multiplicity_eq_native_degree
    (K : Family α) (U : Edge α)
    (hUniform : Uniform 4 K)
    (a b z w : α)
    (haU : a ∈ U) (hbU : b ∈ U)
    (hzU : z ∈ U) (hwU : w ∈ U)
    (hab : a ≠ b) (hzw : z ≠ w)
    (haQ : a ∉ ({z, w} : Edge α))
    (hbQ : b ∉ ({z, w} : Edge α)) :
    graphCommonMultiplicity
      (rawPairLinkGraph K U ({z, w} : Edge α)) a b =
        (nativeTailGraph K U ({a, b} : Edge α) z).degree w := by
  classical
  let F := rawPairLinkGraph K U ({z, w} : Edge α)
  let G := nativeTailGraph K U ({a, b} : Edge α) z
  have hSet :
      (F.neighborFinset a).filter (fun x => F.Adj b x) =
        G.neighborFinset w := by
    ext x
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact raw_pair_common_neighbor_iff_native_neighbor K U hUniform
      a b z w x haU hbU hzU hwU hab hzw haQ hbQ
  unfold graphCommonMultiplicity SimpleGraph.degree
  exact congrArg Finset.card hSet

/-- Outside the selected label, a completion pair has at most one common
neighbor in an ordinary pair link. -/
theorem raw_pair_common_multiplicity_le_one_off_label
    (K : Family α) (U Q : Edge α)
    (hUniform : Uniform 4 K)
    (hQ : Q ∈ U.powersetCard 2)
    (a b z : α)
    (haU : a ∈ U) (hbU : b ∈ U)
    (hab : a ≠ b)
    (hzQ : z ∉ Q)
    (hCenter : ∀ T ∈ commonRootCell K U ({a, b} : Edge α),
      z ∈ T) :
    graphCommonMultiplicity (rawPairLinkGraph K U Q) a b ≤ 1 := by
  classical
  let P : Edge α := {a, b}
  let F := rawPairLinkGraph K U Q
  have hP : P ∈ U.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair hab⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact haU
    · exact (Finset.mem_singleton.mp ht) ▸ hbU
  have hCommon (x : α) (hax : F.Adj a x) (hbx : F.Adj b x) :
      x = z := by
    have hax' := (raw_pair_link_graph_adj K U Q a x).mp hax
    have hbx' := (raw_pair_link_graph_adj K U Q b x).mp hbx
    obtain ⟨_, hxQ, _, hxU, _, hEa⟩ := hax'
    obtain ⟨_, _, _, _, _, hEb⟩ := hbx'
    let T := insert x Q
    have hT : T ∈ U.powersetCard 3 := by
      apply Finset.mem_powersetCard.mpr
      have hQ' := Finset.mem_powersetCard.mp hQ
      exact ⟨Finset.insert_subset hxU hQ'.1,
        by rw [Finset.card_insert_of_notMem hxQ, hQ'.2]⟩
    have hSub : P ⊆ facetCompletions K U T := by
      intro t ht
      simp only [P, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨haU, hEa⟩
      · exact Finset.mem_filter.mpr ⟨hbU, hEb⟩
    have hCell : T ∈ commonRootCell K U P :=
      (common_root_cell_iff_pair_of_facet_completions
        K U P T hUniform hP hT).2 hSub
    have hzT := hCenter T hCell
    rcases Finset.mem_insert.mp hzT with hxz | hzQ'
    · exact hxz.symm
    · exact False.elim (hzQ hzQ')
  unfold graphCommonMultiplicity
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hax : F.Adj a x := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_filter.mp hx).1
  have hbx : F.Adj b x := (Finset.mem_filter.mp hx).2
  have hay : F.Adj a y := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_filter.mp hy).1
  have hby : F.Adj b y := (Finset.mem_filter.mp hy).2
  exact (hCommon x hax hbx).trans (hCommon y hay hby).symm

end JSP523.Rank4
