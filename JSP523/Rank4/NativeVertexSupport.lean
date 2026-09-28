import JSP523.Rank4.NativeDegreeLedger
import JSP523.Rank4.PreprocessSmallCells
import JSP523.Rank4.StarLinkSampling

/-!
# Actual native tail graphs and their vertex support

For a used completion pair, the native graph has an edge between two tail
vertices when adjoining the pair label gives an actual common triple.
Every active tail vertex is outside the completion pair and its label.
This proves the native vertex budget used in the shared star estimate.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The graph of two-vertex tails under a selected center in one actual
common-root cell. -/
noncomputable def nativeTailGraph
    (K : Family α) (U P : Edge α) (z : α) : SimpleGraph α where
  Adj x y := x ≠ y ∧
    insert z ({x, y} : Edge α) ∈ commonRootCell K U P
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    simpa only [Finset.pair_comm x y] using h.2⟩
  loopless := ⟨by
    intro x h
    exact h.1 rfl⟩

noncomputable instance nativeTailGraphDecidableRel
    (K : Family α) (U P : Edge α) (z : α) :
    DecidableRel (nativeTailGraph K U P z).Adj :=
  Classical.decRel _

omit [Fintype α] in
/-- The native tail graph is exactly the ordinary triple link of its
actual common-root cell at the selected center. -/
theorem native_tail_graph_eq_triple_link
    (K : Family α) (U P : Edge α) (z : α) :
    nativeTailGraph K U P z =
      JSP523.Coarse.tripleLinkGraph (commonRootCell K U P) z := by
  rfl

/-- A centered common-root cell has one native graph edge per actual
common triple. -/
theorem native_tail_edge_count_eq_common_root_cell
    (K : Family α) (U P : Edge α) (z : α)
    (hPcard : P.card = 2)
    (hCenter : ∀ T ∈ commonRootCell K U P, z ∈ T) :
    (nativeTailGraph K U P z).edgeFinset.card =
      (commonRootCell K U P).card := by
  classical
  let J := commonRootCell K U P
  have hUniform : ∀ T ∈ J, T.card = 3 := by
    intro T hT
    have hT' : T ∈ commonTripleCell K U
        (pairRootRep P hPcard).1 (pairRootRep P hPcard).2 := by
      simpa only [J, commonRootCell, dite_eq_left hPcard] using hT
    exact (mem_commonTripleCell.mp hT').2.1
  have hFilter : (J.filter fun T => z ∈ T) = J := by
    ext T
    simp only [Finset.mem_filter]
    constructor
    · exact And.left
    · intro hT
      exact ⟨hT, hCenter T hT⟩
  have hEdges :
      (nativeTailGraph K U P z).edgeFinset =
        (JSP523.Coarse.tripleLinkGraph J z).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | hf a b =>
        simp only [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet]
        rfl
  rw [hEdges]
  calc
    (JSP523.Coarse.tripleLinkGraph J z).edgeFinset.card =
      (J.filter fun T => z ∈ T).card :=
        triple_link_edge_count_eq_root_incidence J z hUniform
    _ = J.card := by rw [hFilter]

/-- An active tail vertex belongs to the ambient ground set and avoids
the pair root and its selected center. -/
theorem native_tail_active_vertex_support
    (K : Family α) (U P : Edge α) (z x : α)
    (hPcard : P.card = 2)
    (hx : x ∈ nativeActiveVertices (nativeTailGraph K U P z)) :
    x ∈ U ∧ x ∉ P ∧ x ≠ z := by
  classical
  have hxPos : 0 < (nativeTailGraph K U P z).degree x :=
    (Finset.mem_filter.mp hx).2
  have hNbr : 0 < ((nativeTailGraph K U P z).neighborFinset x).card :=
    hxPos
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hNbr
  have hAdj : (nativeTailGraph K U P z).Adj x y := by
    simpa [SimpleGraph.mem_neighborFinset] using hy
  have hCell : insert z ({x, y} : Edge α) ∈
      commonRootCell K U P := hAdj.2
  simp only [commonRootCell, dite_eq_left hPcard] at hCell
  have hCell' := mem_commonTripleCell.mp hCell
  have hxT : x ∈ insert z ({x, y} : Edge α) := by simp
  have hxU : x ∈ U := hCell'.1 hxT
  have hPspec := pairRootRep_spec P hPcard
  have hDisj : Disjoint (insert z ({x, y} : Edge α)) P := by
    rw [hPspec.2]
    exact hCell'.2.2.1
  have hxP : x ∉ P := by
    intro hxP
    exact (Finset.disjoint_left.mp hDisj) hxT hxP
  have hxz : x ≠ z := by
    have hCard : ({z, x, y} : Edge α).card = 3 :=
      hCell'.2.1
    exact (Finset.card_triple_eq_three_iff.mp hCard).1.symm
  exact ⟨hxU, hxP, hxz⟩

/-- The native tail graph has at most one active vertex for each point
outside the pair root and its selected label. -/
theorem native_tail_active_vertices_card_le
    (K : Family α) (U P : Edge α) (z : α)
    (hPcard : P.card = 2) (hPsub : P ⊆ U)
    (hzU : z ∈ U) (hzP : z ∉ P) :
    (nativeActiveVertices (nativeTailGraph K U P z)).card ≤
      U.card - 3 := by
  classical
  have hSub : nativeActiveVertices (nativeTailGraph K U P z) ⊆
      U \ insert z P := by
    intro x hx
    obtain ⟨hxU, hxP, hxz⟩ :=
      native_tail_active_vertex_support K U P z x hPcard hx
    apply Finset.mem_sdiff.mpr
    refine ⟨hxU, ?_⟩
    intro hIns
    rcases Finset.mem_insert.mp hIns with hEq | hPmem
    · exact hxz hEq
    · exact hxP hPmem
  have hInsSub : insert z P ⊆ U := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxP
    · exact hzU
    · exact hPsub hxP
  have hInsCard : (insert z P).card = 3 := by
    rw [Finset.card_insert_of_notMem hzP, hPcard]
  have hDiffCard : (U \ insert z P).card = U.card - 3 := by
    rw [Finset.card_sdiff_of_subset hInsSub, hInsCard]
  exact (Finset.card_le_card hSub).trans_eq hDiffCard

/-- Sum the active-vertex counts of all actual used-pair native graphs. -/
noncomputable def nativeTailVertexTotal
    (K : Family α) (U : Edge α)
    (used : Family α) (label : Edge α → α) : ℕ :=
  ∑ P ∈ used,
    (nativeActiveVertices
      (nativeTailGraph K U P (label P))).card

/-- The actual native vertex total is bounded by the number of used
pairs times the available vertices outside each pair and its label. -/
theorem native_tail_vertex_total_le
    (K : Family α) (U : Edge α)
    (used : Family α) (label : Edge α → α)
    (hUsed : used ⊆ U.powersetCard 2)
    (hLabel : ∀ P ∈ used, label P ∈ U ∧ label P ∉ P) :
    nativeTailVertexTotal K U used label ≤
      (U.card - 3) * used.card := by
  classical
  unfold nativeTailVertexTotal
  calc
    (∑ P ∈ used,
      (nativeActiveVertices
        (nativeTailGraph K U P (label P))).card) ≤
      ∑ _P ∈ used, (U.card - 3) := by
        apply Finset.sum_le_sum
        intro P hP
        have hP' := Finset.mem_powersetCard.mp (hUsed hP)
        obtain ⟨hzU, hzP⟩ := hLabel P hP
        exact native_tail_active_vertices_card_le
          K U P (label P) hP'.2 hP'.1 hzU hzP
    _ = (U.card - 3) * used.card := by
      simp [mul_comm]

end JSP523.Rank4
