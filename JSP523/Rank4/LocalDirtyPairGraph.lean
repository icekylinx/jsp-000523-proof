import JSP523.Rank4.LocalC4Bound
import JSP523.Rank4.LocalExceptionalSets
import JSP523.Counting.LinearTriple
import JSP523.Counting.BadSetIncidence
import JSP523.Rank4.LocalExactLinear

/-!
# The dirty-pair graph from the rank-four near-star argument
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Vertices are bad two-sets; adjacency records that their disjoint union
is an outside four-edge. -/
def badPairUnionGraph (Bad B₀ : Family α) :
    SimpleGraph {P : Edge α // P ∈ Bad} where
  Adj P Q := P ≠ Q ∧ Disjoint P.val Q.val ∧ P.val ∪ Q.val ∈ B₀
  symm.symm P Q := by
    intro h
    exact ⟨h.1.symm, h.2.1.symm, by simpa [Finset.union_comm] using h.2.2⟩
  loopless.irrefl P := by
    intro h
    exact h.1 rfl

instance badPairUnionGraph_decidableRel (Bad B₀ : Family α) :
    DecidableRel (badPairUnionGraph Bad B₀).Adj := by
  classical
  intro P Q
  unfold badPairUnionGraph
  infer_instance

/-- The rank-four outside edges supported on ordinary vertices `U`. -/
def nearStarOrdinaryOutsideEdges (H : Family α) (W : Edge α) (v : α) : Family α :=
  H.filter fun E => E ⊆ W \ badSingletonVertices H W v 4

/-- Ordinary outside edges containing no exceptional pair. -/
def nearStarCleanOutsideEdges (H : Family α) (W : Edge α) (v : α) : Family α :=
  (nearStarOrdinaryOutsideEdges H W v).filter fun E =>
    ∀ P ∈ nearStarBadPairs H W v, ¬ P ⊆ E

@[simp] theorem mem_nearStarCleanOutsideEdges {H : Family α} {W : Edge α}
    {v : α} {E : Edge α} :
    E ∈ nearStarCleanOutsideEdges H W v ↔
      E ∈ nearStarOrdinaryOutsideEdges H W v ∧
        ∀ P ∈ nearStarBadPairs H W v, ¬ P ⊆ E := by
  simp [nearStarCleanOutsideEdges]

/-- The outside family has no repeated triple completion. -/
def NoTripleOverlap (B₀ : Family α) : Prop :=
  ∀ ⦃E F : Edge α⦄, E ∈ B₀ → F ∈ B₀ → E ≠ F →
    (E ∩ F).card ≤ 2

/-- The unique-completion lemma for ordinary vertices implies that no two
outside edges contained in `U` share a triple. -/
theorem noTripleOverlap_of_ordinary_unique_completion
    {H B₀ : Family α} {W U : Edge α} {v : α}
    (hH : Admissible H) (hUniform : Uniform 4 H)
    (hB₀H : B₀ ⊆ H)
    (hB₀U : ∀ E ∈ B₀, E ⊆ U)
    (hUordinary : U ⊆ W \ badSingletonVertices H W v 4)
    (hvW : v ∉ W) :
    NoTripleOverlap B₀ := by
  intro E F hE hF hEF
  by_contra hnot
  have hInterGe : 3 ≤ (E ∩ F).card := by omega
  have hEcard : E.card = 4 := hUniform (hB₀H hE)
  have hFcard : F.card = 4 := hUniform (hB₀H hF)
  have hInterLe : (E ∩ F).card ≤ 3 := by
    by_contra hnot
    have hInterBound : (E ∩ F).card ≤ 4 := (Finset.card_le_card Finset.inter_subset_left).trans_eq hEcard
    have hInterCard : (E ∩ F).card = 4 := by omega
    have hSub : E ∩ F ⊆ E := Finset.inter_subset_left
    have hEq : E ∩ F = E := Finset.eq_of_subset_of_card_le hSub (by omega)
    have hSubEF : E ⊆ F := by
      intro x hx
      have hxI : x ∈ E ∩ F := hEq.symm ▸ hx
      exact (Finset.mem_inter.mp hxI).2
    have hEqEF : E = F := Finset.eq_of_subset_of_card_le hSubEF (by omega)
    exact hEF hEqEF
  have hInterCard : (E ∩ F).card = 3 := by
    omega
  have hDiffCard : (E \ F).card = 1 := by
    have h := Finset.card_sdiff_add_card_inter E F
    omega
  have hDiffCard' : (F \ E).card = 1 := by
    have h := Finset.card_sdiff_add_card_inter F E
    rw [Finset.inter_comm] at h
    omega
  obtain ⟨x, hxDiff⟩ := Finset.card_eq_one.mp hDiffCard
  obtain ⟨y, hyDiff⟩ := Finset.card_eq_one.mp hDiffCard'
  let P := E ∩ F
  have hxE : x ∈ E := by
    have hx := Finset.mem_sdiff.mp (by rw [hxDiff]; simp : x ∈ E \ F)
    exact hx.1
  have hyF : y ∈ F := by
    have hy := Finset.mem_sdiff.mp (by rw [hyDiff]; simp : y ∈ F \ E)
    exact hy.1
  have hxU : x ∈ U := hB₀U E hE hxE
  have hyU : y ∈ U := hB₀U F hF hyF
  have hPsub : P ⊆ W := by
    intro z hz
    have hzOrd : z ∈ W \ badSingletonVertices H W v 4 :=
      hUordinary ((hB₀U E hE) (Finset.inter_subset_left hz))
    exact (Finset.mem_sdiff.mp hzOrd).1
  have hPcard : P.card = 3 := hInterCard
  have hxy : x ≠ y := by
    intro heq
    have hxnotF : x ∉ F := (Finset.mem_sdiff.mp (by
      rw [hxDiff]
      simp : x ∈ E \ F)).2
    apply hxnotF
    rw [heq]
    exact (Finset.mem_sdiff.mp (by rw [hyDiff]; simp : y ∈ F \ E)).1
  have hErep : E = insert x P := by
    have hEq := Finset.sdiff_union_inter E F
    rw [hxDiff] at hEq
    simpa [P] using hEq.symm
  have hFrep : F = insert y P := by
    have hEq := Finset.sdiff_union_inter F E
    rw [hyDiff, Finset.inter_comm] at hEq
    simpa [P] using hEq.symm
  have hxOrd : x ∈ W \ badSingletonVertices H W v 4 := hUordinary hxU
  have hyOrd : y ∈ W \ badSingletonVertices H W v 4 := hUordinary hyU
  exact False.elim (ordinary_vertices_unique_facet_completion
    hH hUniform (hPsub) hPcard (by omega) hvW hxOrd hyOrd hxy
    (hErep ▸ hB₀H hE) (hFrep ▸ hB₀H hF))

/-- Removing every outside edge containing a bad pair leaves a linear
family: a two-point overlap forces one of the two pair differences to be
exceptional, while larger overlaps violate unique ordinary triple
completion. -/
theorem near_star_clean_outside_linear
    {H : Family α} {W : Edge α} {v : α}
    (hH : Admissible H) (hUniform : Uniform 4 H)
    (hvW : v ∉ W) :
    LinearFamily (nearStarCleanOutsideEdges H W v) := by
  intro E F hE hF hEF
  have hEdata := (mem_nearStarCleanOutsideEdges.mp hE)
  have hFdata := (mem_nearStarCleanOutsideEdges.mp hF)
  have hEsub : E ⊆ W := by
    intro x hx
    exact (Finset.mem_sdiff.mp
      ((Finset.mem_filter.mp hEdata.1).2 hx)).1
  have hFsub : F ⊆ W := by
    intro x hx
    exact (Finset.mem_sdiff.mp
      ((Finset.mem_filter.mp hFdata.1).2 hx)).1
  have hOrdH : nearStarOrdinaryOutsideEdges H W v ⊆ H := by
    intro E hE
    exact (Finset.mem_filter.mp hE).1
  have hEcard : E.card = 4 := hUniform (hOrdH hEdata.1)
  have hFcard : F.card = 4 := hUniform (hOrdH hFdata.1)
  have hNoTriple := noTripleOverlap_of_ordinary_unique_completion
    hH hUniform hOrdH
    (fun E hE => (Finset.mem_filter.mp hE).2)
    Finset.Subset.rfl hvW
  by_contra hLin
  have hInterGe : 2 ≤ (E ∩ F).card := by omega
  have hInterLe : (E ∩ F).card ≤ 2 := hNoTriple hEdata.1 hFdata.1 hEF
  have hInterCard : (E ∩ F).card = 2 := by omega
  have hShared : (E ∩ F).Nonempty := Finset.card_pos.mp (by omega)
  have hDiffEcard : (E \ F).card = 2 := by
    have h := Finset.card_sdiff_add_card_inter E F
    omega
  have hBad := overlapping_edges_have_bad_missing_set
    hH (hOrdH hEdata.1) (hOrdH hFdata.1) hEsub hFsub
    hEcard hFcard hEF hShared hvW
  dsimp only at hBad
  rw [hDiffEcard] at hBad
  have hchoose : (W.card - 4 - 2).choose (4 - 1 - 2) = W.card - 6 := by
    simp only [show 4 - 1 - 2 = 1 by omega, Nat.choose_one_right]
    omega
  rw [hchoose] at hBad
  rcases hBad with hBadE | hBadF
  · exact (hEdata.2 (E \ F) (by simpa [nearStarBadPairs] using hBadE))
      Finset.sdiff_subset
  · exact (hFdata.2 (F \ E) (by simpa [nearStarBadPairs] using hBadF))
      Finset.sdiff_subset

/-- The clean ordinary subfamily pays for its edges by ordinary vertices
and missing triples supported on `U`, as in (III.C.3). -/
theorem near_star_clean_outside_incidence
    {H : Family α} {W : Edge α} {v : α}
    (hH : Admissible H) (hUniform : Uniform 4 H)
    (hvW : v ∉ W) :
    4 * (nearStarCleanOutsideEdges H W v).card ≤
      (W \ badSingletonVertices H W v 4).card +
        (missingStarTriples H (W \ badSingletonVertices H W v 4) v).card := by
  have hCleanH : nearStarCleanOutsideEdges H W v ⊆ H := by
    intro E hE
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).1
  have hCleanUniform : Uniform 4 (nearStarCleanOutsideEdges H W v) := by
    intro E hE
    exact hUniform (hCleanH hE)
  have hCleanU : ∀ E ∈ nearStarCleanOutsideEdges H W v,
      E ⊆ W \ badSingletonVertices H W v 4 := by
    intro E hE
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).2
  have hvU : v ∉ W \ badSingletonVertices H W v 4 := by
    intro hvU
    exact hvW (Finset.mem_sdiff.mp hvU |>.1)
  have hLin := near_star_clean_outside_linear
    hH hUniform hvW
  exact linear_outside_edges_incidence_bound hH hCleanH hCleanUniform
    hLin hCleanU hvU

private theorem pair_union_injective_right
    {P Q R : Edge α} (hPQ : P ≠ Q)
    (hPR : Disjoint P R) (hQR : Disjoint Q R) :
    P ∪ R ≠ Q ∪ R := by
  intro hEq
  have hEq' := congrArg (fun T : Edge α => T \ R) hEq
  rw [Finset.union_sdiff_cancel_right hPR,
    Finset.union_sdiff_cancel_right hQR] at hEq'
  exact hPQ hEq'

/-- Two distinct bad-pair vertices with a common neighbor must be disjoint
when the outside family has unique triple completions. -/
private theorem common_neighbor_forces_disjoint
    {B₀ : Family α} {P Q R : Edge α}
    (hPQ : P ≠ Q)
    (hRcard : R.card = 2)
    (hPR : Disjoint P R) (hQR : Disjoint Q R)
    (hPEdge : P ∪ R ∈ B₀) (hQEdge : Q ∪ R ∈ B₀)
    (hNoTriple : NoTripleOverlap B₀) : Disjoint P Q := by
  by_contra hDisj
  have hInter : (P ∩ Q).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hDisj
  have hEdgesNe : P ∪ R ≠ Q ∪ R :=
    pair_union_injective_right hPQ hPR hQR
  have hSub : R ∪ (P ∩ Q) ⊆ (P ∪ R) ∩ (Q ∪ R) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxR | hxPQ
    · exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_right P hxR, Finset.mem_union_right Q hxR⟩
    · exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_left R (Finset.mem_inter.mp hxPQ).1,
          Finset.mem_union_left R (Finset.mem_inter.mp hxPQ).2⟩
  have hRdisj : Disjoint R (P ∩ Q) := by
    apply Finset.disjoint_left.mpr
    intro x hxR hxPQ
    exact (Finset.disjoint_left.mp hPR) (Finset.mem_inter.mp hxPQ).1 hxR
  have hIntPos : 0 < (P ∩ Q).card := Finset.card_pos.mpr hInter
  have hLower : 3 ≤ ((P ∪ R) ∩ (Q ∪ R)).card := by
    have hcard := Finset.card_le_card hSub
    rw [Finset.card_union_of_disjoint hRdisj] at hcard
    omega
  have hBound := hNoTriple hPEdge hQEdge hEdgesNe
  omega

/-- A cycle on four mutually disjoint bad pairs yields the forbidden
two-versus-two union trade in the outside family. -/
theorem disjoint_pair_cycle_forbidden
    {B₀ : Family α} {P Q R S : Edge α}
    (hPNon : P.Nonempty)
    (hPneQ : P ≠ Q) (hRneS : R ≠ S)
    (hPQ : Disjoint P Q) (hPR : Disjoint P R) (hPS : Disjoint P S)
    (hQR : Disjoint Q R) (hQS : Disjoint Q S) (hRS : Disjoint R S)
    (hPRedge : P ∪ R ∈ B₀) (hQSedge : Q ∪ S ∈ B₀)
    (hPSedge : P ∪ S ∈ B₀) (hQRedge : Q ∪ R ∈ B₀)
    (hAdm : Admissible B₀) : False := by
  let A := P ∪ R
  let B := Q ∪ S
  let C := P ∪ S
  let D := Q ∪ R
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    rcases Finset.mem_union.mp hxA with hxP | hxR
    · rcases Finset.mem_union.mp hxB with hxQ | hxS
      · exact (Finset.disjoint_left.mp hPQ) hxP hxQ
      · exact (Finset.disjoint_left.mp hPS) hxP hxS
    · rcases Finset.mem_union.mp hxB with hxQ | hxS
      · exact (Finset.disjoint_left.mp hQR) hxQ hxR
      · exact (Finset.disjoint_left.mp hRS) hxR hxS
  have hCD : Disjoint C D := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxD
    rcases Finset.mem_union.mp hxC with hxP | hxS
    · rcases Finset.mem_union.mp hxD with hxQ | hxR
      · exact (Finset.disjoint_left.mp hPQ) hxP hxQ
      · exact (Finset.disjoint_left.mp hPR) hxP hxR
    · rcases Finset.mem_union.mp hxD with hxQ | hxR
      · exact (Finset.disjoint_left.mp hQS) hxQ hxS
      · exact (Finset.disjoint_left.mp hRS) hxR hxS
  have hABne : A ≠ B := by
    intro heq
    obtain ⟨x, hx⟩ := hPNon
    have hxA : x ∈ A := Finset.mem_union_left R hx
    have hxB : x ∈ B := heq ▸ hxA
    exact (Finset.disjoint_left.mp hAB) hxA hxB
  have hCDne : C ≠ D := by
    intro heq
    obtain ⟨x, hx⟩ := hPNon
    have hxC : x ∈ C := Finset.mem_union_left S hx
    have hxD : x ∈ D := heq ▸ hxC
    exact (Finset.disjoint_left.mp hCD) hxC hxD
  have hAC : A ≠ C := by
    intro heq
    have hEq := congrArg (fun T : Edge α => T \ P) heq
    dsimp [A, C] at hEq
    rw [Finset.union_sdiff_cancel_left hPR,
      Finset.union_sdiff_cancel_left hPS] at hEq
    exact hRneS hEq
  have hBD : B ≠ D := by
    intro heq
    have hEq := congrArg (fun T : Edge α => T \ Q) heq
    dsimp [B, D] at hEq
    rw [Finset.union_sdiff_cancel_left hQS,
      Finset.union_sdiff_cancel_left hQR] at hEq
    exact hRneS hEq.symm
  have hAD : A ≠ D := by
    intro heq
    have hEq := congrArg (fun T : Edge α => T \ R) heq
    dsimp [A, D] at hEq
    rw [Finset.union_sdiff_cancel_right hPR,
      Finset.union_sdiff_cancel_right hQR] at hEq
    exact hPneQ hEq
  have hBC : B ≠ C := by
    intro heq
    have hEq := congrArg (fun T : Edge α => T \ S) heq
    dsimp [B, C] at hEq
    rw [Finset.union_sdiff_cancel_right hQS,
      Finset.union_sdiff_cancel_right hPS] at hEq
    exact hPneQ hEq.symm
  have hUnion : A ∪ B = C ∪ D := by
    dsimp [A, B, C, D]
    ext x
    simp [or_left_comm, or_assoc, or_comm]
  have hDistinct : FourDistinct A B C D :=
    ⟨hABne, hAC, hAD, hBC, hBD, hCDne⟩
  exact hAdm hPRedge hQSedge hPSedge hQRedge
    ⟨hDistinct, hAB, hCD, hUnion⟩

/-- The actual bad-pair union graph has no four-cycle: overlapping opposite
pair roots would create a repeated triple, while disjoint roots give a
forbidden two-versus-two trade. -/
theorem badPairUnionGraph_fourCycleFree
    {Bad B₀ : Family α} [Fintype {P : Edge α // P ∈ Bad}]
    [DecidableEq {P : Edge α // P ∈ Bad}]
    (hBadUniform : Uniform 2 Bad)
    (hB₀Adm : Admissible B₀)
    (hNoTriple : NoTripleOverlap B₀) :
    JSP523.Coarse.FourCycleFree (badPairUnionGraph Bad B₀) := by
  classical
  intro P Q hPQ
  unfold JSP523.Coarse.graphCodegree
  apply Finset.card_le_one_iff.mpr
  intro R S hR hS
  have hPR : (badPairUnionGraph Bad B₀).Adj P R := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hR).1
  have hQR : (badPairUnionGraph Bad B₀).Adj Q R := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hR).2
  have hPS : (badPairUnionGraph Bad B₀).Adj P S := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hS).1
  have hQS : (badPairUnionGraph Bad B₀).Adj Q S := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hS).2
  change _ ∧ Disjoint P.val R.val ∧ P.val ∪ R.val ∈ B₀ at hPR
  change _ ∧ Disjoint Q.val R.val ∧ Q.val ∪ R.val ∈ B₀ at hQR
  change _ ∧ Disjoint P.val S.val ∧ P.val ∪ S.val ∈ B₀ at hPS
  change _ ∧ Disjoint Q.val S.val ∧ Q.val ∪ S.val ∈ B₀ at hQS
  by_contra hRS
  have hPneQ : P.val ≠ Q.val := by
    intro h
    apply hPQ
    exact Subtype.ext h
  have hRneS : R.val ≠ S.val := by
    intro h
    apply hRS
    exact Subtype.ext h
  have hPcard := hBadUniform P.property
  have hRcard := hBadUniform R.property
  have hDisjPQ : Disjoint P.val Q.val := by
    apply common_neighbor_forces_disjoint hPneQ hRcard
      hPR.2.1 hQR.2.1 hPR.2.2 hQR.2.2 hNoTriple
  have hDisjRS : Disjoint R.val S.val := by
    have hRPEdge : R.val ∪ P.val ∈ B₀ := by
      simpa [Finset.union_comm] using hPR.2.2
    have hSPEdge : S.val ∪ P.val ∈ B₀ := by
      simpa [Finset.union_comm] using hPS.2.2
    apply common_neighbor_forces_disjoint hRneS hPcard
      hPR.2.1.symm hPS.2.1.symm hRPEdge hSPEdge hNoTriple
  exact disjoint_pair_cycle_forbidden
    (Finset.card_pos.mp (by omega : 0 < P.val.card))
    hPneQ hRneS hDisjPQ hPR.2.1 hPS.2.1 hQR.2.1 hQS.2.1 hDisjRS
    hPR.2.2 hQS.2.2 hPS.2.2 hQR.2.2 hB₀Adm

/-- Actual near-star instance: unique ordinary triple completion supplies
the no-triple-overlap property, and admissibility supplies the cycle trade
obstruction. -/
theorem near_star_bad_pair_graph_fourCycleFree
    {H B₀ Bad : Family α} {W U : Edge α} {v : α}
    [Fintype {P : Edge α // P ∈ Bad}]
    [DecidableEq {P : Edge α // P ∈ Bad}]
    (hH : Admissible H) (hUniform : Uniform 4 H)
    (hBadUniform : Uniform 2 Bad)
    (hB₀H : B₀ ⊆ H)
    (hB₀U : ∀ E ∈ B₀, E ⊆ U)
    (hUordinary : U ⊆ W \ badSingletonVertices H W v 4)
    (hvW : v ∉ W) :
    JSP523.Coarse.FourCycleFree (badPairUnionGraph Bad B₀) := by
  have hNoTriple := noTripleOverlap_of_ordinary_unique_completion
    hH hUniform hB₀H hB₀U hUordinary hvW
  exact badPairUnionGraph_fourCycleFree
    hBadUniform (admissible_mono hB₀H hH) hNoTriple

/-- The edge bound for the actual near-star bad-pair graph. -/
theorem near_star_bad_pair_graph_edge_bound
    {H B₀ Bad : Family α} {W U : Edge α} {v : α}
    [Fintype {P : Edge α // P ∈ Bad}]
    [DecidableEq {P : Edge α // P ∈ Bad}]
    (hH : Admissible H) (hUniform : Uniform 4 H)
    (hBadUniform : Uniform 2 Bad)
    (hB₀H : B₀ ⊆ H)
    (hB₀U : ∀ E ∈ B₀, E ⊆ U)
    (hUordinary : U ⊆ W \ badSingletonVertices H W v 4)
    (hvW : v ∉ W) :
    ((badPairUnionGraph Bad B₀).edgeFinset.card : ℝ) ≤
      (Real.sqrt ((Fintype.card {P : Edge α // P ∈ Bad} : ℝ) ^ 3) +
        (Fintype.card {P : Edge α // P ∈ Bad} : ℝ) / 2) / 2 := by
  exact fourCycleFree_edge_sqrt_bound (badPairUnionGraph Bad B₀)
    (near_star_bad_pair_graph_fourCycleFree hH hUniform hBadUniform
      hB₀H hB₀U hUordinary hvW)

/-- Fully instantiated edge estimate for the manuscript's graph on the
actual bad pairs and ordinary outside edges. -/
theorem near_star_actual_bad_pair_graph_edge_bound
    {H : Family α} {W : Edge α} {v : α}
    [Fintype α]
    (hH : Admissible H) (hUniform : Uniform 4 H)
    (hvW : v ∉ W) :
    ((badPairUnionGraph (nearStarBadPairs H W v)
        (nearStarOrdinaryOutsideEdges H W v)).edgeFinset.card : ℝ) ≤
      (Real.sqrt (((nearStarBadPairs H W v).card : ℝ) ^ 3) +
        (nearStarBadPairs H W v).card / 2) / 2 := by
  classical
  let Bad := nearStarBadPairs H W v
  let B₀ := nearStarOrdinaryOutsideEdges H W v
  have hBadUniform : Uniform 2 Bad := by
    intro P hP
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).2
  have hB₀H : B₀ ⊆ H := by
    intro E hE
    exact (Finset.mem_filter.mp hE).1
  have hB₀U : ∀ E ∈ B₀, E ⊆ W \ badSingletonVertices H W v 4 := by
    intro E hE
    exact (Finset.mem_filter.mp hE).2
  have hUordinary :
      (W \ badSingletonVertices H W v 4) ⊆
        W \ badSingletonVertices H W v 4 := Finset.Subset.rfl
  have hBound := near_star_bad_pair_graph_edge_bound
    hH hUniform hBadUniform hB₀H hB₀U hUordinary hvW
  simpa [Bad, B₀, Fintype.card_coe] using hBound

/-- Once the dirty-pair graph is shown four-cycle-free, its edge count has
the C₄ extremal bound from `LocalC4Bound`. -/
theorem badPairUnionGraph_edge_bound
    (Bad B₀ : Family α)
    [Fintype {P : Edge α // P ∈ Bad}]
    [DecidableEq {P : Edge α // P ∈ Bad}]
    (hFree : JSP523.Coarse.FourCycleFree (badPairUnionGraph Bad B₀)) :
    ((badPairUnionGraph Bad B₀).edgeFinset.card : ℝ) ≤
      (Real.sqrt ((Fintype.card {P : Edge α // P ∈ Bad} : ℝ) ^ 3) +
        (Fintype.card {P : Edge α // P ∈ Bad} : ℝ) / 2) / 2 := by
  exact fourCycleFree_edge_sqrt_bound (badPairUnionGraph Bad B₀) hFree

end JSP523.Rank4
