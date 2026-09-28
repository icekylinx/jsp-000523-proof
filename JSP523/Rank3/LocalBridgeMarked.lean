import JSP523.Rank3.LocalDefectActual

/-!
# The exceptional two-page receiver supplies a marked local graph

This connects the exact two-pair common link to the marked neighborhood
intersection in §II.D.  The source-weight comparison (II.D.2), block
removal, and demand nonduplication are separate obligations.
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

private theorem marked_left_neighbor_singleton
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (x y : α) (hMixed : MixedNodeDegreeTwo G A B C)
    (hx : x ∈ A) (hy : y ∈ B)
    (hABEdge : (x, y) ∈ G.ab)
    (hACPos : 0 < bipLeftDegree G.ac C x) :
    B.filter (fun t => (x, t) ∈ G.ab) = {y} := by
  have hABPos : 0 < bipLeftDegree G.ab B x := by
    exact Finset.card_pos.mpr
      ⟨y, Finset.mem_filter.mpr ⟨hy, hABEdge⟩⟩
  have hOne := (hMixed.1 x hx hABPos hACPos).1
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hOne
  have hyMem : y ∈ B.filter (fun t => (x, t) ∈ G.ab) :=
    Finset.mem_filter.mpr ⟨hy, hABEdge⟩
  rw [hz] at hyMem
  have hyz : y = z := by simpa using hyMem
  simpa [hyz] using hz

private theorem marked_right_neighbor_singleton
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (x z : α) (hMixed : MixedNodeDegreeTwo G A B C)
    (hx : x ∈ A) (hz : z ∈ C)
    (hACEdge : (x, z) ∈ G.ac)
    (hABPos : 0 < bipLeftDegree G.ab B x) :
    C.filter (fun t => (x, t) ∈ G.ac) = {z} := by
  have hACPos : 0 < bipLeftDegree G.ac C x := by
    exact Finset.card_pos.mpr
      ⟨z, Finset.mem_filter.mpr ⟨hz, hACEdge⟩⟩
  have hOne := (hMixed.1 x hx hABPos hACPos).2
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hOne
  have hzMem : z ∈ C.filter (fun t => (x, t) ∈ G.ac) :=
    Finset.mem_filter.mpr ⟨hz, hACEdge⟩
  rw [hw] at hzMem
  have hzw : z = w := by simpa using hzMem
  simpa [hzw] using hw

/-- The exact two-pair receiver `J_{bc} = {da, dx}` makes the old
neighborhoods of the tagged `B_d` and `C_d` nodes disjoint. -/
theorem bridge_book_old_neighbors_disjoint
    {H : Family α} {V : Edge α} {a b c d x : α}
    (hUniform : Uniform 3 H)
    (hBook : orientedCommonLink H V b c =
      ({{d, a}, {d, x}} : Family α)) :
    Disjoint
      (((actualLocalPartA H V a b c).erase x).filter
        (fun u => (u, d) ∈ (actualLocalTripartite H V a b c).ab))
      (((actualLocalPartA H V a b c).erase x).filter
        (fun u => (u, d) ∈ (actualLocalTripartite H V a b c).ac)) := by
  apply Finset.disjoint_left.mpr
  intro u huAB huAC
  have huAErase := (Finset.mem_filter.mp huAB).1
  have huA : u ∈ actualLocalPartA H V a b c :=
    (Finset.mem_erase.mp huAErase).2
  have hux : u ≠ x := (Finset.mem_erase.mp huAErase).1
  have huData := mem_actualLocalPartA.mp huA
  have hABData := mem_actualLocalAB.mp (Finset.mem_filter.mp huAB).2
  have hACData := mem_actualLocalAC.mp (Finset.mem_filter.mp huAC).2
  have hdB := mem_actualLocalPartB.mp hABData.2.1
  have hdC := mem_actualLocalPartC.mp hACData.2.1
  have hdu : d ≠ u := by
    intro hEq
    have hCard := hUniform hABData.2.2
    rw [hEq] at hCard
    have hTwo : ({c, u} : Edge α).card ≤ 2 :=
      Finset.card_insert_le c {u}
    simp at hCard
    omega
  have hPair : ({d, u} : Edge α) ∈ orientedCommonLink H V b c := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      refine ⟨?_, Finset.card_pair hdu⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hdB.1
      · exact (Finset.mem_singleton.mp ht) ▸ huData.1
    · refine ⟨?_, ?_, ?_⟩
      · apply Finset.disjoint_left.mpr
        intro t ht hbc
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht hbc
        rcases ht with htd | htu
        · rcases hbc with htb | htc
          · exact hdB.2.2.1 (htd.symm.trans htb)
          · exact hdB.2.2.2.1 (htd.symm.trans htc)
        · rcases hbc with htb | htc
          · exact huData.2.2.1 (htu.symm.trans htb)
          · exact huData.2.2.2.1 (htu.symm.trans htc)
      · have hSet : ({d, u} : Edge α) ∪ {b} = {b, u, d} := by
          ext t
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        rw [hSet]
        exact hACData.2.2
      · have hSet : ({d, u} : Edge α) ∪ {c} = {c, u, d} := by
          ext t
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        rw [hSet]
        exact hABData.2.2
  rw [hBook] at hPair
  simp only [Finset.mem_insert, Finset.mem_singleton] at hPair
  rcases hPair with hda | hdx
  · have huIn : u ∈ ({d, a} : Edge α) := by
      rw [← hda]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at huIn
    rcases huIn with hud | hua
    · exact hdu hud.symm
    · exact huData.2.1 hua
  · have huIn : u ∈ ({d, x} : Edge α) := by
      rw [← hdx]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at huIn
    rcases huIn with hud | hux'
    · exact hdu hud.symm
    · exact hux hux'

/-- A two-page exceptional receiver, together with its four actual bridge
edges, has the full marked surplus in its bridge triple.  The degree
parameters are the two marked graph degrees after the central node is
removed.  The source-weight comparison remains to be connected. -/
theorem bridge_book_actual_defect_gain
    {H : Family α} {V : Edge α} {a b c d x : α} {r s : ℕ}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H)
    (hx : x ∈ actualLocalPartA H V a b c)
    (hdB : d ∈ actualLocalPartB H V a b c)
    (hdC : d ∈ actualLocalPartC H V a b c)
    (hABEdge : (x, d) ∈ (actualLocalTripartite H V a b c).ab)
    (hACEdge : (x, d) ∈ (actualLocalTripartite H V a b c).ac)
    (hBook : orientedCommonLink H V b c =
      ({{d, a}, {d, x}} : Family α))
    (hrDegree : bipRightDegree (actualLocalTripartite H V a b c).ab
      ((actualLocalPartA H V a b c).erase x) d = r)
    (hsDegree : bipRightDegree (actualLocalTripartite H V a b c).ac
      ((actualLocalPartA H V a b c).erase x) d = s)
    (hr : 2 ≤ r) (hs : 2 ≤ s) :
    min (localPhi (r + 1)) (localPhi (s + 1)) ≤
      localSignedDefect H V ({a, b, c} : Edge α) := by
  let G := actualLocalTripartite H V a b c
  let A := actualLocalPartA H V a b c
  let B := actualLocalPartB H V a b c
  let C := actualLocalPartC H V a b c
  have hMixed : MixedNodeDegreeTwo G A B C :=
    actualLocalTripartite_mixed_degree_two hH hUniform hab hac hbc
  have hABPos : 0 < bipLeftDegree G.ab B x :=
    Finset.card_pos.mpr
      ⟨d, Finset.mem_filter.mpr ⟨hdB, hABEdge⟩⟩
  have hACPos : 0 < bipLeftDegree G.ac C x :=
    Finset.card_pos.mpr
      ⟨d, Finset.mem_filter.mpr ⟨hdC, hACEdge⟩⟩
  have hAB := marked_left_neighbor_singleton
    G A B C x d hMixed hx hdB hABEdge hACPos
  have hAC := marked_right_neighbor_singleton
    G A B C x d hMixed hx hdC hACEdge hABPos
  have hDisj := bridge_book_old_neighbors_disjoint
    hUniform hBook
  exact actual_local_defect_ge_marked_graph_gain
    hH hUniform hground hab hac hbc hE
    hx hdB hdC hAB hAC hrDegree hsDegree hr hs hDisj

end JSP523.Rank3
