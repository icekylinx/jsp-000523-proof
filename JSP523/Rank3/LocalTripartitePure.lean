import JSP523.Rank3.LocalTripartitePositive

/-!
# Pure tripartite graph base case

This module proves the pure-node base cases of §II.A.4 on actual
finite graphs.  The two- and three-type cases allocate only the active
nodes; isolated nodes may remain in the original three parts.
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

/-- The actual graph payment when only the `AB` pair type is present. -/
theorem one_pair_type_actual_local_payment
    (G : TripartitePairGraphs α)
    (A B C : Finset α)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, (a, c) ∉ G.ac)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, (b, c) ∉ G.bc) :
    localGraphBudget A.card + localGraphBudget B.card +
        localGraphBudget C.card ≤
      localGraphPayment A.card B.card C.card
        (bipartitePhiTotal G.ab A B)
        (bipartitePhiTotal G.ac A C)
        (bipartitePhiTotal G.bc B C) := by
  rw [bipartitePhiTotal_eq_zero_of_no_relevant_edge
      G.ac A C hAC,
    bipartitePhiTotal_eq_zero_of_no_relevant_edge
      G.bc B C hBC]
  exact one_pair_type_local_payment A.card B.card C.card
    (bipartitePhiTotal G.ab A B)

/-- The actual two-type pure graph payment once the active vertices have
been allocated to the `AB` and `AC` types.  The original parts may also
contain isolated vertices. -/
theorem two_pair_types_allocated_local_payment
    (G : TripartitePairGraphs α)
    (A B C Aab Aac Bab Cac : Finset α)
    (hA : Aab ∪ Aac ⊆ A)
    (hADisj : Disjoint Aab Aac)
    (hB : Bab ⊆ B) (hC : Cac ⊆ C)
    (hAB : ∀ a ∈ A, ∀ b ∈ B,
      (a, b) ∈ G.ab → a ∈ Aab ∧ b ∈ Bab)
    (hAC : ∀ a ∈ A, ∀ c ∈ C,
      (a, c) ∈ G.ac → a ∈ Aac ∧ c ∈ Cac)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, (b, c) ∉ G.bc)
    (haAB : 0 < Aab.card) (haAC : 0 < Aac.card) :
    localGraphBudget A.card + localGraphBudget B.card +
        localGraphBudget C.card ≤
      localGraphPayment A.card B.card C.card
        (bipartitePhiTotal G.ab A B)
        (bipartitePhiTotal G.ac A C)
        (bipartitePhiTotal G.bc B C) := by
  have hAabSub : Aab ⊆ A := by
    exact Finset.subset_union_left.trans hA
  have hAacSub : Aac ⊆ A := by
    exact Finset.subset_union_right.trans hA
  have hABBound := bipartitePhiTotal_le_completePairScore_of_support
    G.ab A B Aab Bab hAabSub hB hAB
  have hACBound := bipartitePhiTotal_le_completePairScore_of_support
    G.ac A C Aac Cac hAacSub hC hAC
  have hCardA := Finset.card_le_card hA
  rw [Finset.card_union_of_disjoint hADisj] at hCardA
  have hCardB := Finset.card_le_card hB
  have hCardC := Finset.card_le_card hC
  have hPay := two_bounded_pair_types_local_payment_with_isolates
    haAB haAC hCardA hCardB hCardC hABBound hACBound
  rw [bipartitePhiTotal_eq_zero_of_no_relevant_edge
    G.bc B C hBC]
  exact hPay

/-- The three-type pure payment for actual finite pair graphs.  Active
nodes are allocated between pair types; unallocated nodes are isolated. -/
theorem three_pair_types_allocated_local_payment
    (G : TripartitePairGraphs α)
    (A B C Aab Aac Bab Bbc Cac Cbc : Finset α)
    (hA : Aab ∪ Aac ⊆ A) (hADisj : Disjoint Aab Aac)
    (hB : Bab ∪ Bbc ⊆ B) (hBDisj : Disjoint Bab Bbc)
    (hC : Cac ∪ Cbc ⊆ C) (hCDisj : Disjoint Cac Cbc)
    (hAB : ∀ a ∈ A, ∀ b ∈ B,
      (a, b) ∈ G.ab → a ∈ Aab ∧ b ∈ Bab)
    (hAC : ∀ a ∈ A, ∀ c ∈ C,
      (a, c) ∈ G.ac → a ∈ Aac ∧ c ∈ Cac)
    (hBC : ∀ b ∈ B, ∀ c ∈ C,
      (b, c) ∈ G.bc → b ∈ Bbc ∧ c ∈ Cbc)
    (haAB : 0 < Aab.card) (haAC : 0 < Aac.card)
    (hbAB : 0 < Bab.card) (hbBC : 0 < Bbc.card)
    (hcAC : 0 < Cac.card) (hcBC : 0 < Cbc.card) :
    localGraphBudget A.card + localGraphBudget B.card +
        localGraphBudget C.card ≤
      localGraphPayment A.card B.card C.card
        (bipartitePhiTotal G.ab A B)
        (bipartitePhiTotal G.ac A C)
        (bipartitePhiTotal G.bc B C) := by
  have hAabSub : Aab ⊆ A := by
    exact Finset.subset_union_left.trans hA
  have hAacSub : Aac ⊆ A := by
    exact Finset.subset_union_right.trans hA
  have hBabSub : Bab ⊆ B := by
    exact Finset.subset_union_left.trans hB
  have hBbcSub : Bbc ⊆ B := by
    exact Finset.subset_union_right.trans hB
  have hCacSub : Cac ⊆ C := by
    exact Finset.subset_union_left.trans hC
  have hCbcSub : Cbc ⊆ C := by
    exact Finset.subset_union_right.trans hC
  have hABBound := bipartitePhiTotal_le_completePairScore_of_support
    G.ab A B Aab Bab hAabSub hBabSub hAB
  have hACBound := bipartitePhiTotal_le_completePairScore_of_support
    G.ac A C Aac Cac hAacSub hCacSub hAC
  have hBCBound := bipartitePhiTotal_le_completePairScore_of_support
    G.bc B C Bbc Cbc hBbcSub hCbcSub hBC
  have hCardA := Finset.card_le_card hA
  rw [Finset.card_union_of_disjoint hADisj] at hCardA
  have hCardB := Finset.card_le_card hB
  rw [Finset.card_union_of_disjoint hBDisj] at hCardB
  have hCardC := Finset.card_le_card hC
  rw [Finset.card_union_of_disjoint hCDisj] at hCardC
  have hPay := three_bounded_pair_types_local_payment_with_isolates
    haAB haAC hbAB hbBC hcAC hcBC
    hCardA hCardB hCardC hABBound hACBound hBCBound
  exact hPay

/-- The pure base case when all three pair types occur, allowing isolated
vertices in any part.  Allocations are the actual positive-degree sets. -/
theorem pure_three_pair_types_local_payment
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (hPureA : ∀ a ∈ A,
      bipLeftDegree G.ab B a = 0 ∨ bipLeftDegree G.ac C a = 0)
    (hPureB : ∀ b ∈ B,
      bipRightDegree G.ab A b = 0 ∨ bipLeftDegree G.bc C b = 0)
    (hPureC : ∀ c ∈ C,
      bipRightDegree G.ac A c = 0 ∨ bipRightDegree G.bc B c = 0)
    (hABedge : ∃ a ∈ A, ∃ b ∈ B, (a, b) ∈ G.ab)
    (hACedge : ∃ a ∈ A, ∃ c ∈ C, (a, c) ∈ G.ac)
    (hBCedge : ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G.bc) :
    localGraphBudget A.card + localGraphBudget B.card +
        localGraphBudget C.card ≤
      localGraphPayment A.card B.card C.card
        (bipartitePhiTotal G.ab A B)
        (bipartitePhiTotal G.ac A C)
        (bipartitePhiTotal G.bc B C) := by
  let Aab := A.filter fun a => 0 < bipLeftDegree G.ab B a
  let Aac := A.filter fun a => 0 < bipLeftDegree G.ac C a
  let Bab := B.filter fun b => 0 < bipRightDegree G.ab A b
  let Bbc := B.filter fun b => 0 < bipLeftDegree G.bc C b
  let Cac := C.filter fun c => 0 < bipRightDegree G.ac A c
  let Cbc := C.filter fun c => 0 < bipRightDegree G.bc B c
  have hA : Aab ∪ Aac ⊆ A := by
    intro a ha
    rcases Finset.mem_union.mp ha with hAB | hAC
    · exact (Finset.mem_filter.mp hAB).1
    · exact (Finset.mem_filter.mp hAC).1
  have hB : Bab ∪ Bbc ⊆ B := by
    intro b hb
    rcases Finset.mem_union.mp hb with hAB | hBC
    · exact (Finset.mem_filter.mp hAB).1
    · exact (Finset.mem_filter.mp hBC).1
  have hC : Cac ∪ Cbc ⊆ C := by
    intro c hc
    rcases Finset.mem_union.mp hc with hAC | hBC
    · exact (Finset.mem_filter.mp hAC).1
    · exact (Finset.mem_filter.mp hBC).1
  have hADisj : Disjoint Aab Aac := by
    apply Finset.disjoint_left.mpr
    intro a haAB haAC
    have ha := (Finset.mem_filter.mp haAB).1
    have hAB := (Finset.mem_filter.mp haAB).2
    have hAC := (Finset.mem_filter.mp haAC).2
    rcases hPureA a ha with hZero | hZero <;> omega
  have hBDisj : Disjoint Bab Bbc := by
    apply Finset.disjoint_left.mpr
    intro b hbAB hbBC
    have hb := (Finset.mem_filter.mp hbAB).1
    have hAB := (Finset.mem_filter.mp hbAB).2
    have hBC := (Finset.mem_filter.mp hbBC).2
    rcases hPureB b hb with hZero | hZero <;> omega
  have hCDisj : Disjoint Cac Cbc := by
    apply Finset.disjoint_left.mpr
    intro c hcAC hcBC
    have hc := (Finset.mem_filter.mp hcAC).1
    have hAC := (Finset.mem_filter.mp hcAC).2
    have hBC := (Finset.mem_filter.mp hcBC).2
    rcases hPureC c hc with hZero | hZero <;> omega
  have hAB : ∀ a ∈ A, ∀ b ∈ B,
      (a, b) ∈ G.ab → a ∈ Aab ∧ b ∈ Bab := by
    intro a ha b hb hab
    have hda : 0 < bipLeftDegree G.ab B a := by
      unfold bipLeftDegree
      exact Finset.card_pos.mpr
        ⟨b, Finset.mem_filter.mpr ⟨hb, hab⟩⟩
    have hdb : 0 < bipRightDegree G.ab A b := by
      unfold bipRightDegree
      exact Finset.card_pos.mpr
        ⟨a, Finset.mem_filter.mpr ⟨ha, hab⟩⟩
    exact ⟨Finset.mem_filter.mpr ⟨ha, hda⟩,
      Finset.mem_filter.mpr ⟨hb, hdb⟩⟩
  have hAC : ∀ a ∈ A, ∀ c ∈ C,
      (a, c) ∈ G.ac → a ∈ Aac ∧ c ∈ Cac := by
    intro a ha c hc hac
    have hda : 0 < bipLeftDegree G.ac C a := by
      unfold bipLeftDegree
      exact Finset.card_pos.mpr
        ⟨c, Finset.mem_filter.mpr ⟨hc, hac⟩⟩
    have hdc : 0 < bipRightDegree G.ac A c := by
      unfold bipRightDegree
      exact Finset.card_pos.mpr
        ⟨a, Finset.mem_filter.mpr ⟨ha, hac⟩⟩
    exact ⟨Finset.mem_filter.mpr ⟨ha, hda⟩,
      Finset.mem_filter.mpr ⟨hc, hdc⟩⟩
  have hBC : ∀ b ∈ B, ∀ c ∈ C,
      (b, c) ∈ G.bc → b ∈ Bbc ∧ c ∈ Cbc := by
    intro b hb c hc hbc
    have hdb : 0 < bipLeftDegree G.bc C b := by
      unfold bipLeftDegree
      exact Finset.card_pos.mpr
        ⟨c, Finset.mem_filter.mpr ⟨hc, hbc⟩⟩
    have hdc : 0 < bipRightDegree G.bc B c := by
      unfold bipRightDegree
      exact Finset.card_pos.mpr
        ⟨b, Finset.mem_filter.mpr ⟨hb, hbc⟩⟩
    exact ⟨Finset.mem_filter.mpr ⟨hb, hdb⟩,
      Finset.mem_filter.mpr ⟨hc, hdc⟩⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hABedge
  obtain ⟨a', ha', c, hc, hac⟩ := hACedge
  obtain ⟨b', hb', c', hc', hbc⟩ := hBCedge
  have haAB : 0 < Aab.card :=
    Finset.card_pos.mpr ⟨a, (hAB a ha b hb hab).1⟩
  have hbAB : 0 < Bab.card :=
    Finset.card_pos.mpr ⟨b, (hAB a ha b hb hab).2⟩
  have haAC : 0 < Aac.card :=
    Finset.card_pos.mpr ⟨a', (hAC a' ha' c hc hac).1⟩
  have hcAC : 0 < Cac.card :=
    Finset.card_pos.mpr ⟨c, (hAC a' ha' c hc hac).2⟩
  have hbBC : 0 < Bbc.card :=
    Finset.card_pos.mpr ⟨b', (hBC b' hb' c' hc' hbc).1⟩
  have hcBC : 0 < Cbc.card :=
    Finset.card_pos.mpr ⟨c', (hBC b' hb' c' hc' hbc).2⟩
  exact three_pair_types_allocated_local_payment G
    A B C Aab Aac Bab Bbc Cac Cbc
    hA hADisj hB hBDisj hC hCDisj
    hAB hAC hBC haAB haAC hbAB hbBC hcAC hcBC

/-- The pure base case with `AB` and `AC` active and `BC` absent.  The
split at `A` follows from the no-mixed-node property; isolated vertices
are allowed in all three parts. -/
theorem pure_two_pair_types_local_payment
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (hPureA : ∀ a ∈ A,
      bipLeftDegree G.ab B a = 0 ∨ bipLeftDegree G.ac C a = 0)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, (b, c) ∉ G.bc)
    (hABedge : ∃ a ∈ A, ∃ b ∈ B, (a, b) ∈ G.ab)
    (hACedge : ∃ a ∈ A, ∃ c ∈ C, (a, c) ∈ G.ac) :
    localGraphBudget A.card + localGraphBudget B.card +
        localGraphBudget C.card ≤
      localGraphPayment A.card B.card C.card
        (bipartitePhiTotal G.ab A B)
        (bipartitePhiTotal G.ac A C)
        (bipartitePhiTotal G.bc B C) := by
  let Aab := A.filter fun a => 0 < bipLeftDegree G.ab B a
  let Aac := A.filter fun a => 0 < bipLeftDegree G.ac C a
  have hA : Aab ∪ Aac ⊆ A := by
    intro a ha
    rcases Finset.mem_union.mp ha with hAB | hAC
    · exact (Finset.mem_filter.mp hAB).1
    · exact (Finset.mem_filter.mp hAC).1
  have hADisj : Disjoint Aab Aac := by
    apply Finset.disjoint_left.mpr
    intro a haAB haAC
    have ha := (Finset.mem_filter.mp haAB).1
    have hAB := (Finset.mem_filter.mp haAB).2
    have hAC := (Finset.mem_filter.mp haAC).2
    rcases hPureA a ha with hZero | hZero <;> omega
  have hAB : ∀ a ∈ A, ∀ b ∈ B,
      (a, b) ∈ G.ab → a ∈ Aab ∧ b ∈ B := by
    intro a ha b hb hab
    have hda : 0 < bipLeftDegree G.ab B a := by
      unfold bipLeftDegree
      exact Finset.card_pos.mpr
        ⟨b, Finset.mem_filter.mpr ⟨hb, hab⟩⟩
    exact ⟨Finset.mem_filter.mpr ⟨ha, hda⟩, hb⟩
  have hAC : ∀ a ∈ A, ∀ c ∈ C,
      (a, c) ∈ G.ac → a ∈ Aac ∧ c ∈ C := by
    intro a ha c hc hac
    have hda : 0 < bipLeftDegree G.ac C a := by
      unfold bipLeftDegree
      exact Finset.card_pos.mpr
        ⟨c, Finset.mem_filter.mpr ⟨hc, hac⟩⟩
    exact ⟨Finset.mem_filter.mpr ⟨ha, hda⟩, hc⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hABedge
  obtain ⟨a', ha', c, hc, hac⟩ := hACedge
  have haAB : 0 < Aab.card :=
    Finset.card_pos.mpr ⟨a, (hAB a ha b hb hab).1⟩
  have haAC : 0 < Aac.card :=
    Finset.card_pos.mpr ⟨a', (hAC a' ha' c hc hac).1⟩
  exact two_pair_types_allocated_local_payment G
    A B C Aab Aac B C hA hADisj subset_rfl subset_rfl
    hAB hAC hBC haAB haAC

/-- Relabel the parts so an `AB` and `BC` pair becomes an `AB` and `AC`
pair.  Transposition is needed because a pair graph is oriented by its
two parts. -/
private def swapPartsAB (G : TripartitePairGraphs α) :
    TripartitePairGraphs α :=
  ⟨bipTranspose G.ab, G.bc, G.ac⟩

/-- Relabel the parts so an `AC` and `BC` pair becomes an `AB` and `AC`
pair. -/
private def movePartCFirst (G : TripartitePairGraphs α) :
    TripartitePairGraphs α :=
  ⟨bipTranspose G.ac, bipTranspose G.bc, G.ab⟩

theorem pure_ab_bc_pair_types_local_payment
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (hPureB : ∀ b ∈ B,
      bipRightDegree G.ab A b = 0 ∨ bipLeftDegree G.bc C b = 0)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, (a, c) ∉ G.ac)
    (hABedge : ∃ a ∈ A, ∃ b ∈ B, (a, b) ∈ G.ab)
    (hBCedge : ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G.bc) :
    localGraphBudget A.card + localGraphBudget B.card +
        localGraphBudget C.card ≤
      localGraphPayment A.card B.card C.card
        (bipartitePhiTotal G.ab A B)
        (bipartitePhiTotal G.ac A C)
        (bipartitePhiTotal G.bc B C) := by
  let G' := swapPartsAB G
  have hPure : ∀ b ∈ B,
      bipLeftDegree G'.ab A b = 0 ∨
        bipLeftDegree G'.ac C b = 0 := by
    intro b hb
    simpa [G', swapPartsAB, bipLeftDegree, bipRightDegree,
      mem_bipTranspose] using hPureB b hb
  have hAB' : ∃ b ∈ B, ∃ a ∈ A, (b, a) ∈ G'.ab := by
    obtain ⟨a, ha, b, hb, hab⟩ := hABedge
    exact ⟨b, hb, a, ha, (mem_bipTranspose G.ab b a).2 hab⟩
  have hAC' : ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G'.ac := by
    simpa [G', swapPartsAB] using hBCedge
  have h := pure_two_pair_types_local_payment G' B A C
    hPure (by simpa [G', swapPartsAB] using hAC) hAB' hAC'
  have h' :
      localGraphBudget B.card + localGraphBudget A.card +
          localGraphBudget C.card ≤
        localGraphPayment B.card A.card C.card
          (bipartitePhiTotal G.ab A B)
          (bipartitePhiTotal G.bc B C) 0 := by
    simpa [G', swapPartsAB, bipartitePhiTotal_transpose,
      bipartitePhiTotal_eq_zero_of_no_relevant_edge
        G.ac A C hAC] using h
  rw [localGraphPayment_swap_first_two B.card A.card C.card
    (bipartitePhiTotal G.ab A B)
    (bipartitePhiTotal G.bc B C) 0] at h'
  rw [bipartitePhiTotal_eq_zero_of_no_relevant_edge
    G.ac A C hAC]
  convert h' using 1
  ring

theorem pure_ac_bc_pair_types_local_payment
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (hPureC : ∀ c ∈ C,
      bipRightDegree G.ac A c = 0 ∨ bipRightDegree G.bc B c = 0)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∉ G.ab)
    (hACedge : ∃ a ∈ A, ∃ c ∈ C, (a, c) ∈ G.ac)
    (hBCedge : ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G.bc) :
    localGraphBudget A.card + localGraphBudget B.card +
        localGraphBudget C.card ≤
      localGraphPayment A.card B.card C.card
        (bipartitePhiTotal G.ab A B)
        (bipartitePhiTotal G.ac A C)
        (bipartitePhiTotal G.bc B C) := by
  let G' := movePartCFirst G
  have hPure : ∀ c ∈ C,
      bipLeftDegree G'.ab A c = 0 ∨
        bipLeftDegree G'.ac B c = 0 := by
    intro c hc
    simpa [G', movePartCFirst, bipLeftDegree, bipRightDegree,
      mem_bipTranspose] using hPureC c hc
  have hAB' : ∃ c ∈ C, ∃ a ∈ A, (c, a) ∈ G'.ab := by
    obtain ⟨a, ha, c, hc, hac⟩ := hACedge
    exact ⟨c, hc, a, ha, (mem_bipTranspose G.ac c a).2 hac⟩
  have hAC' : ∃ c ∈ C, ∃ b ∈ B, (c, b) ∈ G'.ac := by
    obtain ⟨b, hb, c, hc, hbc⟩ := hBCedge
    exact ⟨c, hc, b, hb, (mem_bipTranspose G.bc c b).2 hbc⟩
  have h := pure_two_pair_types_local_payment G' C A B
    hPure (by simpa [G', movePartCFirst] using hAB) hAB' hAC'
  have h' :
      localGraphBudget C.card + localGraphBudget A.card +
          localGraphBudget B.card ≤
        localGraphPayment C.card A.card B.card
          (bipartitePhiTotal G.ac A C)
          (bipartitePhiTotal G.bc B C) 0 := by
    simpa [G', movePartCFirst, bipartitePhiTotal_transpose,
      bipartitePhiTotal_eq_zero_of_no_relevant_edge
        G.ab A B hAB] using h
  rw [localGraphPayment_swap_first_two C.card A.card B.card
    (bipartitePhiTotal G.ac A C)
    (bipartitePhiTotal G.bc B C) 0,
    localGraphPayment_swap_last_two A.card C.card B.card
      (bipartitePhiTotal G.ac A C) 0
      (bipartitePhiTotal G.bc B C)] at h'
  rw [bipartitePhiTotal_eq_zero_of_no_relevant_edge
    G.ab A B hAB]
  convert h' using 1
  ring

/-- §II.A.4 for an arbitrary actual tripartite graph with no mixed
nodes.  Every pattern of present pair types is covered, and vertices of
degree zero are allowed. -/
theorem pure_tripartite_local_payment
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (hPureA : ∀ a ∈ A,
      bipLeftDegree G.ab B a = 0 ∨ bipLeftDegree G.ac C a = 0)
    (hPureB : ∀ b ∈ B,
      bipRightDegree G.ab A b = 0 ∨ bipLeftDegree G.bc C b = 0)
    (hPureC : ∀ c ∈ C,
      bipRightDegree G.ac A c = 0 ∨ bipRightDegree G.bc B c = 0) :
    localGraphBudget A.card + localGraphBudget B.card +
        localGraphBudget C.card ≤
      localGraphPayment A.card B.card C.card
        (bipartitePhiTotal G.ab A B)
        (bipartitePhiTotal G.ac A C)
        (bipartitePhiTotal G.bc B C) := by
  have noAB (h : ¬ ∃ a ∈ A, ∃ b ∈ B, (a, b) ∈ G.ab) :
      ∀ a ∈ A, ∀ b ∈ B, (a, b) ∉ G.ab := by
    intro a ha b hb hab
    exact h ⟨a, ha, b, hb, hab⟩
  have noAC (h : ¬ ∃ a ∈ A, ∃ c ∈ C, (a, c) ∈ G.ac) :
      ∀ a ∈ A, ∀ c ∈ C, (a, c) ∉ G.ac := by
    intro a ha c hc hac
    exact h ⟨a, ha, c, hc, hac⟩
  have noBC (h : ¬ ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G.bc) :
      ∀ b ∈ B, ∀ c ∈ C, (b, c) ∉ G.bc := by
    intro b hb c hc hbc
    exact h ⟨b, hb, c, hc, hbc⟩
  by_cases hAB : ∃ a ∈ A, ∃ b ∈ B, (a, b) ∈ G.ab
  · by_cases hAC : ∃ a ∈ A, ∃ c ∈ C, (a, c) ∈ G.ac
    · by_cases hBC : ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G.bc
      · exact pure_three_pair_types_local_payment G A B C
          hPureA hPureB hPureC hAB hAC hBC
      · exact pure_two_pair_types_local_payment G A B C
          hPureA (noBC hBC) hAB hAC
    · by_cases hBC : ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G.bc
      · exact pure_ab_bc_pair_types_local_payment G A B C
          hPureB (noAC hAC) hAB hBC
      · exact one_pair_type_actual_local_payment G A B C
          (noAC hAC) (noBC hBC)
  · by_cases hAC : ∃ a ∈ A, ∃ c ∈ C, (a, c) ∈ G.ac
    · by_cases hBC : ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G.bc
      · exact pure_ac_bc_pair_types_local_payment G A B C
          hPureC (noAB hAB) hAC hBC
      · rw [bipartitePhiTotal_eq_zero_of_no_relevant_edge
          G.ab A B (noAB hAB),
          bipartitePhiTotal_eq_zero_of_no_relevant_edge
          G.bc B C (noBC hBC)]
        exact one_pair_type_AC_local_payment A.card B.card C.card
          (bipartitePhiTotal G.ac A C)
    · by_cases hBC : ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G.bc
      · rw [bipartitePhiTotal_eq_zero_of_no_relevant_edge
          G.ab A B (noAB hAB),
          bipartitePhiTotal_eq_zero_of_no_relevant_edge
          G.ac A C (noAC hAC)]
        exact one_pair_type_BC_local_payment A.card B.card C.card
          (bipartitePhiTotal G.bc B C)
      · exact one_pair_type_actual_local_payment G A B C
          (noAC hAC) (noBC hBC)

end JSP523.Rank3
