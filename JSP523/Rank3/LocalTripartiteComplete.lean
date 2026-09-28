import JSP523.Rank3.LocalGraphMixedStep

/-!
# The complete signed local graph payment

This assembles the pure-node base case, positive-type cases, and the
mixed-node deletion step into §II.A's finite tripartite graph
theorem.  The input is exactly the degree-two condition for mixed nodes;
no edge-set completeness or bound on the part sizes is assumed.
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

private theorem mixed_first_exists_of_not_pure
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (hNot : ¬ ∀ a ∈ A,
      bipLeftDegree G.ab B a = 0 ∨
        bipLeftDegree G.ac C a = 0) :
    ∃ a ∈ A, 0 < bipLeftDegree G.ab B a ∧
      0 < bipLeftDegree G.ac C a := by
  simp only [not_forall, not_or] at hNot
  obtain ⟨a, ha, hAB, hAC⟩ := hNot
  exact ⟨a, ha, Nat.pos_of_ne_zero hAB, Nat.pos_of_ne_zero hAC⟩

private theorem tripartiteLocalPayment_bound :
    ∀ n : ℕ, ∀ (G : TripartitePairGraphs α) (A B C : Finset α),
      A.card + B.card + C.card ≤ n →
      MixedNodeDegreeTwo G A B C →
      TripartiteLocalPayment G A B C := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G A B C hSize hMixed
    by_cases hPureA : ∀ a ∈ A,
        bipLeftDegree G.ab B a = 0 ∨
          bipLeftDegree G.ac C a = 0
    · by_cases hPureB : ∀ b ∈ B,
          bipRightDegree G.ab A b = 0 ∨
            bipLeftDegree G.bc C b = 0
      · by_cases hPureC : ∀ c ∈ C,
            bipRightDegree G.ac A c = 0 ∨
              bipRightDegree G.bc B c = 0
        · exact pure_tripartite_local_payment G A B C
            hPureA hPureB hPureC
        · obtain ⟨c, hc, hAC, hBC⟩ := by
            simpa only [not_forall, not_or] using hPureC
          let G' := rotatePartsBCA (swapPartsBC G)
          have hMixedSwap : MixedNodeDegreeTwo
              (swapPartsBC G) A C B :=
            mixedNodeDegreeTwo_swapPartsBC G A B C hMixed
          have hMixed' : MixedNodeDegreeTwo G' C B A :=
            mixedNodeDegreeTwo_rotatePartsBCA
              (swapPartsBC G) A C B hMixedSwap
          have hFirstAB : 0 < bipLeftDegree G'.ab B c := by
            change 0 < bipLeftDegree (bipTranspose G.bc) B c
            rw [bipLeftDegree_transpose]
            exact Nat.pos_of_ne_zero hBC
          have hFirstAC : 0 < bipLeftDegree G'.ac A c := by
            change 0 < bipLeftDegree (bipTranspose G.ac) A c
            rw [bipLeftDegree_transpose]
            exact Nat.pos_of_ne_zero hAC
          have hMixedOld : MixedNodeDegreeTwo G'
              (C.erase c) B A :=
            mixedNodeDegreeTwo_restrict_left G' B A
              (Finset.erase_subset c C) hMixed'
          have hLess : (C.erase c).card + B.card + A.card < n := by
            have hCard := Finset.card_erase_add_one hc
            omega
          have hOld : TripartiteLocalPayment G' (C.erase c) B A :=
            ih _ hLess G' (C.erase c) B A le_rfl hMixedOld
          have hNew : TripartiteLocalPayment G' C B A :=
            mixed_first_local_payment_of_smaller G' C B A c
              hc hMixed' hFirstAB hFirstAC hOld
          exact (tripartiteLocalPayment_swapPartsBC G A B C).mp
            ((tripartiteLocalPayment_rotatePartsBCA
              (swapPartsBC G) A C B).mp hNew)
      · obtain ⟨b, hb, hAB, hBC⟩ := by
          simpa only [not_forall, not_or] using hPureB
        let G' := rotatePartsBCA G
        have hMixed' : MixedNodeDegreeTwo G' B C A :=
          mixedNodeDegreeTwo_rotatePartsBCA G A B C hMixed
        have hFirstAB : 0 < bipLeftDegree G'.ab C b :=
          Nat.pos_of_ne_zero hBC
        have hFirstAC : 0 < bipLeftDegree G'.ac A b := by
          change 0 < bipLeftDegree (bipTranspose G.ab) A b
          rw [bipLeftDegree_transpose]
          exact Nat.pos_of_ne_zero hAB
        have hMixedOld : MixedNodeDegreeTwo G'
            (B.erase b) C A :=
          mixedNodeDegreeTwo_restrict_left G' C A
            (Finset.erase_subset b B) hMixed'
        have hLess : (B.erase b).card + C.card + A.card < n := by
          have hCard := Finset.card_erase_add_one hb
          omega
        have hOld : TripartiteLocalPayment G' (B.erase b) C A :=
          ih _ hLess G' (B.erase b) C A le_rfl hMixedOld
        have hNew : TripartiteLocalPayment G' B C A :=
          mixed_first_local_payment_of_smaller G' B C A b
            hb hMixed' hFirstAB hFirstAC hOld
        exact (tripartiteLocalPayment_rotatePartsBCA G A B C).mp hNew
    · obtain ⟨a, ha, hAB, hAC⟩ :=
        mixed_first_exists_of_not_pure G A B C hPureA
      have hMixedOld : MixedNodeDegreeTwo G (A.erase a) B C :=
        mixedNodeDegreeTwo_restrict_left G B C
          (Finset.erase_subset a A) hMixed
      have hLess : (A.erase a).card + B.card + C.card < n := by
        have hCard := Finset.card_erase_add_one ha
        omega
      have hOld : TripartiteLocalPayment G (A.erase a) B C :=
        ih _ hLess G (A.erase a) B C le_rfl hMixedOld
      exact mixed_first_local_payment_of_smaller G A B C a
        ha hMixed hAB hAC hOld

/-- §II.A's full local graph theorem.  It includes isolated nodes,
all pair-type patterns, and arbitrary finite sparse edge sets. -/
theorem tripartite_local_payment
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (hMixed : MixedNodeDegreeTwo G A B C) :
    TripartiteLocalPayment G A B C :=
  tripartiteLocalPayment_bound
    (A.card + B.card + C.card) G A B C le_rfl hMixed

end JSP523.Rank3
