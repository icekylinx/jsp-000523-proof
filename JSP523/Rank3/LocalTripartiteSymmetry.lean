import JSP523.Rank3.LocalTripartitePure

/-!
# Symmetries of the tripartite local graph

The positive-pair theorem was proved with `AB` as the distinguished type.
These relabelings transport it to `AC` and `BC`, including the oriented
finite edge sets and the mixed-node degree-two hypothesis.
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

def swapPartsBC (G : TripartitePairGraphs α) :
    TripartitePairGraphs α :=
  ⟨G.ac, G.ab, bipTranspose G.bc⟩

theorem mixedNodeDegreeTwo_swapPartsBC
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (hMixed : MixedNodeDegreeTwo G A B C) :
    MixedNodeDegreeTwo (swapPartsBC G) A C B := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha hAC hAB
    have h := hMixed.1 a ha hAB hAC
    exact ⟨h.2, h.1⟩
  · intro c hc hAC hBC
    have hBC' : 0 < bipRightDegree G.bc B c := by
      change 0 < bipLeftDegree (bipTranspose G.bc) B c at hBC
      rw [bipLeftDegree_transpose] at hBC
      exact hBC
    have h := hMixed.2.2 c hc hAC hBC'
    change bipRightDegree G.ac A c = 1 ∧
      bipLeftDegree (bipTranspose G.bc) B c = 1
    rw [bipLeftDegree_transpose]
    exact h
  · intro b hb hAB hBC
    have hBC' : 0 < bipLeftDegree G.bc C b := by
      change 0 < bipRightDegree (bipTranspose G.bc) C b at hBC
      rw [bipRightDegree_transpose] at hBC
      exact hBC
    have h := hMixed.2.1 b hb hAB hBC'
    change bipRightDegree G.ab A b = 1 ∧
      bipRightDegree (bipTranspose G.bc) C b = 1
    rw [bipRightDegree_transpose]
    exact h

theorem positive_ac_controls_other_types
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (hMixed : MixedNodeDegreeTwo G A B C)
    (hPositive :
      localGraphBudget A.card + localGraphBudget C.card <
        bipartitePhiTotal G.ac A C) :
    bipartitePhiTotal G.ab A B +
        bipartitePhiTotal G.bc B C ≤ localPhi B.card := by
  have h := positive_ab_controls_other_types
    (swapPartsBC G) A C B
    (mixedNodeDegreeTwo_swapPartsBC G A B C hMixed) hPositive
  simpa [swapPartsBC, bipartitePhiTotal_transpose, add_comm]
    using h

theorem positive_ac_local_payment
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (hMixed : MixedNodeDegreeTwo G A B C)
    (hPositive :
      localGraphBudget A.card + localGraphBudget C.card <
        bipartitePhiTotal G.ac A C) :
    localGraphBudget A.card + localGraphBudget B.card +
        localGraphBudget C.card ≤
      localGraphPayment A.card B.card C.card
        (bipartitePhiTotal G.ab A B)
        (bipartitePhiTotal G.ac A C)
        (bipartitePhiTotal G.bc B C) := by
  have h := positive_ab_local_payment
    (swapPartsBC G) A C B
    (mixedNodeDegreeTwo_swapPartsBC G A B C hMixed) hPositive
  have h' :
      localGraphBudget A.card + localGraphBudget C.card +
          localGraphBudget B.card ≤
        localGraphPayment A.card C.card B.card
          (bipartitePhiTotal G.ac A C)
          (bipartitePhiTotal G.ab A B)
          (bipartitePhiTotal G.bc B C) := by
    simpa [swapPartsBC, bipartitePhiTotal_transpose] using h
  rw [← localGraphPayment_swap_last_two A.card B.card C.card
    (bipartitePhiTotal G.ab A B)
    (bipartitePhiTotal G.ac A C)
    (bipartitePhiTotal G.bc B C)] at h'
  convert h' using 1
  ring

def rotatePartsBCA (G : TripartitePairGraphs α) :
    TripartitePairGraphs α :=
  ⟨G.bc, bipTranspose G.ab, bipTranspose G.ac⟩

theorem mixedNodeDegreeTwo_rotatePartsBCA
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (hMixed : MixedNodeDegreeTwo G A B C) :
    MixedNodeDegreeTwo (rotatePartsBCA G) B C A := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hb hBC hBA
    change 0 < bipLeftDegree (bipTranspose G.ab) A b at hBA
    rw [bipLeftDegree_transpose] at hBA
    have h := hMixed.2.1 b hb hBA hBC
    change bipLeftDegree G.bc C b = 1 ∧
      bipLeftDegree (bipTranspose G.ab) A b = 1
    rw [bipLeftDegree_transpose]
    exact ⟨h.2, h.1⟩
  · intro c hc hBC hCA
    change 0 < bipLeftDegree (bipTranspose G.ac) A c at hCA
    rw [bipLeftDegree_transpose] at hCA
    have h := hMixed.2.2 c hc hCA hBC
    change bipRightDegree G.bc B c = 1 ∧
      bipLeftDegree (bipTranspose G.ac) A c = 1
    rw [bipLeftDegree_transpose]
    exact ⟨h.2, h.1⟩
  · intro a ha hBA hCA
    change 0 < bipRightDegree (bipTranspose G.ab) B a at hBA
    change 0 < bipRightDegree (bipTranspose G.ac) C a at hCA
    rw [bipRightDegree_transpose] at hBA hCA
    have h := hMixed.1 a ha hBA hCA
    change bipRightDegree (bipTranspose G.ab) B a = 1 ∧
      bipRightDegree (bipTranspose G.ac) C a = 1
    rw [bipRightDegree_transpose, bipRightDegree_transpose]
    exact h

theorem positive_bc_local_payment
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (hMixed : MixedNodeDegreeTwo G A B C)
    (hPositive :
      localGraphBudget B.card + localGraphBudget C.card <
        bipartitePhiTotal G.bc B C) :
    localGraphBudget A.card + localGraphBudget B.card +
        localGraphBudget C.card ≤
      localGraphPayment A.card B.card C.card
        (bipartitePhiTotal G.ab A B)
        (bipartitePhiTotal G.ac A C)
        (bipartitePhiTotal G.bc B C) := by
  have h := positive_ab_local_payment
    (rotatePartsBCA G) B C A
    (mixedNodeDegreeTwo_rotatePartsBCA G A B C hMixed) hPositive
  have h' :
      localGraphBudget B.card + localGraphBudget C.card +
          localGraphBudget A.card ≤
        localGraphPayment B.card C.card A.card
          (bipartitePhiTotal G.bc B C)
          (bipartitePhiTotal G.ab A B)
          (bipartitePhiTotal G.ac A C) := by
    simpa [rotatePartsBCA, bipartitePhiTotal_transpose] using h
  have hPay :
      localGraphPayment A.card B.card C.card
          (bipartitePhiTotal G.ab A B)
          (bipartitePhiTotal G.ac A C)
          (bipartitePhiTotal G.bc B C) =
        localGraphPayment B.card C.card A.card
          (bipartitePhiTotal G.bc B C)
          (bipartitePhiTotal G.ab A B)
          (bipartitePhiTotal G.ac A C) := by
    calc
      _ = localGraphPayment B.card A.card C.card
          (bipartitePhiTotal G.ab A B)
          (bipartitePhiTotal G.bc B C)
          (bipartitePhiTotal G.ac A C) :=
        localGraphPayment_swap_first_two _ _ _ _ _ _
      _ = _ := localGraphPayment_swap_last_two _ _ _ _ _ _
  rw [hPay]
  convert h' using 1
  ring

/-- The local payment proposition, packaged for relabeling in the
mixed-node induction. -/
def TripartiteLocalPayment
    (G : TripartitePairGraphs α) (A B C : Finset α) : Prop :=
  localGraphBudget A.card + localGraphBudget B.card +
      localGraphBudget C.card ≤
    localGraphPayment A.card B.card C.card
      (bipartitePhiTotal G.ab A B)
      (bipartitePhiTotal G.ac A C)
      (bipartitePhiTotal G.bc B C)

theorem tripartiteLocalPayment_swapPartsBC
    (G : TripartitePairGraphs α) (A B C : Finset α) :
    TripartiteLocalPayment (swapPartsBC G) A C B ↔
      TripartiteLocalPayment G A B C := by
  unfold TripartiteLocalPayment
  simp only [swapPartsBC, bipartitePhiTotal_transpose]
  constructor
  · intro h
    rw [← localGraphPayment_swap_last_two A.card B.card C.card
      (bipartitePhiTotal G.ab A B)
      (bipartitePhiTotal G.ac A C)
      (bipartitePhiTotal G.bc B C)] at h
    linarith
  · intro h
    rw [localGraphPayment_swap_last_two A.card B.card C.card
      (bipartitePhiTotal G.ab A B)
      (bipartitePhiTotal G.ac A C)
      (bipartitePhiTotal G.bc B C)] at h
    linarith

theorem tripartiteLocalPayment_rotatePartsBCA
    (G : TripartitePairGraphs α) (A B C : Finset α) :
    TripartiteLocalPayment (rotatePartsBCA G) B C A ↔
      TripartiteLocalPayment G A B C := by
  unfold TripartiteLocalPayment
  simp only [rotatePartsBCA, bipartitePhiTotal_transpose]
  constructor
  · intro h
    rw [← localGraphPayment_swap_last_two B.card A.card C.card
      (bipartitePhiTotal G.ab A B)
      (bipartitePhiTotal G.bc B C)
      (bipartitePhiTotal G.ac A C),
      ← localGraphPayment_swap_first_two A.card B.card C.card
        (bipartitePhiTotal G.ab A B)
        (bipartitePhiTotal G.ac A C)
        (bipartitePhiTotal G.bc B C)] at h
    linarith
  · intro h
    rw [localGraphPayment_swap_first_two A.card B.card C.card
      (bipartitePhiTotal G.ab A B)
      (bipartitePhiTotal G.ac A C)
      (bipartitePhiTotal G.bc B C),
      localGraphPayment_swap_last_two B.card A.card C.card
        (bipartitePhiTotal G.ab A B)
        (bipartitePhiTotal G.bc B C)
        (bipartitePhiTotal G.ac A C)] at h
    linarith

end JSP523.Rank3
