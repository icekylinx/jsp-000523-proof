import JSP523.Rank3.FirstMoment
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite exceptional-edge bounds for bounded-label separation

This file formalizes the first two deletions in §III.A.5: four-edges
containing a Q-triple, and four-edges supported by two intersecting pair
cores in one fixed-center link.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Four-edges containing at least one actual triple from `Q`. -/
def internalQTripleEdges (F Q : Family α) : Family α :=
  F.filter fun E => ∃ T ∈ Q, T ⊆ E

/-- Pair codegree of the triple system, in actual containing-edge form. -/
def qPairDegree (Q : Family α) (P : Edge α) : ℕ :=
  (JSP523.Rank3.containingEdges Q P).card

/-- The internal-triple exception has at most `D` times the number of Q
triples edges. -/
theorem internalQTripleEdges_card_le
    (F Q : Family α) (D : ℕ)
    (hFacet : ∀ T ∈ Q,
      (F.filter fun E => T ⊆ E).card ≤ D) :
    (internalQTripleEdges F Q).card ≤ D * Q.card := by
  classical
  let S := Q.biUnion fun T => F.filter fun E => T ⊆ E
  have hSub : internalQTripleEdges F Q ⊆ S := by
    intro E hE
    obtain ⟨T, hT, hTE⟩ := (Finset.mem_filter.mp hE).2
    exact Finset.mem_biUnion.mpr ⟨T, hT,
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hE).1, hTE⟩⟩
  calc
    (internalQTripleEdges F Q).card ≤ S.card := Finset.card_le_card hSub
    _ ≤ ∑ T ∈ Q, (F.filter fun E => T ⊆ E).card := by
      dsimp [S]
      exact Finset.card_biUnion_le
    _ ≤ ∑ _T ∈ Q, D := by
      apply Finset.sum_le_sum
      intro T hT
      exact hFacet T hT
    _ = D * Q.card := by simp [mul_comm]

/-- A pair-degree cap bounds the number of triples in `Q` by the number
of ambient pairs times the cap. -/
theorem q_card_le_pairCount_mul_pairDegree
    (Q : Family α) (U : Edge α) (κ : ℕ)
    (hUniform : Uniform 3 Q)
    (hGround : ∀ T ∈ Q, T ⊆ U)
    (hPair : ∀ P ∈ U.powersetCard 2, qPairDegree Q P ≤ κ) :
    Q.card ≤ (U.powersetCard 2).card * κ := by
  classical
  have hMoment := JSP523.Rank3.containingEdges_first_moment Q U
    hUniform hGround
  have hBound :
      (∑ P ∈ U.powersetCard 2,
        (JSP523.Rank3.containingEdges Q P).card) ≤
        (U.powersetCard 2).card * κ := by
    calc
      _ ≤ ∑ _P ∈ U.powersetCard 2, κ := by
        apply Finset.sum_le_sum
        intro P hP
        exact hPair P hP
      _ = _ := by simp
  rw [hMoment] at hBound
  omega

/-- The first bounded-label exception bound: removing all four-edges that
contain an internal Q-triple costs at most `D κ binom(|U|,2)`. -/
theorem internalQTripleEdges_card_le_degree_caps
    (F Q : Family α) (U : Edge α) (D κ : ℕ)
    (hUniform : Uniform 3 Q)
    (hGround : ∀ T ∈ Q, T ⊆ U)
    (hPair : ∀ P ∈ U.powersetCard 2, qPairDegree Q P ≤ κ)
    (hFacet : ∀ T ∈ Q,
      (F.filter fun E => T ⊆ E).card ≤ D) :
    (internalQTripleEdges F Q).card ≤
      D * κ * (U.powersetCard 2).card := by
  calc
    _ ≤ D * Q.card := internalQTripleEdges_card_le F Q D hFacet
    _ ≤ D * ((U.powersetCard 2).card * κ) :=
      Nat.mul_le_mul_left D (q_card_le_pairCount_mul_pairDegree
        Q U κ hUniform hGround hPair)
    _ = D * κ * (U.powersetCard 2).card := by ring

/-- Ordered witnesses for a shared-endpoint pair-core wedge.  The roots
`{x,a}` have two distinct completion vertices b and c in Q. -/
def qLinkWedgeIndices (Q : Family α) (U : Edge α) :=
  U.sigma fun x => (U.erase x).sigma fun a =>
    let C := JSP523.Rank3.completionVertices Q U {x, a}
    (C.product C).filter fun bc => bc.1 ≠ bc.2

/-- Three-vertex core shared by the two link pair roots of a wedge. -/
def qLinkWedgeCore (w : Σ _x : α, Σ _a : α, α × α) : Edge α :=
  insert w.2.2.2 ({w.2.1, w.2.2.1} : Edge α)

/-- A genuine wedge produces a three-element common core. -/
theorem qLinkWedgeCore_card
    (Q : Family α) (U : Edge α) (w : Σ _x : α, Σ _a : α, α × α)
    (hw : w ∈ qLinkWedgeIndices Q U) : (qLinkWedgeCore w).card = 3 := by
  classical
  have hw' := Finset.mem_sigma.mp hw
  have hw'' := Finset.mem_sigma.mp hw'.2
  have ha : w.2.1 ∈ U.erase w.1 := hw''.1
  have hbc : w.2.2 ∈
      ((JSP523.Rank3.completionVertices Q U {w.1, w.2.1}).product
        (JSP523.Rank3.completionVertices Q U {w.1, w.2.1})).filter
          fun bc => bc.1 ≠ bc.2 := by
    simpa [qLinkWedgeIndices] using hw''.2
  have hfilter := Finset.mem_filter.mp hbc
  have hb := (Finset.mem_product.mp hfilter.1).1
  have hc := (Finset.mem_product.mp hfilter.1).2
  have hDiff := hfilter.2
  have hbNot := (Finset.mem_filter.mp hb).2.1
  have hcNot := (Finset.mem_filter.mp hc).2.1
  have hba : w.2.1 ≠ w.2.2.1 := by
    intro h
    apply hbNot
    simp [h]
  have hca : w.2.2.2 ≠ w.2.1 := by
    intro h
    apply hcNot
    simp [h]
  have hcb : w.2.2.2 ≠ w.2.2.1 := hDiff.symm
  have hCoreNot : w.2.2.2 ∉ ({w.2.1, w.2.2.1} : Edge α) := by
    simp [hca, hcb]
  rw [qLinkWedgeCore, Finset.card_insert_of_notMem hCoreNot,
    Finset.card_pair hba]

/-- The actual completion set of any ambient pair has size at most κ. -/
theorem completionVertices_card_le_qPairDegree
    (Q : Family α) (U P : Edge α) (κ : ℕ)
    (hUniform : Uniform 3 Q) (hGround : ∀ T ∈ Q, T ⊆ U)
    (hP : P ∈ U.powersetCard 2)
    (hPair : qPairDegree Q P ≤ κ) :
    (JSP523.Rank3.completionVertices Q U P).card ≤ κ := by
  rw [JSP523.Rank3.completionVertices_card_eq_containingEdges
    Q U P hUniform hGround hP]
  exact hPair

/-- There are at most `|U|² κ²` ordered shared-endpoint wedges. -/
theorem qLinkWedgeIndices_card_le
    (Q : Family α) (U : Edge α) (κ : ℕ)
    (hUniform : Uniform 3 Q)
    (hGround : ∀ T ∈ Q, T ⊆ U)
    (hPair : ∀ P ∈ U.powersetCard 2, qPairDegree Q P ≤ κ) :
    (qLinkWedgeIndices Q U).card ≤ U.card ^ 2 * κ ^ 2 := by
  classical
  let C (x a : α) := JSP523.Rank3.completionVertices Q U {x, a}
  have hC (x a : α) (hx : x ∈ U) (ha : a ∈ U.erase x) :
      (C x a).card ≤ κ := by
    have hxa : x ≠ a := (Finset.mem_erase.mp ha).1.symm
    have hP : ({x, a} : Edge α) ∈ U.powersetCard 2 := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, Finset.card_pair hxa⟩
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact (Finset.mem_erase.mp ha).2
    exact completionVertices_card_le_qPairDegree Q U {x, a} κ
      hUniform hGround hP (hPair {x, a} hP)
  have hFiber (x : α) (hx : x ∈ U) :
      (∑ a ∈ U.erase x,
        (((C x a).product (C x a)).filter fun bc => bc.1 ≠ bc.2).card) ≤
        U.card * κ ^ 2 := by
    calc
      _ ≤ ∑ a ∈ U.erase x, κ ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        calc
          (((C x a).product (C x a)).filter fun bc => bc.1 ≠ bc.2).card ≤
              ((C x a).product (C x a)).card := Finset.card_filter_le _ _
          _ = (C x a).card * (C x a).card := Finset.card_product _ _
          _ ≤ κ ^ 2 := by
            simpa [pow_two] using Nat.mul_self_le_mul_self (hC x a hx ha)
      _ = (U.erase x).card * κ ^ 2 := by simp
      _ ≤ U.card * κ ^ 2 := Nat.mul_le_mul_right _ Finset.card_erase_le
  have hTotal :
      (∑ x ∈ U, ∑ a ∈ U.erase x,
        (((C x a).product (C x a)).filter fun bc => bc.1 ≠ bc.2).card) ≤
        U.card * (U.card * κ ^ 2) := by
    calc
      _ ≤ ∑ x ∈ U, U.card * κ ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        exact hFiber x hx
      _ = U.card * (U.card * κ ^ 2) := by simp
  have hCard : (qLinkWedgeIndices Q U).card =
      ∑ x ∈ U, ∑ a ∈ U.erase x,
        (((C x a).product (C x a)).filter fun bc => bc.1 ≠ bc.2).card := by
    unfold qLinkWedgeIndices
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.card_sigma]
  calc
    (qLinkWedgeIndices Q U).card = _ := hCard
    _ ≤ U.card * (U.card * κ ^ 2) := hTotal
    _ = U.card ^ 2 * κ ^ 2 := by ring

/-- Actual four-edges containing a shared-endpoint wedge core. -/
def sharedEndpointCoreEdges (F Q : Family α) (U : Edge α) : Family α :=
  F.filter fun E => ∃ w ∈ qLinkWedgeIndices Q U, qLinkWedgeCore w ⊆ E

/-- Charge each edge containing a wedge core to an actual wedge and then
to one of at most D completions of its fixed triple. -/
theorem sharedEndpointCoreEdges_card_le
    (F Q : Family α) (U : Edge α) (D : ℕ)
    (hFacet : ∀ T : Edge α, T.card = 3 →
      (F.filter fun E => T ⊆ E).card ≤ D) :
    (sharedEndpointCoreEdges F Q U).card ≤
      D * (qLinkWedgeIndices Q U).card := by
  classical
  let W := qLinkWedgeIndices Q U
  let S := W.biUnion fun w => F.filter fun E => qLinkWedgeCore w ⊆ E
  have hSub : sharedEndpointCoreEdges F Q U ⊆ S := by
    intro E hE
    obtain ⟨w, hw, hcore⟩ := (Finset.mem_filter.mp hE).2
    exact Finset.mem_biUnion.mpr ⟨w, hw,
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hE).1, hcore⟩⟩
  calc
    _ ≤ S.card := Finset.card_le_card hSub
    _ ≤ ∑ w ∈ W, (F.filter fun E => qLinkWedgeCore w ⊆ E).card := by
      dsimp [S]
      exact Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ W, D := by
      apply Finset.sum_le_sum
      intro w hw
      exact hFacet (qLinkWedgeCore w) (qLinkWedgeCore_card Q U w hw)
    _ = D * W.card := by simp [mul_comm]

/-- The actual finite budget for shared-endpoint pair-core exceptions. -/
theorem sharedEndpointCoreEdges_card_le_degree_caps
    (F Q : Family α) (U : Edge α) (D κ : ℕ)
    (hUniform : Uniform 3 Q)
    (hGround : ∀ T ∈ Q, T ⊆ U)
    (hPair : ∀ P ∈ U.powersetCard 2, qPairDegree Q P ≤ κ)
    (hFacet : ∀ T : Edge α, T.card = 3 →
      (F.filter fun E => T ⊆ E).card ≤ D) :
    (sharedEndpointCoreEdges F Q U).card ≤ D * U.card ^ 2 * κ ^ 2 := by
  calc
    _ ≤ D * (qLinkWedgeIndices Q U).card :=
      sharedEndpointCoreEdges_card_le F Q U D hFacet
    _ ≤ D * (U.card ^ 2 * κ ^ 2) :=
      Nat.mul_le_mul_left D (qLinkWedgeIndices_card_le Q U κ
        hUniform hGround hPair)
    _ = D * U.card ^ 2 * κ ^ 2 := by ring

end JSP523.Rank4
