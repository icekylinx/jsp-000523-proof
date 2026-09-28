import JSP523.Counting.PrefixCollisionCount

/-!
# Prefix counting for an actual chosen-prefix assignment

Each edge has one chosen prefix, and its residual tail is its set
complement in that edge.  This file proves the mass identity and the
four-codegree multiplicity bound, then instantiates the finite quadratic
inequality.  The geometric common-tail cap remains explicitly visible.
-/

namespace JSP523.Counting

open Finset
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- Prefixes actually assigned to the indicated tail. -/
def chosenPrefixesAt (K : Family α) (V : Edge α) (p : ℕ)
    (chosenPrefix : Edge α → Edge α) (P : Edge α) : Family α :=
  (V.powersetCard p).filter (fun Y =>
    Disjoint Y P ∧ Y ∪ P ∈ K ∧ chosenPrefix (Y ∪ P) = Y)

theorem mem_chosen_prefixes_at {K : Family α} {V : Edge α} {p : ℕ}
    {chosenPrefix : Edge α → Edge α} {P Y : Edge α} :
    Y ∈ chosenPrefixesAt K V p chosenPrefix P ↔
      Y ∈ V.powersetCard p ∧ Disjoint Y P ∧
        Y ∪ P ∈ K ∧ chosenPrefix (Y ∪ P) = Y := by
  simp only [chosenPrefixesAt, Finset.mem_filter]

/-- Chosen prefixes at a fixed tail reconstruct distinct actual edges. -/
theorem chosen_prefix_union_inj
    {K : Family α} {V : Edge α} {p : ℕ} {chosenPrefix : Edge α → Edge α}
    {P Y Z : Edge α}
    (hY : Y ∈ chosenPrefixesAt K V p chosenPrefix P)
    (hZ : Z ∈ chosenPrefixesAt K V p chosenPrefix P)
    (hEq : Y ∪ P = Z ∪ P) : Y = Z := by
  have hY' := mem_chosen_prefixes_at.mp hY
  have hZ' := mem_chosen_prefixes_at.mp hZ
  exact hY'.2.2.2.symm.trans ((congrArg chosenPrefix hEq).trans hZ'.2.2.2)

/-- Every edge contributes exactly one assigned prefix/tail pair. -/
theorem chosen_prefix_mass_identity
    (K : Family α) (V : Edge α) (r : ℕ) (chosenPrefix : Edge α → Edge α)
    (hr : 3 ≤ r) (hUniform : Uniform r K)
    (hGround : ∀ E ∈ K, E ⊆ V)
    (hPrefixSub : ∀ E ∈ K, chosenPrefix E ⊆ E)
    (hPrefixCard : ∀ E ∈ K, (chosenPrefix E).card = r - 3) :
    (∑ P ∈ V.powersetCard 3,
      (chosenPrefixesAt K V (r - 3) chosenPrefix P).card) = K.card := by
  classical
  let I := ((V.powersetCard 3) ×ˢ (V.powersetCard (r - 3))).filter
    (fun PY => Disjoint PY.2 PY.1 ∧ PY.2 ∪ PY.1 ∈ K ∧
      chosenPrefix (PY.2 ∪ PY.1) = PY.2)
  let join : Edge α × Edge α → Edge α := fun PY => PY.2 ∪ PY.1
  have hImage : I.image join = K := by
    ext E
    constructor
    · intro hE
      obtain ⟨PY, hPY, rfl⟩ := Finset.mem_image.mp hE
      exact (Finset.mem_filter.mp hPY).2.2.1
    · intro hE
      let Y := chosenPrefix E
      let P := E \ Y
      have hYE : Y ⊆ E := hPrefixSub E hE
      have hYc : Y.card = r - 3 := hPrefixCard E hE
      have hEc : E.card = r := hUniform hE
      have hPc : P.card = 3 := by
        have := Finset.card_sdiff_add_card_eq_card hYE
        change (E \ Y).card = 3
        omega
      have hYP : Disjoint Y P := by
        exact Finset.disjoint_left.mpr
          (fun x hxY hxP => (Finset.mem_sdiff.mp hxP).2 hxY)
      have hJoin : Y ∪ P = E := Finset.union_sdiff_of_subset hYE
      have hPY : (P, Y) ∈ I := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hYP, ?_, ?_⟩
        · exact Finset.mem_powersetCard.mpr
            ⟨Finset.sdiff_subset.trans (hGround E hE), hPc⟩
        · exact Finset.mem_powersetCard.mpr ⟨hYE.trans (hGround E hE), hYc⟩
        · simpa only [hJoin] using hE
        · rw [hJoin]
      exact Finset.mem_image.mpr ⟨(P, Y), hPY, hJoin⟩
  have hInj : Set.InjOn join (I : Set (Edge α × Edge α)) := by
    intro PY hPY QZ hQZ hEq
    change PY.2 ∪ PY.1 = QZ.2 ∪ QZ.1 at hEq
    have hPY' := (Finset.mem_filter.mp hPY).2
    have hQZ' := (Finset.mem_filter.mp hQZ).2
    have hYZ : PY.2 = QZ.2 :=
      hPY'.2.2.symm.trans ((congrArg chosenPrefix hEq).trans hQZ'.2.2)
    have hPQ : PY.1 = QZ.1 := by
      calc
        PY.1 = (PY.2 ∪ PY.1) \ PY.2 :=
          (Finset.union_sdiff_cancel_left hPY'.1).symm
        _ = (QZ.2 ∪ QZ.1) \ QZ.2 := by rw [hEq, hYZ]
        _ = QZ.1 := Finset.union_sdiff_cancel_left hQZ'.1
    exact Prod.ext hPQ hYZ
  have hCount : I.card = K.card := by
    rw [← hImage, Finset.card_image_of_injOn hInj]
  have hRows : I.card = ∑ P ∈ V.powersetCard 3,
      (chosenPrefixesAt K V (r - 3) chosenPrefix P).card := by
    simp only [I, chosenPrefixesAt, Finset.card_filter]
    exact Finset.sum_product' (V.powersetCard 3) (V.powersetCard (r - 3))
      (fun P Y => if Disjoint Y P ∧ Y ∪ P ∈ K ∧ chosenPrefix (Y ∪ P) = Y
        then (1 : ℕ) else 0)
  exact hRows.symm.trans hCount

/-- A vertex in assigned prefixes gives distinct actual edges through the
fixed four-set consisting of that vertex and the three-element tail. -/
theorem chosen_prefix_vertex_degree_le
    (K : Family α) (V : Edge α) (p D : ℕ) (chosenPrefix : Edge α → Edge α)
    (hD : ∀ Q : Edge α, Q.card = 4 →
      (K.filter (fun E => Q ⊆ E)).card ≤ D)
    {P : Edge α} (hP : P ∈ V.powersetCard 3) (x : α) :
    ((chosenPrefixesAt K V p chosenPrefix P).filter (fun Y => x ∈ Y)).card ≤ D := by
  classical
  let A := chosenPrefixesAt K V p chosenPrefix P
  change (A.filter (fun Y => x ∈ Y)).card ≤ D
  by_cases hxP : x ∈ P
  · have hEmpty : A.filter (fun Y => x ∈ Y) = ∅ := by
      ext Y
      constructor
      · intro hY
        obtain ⟨hYA, hxY⟩ := Finset.mem_filter.mp hY
        have hYP := (mem_chosen_prefixes_at.mp hYA).2.1
        exact False.elim ((Finset.disjoint_left.mp hYP) hxY hxP)
      · simp
    simp only [hEmpty, Finset.card_empty, Nat.zero_le]
  · have hQc : (insert x P).card = 4 := by
      rw [Finset.card_insert_of_notMem hxP, (Finset.mem_powersetCard.mp hP).2]
    have hCount : (A.filter (fun Y => x ∈ Y)).card ≤
        (K.filter (fun E => insert x P ⊆ E)).card := by
      apply Finset.card_le_card_of_injOn (fun Y => Y ∪ P)
      · intro Y hY
        obtain ⟨hYA, hxY⟩ := Finset.mem_filter.mp hY
        have hYA' := mem_chosen_prefixes_at.mp hYA
        apply Finset.mem_filter.mpr
        refine ⟨hYA'.2.2.1, ?_⟩
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | haP
        · exact Finset.mem_union_left P hxY
        · exact Finset.mem_union_right Y haP
      · intro Y hY Z hZ hEq
        exact chosen_prefix_union_inj (Finset.mem_filter.mp hY).1
          (Finset.mem_filter.mp hZ).1 hEq
    exact hCount.trans (hD _ hQc)

/-- (IV.B.1) for actual edge assignments, with the common-tail cap (IV.B.2)
as its sole structural input. All codegrees and cardinalities are actual. -/
theorem actual_prefix_collision_bound
    (K : Family α) (V : Edge α) (r D B : ℕ) (chosenPrefix : Edge α → Edge α)
    (hr : 3 ≤ r) (hDpos : 1 ≤ D) (hUniform : Uniform r K)
    (hGround : ∀ E ∈ K, E ⊆ V)
    (hPrefixSub : ∀ E ∈ K, chosenPrefix E ⊆ E)
    (hPrefixCard : ∀ E ∈ K, (chosenPrefix E).card = r - 3)
    (hD : ∀ Q : Edge α, Q.card = 4 →
      (K.filter (fun E => Q ⊆ E)).card ≤ D)
    (hCommon : ∀ Y ∈ V.powersetCard (r - 3),
      ∀ Z ∈ V.powersetCard (r - 3), Disjoint Y Z →
      ((V.powersetCard 3).filter (fun P =>
        Y ∈ chosenPrefixesAt K V (r - 3) chosenPrefix P ∧
        Z ∈ chosenPrefixesAt K V (r - 3) chosenPrefix P)).card ≤ B) :
    K.card ^ 2 ≤ V.card.choose 3 *
      ((1 + (r - 3) * (D - 1)) * K.card +
        V.card.choose (r - 3) * (V.card - (r - 3)).choose (r - 3) * B) := by
  have h := prefix_collision_quadratic_bound V (V.powersetCard 3)
    (r - 3) D B (chosenPrefixesAt K V (r - 3) chosenPrefix) hDpos
    (by intro P hP; exact Finset.filter_subset _ _)
    (by intro P hP x; exact chosen_prefix_vertex_degree_le K V (r - 3) D chosenPrefix hD hP x)
    hCommon
  rw [chosen_prefix_mass_identity K V r chosenPrefix hr hUniform hGround
    hPrefixSub hPrefixCard, Finset.card_powersetCard] at h
  exact h

/-- The exact real-budget version of (IV.B.1) for actual assignments. -/
theorem actual_prefix_collision_bound_real
    (K : Family α) (V : Edge α) (r D : ℕ) (B : ℝ)
    (chosenPrefix : Edge α → Edge α)
    (hr : 3 ≤ r) (hDpos : 1 ≤ D) (hUniform : Uniform r K)
    (hGround : ∀ E ∈ K, E ⊆ V)
    (hPrefixSub : ∀ E ∈ K, chosenPrefix E ⊆ E)
    (hPrefixCard : ∀ E ∈ K, (chosenPrefix E).card = r - 3)
    (hD : ∀ Q : Edge α, Q.card = 4 →
      (K.filter (fun E => Q ⊆ E)).card ≤ D)
    (hCommon : ∀ Y ∈ V.powersetCard (r - 3),
      ∀ Z ∈ V.powersetCard (r - 3), Disjoint Y Z →
      (((V.powersetCard 3).filter (fun P =>
        Y ∈ chosenPrefixesAt K V (r - 3) chosenPrefix P ∧
        Z ∈ chosenPrefixesAt K V (r - 3) chosenPrefix P)).card : ℝ) ≤ B) :
    (K.card : ℝ) ^ 2 ≤ (V.card.choose 3 : ℝ) *
      (((1 + (r - 3) * (D - 1) : ℕ) : ℝ) * (K.card : ℝ) +
        ((V.card.choose (r - 3) *
          (V.card - (r - 3)).choose (r - 3) : ℕ) : ℝ) * B) := by
  have h := prefix_collision_quadratic_bound_real V (V.powersetCard 3)
    (r - 3) D B (chosenPrefixesAt K V (r - 3) chosenPrefix) hDpos
    (by intro P hP; exact Finset.filter_subset _ _)
    (by intro P hP x; exact chosen_prefix_vertex_degree_le K V (r - 3) D chosenPrefix hD hP x)
    hCommon
  rw [chosen_prefix_mass_identity K V r chosenPrefix hr hUniform hGround
    hPrefixSub hPrefixCard, Finset.card_powersetCard] at h
  exact h

end JSP523.Counting
