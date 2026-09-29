import JSP523.Rank4.PreprocessBicoloredWedgeBudget
import JSP523.Rank4.PreprocessCenterGraphDegree

/-! # Center-graph bounds before the bicolored deletion -/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

private theorem raw_incidence_card_bound
    {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (R : Finset β) (S : Finset γ) (P : β → γ → Prop)
    [DecidableRel P]
    (t D : ℕ)
    (hLower : ∀ r ∈ R, t ≤ (S.filter (P r)).card)
    (hUpper : ∀ e ∈ S, (R.filter fun r => P r e).card ≤ D) :
    t * R.card ≤ D * S.card := by
  classical
  have hSwap :
      (∑ r ∈ R, (S.filter (P r)).card) =
        ∑ e ∈ S, (R.filter fun r => P r e).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  calc
    t * R.card = ∑ _r ∈ R, t := by simp [Nat.mul_comm]
    _ ≤ ∑ r ∈ R, (S.filter (P r)).card :=
      Finset.sum_le_sum hLower
    _ = ∑ e ∈ S, (R.filter fun r => P r e).card := hSwap
    _ ≤ ∑ _e ∈ S, D := Finset.sum_le_sum hUpper
    _ = D * S.card := by simp [Nat.mul_comm]

theorem raw_common_triple_cells_cleared_of_common_roots
    (K : Family α) (U : Edge α) (t : ℕ)
    (hGround : ∀ E ∈ K, E ⊆ U)
    (hRoots : ∀ P ∈ U.powersetCard 2,
      (commonRootCell K U P).card = 0 ∨
        t ≤ (commonRootCell K U P).card)
    (a b : α) (hab : a ≠ b) :
    (commonTripleCell K U a b).card = 0 ∨
      t ≤ (commonTripleCell K U a b).card := by
  classical
  by_cases hZero : (commonTripleCell K U a b).card = 0
  · exact Or.inl hZero
  obtain ⟨T, hT⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hZero)
  have hCell := mem_common_triple_cell.mp hT
  have ha : a ∈ U := hGround (insert a T) hCell.2.2.2.1
    (Finset.mem_insert_self a T)
  have hb : b ∈ U := hGround (insert b T) hCell.2.2.2.2
    (Finset.mem_insert_self b T)
  let P : Edge α := {a, b}
  have hPcard : P.card = 2 := Finset.card_pair hab
  have hPmem : P ∈ U.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hPcard⟩
    intro x hx
    rcases (by simpa [P] using hx : x = a ∨ x = b) with rfl | rfl
    · exact ha
    · exact hb
  have hRootEq : commonRootCell K U P =
      commonTripleCell K U a b := by
    unfold commonRootCell
    simp only [dite_eq_left hPcard]
    apply common_triple_cell_eq_of_pair_eq
    simpa [P] using (pair_root_rep_spec P hPcard).2.symm
  have hFromRoots := hRoots P hPmem
  rw [hRootEq] at hFromRoots
  rcases hFromRoots with hEmpty | hLarge
  · exact False.elim (hZero hEmpty)
  · exact Or.inr hLarge

theorem raw_used_label_fiber_mul_cell_min_le_pair_degree
    (K : Family α) (U : Edge α) (label : α → α → α)
    (hUniform : Uniform 4 K)
    (hCenter : ∀ x y, x ≠ y → ∀ T ∈ commonTripleCell K U x y, label x y ∈ T)
    (a b : α) (t D : ℕ)
    (ha : a ∈ U)
    (hLarge : ∀ r ∈ rawUsedCompletionLabelFiber K U label a b,
      t ≤ (commonTripleCell K U a r).card)
    (hFacet : ∀ T : Edge α, T.card = 3 →
      (facetCompletions K U T).card ≤ D) :
    t * (rawUsedCompletionLabelFiber K U label a b).card ≤
      (D - 1) * rankFourPairDegree K ({a, b} : Edge α) := by
  classical
  let R := rawUsedCompletionLabelFiber K U label a b
  let S := K.filter fun E => ({a, b} : Edge α) ⊆ E
  let P : α → Edge α → Prop := fun r E =>
    E.erase a ∈ commonTripleCell K U a r
  have hLower : ∀ r ∈ R, t ≤ (S.filter (P r)).card := by
    intro r hr
    let J := commonTripleCell K U a r
    have hMap : Set.MapsTo (fun T : Edge α => insert a T)
        (↑J : Set (Edge α)) (↑(S.filter (P r)) : Set (Edge α)) := by
      intro T hTJ
      have hCell := mem_common_triple_cell.mp hTJ
      have haT : a ∉ T := by
        intro ha
        exact (Finset.disjoint_left.mp hCell.2.2.1) ha (by simp)
      have hbT : b ∈ T := by
        have hrParts := Finset.mem_filter.mp hr
        have hrLabel := (Finset.mem_filter.mp hrParts.1).2.2
        rw [← hrLabel]
        exact hCenter a r (by
          intro har
          exact (Finset.mem_filter.mp hrParts.1).2.1 har)
          T hTJ
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hCell.2.2.2.1, ?_⟩, ?_⟩
      · intro x hx
        rcases (by simpa using hx : x = a ∨ x = b) with rfl | rfl
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem hbT
      · simpa [P, haT] using hTJ
    have hInj : (↑J : Set (Edge α)).InjOn (fun T => insert a T) := by
      intro T hT U hU hEq
      have haT : a ∉ T := by
        intro ha
        exact (Finset.disjoint_left.mp
          (mem_common_triple_cell.mp hT).2.2.1) ha (by simp)
      have haU : a ∉ U := by
        intro ha
        exact (Finset.disjoint_left.mp
          (mem_common_triple_cell.mp hU).2.2.1) ha (by simp)
      have hErase := congrArg (fun E : Edge α => E.erase a) hEq
      simpa [haT, haU] using hErase
    exact (hLarge r hr).trans
      (Finset.card_le_card_of_injOn (f := fun T => insert a T) hMap hInj)
  have hUpper : ∀ E ∈ S, (R.filter fun r => P r E).card ≤ D - 1 := by
    intro E hES
    have hES' := Finset.mem_filter.mp hES
    have haE : a ∈ E := hES'.2 (by simp)
    have hCard : (E.erase a).card = 3 := by
      rw [Finset.card_erase_of_mem haE, hUniform hES'.1]
    have hSub : (R.filter fun r => P r E) ⊆
        facetCompletions K U (E.erase a) := by
      intro r hr
      have hr' := Finset.mem_filter.mp hr
      have hCell := mem_common_triple_cell.mp hr'.2
      have hrGround := (Finset.mem_filter.mp
        (Finset.mem_filter.mp hr'.1).1).1
      exact Finset.mem_filter.mpr ⟨hrGround, hCell.2.2.2.2⟩
    have haNot : a ∉ R.filter (fun r => P r E) := by
      intro hMem
      have hR := (Finset.mem_filter.mp hMem).1
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).2.1 rfl
    have haComp : a ∈ facetCompletions K U (E.erase a) := by
      apply Finset.mem_filter.mpr
      refine ⟨ha, ?_⟩
      simpa [Finset.insert_erase haE] using hES'.1
    have hSub' : insert a (R.filter fun r => P r E) ⊆
        facetCompletions K U (E.erase a) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact haComp
      · exact hSub hx
    have hBound := (Finset.card_le_card hSub').trans (hFacet _ hCard)
    rw [Finset.card_insert_of_notMem haNot] at hBound
    omega
  simpa only [R, S, rankFourPairDegree] using
    raw_incidence_card_bound R S P t (D - 1) hLower hUpper

/-- The fixed-parent center graph has the required bounded used fibers
before any bicolored triangle is removed. -/
theorem raw_used_label_fiber_card_le_of_cleared_roots
    (K : Family α) (U : Edge α) (label : α → α → α) (t d M κ : ℕ)
    (hUniform : Uniform 4 K) (hGround : ∀ E ∈ K, E ⊆ U)
    (hCenter : ∀ x y, x ≠ y → ∀ T ∈ commonTripleCell K U x y, label x y ∈ T)
    (ht : 0 < t)
    (hRoots : ∀ P ∈ U.powersetCard 2,
      (commonRootCell K U P).card = 0 ∨ t ≤ (commonRootCell K U P).card)
    (hFacet : ∀ T : Edge α, T.card = 3 → (facetCompletions K U T).card ≤ d)
    (hPair : ∀ P : Edge α, P.card = 2 → rankFourPairDegree K P ≤ M)
    (hScale : (d - 1) * M ≤ t * κ) :
    ∀ a b, (rawUsedCompletionLabelFiber K U label a b).card ≤ κ := by
  intro a b
  by_cases hab : a = b
  · subst b
    have hEmpty : rawUsedCompletionLabelFiber K U label a a = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      have hrParts := Finset.mem_filter.mp hr
      have hrLabel := (Finset.mem_filter.mp hrParts.1).2
      obtain ⟨T, hT⟩ := hrParts.2
      have haT : a ∈ T := hrLabel.2 ▸ hCenter a r hrLabel.1 T hT
      exact (Finset.disjoint_left.mp (mem_common_triple_cell.mp hT).2.2.1) haT (by simp)
    simp [hEmpty]
  by_cases ha : a ∈ U
  · have hLarge : ∀ r ∈ rawUsedCompletionLabelFiber K U label a b,
        t ≤ (commonTripleCell K U a r).card := by
      intro r hr
      have hUsed := (Finset.mem_filter.mp hr).2
      have har := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.1
      have hCleared := raw_common_triple_cells_cleared_of_common_roots K U t hGround hRoots a r har
      have hPos := Finset.card_pos.mpr hUsed
      omega
    have hInc := raw_used_label_fiber_mul_cell_min_le_pair_degree K U label hUniform hCenter a b t d ha hLarge hFacet
    have hBound := Nat.mul_le_mul_left (d - 1) (hPair {a, b} (Finset.card_pair hab))
    nlinarith
  · have hEmpty : rawUsedCompletionLabelFiber K U label a b = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      obtain ⟨T, hT⟩ := (Finset.mem_filter.mp hr).2
      exact ha (hGround _ (mem_common_triple_cell.mp hT).2.2.2.1 (Finset.mem_insert_self a T))
    simp [hEmpty]

end JSP523.Rank4
