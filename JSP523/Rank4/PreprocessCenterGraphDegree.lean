import JSP523.Rank4.PreprocessReciprocalDeletion
import JSP523.Rank4.PreprocessCellMoment
import JSP523.Rank4.PreprocessParentTails

/-!
# Center-graph degree from actual common cells

For each used completion pair `ar` labeled by `b`, every member of its
common cell yields an edge through `ab`.  Double counting these incidences
against facet completions bounds the degree of the center graph at `a`.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

private theorem incidence_card_bound
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

/-- Weak-cell clearing indexed by unordered pair roots also gives the
ordered distinct-pair version needed for center-graph incidences. -/
theorem common_triple_cells_cleared_of_common_roots
    (D₀ : FiniteCompletionCliqueData α) (t : ℕ)
    (hGround : ∀ E ∈ D₀.K, E ⊆ D₀.ground)
    (hRoots : ∀ P ∈ D₀.ground.powersetCard 2,
      (commonRootCell D₀.K D₀.ground P).card = 0 ∨
        t ≤ (commonRootCell D₀.K D₀.ground P).card)
    (a b : α) (hab : a ≠ b) :
    (commonTripleCell D₀.K D₀.ground a b).card = 0 ∨
      t ≤ (commonTripleCell D₀.K D₀.ground a b).card := by
  classical
  by_cases hZero : (commonTripleCell D₀.K D₀.ground a b).card = 0
  · exact Or.inl hZero
  obtain ⟨T, hT⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hZero)
  have hCell := mem_common_triple_cell.mp hT
  have ha : a ∈ D₀.ground := hGround (insert a T) hCell.2.2.2.1
    (Finset.mem_insert_self a T)
  have hb : b ∈ D₀.ground := hGround (insert b T) hCell.2.2.2.2
    (Finset.mem_insert_self b T)
  let P : Edge α := {a, b}
  have hPcard : P.card = 2 := Finset.card_pair hab
  have hPmem : P ∈ D₀.ground.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hPcard⟩
    intro x hx
    rcases (by simpa [P] using hx : x = a ∨ x = b) with rfl | rfl
    · exact ha
    · exact hb
  have hRootEq : commonRootCell D₀.K D₀.ground P =
      commonTripleCell D₀.K D₀.ground a b := by
    unfold commonRootCell
    simp only [dite_eq_left hPcard]
    apply common_triple_cell_eq_of_pair_eq
    simpa [P] using (pair_root_rep_spec P hPcard).2.symm
  have hFromRoots := hRoots P hPmem
  rw [hRootEq] at hFromRoots
  rcases hFromRoots with hEmpty | hLarge
  · exact False.elim (hZero hEmpty)
  · exact Or.inr hLarge

/-- The exact finite incidence estimate behind the center-graph bound in
§III.A.6. The endpoint `a` occupies one of the `D` facet-completion slots. -/
theorem reciprocal_used_label_fiber_mul_cell_min_le_pair_degree
    (D₀ : FiniteCompletionCliqueData α) (a b : α) (t D : ℕ)
    (ha : a ∈ D₀.ground)
    (hLarge : ∀ r ∈ reciprocalUsedLabelFiber D₀ a b,
      t ≤ (commonTripleCell D₀.K D₀.ground a r).card)
    (hFacet : ∀ T : Edge α, T.card = 3 →
      (facetCompletions D₀.K D₀.ground T).card ≤ D) :
    t * (reciprocalUsedLabelFiber D₀ a b).card ≤
      (D - 1) * rankFourPairDegree D₀.K ({a, b} : Edge α) := by
  classical
  let R := reciprocalUsedLabelFiber D₀ a b
  let S := D₀.K.filter fun E => ({a, b} : Edge α) ⊆ E
  let P : α → Edge α → Prop := fun r E =>
    E.erase a ∈ commonTripleCell D₀.K D₀.ground a r
  have hLower : ∀ r ∈ R, t ≤ (S.filter (P r)).card := by
    intro r hr
    let J := commonTripleCell D₀.K D₀.ground a r
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
        exact D₀.label_center a r (by
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
      rw [Finset.card_erase_of_mem haE, D₀.uniform_four hES'.1]
    have hSub : (R.filter fun r => P r E) ⊆
        facetCompletions D₀.K D₀.ground (E.erase a) := by
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
    have haComp : a ∈ facetCompletions D₀.K D₀.ground (E.erase a) := by
      apply Finset.mem_filter.mpr
      refine ⟨ha, ?_⟩
      simpa [Finset.insert_erase haE] using hES'.1
    have hSub' : insert a (R.filter fun r => P r E) ⊆
        facetCompletions D₀.K D₀.ground (E.erase a) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact haComp
      · exact hSub hx
    have hBound := (Finset.card_le_card hSub').trans (hFacet _ hCard)
    rw [Finset.card_insert_of_notMem haNot] at hBound
    omega
  simpa only [R, S, rankFourPairDegree] using
    incidence_card_bound R S P t (D - 1) hLower hUpper

/-- A weak-cell lower threshold and a pair-degree cap give a concrete bound
on every used center-graph fiber. -/
theorem reciprocal_used_label_fiber_card_le_of_degree_caps
    (D₀ : FiniteCompletionCliqueData α) (a b : α)
    (t D M : ℕ) (ht : 0 < t) (ha : a ∈ D₀.ground)
    (hCleared : ∀ x y : α, x ≠ y →
      (commonTripleCell D₀.K D₀.ground x y).card = 0 ∨
        t ≤ (commonTripleCell D₀.K D₀.ground x y).card)
    (hFacet : ∀ T : Edge α, T.card = 3 →
      (facetCompletions D₀.K D₀.ground T).card ≤ D)
    (hPair : rankFourPairDegree D₀.K ({a, b} : Edge α) ≤ M) :
    (reciprocalUsedLabelFiber D₀ a b).card ≤ (D - 1) * M / t := by
  have hLarge : ∀ r ∈ reciprocalUsedLabelFiber D₀ a b,
      t ≤ (commonTripleCell D₀.K D₀.ground a r).card := by
    intro r hr
    have hUsed := (Finset.mem_filter.mp hr).2
    have har := (Finset.mem_filter.mp
      (Finset.mem_filter.mp hr).1).2.1
    rcases hCleared a r har with hZero | hLarge
    · obtain ⟨T, hT⟩ := hUsed
      have hPos := Finset.card_pos.mpr ⟨T, hT⟩
      omega
    · exact hLarge
  have hIncidence := reciprocal_used_label_fiber_mul_cell_min_le_pair_degree
    D₀ a b t D ha hLarge hFacet
  have hBound : t * (reciprocalUsedLabelFiber D₀ a b).card ≤
      (D - 1) * M :=
    hIncidence.trans (Nat.mul_le_mul_left (D - 1) hPair)
  exact (Nat.le_div_iff_mul_le ht).2 (by
    simpa only [Nat.mul_comm] using hBound)

/-- A linear pair-degree budget together with the weak-cell threshold
provides the fixed center-graph degree cap consumed by reciprocal cleanup. -/
theorem reciprocal_used_label_fiber_card_le_of_scale_budget
    (D₀ : FiniteCompletionCliqueData α) (a b : α)
    (t D M Kstar : ℕ) (ht : 0 < t) (ha : a ∈ D₀.ground)
    (hCleared : ∀ x y : α, x ≠ y →
      (commonTripleCell D₀.K D₀.ground x y).card = 0 ∨
        t ≤ (commonTripleCell D₀.K D₀.ground x y).card)
    (hFacet : ∀ T : Edge α, T.card = 3 →
      (facetCompletions D₀.K D₀.ground T).card ≤ D)
    (hPair : rankFourPairDegree D₀.K ({a, b} : Edge α) ≤ M)
    (hScale : (D - 1) * M ≤ t * Kstar) :
    (reciprocalUsedLabelFiber D₀ a b).card ≤ Kstar := by
  have hDiv := reciprocal_used_label_fiber_card_le_of_degree_caps
    D₀ a b t D M ht ha hCleared hFacet hPair
  exact hDiv.trans (Nat.div_le_of_le_mul (by
    simpa only [Nat.mul_comm t Kstar] using hScale))

/-- If every parent edge lies in the ground set, a used pair has both
endpoints in that set. -/
theorem reciprocal_used_label_fiber_empty_of_outside_ground
    (D₀ : FiniteCompletionCliqueData α) (a b : α)
    (hGround : ∀ E ∈ D₀.K, E ⊆ D₀.ground)
    (ha : a ∉ D₀.ground) :
    reciprocalUsedLabelFiber D₀ a b = ∅ := by
  classical
  ext r
  constructor
  · intro hr
    obtain ⟨T, hT⟩ := (Finset.mem_filter.mp hr).2
    have hCell := mem_common_triple_cell.mp hT
    exact False.elim (ha (hGround (insert a T) hCell.2.2.2.1
      (Finset.mem_insert_self a T)))
  · intro hr
    simp at hr

end JSP523.Rank4
