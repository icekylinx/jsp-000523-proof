import JSP523.Rank4.CommonTripleCells

/-!
# A finite small-cell deletion step for rank four

For a fixed pair of vertices, deleting the two endpoint facets of every
actual common triple clears that common cell at a cost at most twice its
size.  Iterating this step over pair roots is the finite core of the weak
cell clearing operation in §III.A.6.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- The two four-edges witnessing one actual common triple cell. -/
def commonCellEndpointEdges (H : Family α) (V : Edge α) (a b : α) : Family α :=
  (commonTripleCell H V a b).image (fun T => insert a T) ∪
    (commonTripleCell H V a b).image (fun T => insert b T)

/-- Removing the endpoint facets of a common cell costs at most twice the
number of triples in that cell. -/
theorem commonCellEndpointEdges_card_le
    (H : Family α) (V : Edge α) (a b : α) :
    (commonCellEndpointEdges H V a b).card ≤
      2 * (commonTripleCell H V a b).card := by
  unfold commonCellEndpointEdges
  calc
    _ ≤ ((commonTripleCell H V a b).image (fun T => insert a T)).card +
        ((commonTripleCell H V a b).image (fun T => insert b T)).card :=
          Finset.card_union_le _ _
    _ ≤ (commonTripleCell H V a b).card +
        (commonTripleCell H V a b).card := by
          exact Nat.add_le_add
            (Finset.card_image_le (f := fun T => insert a T))
            (Finset.card_image_le (f := fun T => insert b T))
    _ = 2 * (commonTripleCell H V a b).card := by omega

/-- Clear one actual common triple cell by deleting its two endpoint
facets.  The resulting family is a subfamily, and the number of deleted
edges is at most twice the old cell size. -/
theorem clear_commonTripleCell
    (H : Family α) (V : Edge α) (a b : α) :
    ∃ H' : Family α,
      H' ⊆ H ∧
      (commonTripleCell H' V a b).card = 0 ∧
      (H \ H').card ≤ 2 * (commonTripleCell H V a b).card := by
  let S := commonCellEndpointEdges H V a b
  let H' := H \ S
  refine ⟨H', ?_, ?_, ?_⟩
  · intro E hE
    exact Finset.mem_sdiff.mp hE |>.1
  · apply Finset.card_eq_zero.mpr
    ext T
    constructor
    · intro hT
      have hcell := (mem_commonTripleCell.mp hT)
      have hA : insert a T ∈ H' := by
        exact (mem_commonTripleCell.mp hT).2.2.2.1
      have hB : insert b T ∈ H' := by
        exact (mem_commonTripleCell.mp hT).2.2.2.2
      have hTold : T ∈ commonTripleCell H V a b := by
        apply mem_commonTripleCell.mpr
        refine ⟨hcell.1, hcell.2.1, hcell.2.2.1, ?_, ?_⟩
        · exact (Finset.mem_sdiff.mp hA).1
        · exact (Finset.mem_sdiff.mp hB).1
      have hAinS : insert a T ∈ S := by
        dsimp [S, commonCellEndpointEdges]
        apply Finset.mem_union.mpr
        left
        exact Finset.mem_image.mpr ⟨T, hTold, rfl⟩
      have hFalse : False := (Finset.mem_sdiff.mp hA).2 hAinS
      exact False.elim hFalse
    · intro hFalse
      simp at hFalse
  · have hDiff : H \ H' ⊆ S := by
      intro E hE
      have hEH : E ∈ H := (Finset.mem_sdiff.mp hE).1
      have hEnH' : E ∉ H' := (Finset.mem_sdiff.mp hE).2
      by_contra hES
      exact hEnH' (Finset.mem_sdiff.mpr ⟨hEH, hES⟩)
    calc
      (H \ H').card ≤ S.card := Finset.card_le_card hDiff
      _ ≤ 2 * (commonTripleCell H V a b).card := by
        simpa [S] using commonCellEndpointEdges_card_le H V a b

/-- The small-cell form used in repeated weak-cell clearing: if the cell
has fewer than `t` triples, it can be emptied while deleting at most
`2 * (t - 1)` edges. -/
theorem clear_small_commonTripleCell
    (H : Family α) (V : Edge α) (a b : α) (t : ℕ)
    (hSmall : (commonTripleCell H V a b).card < t) :
    ∃ H' : Family α,
      H' ⊆ H ∧
      (commonTripleCell H' V a b).card = 0 ∧
      (H \ H').card ≤ 2 * (t - 1) := by
  obtain ⟨H', hSub, hEmpty, hLoss⟩ := clear_commonTripleCell H V a b
  refine ⟨H', hSub, hEmpty, ?_⟩
  have hCard : (commonTripleCell H V a b).card ≤ t - 1 := by omega
  exact hLoss.trans (Nat.mul_le_mul_left 2 hCard)

/-- A chosen presentation of a two-element pair root. -/
noncomputable def pairRootRep (P : Edge α) (hP : P.card = 2) : α × α :=
  Classical.choose (show ∃ e : α × α,
      e.1 ≠ e.2 ∧ P = ({e.1, e.2} : Edge α) from by
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hP
    exact ⟨(a, b), hab, rfl⟩)

theorem pairRootRep_spec (P : Edge α) (hP : P.card = 2) :
    (pairRootRep P hP).1 ≠ (pairRootRep P hP).2 ∧
      P = ({(pairRootRep P hP).1, (pairRootRep P hP).2} : Edge α) :=
  Classical.choose_spec (show ∃ e : α × α,
      e.1 ≠ e.2 ∧ P = ({e.1, e.2} : Edge α) from by
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hP
    exact ⟨(a, b), hab, rfl⟩)

/-- The common triple cell indexed by an unordered pair root. -/
noncomputable def commonRootCell (H : Family α) (V P : Edge α) : Family α :=
  if hP : P.card = 2 then
    commonTripleCell H V (pairRootRep P hP).1 (pairRootRep P hP).2
  else ∅

/-- Pair roots in `V` whose actual common cells are nonempty. -/
noncomputable def nonemptyCommonRoots (H : Family α) (V : Edge α) : Family α :=
  (V.powersetCard 2).filter fun P => 0 < (commonRootCell H V P).card

theorem commonRootCell_mono {H K : Family α} {V P : Edge α}
    (hKH : K ⊆ H) : commonRootCell K V P ⊆ commonRootCell H V P := by
  classical
  unfold commonRootCell
  split_ifs with hP
  · intro T hT
    apply mem_commonTripleCell.mpr
    have h := mem_commonTripleCell.mp hT
    refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_⟩
    · exact hKH h.2.2.2.1
    · exact hKH h.2.2.2.2
  · simp

theorem nonemptyCommonRoots_mono {H K : Family α} {V : Edge α}
    (hKH : K ⊆ H) : nonemptyCommonRoots K V ⊆ nonemptyCommonRoots H V := by
  intro P hP
  apply Finset.mem_filter.mpr
  have h := Finset.mem_filter.mp hP
  refine ⟨h.1, ?_⟩
  have hle := Finset.card_le_card
    (commonRootCell_mono (V := V) (P := P) hKH)
  omega

/-- Iteratively clear currently small nonempty cells.  Every step permanently
empties one pair root; cells can only shrink afterwards, so induction on the
number of nonempty roots gives a finite process and the sharp per-root loss. -/
theorem clear_all_small_commonCells_aux
    (H : Family α) (V : Edge α) (t m : ℕ)
    (hMeasure : (nonemptyCommonRoots H V).card ≤ m) :
    ∃ K : Family α,
      K ⊆ H ∧
      (∀ P ∈ V.powersetCard 2,
        (commonRootCell K V P).card = 0 ∨
          t ≤ (commonRootCell K V P).card) ∧
      (H \ K).card ≤ 2 * (t - 1) * m := by
  classical
  induction m using Nat.strong_induction_on generalizing H with
  | h m ih =>
      by_cases hgood : ∀ P ∈ V.powersetCard 2,
          (commonRootCell H V P).card = 0 ∨
            t ≤ (commonRootCell H V P).card
      · refine ⟨H, Finset.Subset.rfl, hgood, ?_⟩
        simp
      · have hbad : ∃ P ∈ V.powersetCard 2,
            (commonRootCell H V P).card ≠ 0 ∧
              (commonRootCell H V P).card < t := by
          push Not at hgood
          obtain ⟨P, hPV, hnot⟩ := hgood
          refine ⟨P, hPV, ?_, ?_⟩
          rcases hnot with ⟨hneq, hnotLe⟩
          · intro hzero
            exact hneq hzero
          · omega
        obtain ⟨P, hPV, hNonzero, hSmall⟩ := hbad
        have hPcard : P.card = 2 :=
          (Finset.mem_powersetCard.mp hPV).2
        let ab := pairRootRep P hPcard
        have hRootEq : commonRootCell H V P =
            commonTripleCell H V ab.1 ab.2 := by
          simp [commonRootCell, hPcard, ab]
        have hRootPos : 0 < (commonRootCell H V P).card :=
          Nat.pos_of_ne_zero hNonzero
        have hCellPos : 0 < (commonTripleCell H V ab.1 ab.2).card := by
          rw [← hRootEq]
          exact hRootPos
        have hSmall' : (commonTripleCell H V ab.1 ab.2).card < t := by
          rw [← hRootEq]
          exact hSmall
        obtain ⟨K₁, hK₁H, hEmpty, hLoss₁⟩ :=
          clear_small_commonTripleCell H V ab.1 ab.2 t hSmall'
        have hEmptySet : commonTripleCell K₁ V ab.1 ab.2 = ∅ :=
          Finset.card_eq_zero.mp hEmpty
        have hRootEqK : commonRootCell K₁ V P =
            commonTripleCell K₁ V ab.1 ab.2 := by
          simp [commonRootCell, hPcard, ab]
        have hRootEmpty : commonRootCell K₁ V P = ∅ := by
          rw [hRootEqK, hEmptySet]
        have hRootEmpty' : (commonRootCell K₁ V P).card = 0 := by
          simp [hRootEmpty]
        have hRootsSub : nonemptyCommonRoots K₁ V ⊆ nonemptyCommonRoots H V :=
          nonemptyCommonRoots_mono hK₁H
        have hPnot : P ∉ nonemptyCommonRoots K₁ V := by
          intro hmem
          have hMem' := Finset.mem_filter.mp hmem
          rw [hRootEmpty] at hMem'
          simp at hMem'
        have hCardRoots : (nonemptyCommonRoots K₁ V).card < m := by
          have hInc : insert P (nonemptyCommonRoots K₁ V) ⊆
              nonemptyCommonRoots H V := by
            intro Q hQ
            rcases Finset.mem_insert.mp hQ with hEq | hQ'
            · subst Q
              apply Finset.mem_filter.mpr
              exact ⟨hPV, hRootPos⟩
            · exact hRootsSub hQ'
          have hPmem : P ∈ insert P (nonemptyCommonRoots K₁ V) := by simp
          have hCardInsert :
              (insert P (nonemptyCommonRoots K₁ V)).card =
                (nonemptyCommonRoots K₁ V).card + 1 := by
            simp [hPnot]
          have hIncCard := Finset.card_le_card hInc
          rw [hCardInsert] at hIncCard
          have hBound := Nat.le_trans hIncCard hMeasure
          omega
        obtain ⟨K₂, hK₂K₁, hGood₂, hLoss₂⟩ :=
          ih (nonemptyCommonRoots K₁ V).card hCardRoots K₁ (Nat.le_refl _)
        refine ⟨K₂, hK₂K₁.trans hK₁H, hGood₂, ?_⟩
        have hLossUnion : H \ K₂ ⊆ (H \ K₁) ∪ (K₁ \ K₂) := by
          intro E hE
          have hEH : E ∈ H := (Finset.mem_sdiff.mp hE).1
          have hEnK₂ : E ∉ K₂ := (Finset.mem_sdiff.mp hE).2
          by_cases hEK₁ : E ∈ K₁
          · exact Finset.mem_union.mpr (Or.inr
              (Finset.mem_sdiff.mpr ⟨hEK₁, hEnK₂⟩))
          · exact Finset.mem_union.mpr (Or.inl
              (Finset.mem_sdiff.mpr ⟨hEH, hEK₁⟩))
        have hLossAdd : (H \ K₂).card ≤ (H \ K₁).card + (K₁ \ K₂).card :=
          (Finset.card_le_card hLossUnion).trans (Finset.card_union_le _ _)
        have hLossBound₁ : (H \ K₁).card ≤ 2 * (t - 1) := by
          exact hLoss₁
        calc
          (H \ K₂).card ≤ (H \ K₁).card + (K₁ \ K₂).card := hLossAdd
          _ ≤ 2 * (t - 1) +
              2 * (t - 1) * (nonemptyCommonRoots K₁ V).card := by
                exact Nat.add_le_add hLossBound₁ hLoss₂
          _ ≤ 2 * (t - 1) * m := by
                have hFactor : 2 * (t - 1) +
                    2 * (t - 1) * (nonemptyCommonRoots K₁ V).card =
                    2 * (t - 1) * ((nonemptyCommonRoots K₁ V).card + 1) := by
                  rw [Nat.mul_add]
                  simp [Nat.add_comm]
                rw [hFactor]
                exact Nat.mul_le_mul_left (2 * (t - 1))
                  (Nat.succ_le_of_lt hCardRoots)

/-- Clear every small actual common triple cell over the pair roots of `V`.
The resulting family has no nonempty cell of size below `t`, and the total
edge loss is at most `2 (t-1) * choose(|V|,2)`. -/
theorem clear_all_small_commonCells
    (H : Family α) (V : Edge α) (t : ℕ) :
    ∃ K : Family α,
      K ⊆ H ∧
      (∀ P ∈ V.powersetCard 2,
        (commonRootCell K V P).card = 0 ∨
          t ≤ (commonRootCell K V P).card) ∧
      (H \ K).card ≤ 2 * (t - 1) * (V.card.choose 2) := by
  obtain ⟨K, hKH, hGood, hLoss⟩ :=
    clear_all_small_commonCells_aux H V t
      (nonemptyCommonRoots H V).card (Nat.le_refl _)
  refine ⟨K, hKH, hGood, ?_⟩
  have hRoots : (nonemptyCommonRoots H V).card ≤ V.card.choose 2 := by
    unfold nonemptyCommonRoots
    exact (Finset.card_filter_le _ _).trans (by
      rw [Finset.card_powersetCard])
  exact hLoss.trans (Nat.mul_le_mul_left (2 * (t - 1)) hRoots)

end JSP523.Rank4
