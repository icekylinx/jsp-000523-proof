import JSP523.Rank4.StarLinkActualBudget
import JSP523.Rank4.PreprocessFixedDecomposition

/-!
# Parent matching tails from a large centered common cell

A large centered triple cell with bounded pair degree contains three tails
that are pairwise disjoint.  The tails are selected in the parent cell, so
they remain valid witnesses after any later edge deletions.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Members of a centered triple family whose tails meet a fixed tail. -/
private def centeredTailConflicts (J : Family α) (z : α) (R : Edge α) :
    Family α :=
  J.filter fun S => ¬ Disjoint (S.erase z) (R.erase z)

/-- At most `2D` triples of a centered cell conflict with a fixed tail when
every pair has degree at most `D`. -/
private theorem centeredTailConflicts_card_le
    {J : Family α} {z : α} {R : Edge α} {D : ℕ}
    (hUniform : ∀ S ∈ J, S.card = 3)
    (hz : ∀ S ∈ J, z ∈ S)
    (hPair : ∀ P : Edge α, P.card = 2 → triplePairDegree J P ≤ D)
    (hR : R ∈ J) :
    (centeredTailConflicts J z R).card ≤ 2 * D := by
  classical
  let W := R.erase z
  let conflictUnion : Family α := W.biUnion fun x =>
    J.filter fun S => ({z, x} : Edge α) ⊆ S
  have hTailCard : W.card = 2 := by
    have hzR := hz R hR
    have hRcard := hUniform R hR
    calc
      W.card = R.card - 1 := by simp [W, hzR]
      _ = 2 := by simp [hRcard]
  have hConflictSub : centeredTailConflicts J z R ⊆ conflictUnion := by
    intro S hS
    have hSJ := (Finset.mem_filter.mp hS).1
    have hNotDisj := (Finset.mem_filter.mp hS).2
    have hInter : ((S.erase z) ∩ W).Nonempty := by
      by_contra hEmpty
      have hEq : (S.erase z) ∩ W = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hEmpty
      exact hNotDisj (Finset.disjoint_iff_inter_eq_empty.mpr hEq)
    obtain ⟨x, hx⟩ := hInter
    have hxW : x ∈ W := (Finset.mem_inter.mp hx).2
    have hxS : x ∈ S := (Finset.mem_erase.mp
      (Finset.mem_inter.mp hx).1).2
    have hxNe : x ≠ z := (Finset.mem_erase.mp hxW).1
    have hp : ({z, x} : Edge α) ⊆ S := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hz S hSJ
      · exact hxS
    exact Finset.mem_biUnion.mpr ⟨x, hxW,
      Finset.mem_filter.mpr ⟨hSJ, hp⟩⟩
  have hFiber : ∀ x ∈ W,
      (J.filter fun S => ({z, x} : Edge α) ⊆ S).card ≤ D := by
    intro x hx
    have hxNe : x ≠ z := (Finset.mem_erase.mp hx).1
    exact hPair {z, x} (Finset.card_pair (Ne.symm hxNe))
  have hUnionCard : conflictUnion.card ≤ W.card * D := by
    dsimp [conflictUnion]
    exact Finset.card_biUnion_le_card_mul W _ D hFiber
  calc
    (centeredTailConflicts J z R).card ≤ conflictUnion.card :=
      Finset.card_le_card hConflictSub
    _ ≤ W.card * D := hUnionCard
    _ = 2 * D := by rw [hTailCard]

/-- A cell larger than `9D`, with a common center and pair-degree at most
`D`, supplies three pairwise-disjoint parent tails in the ground set. -/
theorem large_centered_cell_has_three_parent_tails
    {H : Family α} {V : Edge α} {a b z : α} {D : ℕ}
    (hCellLarge : 9 * D < (commonTripleCell H V a b).card)
    (hCenter : ∀ ⦃T : Edge α⦄,
      T ∈ commonTripleCell H V a b → z ∈ T)
    (hPair : ∀ P : Edge α, P.card = 2 →
      triplePairDegree (commonTripleCell H V a b) P ≤ D) :
    HasThreeParentTails H V V a b z := by
  classical
  let J := commonTripleCell H V a b
  have hUniform : ∀ T ∈ J, T.card = 3 := by
    intro T hT
    exact (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hT).1).2
  have hz : ∀ T ∈ J, z ∈ T := by
    intro T hT
    exact hCenter hT
  have hLarge : J.card > 4 * D := by
    dsimp [J] at hCellLarge ⊢
    omega
  obtain ⟨R₀, hR₀⟩ := Finset.card_pos.mp (by omega : 0 < J.card)
  let R := R₀.erase z
  have hR₀z : z ∈ R₀ := hz R₀ hR₀
  have hRmem : insert z R ∈ J := by
    simpa [R, hR₀z] using hR₀
  have hBadR : (centeredTailConflicts J z R₀).card ≤ 2 * D :=
    centeredTailConflicts_card_le hUniform hz hPair hR₀
  have hBadRsub : centeredTailConflicts J z R₀ ⊆ J := by
    intro T hT
    exact (Finset.mem_filter.mp hT).1
  have hRemainR : (J \ centeredTailConflicts J z R₀).Nonempty := by
    apply Finset.card_pos.mp
    have hEq := Finset.card_sdiff_add_card_eq_card hBadRsub
    omega
  obtain ⟨S₀, hS₀⟩ := hRemainR
  have hS₀J : S₀ ∈ J := (Finset.mem_sdiff.mp hS₀).1
  have hS₀NotConflict : S₀ ∉ centeredTailConflicts J z R₀ :=
    (Finset.mem_sdiff.mp hS₀).2
  have hSDisj : Disjoint (S₀.erase z) R := by
    by_contra hNot
    apply hS₀NotConflict
    exact Finset.mem_filter.mpr ⟨hS₀J, hNot⟩
  let S := S₀.erase z
  have hS₀z : z ∈ S₀ := hz S₀ hS₀J
  have hSmem : insert z S ∈ J := by
    simpa [S, hS₀z] using hS₀J
  have hBadS : (centeredTailConflicts J z S₀).card ≤ 2 * D :=
    centeredTailConflicts_card_le hUniform hz hPair hS₀J
  have hBadSsub : centeredTailConflicts J z S₀ ⊆ J := by
    intro T hT
    exact (Finset.mem_filter.mp hT).1
  have hBadUnionSub :
      centeredTailConflicts J z R₀ ∪ centeredTailConflicts J z S₀ ⊆ J := by
    intro T hT
    rcases Finset.mem_union.mp hT with hT | hT
    · exact hBadRsub hT
    · exact hBadSsub hT
  have hRemainBoth :
      (J \ (centeredTailConflicts J z R₀ ∪
        centeredTailConflicts J z S₀)).Nonempty := by
    apply Finset.card_pos.mp
    have hEq := Finset.card_sdiff_add_card_eq_card hBadUnionSub
    have hUnionCard :
        (centeredTailConflicts J z R₀ ∪
          centeredTailConflicts J z S₀).card ≤
          (centeredTailConflicts J z R₀).card +
            (centeredTailConflicts J z S₀).card := Finset.card_union_le _ _
    omega
  obtain ⟨T₀, hT₀⟩ := hRemainBoth
  have hT₀J : T₀ ∈ J := (Finset.mem_sdiff.mp hT₀).1
  have hT₀NotConflictR : T₀ ∉ centeredTailConflicts J z R₀ := by
    intro h
    exact (Finset.mem_sdiff.mp hT₀).2
      (Finset.mem_union.mpr (Or.inl h))
  have hT₀NotConflictS : T₀ ∉ centeredTailConflicts J z S₀ := by
    intro h
    exact (Finset.mem_sdiff.mp hT₀).2
      (Finset.mem_union.mpr (Or.inr h))
  have hTR : Disjoint (T₀.erase z) R := by
    by_contra hNot
    exact hT₀NotConflictR (Finset.mem_filter.mpr ⟨hT₀J, hNot⟩)
  have hTS : Disjoint (T₀.erase z) S := by
    by_contra hNot
    exact hT₀NotConflictS (Finset.mem_filter.mpr ⟨hT₀J, hNot⟩)
  have hT₀z : z ∈ T₀ := hz T₀ hT₀J
  have hRsub : R ⊆ V := by
    intro x hx
    have hx' : x ∈ insert z R := Finset.mem_insert_of_mem hx
    exact (mem_commonTripleCell.mp hRmem).1 hx'
  have hSsub : S ⊆ V := by
    intro x hx
    have hx' : x ∈ insert z S := Finset.mem_insert_of_mem hx
    exact (mem_commonTripleCell.mp hSmem).1 hx'
  have hTmem : insert z (T₀.erase z) ∈ J := by
    simpa [Finset.insert_erase hT₀z] using hT₀J
  have hTsub : T₀.erase z ⊆ V := by
    intro x hx
    have hx' : x ∈ insert z (T₀.erase z) := Finset.mem_insert_of_mem hx
    exact (mem_commonTripleCell.mp hTmem).1 hx'
  have hzV : z ∈ V := (mem_commonTripleCell.mp hRmem).1 (by simp)
  refine ⟨R, S, T₀.erase z, hzV, hSDisj.symm, hTR.symm, hTS.symm,
    hRsub, hSsub, hTsub, hRmem, hSmem, hTmem⟩

/-- Monotonicity of the actual common cell in both the family and the
ground set. -/
theorem commonTripleCell_mono_family_ground
    {K H : Family α} {U V : Edge α} {a b : α}
    (hKH : K ⊆ H) (hUV : U ⊆ V) :
    commonTripleCell K U a b ⊆ commonTripleCell H V a b := by
  intro T hT
  have h := mem_commonTripleCell.mp hT
  apply mem_commonTripleCell.mpr
  refine ⟨h.1.trans hUV, h.2.1, h.2.2.1, ?_, ?_⟩
  · exact hKH h.2.2.2.1
  · exact hKH h.2.2.2.2

/-- The common cell depends on its two endpoints as an unordered pair. -/
theorem commonTripleCell_swap
    (H : Family α) (V : Edge α) (a b : α) :
    commonTripleCell H V a b = commonTripleCell H V b a := by
  ext T
  simp [commonTripleCell, Finset.pair_comm, and_left_comm, and_comm]

/-- Equality of the endpoint pairs identifies the corresponding common
triple cells. -/
theorem commonTripleCell_eq_of_pair_eq
    (H : Family α) (V : Edge α) {a b c d : α}
    (hPair : ({a, b} : Edge α) = {c, d}) :
    commonTripleCell H V a b = commonTripleCell H V c d := by
  have hc : c = a ∨ c = b := by
    have hc' : c ∈ ({a, b} : Edge α) := by rw [hPair]; simp
    simpa using hc'
  rcases hc with hca | hcb
  · subst c
    have hd : d = b := by
      have hb' : b ∈ ({a, d} : Edge α) := by rw [← hPair]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
      rcases hb' with hba | hbd
      · subst b
        have hd' : d ∈ ({a, a} : Edge α) := by
          have hd'' := congrArg (fun P : Edge α => d ∈ P) hPair
          simpa using hd''.symm
        simpa using hd'
      · exact hbd.symm
    subst d
    rfl
  · subst c
    have hd : d = a := by
      have ha' : a ∈ ({b, d} : Edge α) := by rw [← hPair]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha'
      rcases ha' with hab | had
      · subst a
        have hd' : d ∈ ({b, b} : Edge α) := by
          have hd'' := congrArg (fun P : Edge α => d ∈ P) hPair
          simpa using hd''.symm
        simpa using hd'
      · exact had.symm
    subst d
    exact commonTripleCell_swap H V a b

/-- The bounded-pair-degree large-cell lemma yields the exact parent-tail
record consumed by `StarLinkActualBudget`; the cell is measured in the
surviving family on `U`, while its witnesses are retained as edges of the
original parent family `H` on the larger ground set `V`. -/
theorem surviving_common_cell_has_parent_tails
    {K H : Family α} {U V : Edge α} {a b z : α} {D : ℕ}
    (hKH : K ⊆ H) (hUV : U ⊆ V)
    (hLarge : 9 * D < (commonTripleCell K U a b).card)
    (hCenter : ∀ ⦃T : Edge α⦄,
      T ∈ commonTripleCell K U a b → z ∈ T)
    (hPair : ∀ P : Edge α, P.card = 2 →
      triplePairDegree (commonTripleCell K U a b) P ≤ D) :
    HasThreeParentTails H V U a b z := by
  obtain ⟨R, S, T, hzU, hRS, hRT, hST, hRU, hSU, hTU,
    hRK, hSK, hTK⟩ :=
    large_centered_cell_has_three_parent_tails
      (H := K) (V := U) hLarge hCenter hPair
  refine ⟨R, S, T, ?_, hRS, hRT, hST, hRU, hSU, hTU, ?_, ?_, ?_⟩
  · exact hzU
  · exact commonTripleCell_mono_family_ground hKH hUV hRK
  · exact commonTripleCell_mono_family_ground hKH hUV hSK
  · exact commonTripleCell_mono_family_ground hKH hUV hTK

/-- After finite small-cell clearing on the fixed core, every surviving
large actual cell has a unique center and three pairwise-disjoint parent
tails in the original family. -/
theorem clear_small_cells_and_get_parent_tails
    {H : Family α} {U V : Edge α} (t D : ℕ)
    (hH : Admissible H) (hUsubV : U ⊆ V)
    (hCap : ∀ T : Edge α, T.card = 3 →
      (facetCompletions H U T).card ≤ D)
    (hLarge : 9 * D < t) :
    ∃ K : Family α,
      K ⊆ fixedDecompositionCore H U ∧
      (fixedDecompositionCore H U \ K).card ≤
        2 * (t - 1) * U.card.choose 2 ∧
      ∀ a b : α, a ≠ b →
        t ≤ (commonTripleCell K U a b).card →
        ∃! z : α,
          (∀ ⦃T : Edge α⦄, T ∈ commonTripleCell K U a b → z ∈ T) ∧
          HasThreeParentTails H V U a b z := by
  classical
  let B := fixedDecompositionCore H U
  have hBH : B ⊆ H := by
    intro E hE
    exact (Finset.mem_filter.mp hE).1
  have hBAdmissible : Admissible B := admissible_mono hBH hH
  have hBCap : ∀ T : Edge α, T.card = 3 →
      (facetCompletions B U T).card ≤ D := by
    intro T hT
    apply (Finset.card_le_card ?_).trans (hCap T hT)
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx'.1, hBH hx'.2⟩
  obtain ⟨K, hKB, hLoss, hLabels⟩ :=
    clear_small_cells_and_get_unique_labels U t D hBAdmissible hBCap hLarge
  have hKH : K ⊆ H := fun E hE => hBH (hKB hE)
  refine ⟨K, hKB, hLoss, ?_⟩
  intro a b hab hCellLarge
  have hKAdmissible := admissible_mono hKB hBAdmissible
  have hPair : ∀ P : Edge α, P.card = 2 →
      triplePairDegree (commonTripleCell K U a b) P ≤ D :=
    commonTripleCell_pairDegree_le_of_facet_cap
      (by
        intro T hT
        have hFacetSub : facetCompletions K U T ⊆ facetCompletions H U T := by
          intro x hx
          have hx' := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨hx'.1, hKH hx'.2⟩
        exact (Finset.card_le_card hFacetSub).trans (hCap T hT))
  have hCellLarge' : 9 * D < (commonTripleCell K U a b).card := by
    omega
  obtain ⟨z, hz⟩ := commonTripleCell_large_has_center_of_facet_cap
    hKAdmissible hab
    (by
      intro T hT
      have hFacetSub : facetCompletions K U T ⊆ facetCompletions H U T := by
        intro x hx
        have hx' := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hx'.1, hKH hx'.2⟩
      exact (Finset.card_le_card hFacetSub).trans (hCap T hT))
    hCellLarge'
  have hPairUnique : ∀ P : Edge α, P.card = 2 →
      triplePairDegree (commonTripleCell K U a b) P ≤ D := hPair
  have hzD : D < (commonTripleCell K U a b).card := by omega
  have hTails := surviving_common_cell_has_parent_tails
    hKH hUsubV hCellLarge' hz hPair
  refine ⟨z, ⟨hz, hTails⟩, ?_⟩
  intro y hy
  have hEq := commonTripleCell_center_unique hPairUnique hzD hz hy.1
  subst y
  rfl

/-- Weak-cell clearing supplies the exact `hTails` premise expected by the
chosen-label native budget, with labels selected from the same surviving
common-root cells. -/
theorem clear_small_cells_and_get_chosen_parent_tails
    {H : Family α} {U V : Edge α} (t D : ℕ) (fallback : α)
    (hH : Admissible H) (hUsubV : U ⊆ V)
    (hCap : ∀ T : Edge α, T.card = 3 →
      (facetCompletions H U T).card ≤ D)
    (hLarge : 9 * D < t) :
    ∃ K : Family α,
      ∃ hCenters : UniqueCommonRootCenters K U,
      K ⊆ fixedDecompositionCore H U ∧
      (fixedDecompositionCore H U \ K).card ≤
        2 * (t - 1) * U.card.choose 2 ∧
      ∀ a ∈ U, ∀ b ∈ U.erase a,
        ({a, b} : Edge α) ∈ nonemptyCommonRoots K U →
        HasThreeParentTails H V U a b
          (chosenCommonRootLabel K U fallback
            (by assumption : UniqueCommonRootCenters K U) ({a, b} : Edge α)) := by
  classical
  let B := fixedDecompositionCore H U
  have hBH : B ⊆ H := by
    intro E hE
    exact (Finset.mem_filter.mp hE).1
  have hBAdmissible : Admissible B := admissible_mono hBH hH
  have hBCap : ∀ T : Edge α, T.card = 3 →
      (facetCompletions B U T).card ≤ D := by
    intro T hT
    apply (Finset.card_le_card ?_).trans (hCap T hT)
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx'.1, hBH hx'.2⟩
  obtain ⟨K, hKB, hCells, hLoss⟩ := clear_all_small_commonCells B U t
  have hKH : K ⊆ H := fun E hE => hBH (hKB hE)
  have hKAdmissible := admissible_mono hKB hBAdmissible
  have hCapK : ∀ T : Edge α, T.card = 3 →
      (facetCompletions K U T).card ≤ D := by
    intro T hT
    apply (Finset.card_le_card ?_).trans (hCap T hT)
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx'.1, hKH hx'.2⟩
  have hCenters : UniqueCommonRootCenters K U := by
    intro P hP
    rcases hCells P hP with hZero | hBig
    · exact Or.inl hZero
    · right
      have hPcard : P.card = 2 :=
        (Finset.mem_powersetCard.mp hP).2
      let ab := pairRootRep P hPcard
      have hRootEq : commonRootCell K U P =
          commonTripleCell K U ab.1 ab.2 := by
        simp [commonRootCell, hPcard, ab]
      have hCellLarge : 9 * D <
          (commonTripleCell K U ab.1 ab.2).card := by
        rw [← hRootEq]
        omega
      have hab : ab.1 ≠ ab.2 := (pairRootRep_spec P hPcard).1
      have hPair : ∀ Q : Edge α, Q.card = 2 →
          triplePairDegree (commonTripleCell K U ab.1 ab.2) Q ≤ D :=
        commonTripleCell_pairDegree_le_of_facet_cap hCapK
      obtain ⟨z, hz⟩ := commonTripleCell_large_has_center_of_facet_cap
        hKAdmissible hab hCapK hCellLarge
      have hzRoot : ∀ ⦃T : Edge α⦄,
          T ∈ commonRootCell K U P → z ∈ T := by
        intro T hT
        exact hz (hRootEq ▸ hT)
      have hzUnique : ∀ y : α,
          (∀ ⦃T : Edge α⦄,
            T ∈ commonRootCell K U P → y ∈ T) → y = z := by
        intro y hy
        have hy' : ∀ ⦃T : Edge α⦄,
            T ∈ commonTripleCell K U ab.1 ab.2 → y ∈ T := by
          intro T hT
          exact hy (hRootEq.symm ▸ hT)
        exact (commonTripleCell_center_unique hPair
          (by omega : D < (commonTripleCell K U ab.1 ab.2).card)
          hz hy').symm
      exact ⟨z, hzRoot, hzUnique⟩
  refine ⟨K, hCenters, hKB, hLoss, ?_⟩
  intro a ha b hb hUsed
  let P : Edge α := {a, b}
  have hPcard : P.card = 2 := by
    exact Finset.card_pair (Finset.ne_of_mem_erase hb).symm
  have hPmem : P ∈ U.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hPcard⟩
    intro x hx
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact (Finset.mem_erase.mp hb).2
  have hPused : P ∈ nonemptyCommonRoots K U := hUsed
  have hPnonempty := (Finset.mem_filter.mp hPused).2
  have hBigOr := hCells P hPmem
  have hBig : t ≤ (commonRootCell K U P).card := by
    rcases hBigOr with hZero | hBig
    · omega
    · exact hBig
  let ab := pairRootRep P hPcard
  have hPairEq : ({a, b} : Edge α) = ({ab.1, ab.2} : Edge α) :=
    by simpa [P] using (pairRootRep_spec P hPcard).2
  have hRootEq : commonRootCell K U P =
      commonTripleCell K U ab.1 ab.2 := by
    simp [commonRootCell, hPcard, ab]
  have hCellLarge : 9 * D <
      (commonTripleCell K U ab.1 ab.2).card := by
    rw [← hRootEq]
    omega
  have hCapPair : ∀ Q : Edge α, Q.card = 2 →
      triplePairDegree (commonTripleCell K U ab.1 ab.2) Q ≤ D :=
    commonTripleCell_pairDegree_le_of_facet_cap hCapK
  have hab : ab.1 ≠ ab.2 := (pairRootRep_spec P hPcard).1
  obtain ⟨z, hz⟩ := commonTripleCell_large_has_center_of_facet_cap
    hKAdmissible hab hCapK hCellLarge
  have hLabelCenter := chosen_common_root_label_center K U fallback
    hCenters P hPused
  have hLabelOnRep : ∀ ⦃T : Edge α⦄,
      T ∈ commonTripleCell K U ab.1 ab.2 →
        chosenCommonRootLabel K U fallback hCenters P ∈ T := by
    intro T hT
    apply hLabelCenter T
    rw [hRootEq]
    exact hT
  have hLabelEq : chosenCommonRootLabel K U fallback hCenters P = z :=
    (commonTripleCell_center_unique hCapPair
      (by omega : D < (commonTripleCell K U ab.1 ab.2).card)
      hz hLabelOnRep).symm
  have hTailRep := surviving_common_cell_has_parent_tails
    hKH hUsubV hCellLarge hz hCapPair
  obtain ⟨R, S, T, hzU, hRS, hRT, hST,
    hRU, hSU, hTU, hR, hS, hT⟩ := hTailRep
  have hCellEq := commonTripleCell_eq_of_pair_eq H V hPairEq
  have hR' : insert z R ∈ commonTripleCell H V a b := by
    rw [hCellEq]
    exact hR
  have hS' : insert z S ∈ commonTripleCell H V a b := by
    rw [hCellEq]
    exact hS
  have hT' : insert z T ∈ commonTripleCell H V a b := by
    rw [hCellEq]
    exact hT
  subst z
  exact ⟨R, S, T, hzU, hRS, hRT, hST, hRU, hSU, hTU,
    hR', hS', hT'⟩

end JSP523.Rank4
