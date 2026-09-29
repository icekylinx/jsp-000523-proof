import JSP523.Rank4.PreprocessRawCenterGraphBudget

/-! # Retaining the actual weak-cell threshold in the cleanup output -/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

theorem clear_small_cells_and_get_chosen_parent_tails_with_threshold
    {H : Family α} {U V : Edge α} (t D : ℕ) (fallback : α)
    (hH : Admissible H) (hUsubV : U ⊆ V)
    (hCap : ∀ T : Edge α, T.card = 3 →
      (facetCompletions H U T).card ≤ D)
    (hLarge : 9 * D < t) :
    ∃ K : Family α,
      ∃ hCenters : UniqueCommonRootCenters K U,
      (∀ P ∈ U.powersetCard 2,
        (commonRootCell K U P).card = 0 ∨ t ≤ (commonRootCell K U P).card) ∧
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
  obtain ⟨K, hKB, hCells, hLoss⟩ := clear_all_small_common_cells B U t
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
      have hab : ab.1 ≠ ab.2 := (pair_root_rep_spec P hPcard).1
      have hPair : ∀ Q : Edge α, Q.card = 2 →
          triplePairDegree (commonTripleCell K U ab.1 ab.2) Q ≤ D :=
        common_triple_cell_pair_degree_le_of_facet_cap hCapK
      obtain ⟨z, hz⟩ := common_triple_cell_large_has_center_of_facet_cap
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
        exact (common_triple_cell_center_unique hPair
          (by omega : D < (commonTripleCell K U ab.1 ab.2).card)
          hz hy').symm
      exact ⟨z, hzRoot, hzUnique⟩
  refine ⟨K, hCenters, hCells, hKB, hLoss, ?_⟩
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
    by simpa [P] using (pair_root_rep_spec P hPcard).2
  have hRootEq : commonRootCell K U P =
      commonTripleCell K U ab.1 ab.2 := by
    simp [commonRootCell, hPcard, ab]
  have hCellLarge : 9 * D <
      (commonTripleCell K U ab.1 ab.2).card := by
    rw [← hRootEq]
    omega
  have hCapPair : ∀ Q : Edge α, Q.card = 2 →
      triplePairDegree (commonTripleCell K U ab.1 ab.2) Q ≤ D :=
    common_triple_cell_pair_degree_le_of_facet_cap hCapK
  have hab : ab.1 ≠ ab.2 := (pair_root_rep_spec P hPcard).1
  obtain ⟨z, hz⟩ := common_triple_cell_large_has_center_of_facet_cap
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
    (common_triple_cell_center_unique hCapPair
      (by omega : D < (commonTripleCell K U ab.1 ab.2).card)
      hz hLabelOnRep).symm
  have hTailRep := surviving_common_cell_has_parent_tails
    hKH hUsubV hCellLarge hz hCapPair
  obtain ⟨R, S, T, hzU, hRS, hRT, hST,
    hRU, hSU, hTU, hR, hS, hT⟩ := hTailRep
  have hCellEq := common_triple_cell_eq_of_pair_eq H V hPairEq
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
