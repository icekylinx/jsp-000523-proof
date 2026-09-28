import JSP523.Rank4.PreprocessParentTails

/-!
# Actual parent-label inheritance after weak-cell clearing

This combines the finite weak-cell deletion with its parent three-tail
witnesses and the label-inheritance argument used when a star edge is
attached to that root.  All cells and witnesses remain in the fixed parent.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- Clear the weak cells on the actual fixed core. Every used pair receives
its unique surviving-cell label and three disjoint tails in the original
parent; when a star completion belongs to the same parent cell, that label
is forced into the star pair. -/
theorem clear_small_cells_with_actual_parent_label_inheritance
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
      (∀ a ∈ U, ∀ b ∈ U.erase a,
        ({a, b} : Edge α) ∈ nonemptyCommonRoots K U →
        HasThreeParentTails H V U a b
          (chosenCommonRootLabel K U fallback hCenters ({a, b} : Edge α))) ∧
      (∀ a ∈ U, ∀ b ∈ U.erase a,
        ({a, b} : Edge α) ∈ nonemptyCommonRoots K U →
        ∀ c : α, c ∉ U →
          insert c ({a, b} : Edge α) ∈ commonTripleCell H V a b →
          chosenCommonRootLabel K U fallback hCenters
            ({a, b} : Edge α) ∈ ({a, b} : Edge α)) := by
  obtain ⟨K, hCenters, hKCore, hLoss, hTails⟩ :=
    clear_small_cells_and_get_chosen_parent_tails
      t D fallback hH hUsubV hCap hLarge
  refine ⟨K, hCenters, hKCore, hLoss, hTails, ?_⟩
  intro a ha b hb hUsed c hcU hStar
  have hab : a ≠ b := (Finset.mem_erase.mp hb).1.symm
  have hPairCard : ({a, b} : Edge α).card = 2 := Finset.card_pair hab
  obtain ⟨R, S, T, hzU, hRS, hRT, hST,
    hRU, hSU, hTU, hR, hS, hT⟩ := hTails a ha b hb hUsed
  have hcz : c ≠ chosenCommonRootLabel K U fallback hCenters
      ({a, b} : Edge α) := by
    intro hEq
    apply hcU
    rw [hEq]
    exact hzU
  have hcR : c ∉ R := fun hcR => hcU (hRU hcR)
  have hcS : c ∉ S := fun hcS => hcU (hSU hcS)
  have hcT : c ∉ T := fun hcT => hcU (hTU hcT)
  exact three_parent_tails_force_label_in_pair
    hH hab hcz hPairCard hRS hRT hST hcR hcS hcT
    hStar hR hS hT

end JSP523.Rank4
