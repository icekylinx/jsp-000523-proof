import JSP523.Rank4.GraphActualPairExcess

/-!
# Actual selected excess over every base pair

For each used completion pair, only on-label base pairs contribute
positive excess. The on-label finite-set bijection converts their sum
to the native-tail sum already identified pointwise.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Selected common-neighbor excess for a finite completion pair at an
actual base pair. Invalid pair roots have value zero. -/
noncomputable def actualSelectedPairExcessAtBase
    (D : FiniteCompletionCliqueData α) (Q P : Edge α) : ℕ :=
  if hP : P.card = 2 then
    let ab := pairRootRep P hP
    graphCommonMultiplicity
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q) ab.1 ab.2 - 1
  else 0

/-- At a used completion pair, the selected excess over all valid base
pairs equals the sum of its on-label excess over admissible native tails. -/
theorem actual_selected_excess_over_bases_eq_on_label_tails
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground)
    (P : Edge α) (hUsed : P ∈ nonemptyCommonRoots D.K D.ground) :
    (D.ground.powersetCard 2).sum
      (fun Q => actualSelectedPairExcessAtBase D Q P) =
      (D.ground \ insert
        (chosenCommonRootLabel D.K D.ground fallback hCenters P) P).sum
        (fun w => selectedOnLabelPairExcess D fallback hCenters P w) := by
  classical
  let z := chosenCommonRootLabel D.K D.ground fallback hCenters P
  have hPcard : P.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hUsed).1).2
  let ab := pairRootRep P hPcard
  have hSpec := pair_root_rep_spec P hPcard
  have haP : ab.1 ∈ P := by rw [hSpec.2]; simp [ab]
  have hbP : ab.2 ∈ P := by rw [hSpec.2]; simp [ab]
  have hPsub : P ⊆ D.ground :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hUsed).1).1
  have haU : ab.1 ∈ D.ground := hPsub haP
  have hbU : ab.2 ∈ D.ground := hPsub hbP
  have hUsedAB : ({ab.1, ab.2} : Edge α) ∈
      nonemptyCommonRoots D.K D.ground := by
    rw [← hSpec.2]
    exact hUsed
  let S := (D.ground.powersetCard 2).filter
    (fun Q => z ∈ Q ∧ Disjoint Q P)
  have hZeroOutside : ∀ Q ∈ D.ground.powersetCard 2,
      Q ∉ S → actualSelectedPairExcessAtBase D Q P = 0 := by
    intro Q hQ hNot
    have hOff : z ∉ Q ∨ ¬ Disjoint Q P := by
      by_contra h
      have hzQ : z ∈ Q := by
        by_contra hz
        exact h (Or.inl hz)
      have hDisj : Disjoint Q P := by
        by_contra hd
        exact h (Or.inr hd)
      exact hNot (Finset.mem_filter.mpr ⟨hQ, hzQ, hDisj⟩)
    have hZero := actual_selected_pair_excess_zero_off_support
      D fallback hCenters Q hQ ab.1 ab.2 haU hbU hSpec.1
      hUsedAB (by
        rw [← hSpec.2]
        exact hOff)
    unfold actualSelectedPairExcessAtBase
    rw [dite_eq_left hPcard]
    simpa only [ab] using hZero
  have hRestrict :
      S.sum (fun Q => actualSelectedPairExcessAtBase D Q P) =
        (D.ground.powersetCard 2).sum
          (fun Q => actualSelectedPairExcessAtBase D Q P) :=
    Finset.sum_subset (Finset.filter_subset _ _) hZeroOutside
  have hReindex := on_label_pair_bases_sum_eq_tail_sum
    D fallback hCenters P hUsed
      (fun Q => actualSelectedPairExcessAtBase D Q P)
  change S.sum (fun Q => actualSelectedPairExcessAtBase D Q P) =
    (D.ground \ insert z P).sum
      (fun w => actualSelectedPairExcessAtBase D ({z, w} : Edge α) P)
    at hReindex
  have hTail : (D.ground \ insert z P).sum
      (fun w => actualSelectedPairExcessAtBase D ({z, w} : Edge α) P) =
      (D.ground \ insert z P).sum
        (fun w => selectedOnLabelPairExcess D fallback hCenters P w) := by
    apply Finset.sum_congr rfl
    intro w _
    unfold actualSelectedPairExcessAtBase selectedOnLabelPairExcess
    rw [dite_eq_left hPcard]
  exact hRestrict.symm.trans (hReindex.trans hTail)

end JSP523.Rank4
