import JSP523.Rank4.GlobalActualEndToEndSucc
import JSP523.Rank4.GlobalActualInitialOuterUncleaned

namespace JSP523.Rank4

open Filter

/-- Fixed actual outer objects support arbitrarily small actual master errors.
All regularization and reciprocal cleanup are performed on the original family. -/
theorem exists_actual_master_sequence
    (H : (n : ℕ) → Family (Fin (n + 1)))
    (hAdm : ∀ᶠ n in atTop, Admissible (H n))
    (hUniform : ∀ᶠ n in atTop, Uniform 4 (H n)) :
    ∃ Z X : (n : ℕ) → Edge (Fin (n + 1)),
    ∃ owner : (n : ℕ) → Edge (Fin (n + 1)) → Fin (n + 1),
    ∃ outerLoss overlap : ℕ → ℕ,
      (∀ᶠ n in atTop, ActualInitialOuterData (H n) (Z n) (X n) (owner n) (outerLoss n)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ r : ℕ → ℝ, Tendsto r atTop (nhds 0) ∧
        ∀ᶠ n in atTop, ∃ level : ℕ, ∃ a : ℝ,
          ∃ A : ActualEndToEndData (H n) (endToEndGround (Z n) (X n)) level a (overlap n) (outerLoss n),
            (A.masterError : ℝ) / (n : ℝ) ^ 3 ≤ ε / 2 + r n) := by
  classical
  obtain ⟨Z, X, owner, loss, hInitial, hLoss, hOverlap⟩ :=
    exists_actual_initial_outer_sequence_with_uncleaned_overlap H hAdm hUniform
  let overlap := fun n => endToEndOverlap (H n) (Z n) (X n)
  refine ⟨Z, X, owner, loss, overlap, hInitial, ?_⟩
  intro ε hε
  have hp := end_to_end_parameter_bounds (ε / 8) (by positivity)
  have hExists : ∀ᶠ n in atTop,
      Nonempty (ActualEndToEndData (H n) (endToEndGround (Z n) (X n))
        (endToEndLevel (ε / 8)) (endToEndWeakCoefficient (ε / 8)) (overlap n) (loss n)) := by
    have hFinite := (tendsto_add_atTop_nat 1).eventually
      (eventually_actual_end_to_end_data _ hp.1 _ hp.2.1)
    filter_upwards [hInitial, hAdm, hUniform, hFinite] with n hi hA hF hm
    let U := endToEndGround (Z n) (X n)
    let L := fun c => rankFourStarLink (H n) U c
    have hOutside : ∀ c ∈ Z n, c ∉ U := by
      intro c hc hIn
      exact (Finset.mem_sdiff.mp hIn).2 (Finset.mem_union_left _ hc)
    have hEdges : ∀ c ∈ Z n, ∀ Q ∈ L c, insert c Q ∈ H n := by
      intro c _ Q hQ
      exact (Finset.mem_filter.mp hQ).2
    have hGround : ∀ c ∈ Z n, ∀ Q ∈ L c, Q ∈ U.powersetCard 3 := by
      intro c _ Q hQ
      exact (Finset.mem_filter.mp hQ).1
    have hOL : ((Z n).biUnion (pairOwnerCleanedLink L (owner n)) ∩
        rankFourFacetShadow (fixedDecompositionCore (H n) U) U).card ≤ overlap n := by
      apply Finset.card_le_card
      intro Q hQ
      obtain ⟨hc, hShadow⟩ := Finset.mem_inter.mp hQ
      obtain ⟨c, hcZ, hQc⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr
        ⟨c, hcZ, pair_owner_cleaned_link_subset L (owner n) c hQc⟩, hShadow⟩
    exact hm (H n) U Finset.univ 0 L (Z n) (owner n) (overlap n) (loss n)
      hA hF (Finset.subset_univ U) hi.cover.2.2.2.2.2.1 hi.cover.2.2.2.2.2.2
      (fun c _ => Finset.mem_univ c) hOutside hEdges hGround
      (by change 3 ≤ (Finset.univ \ (Z n ∪ X n)).card; have := hi.ground_large; omega) hOL hi.original_mass
  obtain ⟨D, r, hr, hActual⟩ := select_actual_end_to_end_succ_with_small_error H
    (fun n => endToEndGround (Z n) (X n)) overlap loss ε hε hExists hOverlap hLoss
  refine ⟨r, hr, ?_⟩
  filter_upwards [hActual] with n hn
  obtain ⟨A, _, hA⟩ := hn
  exact ⟨_, _, A, hA⟩

end JSP523.Rank4
