import JSP523.Rank4.PreprocessCollisionMoment

/-!
# Finite iteration of actual triple-codegree cleanup

This file iterates the proved one-step high-codegree deletion over any
nonempty finite threshold schedule.  Pair and facet caps are inherited by
every subfamily, and the total loss is bounded from the actual layer losses.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

private theorem rank_four_pair_degree_mono {F K : Family α}
    (hKF : K ⊆ F) (P : Edge α) :
    rankFourPairDegree K P ≤ rankFourPairDegree F P := by
  unfold rankFourPairDegree
  apply Finset.card_le_card
  intro E hE
  exact Finset.mem_filter.mpr ⟨hKF (Finset.mem_filter.mp hE).1,
    (Finset.mem_filter.mp hE).2⟩

private theorem facet_completions_mono {F K : Family α}
    (hKF : K ⊆ F) (U T : Edge α) :
    facetCompletions K U T ⊆ facetCompletions F U T := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
    hKF (Finset.mem_filter.mp hx).2⟩

private theorem nested_sdiff_card_bound
    (F K₁ K₂ : Family α) :
    (F \ K₂).card ≤ (F \ K₁).card + (K₁ \ K₂).card := by
  have hSub : F \ K₂ ⊆ (F \ K₁) ∪ (K₁ \ K₂) := by
    intro E hE
    have hEF := (Finset.mem_sdiff.mp hE).1
    have hEK₂ := (Finset.mem_sdiff.mp hE).2
    by_cases hEK₁ : E ∈ K₁
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hEK₁, hEK₂⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hEF, hEK₁⟩))
  calc
    _ ≤ ((F \ K₁) ∪ (K₁ \ K₂)).card := Finset.card_le_card hSub
    _ ≤ (F \ K₁).card + (K₁ \ K₂).card := Finset.card_union_le _ _

/-- A finite list of target triple codegrees can be applied successively.
The output is a subfamily with the final surviving degree bounded by one of
the supplied targets, and a weighted total loss bound.  The explicit finite
premises are the pair and facet codegree caps used in each one-step moment
estimate. -/
theorem iterate_high_codegree_regularization
    (U : Edge α) (M D rmin : ℕ) (targets : List ℕ) (F : Family α)
    (hNonempty : targets ≠ [])
    (hTargets : ∀ r ∈ targets, rmin ≤ r)
    (hUniform : Uniform 4 F)
    (hAdmissible : Admissible F)
    (hPair : ∀ P : Edge α, P.card = 2 → rankFourPairDegree F P ≤ M)
    (hFacet : ∀ T : Edge α, T.card = 3 →
      (facetCompletions F U T).card ≤ D) :
    ∃ K : Family α,
      K ⊆ F ∧
      (∃ r ∈ targets, ∀ T ∈ U.powersetCard 3,
        (tripleCompletionVertices K U T).card ≤ r) ∧
      rmin * (F \ K).card ≤
        targets.length * (2 * (U.powersetCard 2).card * max M (9 * D)) := by
  induction targets generalizing F with
  | nil =>
      contradiction
  | cons R rest ih =>
      have hRmin : rmin ≤ R := hTargets R (by simp)
      have hStep := high_codegree_deletion_regularizes_of_degree_caps
        F U R M D hUniform hAdmissible hPair hFacet
      obtain ⟨K₁, hK₁F, hLoss₁, hReg₁⟩ := hStep
      by_cases hRest : rest = []
      · subst rest
        refine ⟨K₁, hK₁F, ⟨R, by simp, hReg₁⟩, ?_⟩
        have hMul := Nat.mul_le_mul_right (F \ K₁).card hRmin
        calc
          rmin * (F \ K₁).card ≤ R * (F \ K₁).card := hMul
          _ ≤ 2 * (U.powersetCard 2).card * max M (9 * D) := hLoss₁
          _ = (R :: []).length *
              (2 * (U.powersetCard 2).card * max M (9 * D)) := by simp
      · have hKUniform : Uniform 4 K₁ := by
          intro E hE
          exact hUniform (hK₁F hE)
        have hKAdmissible : Admissible K₁ := admissible_mono hK₁F hAdmissible
        have hKPair : ∀ P : Edge α, P.card = 2 →
            rankFourPairDegree K₁ P ≤ M := by
          intro P hP
          exact (rank_four_pair_degree_mono hK₁F P).trans (hPair P hP)
        have hKFacet : ∀ T : Edge α, T.card = 3 →
            (facetCompletions K₁ U T).card ≤ D := by
          intro T hT
          exact (Finset.card_le_card (facet_completions_mono hK₁F U T)).trans
            (hFacet T hT)
        obtain ⟨K₂, hK₂K₁, hReg₂, hLoss₂⟩ :=
          ih K₁ hRest (fun r hr => hTargets r (by simp [hr]))
            hKUniform hKAdmissible hKPair hKFacet
        obtain ⟨r₂, hr₂, hReg₂⟩ := hReg₂
        refine ⟨K₂, hK₂K₁.trans hK₁F, ⟨r₂, by simp [hr₂], hReg₂⟩, ?_⟩
        have hLossAdd := nested_sdiff_card_bound F K₁ K₂
        have hMul := Nat.mul_le_mul_left rmin hLossAdd
        rw [Nat.mul_add] at hMul
        have hFirst : rmin * (F \ K₁).card ≤
            2 * (U.powersetCard 2).card * max M (9 * D) := by
          have h := Nat.mul_le_mul_right (F \ K₁).card hRmin
          exact h.trans hLoss₁
        have hCombined : rmin * (F \ K₂).card ≤
            2 * (U.powersetCard 2).card * max M (9 * D) +
              rest.length * (2 * (U.powersetCard 2).card * max M (9 * D)) :=
          hMul.trans (Nat.add_le_add hFirst hLoss₂)
        simpa [List.length_cons, Nat.add_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hCombined

end JSP523.Rank4
