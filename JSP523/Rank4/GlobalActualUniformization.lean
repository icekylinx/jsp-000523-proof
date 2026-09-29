import JSP523.Rank4.GlobalActualSequenceUniformization
import JSP523.Rank4.GlobalActualSingleCenterEndpoint

/-! # Uniform rank-four exactness from sequence stability -/

namespace JSP523.Rank4

open Filter

/-- A sequence exactness theorem for all admissible families above the
star lower bound yields a uniform eventual exact upper bound. -/
theorem eventually_uniform_rank_four_exact_of_sequence_endpoint
    (hEndpoint : ∀ H : (n : ℕ) → Family (Fin (n + 1)),
      (∀ n, Admissible (H n)) → (∀ n, Uniform 4 (H n)) →
      (∀ᶠ n in atTop, n.choose 3 ≤ (H n).card) →
      ∀ᶠ n in atTop, (H n).card ≤ n.choose 3 + n / 4) :
    ∀ᶠ n : ℕ in atTop, ∀ F : Family (Fin (n + 1)),
      Admissible F → Uniform 4 F → F.card ≤ n.choose 3 + n / 4 := by
  have hUpper := eventually_uniform_of_rank_four_sequence_property
    (fun n F => F.card ≤ n.choose 3 + n / 4)
    (fun H hAdm hUniform hLower => hEndpoint H hAdm hUniform
      (Eventually.of_forall hLower))
  filter_upwards [hUpper] with n hn
  intro F hAdm hUniform
  by_cases hLower : n.choose 3 ≤ F.card
  · exact hn F hAdm hUniform hLower
  · omega

/-- Sequence star stability now yields the exact uniform upper bound at
rank four, with the complete-star plus matching construction attaining it. -/
theorem eventually_rank_four_extremal_exact_of_sequence_stability
    (hOutside : ∀ H : (n : ℕ) → Family (Fin (n + 1)),
      (∀ n, Admissible (H n)) → (∀ n, Uniform 4 (H n)) →
      (∀ᶠ n in atTop, n.choose 3 ≤ (H n).card) →
      Filter.Tendsto
        (fun n => ((outsideEdges (H n)
          (Finset.univ.erase (actualGlobalMainCenter (H n)))).card : ℝ) /
          (n : ℝ) ^ 3) atTop (nhds 0)) :
    ∀ᶠ n : ℕ in atTop,
      (∃ F : Family (Fin (n + 1)), Admissible F ∧ Uniform 4 F ∧
        F.card = n.choose 3 + n / 4) ∧
      (∀ F : Family (Fin (n + 1)), Admissible F → Uniform 4 F →
        F.card ≤ n.choose 3 + n / 4) := by
  have hUpper := eventually_uniform_rank_four_exact_of_sequence_endpoint
    (fun H hAdm hUniform hLower =>
      (rank_four_eventual_exact_bound_of_outside_stability H
        (fun n => actualGlobalMainCenter (H n)) hAdm hUniform hLower
        (hOutside H hAdm hUniform hLower)).mono (fun _ h => h.1))
  filter_upwards [hUpper] with n hn
  have hConstruction := JSP523.exists_star_plus_matching_exact
    (0 : Fin (n + 1)) 4 (by omega)
  obtain ⟨F, hFU, hFA, hCard⟩ := hConstruction
  have hSize : (Finset.univ.erase (0 : Fin (n + 1)) : Edge (Fin (n + 1))).card = n := by simp
  refine ⟨⟨F, hFA, hFU, ?_⟩, hn⟩
  simpa only [hSize] using hCard

/-- Every sufficiently large extremizer has one of the two local equality
forms at the canonical original-family center. -/
theorem eventually_rank_four_extremal_classification_of_sequence_stability
    (hOutside : ∀ H : (n : ℕ) → Family (Fin (n + 1)),
      (∀ n, Admissible (H n)) → (∀ n, Uniform 4 (H n)) →
      (∀ᶠ n in atTop, n.choose 3 ≤ (H n).card) →
      Filter.Tendsto
        (fun n => ((outsideEdges (H n)
          (Finset.univ.erase (actualGlobalMainCenter (H n)))).card : ℝ) /
          (n : ℝ) ^ 3) atTop (nhds 0)) :
    ∀ᶠ n : ℕ in atTop, ∀ F : Family (Fin (n + 1)),
      Admissible F → Uniform 4 F →
      F.card = n.choose 3 + n / 4 →
      RankFourNearStarEqualityFamily F
        (Finset.univ.erase (actualGlobalMainCenter F))
        (actualGlobalMainCenter F) := by
  have hUniformClass := eventually_uniform_of_rank_four_sequence_property
    (fun n F => F.card = n.choose 3 + n / 4 →
      RankFourNearStarEqualityFamily F
        (Finset.univ.erase (actualGlobalMainCenter F))
        (actualGlobalMainCenter F))
    (fun H hAdm hUniform hLower => by
      have hRatio := hOutside H hAdm hUniform (Eventually.of_forall hLower)
      have hThreshold := outside_ratio_tendsto_zero_implies_threshold
        (fun n => (outsideEdges (H n)
          (Finset.univ.erase (actualGlobalMainCenter (H n)))).card) hRatio
      filter_upwards [hThreshold] with n hn
      intro hEquality
      let v := actualGlobalMainCenter (H n)
      let W : Edge (Fin (n + 1)) := Finset.univ.erase v
      have hW : W.card = n := by simp [W]
      have hvW : v ∉ W := by simp [W]
      have hSupport : ∀ E ∈ H n, E ⊆ insert v W := by
        intro E _ x hx
        have hFull : insert v W = Finset.univ := by simp [W]
        rw [hFull]
        exact Finset.mem_univ x
      have hStar : W.card.choose 3 ≤ (H n).card := by
        rw [hW]
        exact hLower n
      have hMissing := rank_four_near_star_threshold_of_outside
        (hUniform n) hSupport hvW hStar (by simpa only [hW] using hn.2)
      have hForm := (rank_four_near_star_equality_iff
        (hAdm n) (hUniform n) hSupport hvW
        (by simpa only [hW] using hn.1) hMissing).mp
          (by simpa only [hW] using hEquality)
      simpa only [W, v] using hForm)
  filter_upwards [hUniformClass] with n hn
  intro F hAdm hUniform hEquality
  have hLower : n.choose 3 ≤ F.card := by rw [hEquality]; omega
  exact hn F hAdm hUniform hLower hEquality

end JSP523.Rank4
