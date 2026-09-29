import JSP523.Rank5.HigherRankLowerFirstWitness

/-! # The weighted s=3 inheritance witness bound -/
namespace JSP523.Rank5.HigherRankLower
variable {α : Type*} [DecidableEq α]

theorem upper_strong_witnesses_eq_strong_second_sigma
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (n tLower tUpper : ℕ)
    (upper lower : Edge α → α) :
    lowerUpperStrongWitnesses n I K H V tLower tUpper upper lower =
      I.sigma (fun i => (strongSecondRoots K H V n tUpper upper i).sigma
        (fun R => lowerWitnessThirdRoots n H V tLower lower i R)) := by
  classical
  ext w
  simp only [lowerUpperStrongWitnesses, lowerInheritanceWitnesses,
    lowerWitnessesFor, strongSecondRoots, Finset.mem_filter, Finset.mem_sigma]
  tauto

/-- Both retained-degree halves produce actual upper-strong witnesses. -/
theorem weighted_upper_strong_witness_lower_bound
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (n tLower tUpper : ℕ)
    (upper lower : Edge α → α)
    (hFirst : ∀ i ∈ I,
      (facetParents K i.1.2).card ≤
        2 * (strongSecondRoots K H V n tUpper upper i).card)
    (hThird : ∀ i ∈ I, ∀ R ∈ strongSecondRoots K H V n tUpper upper i,
      (parentTripleLink K V (lowerWitnessCore i)).card ≤
        2 * (lowerWitnessThirdRoots n H V tLower lower i R).card) :
    (∑ i ∈ I, (facetParents K i.1.2).card *
      (parentTripleLink K V (lowerWitnessCore i)).card) ≤
      4 * (lowerUpperStrongWitnesses n I K H V tLower tUpper upper lower).card := by
  classical
  rw [upper_strong_witnesses_eq_strong_second_sigma, Finset.card_sigma,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  let S := strongSecondRoots K H V n tUpper upper i
  let d := (parentTripleLink K V (lowerWitnessCore i)).card
  have hSum : S.card * d ≤
      2 * ∑ R ∈ S, (lowerWitnessThirdRoots n H V tLower lower i R).card := by
    calc
      _ = ∑ _R ∈ S, d := by simp
      _ ≤ ∑ R ∈ S, 2 * (lowerWitnessThirdRoots n H V tLower lower i R).card :=
        Finset.sum_le_sum (fun R hR => hThird i hi R hR)
      _ = _ := by rw [Finset.mul_sum]
  have hFirst' := hFirst i hi
  rw [Finset.card_sigma]
  change (facetParents K i.1.2).card * d ≤
    4 * ∑ R ∈ S, (lowerWitnessThirdRoots n H V tLower lower i R).card
  nlinarith

/-- IV.9.3 for s=3: the two witness halves and the pinned upper count. -/
theorem lower_inheritance_weighted_incidence_bound
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (n tLower tUpper D₄ D₅ Dₙ : ℕ)
    (upper lower : Edge α → α)
    (hI : I ⊆ badIncidences K V (n + 1) upper lower)
    (hKH : K ⊆ H) (hUniform : Uniform (n + 3) K)
    (hAmbient : ∀ E ∈ K, E ⊆ V)
    (hUpperLabels : ActualRankLabels K (n + 1) upper)
    (hLowerLabels : ActualRankLabels K n lower)
    (ht : 1 ≤ tLower)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄)
    (hDₙ : ∀ S : Edge α, S.card = n + 1 →
      (H.filter fun E => S ⊆ E).card ≤ Dₙ)
    (hD₅ : ∀ S : Edge α, S.card = 5 →
      (H.filter fun E => S ⊆ E).card ≤ D₅)
    (hFirst : ∀ i ∈ I,
      (facetParents K i.1.2).card ≤
        2 * (strongSecondRoots K H V n tUpper upper i).card)
    (hThird : ∀ i ∈ I, ∀ R ∈ strongSecondRoots K H V n tUpper upper i,
      (parentTripleLink K V (lowerWitnessCore i)).card ≤
        2 * (lowerWitnessThirdRoots n H V tLower lower i R).card) :
    tLower * (∑ i ∈ I, (facetParents K i.1.2).card *
      (parentTripleLink K V (lowerWitnessCore i)).card) ≤
      12 * (V.powersetCard 3).card ^ 2 * D₄ * Dₙ * D₅ := by
  have hLow := weighted_upper_strong_witness_lower_bound I K H V n tLower tUpper
    upper lower hFirst hThird
  have hUp := lower_upper_strong_witness_global_pinned_bound n I K H V
    tLower tUpper D₄ D₅ Dₙ upper lower hI hKH hUniform hAmbient
    hUpperLabels hLowerLabels ht hD₄ hDₙ hD₅
  have hScaled := Nat.mul_le_mul_left tLower hLow
  nlinarith

end JSP523.Rank5.HigherRankLower
