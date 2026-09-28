import JSP523.Rank5.HeavyRootAllRanks
import JSP523.Rank5.RegularizationAssembly

/-!
# Heavy-root cover assembled with facet regularization

This is the finite structural part of Theorem IV.4.1. The only external
round budget is the size of the layer meeting the selected cover; Lemma
IV.3.2 and equation (IV.3.2) supply that budget in the manuscript after
their shadow estimates are applied. All root degrees and final facet degrees are actual
codegrees of the constructed retained family.
-/

namespace JSP523.Rank5

open JSP523

/-- An explicit numerical heavy-root gap and a bound for the layer meeting
any eligible cover produce a genuinely regularized subfamily. -/
theorem regularization_round_from_actual_heavy_roots
    {α : Type*} [DecidableEq α]
    (H : Family α) (V : Edge α) (r t D₂ L : ℕ)
    (d D a : ℕ → ℕ)
    (hAdm : Admissible H) (hU : Uniform r H)
    (hGround : ∀ E ∈ H, E ⊆ V) (hr : 4 ≤ r)
    (hOffPrefixCap : ∀ s, 1 ≤ s → s ≤ r - 2 →
      ∀ P ∈ V.powersetCard s, ∀ x : α, x ∉ P →
        (H.filter fun E => P ∪ {x} ⊆ E).card ≤ D s)
    (hGap : ∀ s, 1 ≤ s → s ≤ r - 2 →
      (V.powersetCard (r - s)).card +
        a s * a s * ((r - s) * D s) < a s * d s)
    (hLayer : ∀ X : Edge α, X ⊆ V →
      X.card ≤ ∑ s ∈ Finset.Icc 1 (r - 2), s * (a s - 1) →
      H.card - (H.filter fun E => Disjoint E X).card ≤ L)
    (hPair : ∀ Q : Edge α, Q.card = 2 →
      (H.filter fun E => Q ⊆ E).card ≤ D₂) :
    ∃ X : Edge α, X ⊆ V ∧
      X.card ≤ ∑ s ∈ Finset.Icc 1 (r - 2), s * (a s - 1) ∧
      ∃ H' : Family α, H' ⊆ H ∧ Admissible H' ∧ Uniform r H' ∧
        (∀ s, 1 ≤ s → s ≤ r - 2 →
          ∀ S ∈ V.powersetCard s,
            (H'.filter fun E => S ⊆ E).card ≤ d s) ∧
        (∀ A ∈ V.powersetCard (r - 1),
          (H'.filter fun E => A ⊆ E).card ≤ t) ∧
        (t - 1) * (H.card - H'.card) ≤
          (t - 1) * L +
            2 * (V.card.choose 2 * ((r - 1) * D₂)) := by
  obtain ⟨X, hXV, hXcard, hCover⟩ :=
    exists_all_ranks_actual_heavy_root_cover H V r d D a
      hU hGround hAdm hr hOffPrefixCap hGap
  obtain ⟨H', hH'sub, hH'Adm, hH'U, hSmall, hFacet, hLoss⟩ :=
    regularization_round_from_cover_and_layer_bound H V X r t D₂ L d
      hAdm hU hGround hr hCover (hLayer X hXV hXcard) hPair
  exact ⟨X, hXV, hXcard, H', hH'sub, hH'Adm, hH'U,
    hSmall, hFacet, hLoss⟩

end JSP523.Rank5
