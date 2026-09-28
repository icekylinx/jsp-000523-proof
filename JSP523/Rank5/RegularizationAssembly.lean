import JSP523.Rank5.FacetEnergy
import JSP523.Rank5.MultiHitCodegree

/-!
# Finite assembly of one regularization round

This combines the vertex-cover stage and the actual facet-energy deletion
of §IV.4. The hypotheses expose the two estimates supplied by the heavy-root
cover and shadow-separation arguments: outside the cover, small-root degrees
are bounded; the layer meeting the cover has a stated deletion budget.
The conclusion uses the actual retained subfamily and its actual loss.
-/

namespace JSP523.Rank5

open JSP523

/-- Actual edges meeting a specified removed set at exactly one vertex. -/
def oneHitEdges {α : Type*} [DecidableEq α]
    (H : Family α) (X : Edge α) : Family α :=
  H.filter fun E => (E ∩ X).card = 1

/-- The layer removed with `X` splits into edges meeting it once and edges
meeting it at least twice. -/
theorem avoid_x_layer_le_one_hit_plus_multi
    {α : Type*} [DecidableEq α]
    (H : Family α) (X : Edge α) :
    H.card - (H.filter fun E => Disjoint E X).card ≤
      (oneHitEdges H X).card + (multipleRemovedEdges H X).card := by
  classical
  let H₀ : Family α := H.filter fun E => Disjoint E X
  let R : Family α := H \ H₀
  have hRsub : R ⊆ oneHitEdges H X ∪ multipleRemovedEdges H X := by
    intro E hE
    obtain ⟨hEH, hNotAvoid⟩ := Finset.mem_sdiff.mp hE
    have hPos : 1 ≤ (E ∩ X).card := by
      by_contra hN
      have hZero : (E ∩ X).card = 0 := by omega
      have hDisj : Disjoint E X :=
        Finset.disjoint_iff_inter_eq_empty.mpr
          (Finset.card_eq_zero.mp hZero)
      exact hNotAvoid (Finset.mem_filter.mpr ⟨hEH, hDisj⟩)
    by_cases hOne : (E ∩ X).card = 1
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hEH, hOne⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hEH, by omega⟩)
  have hRcard : R.card = H.card - H₀.card := by
    have hSub : H₀ ⊆ H := Finset.filter_subset _ _
    have hPart : R.card + H₀.card = H.card := by
      simpa [R] using Finset.card_sdiff_add_card_eq_card hSub
    omega
  calc
    H.card - H₀.card = R.card := hRcard.symm
    _ ≤ (oneHitEdges H X ∪ multipleRemovedEdges H X).card :=
      Finset.card_le_card hRsub
    _ ≤ (oneHitEdges H X).card + (multipleRemovedEdges H X).card :=
      Finset.card_union_le _ _

/-- With a pair-codegree cap, the multi-hit part of the removed layer is
paid by `choose(|X|,2) D₂(H)`, as in (IV.4.3). -/
theorem avoid_x_layer_le_one_hit_plus_pair_budget
    {α : Type*} [DecidableEq α]
    (H : Family α) (X : Edge α) (D : ℕ)
    (hPair : ∀ Q ∈ X.powersetCard 2,
      (H.filter fun E => Q ⊆ E).card ≤ D) :
    H.card - (H.filter fun E => Disjoint E X).card ≤
      (oneHitEdges H X).card + X.card.choose 2 * D := by
  have hLayer := avoid_x_layer_le_one_hit_plus_multi H X
  have hMulti := multiple_removed_edges_le_pair_codegree H X D hPair
  omega

/-- On an `r`-uniform family supported in `V`, completing an `(r-1)`-facet
is exactly the corresponding ordinary codegree fiber. -/
theorem facet_completions_card_eq_codegree
    {α : Type*} [DecidableEq α]
    {H : Family α} {V A : Edge α} {r : ℕ}
    (hU : Uniform r H) (hGround : ∀ E ∈ H, E ⊆ V)
    (hr : 1 ≤ r)
    (hA : A ∈ V.powersetCard (r - 1)) :
    (facetCompletions H V A).card =
      (H.filter fun E => A ⊆ E).card := by
  classical
  let C := facetCompletions H V A
  let D := H.filter fun E => A ⊆ E
  let f : α → Edge α := fun x => insert x A
  have hImage : C.image f = D := by
    ext E
    constructor
    · intro hE
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hE
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hx).2.2, Finset.subset_insert x A⟩
    · intro hE
      obtain ⟨hEH, hAE⟩ := Finset.mem_filter.mp hE
      have hAcard := (Finset.mem_powersetCard.mp hA).2
      have hEcard := hU hEH
      have hAdd : A.card + 1 = E.card := by omega
      obtain ⟨x, hxA, hEq⟩ :=
        Finset.exists_eq_insert_iff.mpr ⟨hAE, hAdd⟩
      have hxV : x ∈ V := hGround E hEH (hEq ▸ Finset.mem_insert_self x A)
      have hxC : x ∈ C :=
        Finset.mem_filter.mpr ⟨hxV, hxA, hEq ▸ hEH⟩
      exact Finset.mem_image.mpr ⟨x, hxC, hEq⟩
  have hInj : Set.InjOn f (↑C : Set α) := by
    intro x hx y hy hEq
    have hxA : x ∉ A := (Finset.mem_filter.mp hx).2.1
    change insert x A = insert y A at hEq
    have hxIn : x ∈ insert y A := hEq ▸ Finset.mem_insert_self x A
    rcases Finset.mem_insert.mp hxIn with hxy | hxA'
    · exact hxy
    · exact False.elim (hxA hxA')
  change C.card = D.card
  rw [← hImage, Finset.card_image_of_injOn hInj]

/-- Once heavy small roots are covered by `X`, deleting the `X` layer and
then high-degree facets yields a family with all prescribed degree caps.
The weighted loss is the exact finite form needed before choosing the
numerical scales in Theorem IV.4.1. -/
theorem regularization_round_from_cover_and_layer_bound
    {α : Type*} [DecidableEq α]
    (H : Family α) (V X : Edge α) (r t D L : ℕ)
    (C : ℕ → ℕ)
    (hAdm : Admissible H) (hU : Uniform r H)
    (hGround : ∀ E ∈ H, E ⊆ V) (hr : 4 ≤ r)
    (hCover : ∀ s, 1 ≤ s → s ≤ r - 2 →
      ∀ S ∈ V.powersetCard s, Disjoint S X →
        (H.filter fun E => S ⊆ E).card ≤ C s)
    (hLayer : H.card - (H.filter fun E => Disjoint E X).card ≤ L)
    (hPair : ∀ Q : Edge α, Q.card = 2 →
      (H.filter fun E => Q ⊆ E).card ≤ D) :
    ∃ H' : Family α, H' ⊆ H ∧ Admissible H' ∧ Uniform r H' ∧
      (∀ s, 1 ≤ s → s ≤ r - 2 →
        ∀ S ∈ V.powersetCard s,
          (H'.filter fun E => S ⊆ E).card ≤ C s) ∧
      (∀ A ∈ V.powersetCard (r - 1),
        (H'.filter fun E => A ⊆ E).card ≤ t) ∧
      (t - 1) * (H.card - H'.card) ≤
        (t - 1) * L + 2 * (V.card.choose 2 * ((r - 1) * D)) := by
  classical
  let H₀ : Family α := H.filter fun E => Disjoint E X
  let H' : Family α := facetCleanedFamily H₀ V r t
  have hH₀sub : H₀ ⊆ H := Finset.filter_subset _ _
  have hH'sub₀ : H' ⊆ H₀ := facet_cleaned_family_subset H₀ V r t
  have hH'sub : H' ⊆ H := hH'sub₀.trans hH₀sub
  have hAdm₀ : Admissible H₀ := admissible_mono hH₀sub hAdm
  have hU₀ : Uniform r H₀ := fun E hE => hU (hH₀sub hE)
  have hGround₀ : ∀ E ∈ H₀, E ⊆ V :=
    fun E hE => hGround E (hH₀sub hE)
  have hPair₀ : ∀ Q : Edge α, Q.card = 2 →
      (H₀.filter fun E => Q ⊆ E).card ≤ D := by
    intro Q hQ
    have hSub : (H₀.filter fun E => Q ⊆ E) ⊆
        (H.filter fun E => Q ⊆ E) := by
      intro E hE
      exact Finset.mem_filter.mpr
        ⟨hH₀sub (Finset.mem_filter.mp hE).1,
          (Finset.mem_filter.mp hE).2⟩
    exact (Finset.card_le_card hSub).trans (hPair Q hQ)
  have hSmall₀ : ∀ s, 1 ≤ s → s ≤ r - 2 →
      ∀ S ∈ V.powersetCard s,
        (H₀.filter fun E => S ⊆ E).card ≤ C s := by
    intro s hs hsr S hS
    by_cases hSX : Disjoint S X
    · have hSub : (H₀.filter fun E => S ⊆ E) ⊆
          (H.filter fun E => S ⊆ E) := by
        intro E hE
        exact Finset.mem_filter.mpr
          ⟨hH₀sub (Finset.mem_filter.mp hE).1,
            (Finset.mem_filter.mp hE).2⟩
      exact (Finset.card_le_card hSub).trans (hCover s hs hsr S hS hSX)
    · have hEmpty : (H₀.filter fun E => S ⊆ E) = ∅ := by
        ext E
        constructor
        · intro hE
          exfalso
          have hAvoid : Disjoint E X :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).2
          have hSE : S ⊆ E := (Finset.mem_filter.mp hE).2
          apply hSX
          exact Finset.disjoint_left.mpr (fun x hxS hxX =>
            (Finset.disjoint_left.mp hAvoid) (hSE hxS) hxX)
        · simp
      simp [hEmpty]
  have hSmall' : ∀ s, 1 ≤ s → s ≤ r - 2 →
      ∀ S ∈ V.powersetCard s,
        (H'.filter fun E => S ⊆ E).card ≤ C s := by
    intro s hs hsr S hS
    have hSub : (H'.filter fun E => S ⊆ E) ⊆
        (H₀.filter fun E => S ⊆ E) := by
      intro E hE
      exact Finset.mem_filter.mpr
        ⟨hH'sub₀ (Finset.mem_filter.mp hE).1,
          (Finset.mem_filter.mp hE).2⟩
    exact (Finset.card_le_card hSub).trans (hSmall₀ s hs hsr S hS)
  have hFacet : ∀ A ∈ V.powersetCard (r - 1),
      (H'.filter fun E => A ⊆ E).card ≤ t := by
    intro A hA
    have hGround' : ∀ E ∈ H', E ⊆ V :=
      fun E hE => hGround E (hH'sub hE)
    rw [← facet_completions_card_eq_codegree
      (facet_cleaned_family_uniform hU₀) hGround' (by omega : 1 ≤ r) hA]
    exact facet_cleaned_family_facet_degree_le H₀ V r t hA
  have hFacetBudget :
      (t - 1) * (H₀.card - H'.card) ≤
        2 * (V.card.choose 2 * ((r - 1) * D)) := by
    exact facet_cleaned_family_loss_bound hAdm₀ hU₀ hGround₀
      (by omega : 2 ≤ r) hPair₀
  have hLossSplit : H.card - H'.card =
      (H.card - H₀.card) + (H₀.card - H'.card) := by
    have hCard₀ := Finset.card_le_card hH₀sub
    have hCard' := Finset.card_le_card hH'sub₀
    omega
  refine ⟨H', hH'sub, facet_cleaned_family_admissible hAdm₀,
    facet_cleaned_family_uniform hU₀, hSmall', hFacet, ?_⟩
  rw [hLossSplit, mul_add]
  exact Nat.add_le_add (Nat.mul_le_mul_left (t - 1) hLayer) hFacetBudget

end JSP523.Rank5
