import JSP523.Counting.LinearNearStar

/-!
# Exact star and outside decomposition at arbitrary rank

This proves the finite counting identity (IV.2.1) of
`jsp-000523-proof/paper/proof.md`.
It also provides the rank-four specialization used in §III.C.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Actual edges entirely outside the specified star center. -/
def outsideFamily (H : Family α) (W : Edge α) : Family α :=
  H.filter fun E => E ⊆ W

/-- Present facets of the star centered at `v`. -/
def presentStarFacets (H : Family α) (W : Edge α) (v : α)
    (r : ℕ) : Family α :=
  (W.powersetCard (r - 1)).filter fun T => insert v T ∈ H

/-- Exact star/outside decomposition of a uniform family supported on
`insert v W`. -/
theorem star_outside_card
    {H : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hU : Uniform r H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) :
    H.card = (presentStarFacets H W v r).card +
      (outsideFamily H W).card := by
  classical
  let starEdges := H.filter fun E => v ∈ E
  have hNoStarEq : (H.filter fun E => v ∉ E) = outsideFamily H W := by
    ext E
    simp only [outsideFamily, Finset.mem_filter]
    constructor
    · rintro ⟨hE, hvE⟩
      refine ⟨hE, ?_⟩
      intro x hxE
      have hxSupport := hSupport E hE hxE
      rcases Finset.mem_insert.mp hxSupport with hEq | hxW
      · exact False.elim (hvE (hEq ▸ hxE))
      · exact hxW
    · rintro ⟨hE, hEW⟩
      exact ⟨hE, fun hvE => hvW (hEW hvE)⟩
  have hStarEq : starEdges =
      (presentStarFacets H W v r).image (fun T => insert v T) := by
    ext E
    constructor
    · intro hE
      have hEf := Finset.mem_filter.mp hE
      let T := E.erase v
      have hTcard : T.card = r - 1 := by
        have hErase := Finset.card_erase_add_one hEf.2
        have hEcard := hU hEf.1
        dsimp [T]
        omega
      have hTsub : T ⊆ W := by
        intro x hxT
        have hxE : x ∈ E := Finset.mem_of_mem_erase hxT
        have hxSupport := hSupport E hEf.1 hxE
        rcases Finset.mem_insert.mp hxSupport with hEq | hxW
        · exact False.elim ((Finset.ne_of_mem_erase hxT) hEq)
        · exact hxW
      have hTstar : T ∈ presentStarFacets H W v r := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩, ?_⟩
        simpa [T, Finset.insert_erase hEf.2] using hEf.1
      exact Finset.mem_image.mpr
        ⟨T, hTstar, Finset.insert_erase hEf.2⟩
    · intro hE
      obtain ⟨T, hT, hTE⟩ := Finset.mem_image.mp hE
      have hTf := Finset.mem_filter.mp hT
      exact Finset.mem_filter.mpr
        ⟨hTE ▸ hTf.2, hTE ▸ Finset.mem_insert_self v T⟩
  have hStarCard : starEdges.card = (presentStarFacets H W v r).card := by
    rw [hStarEq]
    apply Finset.card_image_iff.mpr
    intro T hT S hS hEq
    have hTsub : T ⊆ W :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).1
    have hSsub : S ⊆ W :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).1
    have hvT : v ∉ T := fun hvT => hvW (hTsub hvT)
    have hvS : v ∉ S := fun hvS => hvW (hSsub hvS)
    have hErase := congrArg (fun E : Edge α => E.erase v) hEq
    simpa [Finset.erase_insert hvT, Finset.erase_insert hvS] using hErase
  have hPartition := H.card_filter_add_card_filter_not (fun E => v ∈ E)
  simpa only [starEdges, hNoStarEq, hStarCard] using hPartition.symm

/-- Present and missing star facets partition all `(r-1)`-sets on `W`. -/
theorem present_add_missing_star_facets
    (H : Family α) (W : Edge α) (v : α) (r : ℕ) :
    (presentStarFacets H W v r).card +
      (missingStarFacets H W v r).card = W.card.choose (r - 1) := by
  classical
  simpa only [presentStarFacets, missingStarFacets,
    Finset.card_powersetCard] using
    (W.powersetCard (r - 1)).card_filter_add_card_filter_not
      (fun T => insert v T ∈ H)

/-- Exact near-star edge identity (IV.2.1), with natural-number
subtraction justified by the facet partition. -/
theorem near_star_card_identity
    {H : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hU : Uniform r H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) :
    H.card = W.card.choose (r - 1) -
      (missingStarFacets H W v r).card +
      (outsideFamily H W).card := by
  have hSplit := star_outside_card hU hSupport hvW
  have hFacets := present_add_missing_star_facets H W v r
  omega

/-- The integer step from `r b ≤ w+q` to `b-q ≤ floor(w/r)`.
It is stated without subtraction so it also covers `b < q`. -/
private theorem incidence_implies_excess_bound
    {r b w q : ℕ} (hr : 1 ≤ r) (hInc : r * b ≤ w + q) :
    b ≤ q + w / r := by
  have hRem : w % r < r := Nat.mod_lt w (by omega)
  have hDiv : w = r * (w / r) + w % r := by
    simpa [add_comm, mul_comm] using (Nat.mod_add_div w r).symm
  by_contra hNot
  have hb : q + w / r + 1 ≤ b := by omega
  have hMul := Nat.mul_le_mul_left r hb
  nlinarith

/-- Once the outside family is linear, the exact near-star upper bound
follows from (IV.2.1) and (IV.2.6), for every rank `r ≥ 3`. -/
theorem near_star_upper_of_linear_outside
    {H : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hU : Uniform r H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) (hr : 3 ≤ r)
    (hLin : LinearFamily (outsideFamily H W)) :
    H.card ≤ W.card.choose (r - 1) + W.card / r := by
  let B := outsideFamily H W
  let q := (missingStarFacets H W v r).card
  have hBH : B ⊆ H := Finset.filter_subset _ _
  have hBU : Uniform r B := by
    intro E hE
    exact hU (hBH hE)
  have hBW : ∀ E ∈ B, E ⊆ W := by
    intro E hE
    exact (Finset.mem_filter.mp hE).2
  have hInc : r * B.card ≤ W.card + q :=
    linear_near_star_incidence_bound hH hBH hBU hLin hr hBW hvW
  have hExcess : B.card ≤ q + W.card / r :=
    incidence_implies_excess_bound (by omega) hInc
  have hFacets := present_add_missing_star_facets H W v r
  have hQBound : q ≤ W.card.choose (r - 1) := by
    change (presentStarFacets H W v r).card + q =
      W.card.choose (r - 1) at hFacets
    omega
  have hId := near_star_card_identity hU hSupport hvW
  change H.card = W.card.choose (r - 1) - q + B.card at hId
  omega

/-- The equality arithmetic in §IV.2: at most one star facet is missing,
and a single missing facet requires remainder `r-1`. This also recovers
the rank-four restriction in §III.C. -/
theorem near_star_equality_missing_restriction
    {H : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hU : Uniform r H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) (hr : 3 ≤ r)
    (hLin : LinearFamily (outsideFamily H W))
    (hEquality : H.card = W.card.choose (r - 1) + W.card / r) :
    (missingStarFacets H W v r).card ≤ 1 ∧
      ((missingStarFacets H W v r).card = 1 → W.card % r = r - 1) := by
  let B := outsideFamily H W
  let q := (missingStarFacets H W v r).card
  have hBH : B ⊆ H := Finset.filter_subset _ _
  have hBU : Uniform r B := by
    intro E hE
    exact hU (hBH hE)
  have hBW : ∀ E ∈ B, E ⊆ W := by
    intro E hE
    exact (Finset.mem_filter.mp hE).2
  have hInc : r * B.card ≤ W.card + q :=
    linear_near_star_incidence_bound hH hBH hBU hLin hr hBW hvW
  have hFacets := present_add_missing_star_facets H W v r
  have hQBound : q ≤ W.card.choose (r - 1) := by
    change (presentStarFacets H W v r).card + q =
      W.card.choose (r - 1) at hFacets
    omega
  have hId := near_star_card_identity hU hSupport hvW
  change H.card = W.card.choose (r - 1) - q + B.card at hId
  have hb : B.card = q + W.card / r := by omega
  have hRem : W.card % r < r := Nat.mod_lt _ (by omega)
  have hDiv : W.card = r * (W.card / r) + W.card % r := by
    simpa [add_comm, mul_comm] using (Nat.mod_add_div W.card r).symm
  have hrPred : r - 1 + 1 = r := by omega
  have hBudget : (r - 1) * q ≤ W.card % r := by
    rw [hb] at hInc
    nlinarith [hDiv, hrPred]
  constructor
  · by_contra hqNot
    have hqTwo : 2 ≤ q := by omega
    have hMul := Nat.mul_le_mul_left (r - 1) hqTwo
    omega
  · intro hq
    change q = 1 at hq
    rw [hq] at hBudget
    omega

end JSP523
