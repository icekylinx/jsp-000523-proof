import JSP523.Rank5.OutsideLayerPartition
import JSP523.Rank5.ExceptionalOneVertexBudget
import JSP523.Counting.LocalExactGap

/-!
# Finite outside-edge contraction before asymptotic estimates

This combines the ordinary-layer incidence estimate with deletion cost,
the `b₁` numerator bound from (IV.2.9), the mixed-layer `J` bound, and the
actual all-exceptional layer. It is a finite predecessor to (IV.2.10):
the dirty-edge term and `bᵣ` remain explicit and no asymptotic estimate or
division is used.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Finite contraction inequality for the actual outside family. Here
`q_U` and `q_D` are the missing facets wholly inside `U` and meeting `D`,
respectively; `J` is the exceptional-pair budget; and `bᵣ` is the actual
all-exceptional layer. -/
theorem outside_finite_contraction_predecessor
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 5 ≤ r) (hvW : v ∉ W) :
    let D := badSingletonVertices H W v r
    let U := W \ D
    let M := missingStarFacets H W v r
    let qU := (missingStarFacets H U v r).card
    let qD := (M.filter fun S => (S ∩ D).Nonempty).card
    let J := D.card.choose 2 * (W.card - 2).choose (r - 3)
    let Δ := W.card.choose (r - 2) - (W.card - r - 1).choose (r - 2)
    let dirty := (actualDirtyOutsideEdges H W v r).card
    let bᵣ := (outsideFamily H D).card
    r * (r - 1) * (outsideFamily H W).card ≤
      (r - 1) * (U.card + qU + r * dirty) +
        r * (2 * qD + 2 * J + D.card * Δ) +
        r * (r - 1) * J + r * (r - 1) * bᵣ := by
  classical
  let D := badSingletonVertices H W v r
  let U := W \ D
  let B := outsideFamily H W
  let O := ordinaryOutsideFamily H W v r
  let B₁ := outsideOneBadSingleton H W v r
  let B₂ := outsideSeveralBadWithOrdinary H W v r
  let Bᵣ := outsideFamily H D
  let M := missingStarFacets H W v r
  let qU := (missingStarFacets H U v r).card
  let qD := (M.filter fun S => (S ∩ D).Nonempty).card
  let J := D.card.choose 2 * (W.card - 2).choose (r - 3)
  let Δ := W.card.choose (r - 2) - (W.card - r - 1).choose (r - 2)
  let dirty := (actualDirtyOutsideEdges H W v r).card
  let bᵣ := Bᵣ.card
  let R := r * (r - 1)
  have hLayer := outside_edge_layer_card_bound H W v r
  change B.card ≤ O.card + B₁.card + B₂.card + Bᵣ.card at hLayer
  have hOrd := ordinary_outside_incidence_with_deletion H W v r
    hAdm hUniform (by omega : 3 ≤ r) hvW
  change r * O.card ≤ U.card + qU + r * dirty at hOrd
  have hOne := outside_one_bad_singleton_budget_numerator H W v r
    hAdm hUniform (by omega : 3 ≤ r) hvW
  change (r - 1) * B₁.card ≤ 2 * qD + 2 * J + D.card * Δ at hOne
  have hMulti := outside_several_bad_with_ordinary_card_le_j H W v r
    hAdm hUniform (by omega : 3 ≤ r) hvW
  change B₂.card ≤ J at hMulti
  have hOrdScaled : R * O.card ≤
      (r - 1) * (U.card + qU + r * dirty) := by
    calc
      R * O.card = (r - 1) * (r * O.card) := by
        dsimp [R]
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ (r - 1) * (U.card + qU + r * dirty) :=
        Nat.mul_le_mul_left (r - 1) hOrd
  have hOneScaled : R * B₁.card ≤ r * (2 * qD + 2 * J + D.card * Δ) := by
    calc
      R * B₁.card = r * ((r - 1) * B₁.card) := by
        dsimp [R]
        simp [Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ r * (2 * qD + 2 * J + D.card * Δ) :=
        Nat.mul_le_mul_left r hOne
  have hMultiScaled : R * B₂.card ≤ R * J :=
    Nat.mul_le_mul_left R hMulti
  have hExpand : R * (O.card + B₁.card + B₂.card + Bᵣ.card) =
      R * O.card + R * B₁.card + R * B₂.card + R * Bᵣ.card := by
    simp [Nat.mul_add, Nat.add_assoc]
  have hSum := Nat.add_le_add
    (Nat.add_le_add hOrdScaled hOneScaled) hMultiScaled
  have hSum' := Nat.add_le_add_right hSum (R * Bᵣ.card)
  change R * B.card ≤
    (r - 1) * (U.card + qU + r * dirty) +
      r * (2 * qD + 2 * J + D.card * Δ) + R * J + R * Bᵣ.card
  calc
    R * B.card ≤ R * (O.card + B₁.card + B₂.card + Bᵣ.card) :=
      Nat.mul_le_mul_left R hLayer
    _ = R * O.card + R * B₁.card + R * B₂.card + R * Bᵣ.card := hExpand
    _ ≤ (r - 1) * (U.card + qU + r * dirty) +
        r * (2 * qD + 2 * J + D.card * Δ) + R * J + R * Bᵣ.card := by
      exact hSum'

/-- The missing star facets split exactly according to whether they meet
the bad singleton set. The nonmeeting part is precisely the missing facet
family induced on `U`. -/
theorem missing_star_facets_card_split_bad_singletons
    (H : Family α) (W : Edge α) (v : α) (r : ℕ) :
    let D := badSingletonVertices H W v r
    let U := W \ D
    let M := missingStarFacets H W v r
    M.card = (missingStarFacets H U v r).card +
      (M.filter fun S => (S ∩ D).Nonempty).card := by
  classical
  let D := badSingletonVertices H W v r
  let U := W \ D
  let M := missingStarFacets H W v r
  let MU := missingStarFacets H U v r
  let MD := M.filter fun S => (S ∩ D).Nonempty
  have hUW : U ⊆ W := Finset.sdiff_subset
  have hParts : M = MU ∪ MD := by
    ext S
    constructor
    · intro hS
      have ⟨hSCard, hMissing⟩ := Finset.mem_filter.mp hS
      obtain ⟨hSW, hScard⟩ := Finset.mem_powersetCard.mp hSCard
      by_cases hMeet : (S ∩ D).Nonempty
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨hS, hMeet⟩))
      · have hSU : S ⊆ U := by
          intro x hxS
          refine Finset.mem_sdiff.mpr ⟨hSW hxS, ?_⟩
          intro hxD
          exact hMeet ⟨x, Finset.mem_inter.mpr ⟨hxS, hxD⟩⟩
        exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr
            ⟨Finset.mem_powersetCard.mpr ⟨hSU, hScard⟩, hMissing⟩))
    · intro hS
      rcases Finset.mem_union.mp hS with hSU | hSD
      · have ⟨hSUCard, hMissing⟩ := Finset.mem_filter.mp hSU
        obtain ⟨hSU, hScard⟩ := Finset.mem_powersetCard.mp hSUCard
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_powersetCard.mpr ⟨hSU.trans hUW, hScard⟩, hMissing⟩
      · exact (Finset.mem_filter.mp hSD).1
  have hDisj : Disjoint MU MD := by
    apply Finset.disjoint_left.mpr
    intro S hSU hSD
    have hSsubU := (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hSU).1).1
    have hMeet := (Finset.mem_filter.mp hSD).2
    obtain ⟨x, hx⟩ := hMeet
    exact (Finset.mem_sdiff.mp (hSsubU (Finset.mem_inter.mp hx).1)).2
      (Finset.mem_inter.mp hx).2
  change M.card = MU.card + MD.card
  rw [hParts, Finset.card_union_of_disjoint hDisj]

/-- The finite predecessor with the manuscript's principal terms exposed.
After division by `r*(r-1)` its main terms are exactly
`2*q/(r-1) + w/r`, as in (IV.2.10); all finite error terms remain explicit. -/
theorem outside_finite_contraction_main_terms
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 5 ≤ r) (hvW : v ∉ W) :
    let D := badSingletonVertices H W v r
    let M := missingStarFacets H W v r
    let q := M.card
    let J := D.card.choose 2 * (W.card - 2).choose (r - 3)
    let Δ := W.card.choose (r - 2) - (W.card - r - 1).choose (r - 2)
    let dirty := (actualDirtyOutsideEdges H W v r).card
    let bᵣ := (outsideFamily H D).card
    r * (r - 1) * (outsideFamily H W).card ≤
      2 * r * q + (r - 1) * W.card +
        r * (r - 1) * dirty +
        r * (2 * J + D.card * Δ) +
        r * (r - 1) * J + r * (r - 1) * bᵣ := by
  classical
  let D := badSingletonVertices H W v r
  let U := W \ D
  let M := missingStarFacets H W v r
  let qU := (missingStarFacets H U v r).card
  let qD := (M.filter fun S => (S ∩ D).Nonempty).card
  let q := M.card
  let J := D.card.choose 2 * (W.card - 2).choose (r - 3)
  let Δ := W.card.choose (r - 2) - (W.card - r - 1).choose (r - 2)
  let dirty := (actualDirtyOutsideEdges H W v r).card
  let bᵣ := (outsideFamily H D).card
  let R := r * (r - 1)
  have hQsplit := missing_star_facets_card_split_bad_singletons H W v r
  change q = qU + qD at hQsplit
  have hPrev := outside_finite_contraction_predecessor H W v r
    hAdm hUniform hr hvW
  change R * (outsideFamily H W).card ≤
    (r - 1) * (U.card + qU + r * dirty) +
      r * (2 * qD + 2 * J + D.card * Δ) +
      R * J + R * bᵣ at hPrev
  change R * (outsideFamily H W).card ≤
    2 * r * q + (r - 1) * W.card + R * dirty +
      r * (2 * J + D.card * Δ) + R * J + R * bᵣ
  have hOrdBound : (r - 1) * U.card ≤ (r - 1) * W.card :=
    Nat.mul_le_mul_left (r - 1) (Finset.card_le_card Finset.sdiff_subset)
  have hQUBound : (r - 1) * qU ≤ 2 * r * qU := by
    exact Nat.mul_le_mul_right qU (by omega : r - 1 ≤ 2 * r)
  have hQDBound : (r - 1) * qU + 2 * r * qD ≤ 2 * r * q := by
    calc
      (r - 1) * qU + 2 * r * qD ≤ 2 * r * qU + 2 * r * qD :=
        Nat.add_le_add_right hQUBound _
      _ = 2 * r * (qU + qD) := by rw [Nat.mul_add]
      _ = 2 * r * q := by rw [hQsplit]
  have hDirtyEq : (r - 1) * (r * dirty) = R * dirty := by
    dsimp [R]
    calc
      (r - 1) * (r * dirty) = ((r - 1) * r) * dirty :=
        (Nat.mul_assoc (r - 1) r dirty).symm
      _ = (r * (r - 1)) * dirty := by rw [Nat.mul_comm (r - 1) r]
      _ = r * (r - 1) * dirty := rfl
  have hQDEq : r * (2 * qD) = 2 * r * qD := by
    simp [Nat.mul_assoc, Nat.mul_comm]
  have hPrevExpand :
      (r - 1) * (U.card + qU + r * dirty) +
        r * (2 * qD + 2 * J + D.card * Δ) + R * J + R * bᵣ =
      ((r - 1) * U.card + (r - 1) * qU + 2 * r * qD) +
        R * dirty + r * (2 * J + D.card * Δ) + R * J + R * bᵣ := by
    simp only [Nat.mul_add]
    rw [hQDEq, hDirtyEq]
    omega
  calc
    R * (outsideFamily H W).card ≤
        (r - 1) * (U.card + qU + r * dirty) +
          r * (2 * qD + 2 * J + D.card * Δ) + R * J + R * bᵣ := hPrev
    _ = ((r - 1) * U.card + (r - 1) * qU + 2 * r * qD) +
          R * dirty + r * (2 * J + D.card * Δ) + R * J + R * bᵣ := hPrevExpand
    _ ≤ 2 * r * q + (r - 1) * W.card + R * dirty +
          r * (2 * J + D.card * Δ) + R * J + R * bᵣ := by
      have hBase : (r - 1) * U.card +
          ((r - 1) * qU + 2 * r * qD) ≤
          (r - 1) * W.card + 2 * r * q :=
        Nat.add_le_add hOrdBound hQDBound
      omega

/-- Actual near-star exactness from the finite contraction chain and an
explicit absorption hypothesis. The error is exactly the sum of the dirty
deletion, exceptional-pair, `dΔ`, and all-exceptional terms from
`outside_finite_contraction_main_terms`; no abstract contraction premise is
used. -/
theorem near_star_exact_of_explicit_outside_error
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) (hr : 5 ≤ r)
    (hw : r * (r - 3) * (2 * r - 1) ≤ W.card)
    (hqb : (missingStarFacets H W v r).card ≤
      (outsideFamily H W).card)
    (hError : 2 * (
      r * (r - 1) * (actualDirtyOutsideEdges H W v r).card +
      r * (2 * (badSingletonVertices H W v r).card.choose 2 *
        (W.card - 2).choose (r - 3) +
        (badSingletonVertices H W v r).card *
          (W.card.choose (r - 2) - (W.card - r - 1).choose (r - 2))) +
      r * (r - 1) *
        (badSingletonVertices H W v r).card.choose 2 *
          (W.card - 2).choose (r - 3) +
      r * (r - 1) *
        (outsideFamily H (badSingletonVertices H W v r)).card) ≤
      r * (r - 3) * (missingStarFacets H W v r).card) :
    H.card ≤ W.card.choose (r - 1) + W.card / r := by
  let D := badSingletonVertices H W v r
  let q := (missingStarFacets H W v r).card
  let J := D.card.choose 2 * (W.card - 2).choose (r - 3)
  let Δ := W.card.choose (r - 2) - (W.card - r - 1).choose (r - 2)
  let dirty := (actualDirtyOutsideEdges H W v r).card
  let bᵣ := (outsideFamily H D).card
  let err := r * (r - 1) * dirty + r * (2 * J + D.card * Δ) +
    r * (r - 1) * J + r * (r - 1) * bᵣ
  have hFinite := outside_finite_contraction_main_terms H W v r
    hAdm hUniform hr hvW
  have hFinite' : r * (r - 1) * (outsideFamily H W).card ≤
      2 * r * q + (r - 1) * W.card + err := by
    simpa [err, Nat.add_assoc] using hFinite
  have hError' : 2 * err ≤ r * (r - 3) * q := by
    simpa [err, D, J, Δ, dirty, bᵣ, q,
      Nat.add_assoc, Nat.mul_assoc] using hError
  have hContract := scaled_contraction_of_error_bound
    r W.card q (outsideFamily H W).card err (by omega : 3 ≤ r)
    hFinite' hError'
  exact near_star_exact_of_scaled_contraction hAdm hUniform hSupport
    hvW hr hw hqb hContract

end JSP523
