import JSP523.Rank5.StarLayerAllocation
import JSP523.Rank5.RegularizationAssembly

/-!
# An actual removed-layer bound from codegrees and scalar budgets

This supplies a concrete replacement for the previously external `hLayer`
premise.  The inputs are maximum vertex/pair/triple codegrees, a cover-size
bound, an integer link radius, and a scalar collision budget.
-/

namespace JSP523.Rank5

open Finset
open scoped BigOperators
open JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- Star-link members inject into actual edges through the center. -/
theorem actual_star_link_card_le_vertex_degree
    (H : Family α) (U : Edge α) (z : α) (r : ℕ) (hzU : z ∉ U) :
    (actualStarLink H U z r).card ≤ (H.filter (fun E => z ∈ E)).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun T => insert z T)
  · intro T hT
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hT).2, Finset.mem_insert_self _ _⟩
  · intro T hT S hS hEq
    have hzT : z ∉ T := by
      intro hz
      exact hzU ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).1 hz)
    have hzS : z ∉ S := by
      intro hz
      exact hzU ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).1 hz)
    have h := congrArg (fun E : Edge α => E.erase z) hEq
    simpa only [Finset.erase_insert hzT, Finset.erase_insert hzS] using h

/-- Every exactly-once edge is represented by an actual colored star
member on the complement of the removed set. -/
theorem one_hit_edges_le_actual_star_objects
    (H : Family α) (V X : Edge α) (r : ℕ)
    (hUniform : Uniform r H) (hGround : ∀ E ∈ H, E ⊆ V) :
    (oneHitEdges H X).card ≤ (actualStarLayerObjects H (V \ X) X r).card := by
  classical
  let O := actualStarLayerObjects H (V \ X) X r
  let join : α × Edge α → Edge α := fun zT => insert zT.1 zT.2
  have hSub : oneHitEdges H X ⊆ O.image join := by
    intro E hE
    obtain ⟨hEH, hOne⟩ := Finset.mem_filter.mp hE
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hOne
    have hzEX : z ∈ E ∩ X := by rw [hz]; simp
    have hzE : z ∈ E := (Finset.mem_inter.mp hzEX).1
    have hzX : z ∈ X := (Finset.mem_inter.mp hzEX).2
    have hTail : E.erase z ⊆ V \ X := by
      intro x hx
      obtain ⟨hxz, hxE⟩ := Finset.mem_erase.mp hx
      refine Finset.mem_sdiff.mpr ⟨hGround E hEH hxE, ?_⟩
      intro hxX
      have hxEX : x ∈ E ∩ X := Finset.mem_inter.mpr ⟨hxE, hxX⟩
      rw [hz] at hxEX
      exact hxz (Finset.mem_singleton.mp hxEX)
    have hTailCard : (E.erase z).card = r - 1 := by
      have := Finset.card_erase_add_one hzE
      have := hUniform hEH
      omega
    have hO : (z, E.erase z) ∈ O := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr
        ⟨hzX, Finset.mem_powersetCard.mpr ⟨hTail, hTailCard⟩⟩, ?_⟩
      simpa only [Finset.insert_erase hzE] using hEH
    exact Finset.mem_image.mpr ⟨(z, E.erase z), hO, Finset.insert_erase hzE⟩
  exact (Finset.card_le_card hSub).trans Finset.card_image_le

/-- Monotonicity of the explicit squared collision budget. -/
theorem star_collision_budget_mono
    (u n h c r D₂ D₃ : ℕ) (hu : u ≤ n) (hc : c ≤ h) :
    u.choose (r - 2) * (c * (c - 1) *
      ((r - 1) * (r - 1) * D₂ + u * (u - 1) * (r - 2) * D₃)) ≤
    n.choose (r - 2) * (h * (h - 1) *
      ((r - 1) * (r - 1) * D₂ + n * (n - 1) * (r - 2) * D₃)) := by
  have hPairU : u * (u - 1) ≤ n * (n - 1) :=
    Nat.mul_le_mul hu (by omega)
  have hPairC : c * (c - 1) ≤ h * (h - 1) :=
    Nat.mul_le_mul hc (by omega)
  apply Nat.mul_le_mul (Nat.choose_le_choose (r - 2) hu)
  apply Nat.mul_le_mul hPairC
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right D₃ (Nat.mul_le_mul_right (r - 2) hPairU)) _

/-- The entire layer touching `X` is bounded from actual codegrees.
There is no hypothesis about the layer cardinality itself. -/
theorem removed_layer_bound_from_codegrees_on_ground
    {n : ℕ} [Inhabited (Fin n)]
    (H : Family (Fin n)) (V X : Edge (Fin n))
    (r h D₁ D₂ D₃ L b : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hGround : ∀ E ∈ H, E ⊆ V) (hr : 4 ≤ r) (hX : X.card ≤ h)
    (hD₁ : ∀ z : Fin n, (H.filter (fun E => z ∈ E)).card ≤ D₁)
    (hD₂ : ∀ S : Edge (Fin n), S.card = 2 →
      (H.filter (fun E => S ⊆ E)).card ≤ D₂)
    (hD₃ : ∀ S : Edge (Fin n), S.card = 3 →
      (H.filter (fun E => S ⊆ E)).card ≤ D₃)
    (hRadius : (r - 1).factorial * D₁ ≤ L ^ (r - 1))
    (hCollision : n.choose (r - 2) * (h * (h - 1) *
      ((r - 1) * (r - 1) * D₂ + n * (n - 1) * (r - 2) * D₃)) ≤ b ^ 2) :
    H.card - (H.filter (fun E => Disjoint E X)).card ≤
      b + ((L + (r - 1)) * (V \ X).card.choose (r - 2)) / (r - 1) +
        h.choose 2 * D₂ := by
  classical
  let U := V \ X
  have hCenters : ∀ z ∈ X, z ∉ U := by
    intro z hz hzU
    exact (Finset.mem_sdiff.mp hzU).2 hz
  have hSize : ∀ z ∈ X,
      (r - 1).factorial * (actualStarLink H U z r).card ≤ L ^ (r - 1) := by
    intro z hz
    exact (Nat.mul_le_mul_left _ ((actual_star_link_card_le_vertex_degree
      H U z r (hCenters z hz)).trans (hD₁ z))).trans hRadius
  obtain ⟨owner, hLossSq, _, hOriginal⟩ :=
    actual_star_layer_radius_bound_on_ground hAdm hCenters hr hD₂ hD₃ hSize
  have hu : U.card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ U)
  have hBudget := star_collision_budget_mono U.card n h X.card r D₂ D₃ hu hX
  rw [Finset.card_powersetCard] at hLossSq
  have hLossSq' : (lostStarObjects H U X r owner).card ^ 2 ≤ b ^ 2 :=
    hLossSq.trans (hBudget.trans hCollision)
  have hLoss : (lostStarObjects H U X r owner).card ≤ b := by nlinarith
  have hPartition := star_layer_ownership_card_partition H U X r owner
  let kept := ∑ z ∈ X, (ownedStarLink H U r owner z).card
  have hKeptMul : (r - 1) * kept ≤
      (L + (r - 1)) * U.card.choose (r - 2) := by
    dsimp [kept]
    rw [← hPartition, Nat.mul_add] at hOriginal
    omega
  have hKept : kept ≤
      ((L + (r - 1)) * U.card.choose (r - 2)) / (r - 1) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < r - 1)).2
    simpa only [Nat.mul_comm] using hKeptMul
  have hObjects : (actualStarLayerObjects H U X r).card ≤
      b + ((L + (r - 1)) * U.card.choose (r - 2)) / (r - 1) := by
    change (lostStarObjects H U X r owner).card + kept = _ at hPartition
    omega
  have hOne := (one_hit_edges_le_actual_star_objects H V X r hUniform hGround).trans
    hObjects
  have hLayer := avoid_x_layer_le_one_hit_plus_pair_budget H X D₂
    (by intro Q hQ; exact hD₂ Q (Finset.mem_powersetCard.mp hQ).2)
  have hPairs : X.card.choose 2 * D₂ ≤ h.choose 2 * D₂ :=
    Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 hX)
  exact hLayer.trans (Nat.add_le_add hOne hPairs)

/-- The ambient-size version used by the finite regularization round. -/
theorem removed_layer_bound_from_codegrees
    {n : ℕ} [Inhabited (Fin n)]
    (H : Family (Fin n)) (V X : Edge (Fin n))
    (r h D₁ D₂ D₃ L b : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hGround : ∀ E ∈ H, E ⊆ V) (hr : 4 ≤ r) (hX : X.card ≤ h)
    (hD₁ : ∀ z : Fin n, (H.filter (fun E => z ∈ E)).card ≤ D₁)
    (hD₂ : ∀ S : Edge (Fin n), S.card = 2 →
      (H.filter (fun E => S ⊆ E)).card ≤ D₂)
    (hD₃ : ∀ S : Edge (Fin n), S.card = 3 →
      (H.filter (fun E => S ⊆ E)).card ≤ D₃)
    (hRadius : (r - 1).factorial * D₁ ≤ L ^ (r - 1))
    (hCollision : n.choose (r - 2) * (h * (h - 1) *
      ((r - 1) * (r - 1) * D₂ + n * (n - 1) * (r - 2) * D₃)) ≤ b ^ 2) :
    H.card - (H.filter (fun E => Disjoint E X)).card ≤
      b + ((L + (r - 1)) * n.choose (r - 2)) / (r - 1) +
        h.choose 2 * D₂ := by
  have hGroundBound := removed_layer_bound_from_codegrees_on_ground H V X
    r h D₁ D₂ D₃ L b hAdm hUniform hGround hr hX hD₁ hD₂ hD₃
    hRadius hCollision
  have hCard : (V \ X).card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (V \ X))
  have hChoose : (V \ X).card.choose (r - 2) ≤ n.choose (r - 2) :=
    Nat.choose_le_choose (r - 2) hCard
  have hMul := Nat.mul_le_mul_left (L + (r - 1)) hChoose
  have hDiv : ((L + (r - 1)) * (V \ X).card.choose (r - 2)) / (r - 1) ≤
      ((L + (r - 1)) * n.choose (r - 2)) / (r - 1) :=
    Nat.div_le_div_right hMul
  exact hGroundBound.trans (by omega)

end JSP523.Rank5
