import JSP523.Rank5.StarLayerCollisionGlobal
import Mathlib.Tactic

/-!
# Polynomial scales for the finite star-shadow deletion bound

These are the two finite numerical specializations of the deletion estimate
in Lemma IV.3.2: the ambient-codegree scale and the regularized scale.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

private def starCollisionConstant (r : ℕ) : ℕ :=
  (r - 1) * (r - 1) + (r - 2)

private theorem pow_rminus2_le_pow_rminus1
    (n r : ℕ) (hr : 3 ≤ r) (hn : 1 ≤ n) :
    n ^ (r - 2) ≤ n ^ (r - 1) := by
  have he : r - 1 = (r - 2) + 1 := by omega
  rw [he, pow_succ]
  calc
    n ^ (r - 2) = n ^ (r - 2) * 1 := by simp
    _ ≤ n ^ (r - 2) * n := Nat.mul_le_mul_left _ hn

private theorem pow_rminus3_le_pow_rminus2
    (n r : ℕ) (hr : 4 ≤ r) (hn : 1 ≤ n) :
    n ^ (r - 3) ≤ n ^ (r - 2) := by
  have he : r - 2 = (r - 3) + 1 := by omega
  rw [he, pow_succ]
  calc
    n ^ (r - 3) = n ^ (r - 3) * 1 := by simp
    _ ≤ n ^ (r - 3) * n := Nat.mul_le_mul_left _ hn

private theorem pair_card_le_square (h : ℕ) :
    h * (h - 1) ≤ h ^ 2 := by
  calc
    h * (h - 1) ≤ h * h := Nat.mul_le_mul_left h (Nat.sub_le h 1)
    _ = h ^ 2 := by simp [pow_two]

private theorem pow_coarse_product (n r : ℕ) (hr : 4 ≤ r) :
    n ^ (r - 2) * n ^ (r - 1) = n ^ (2 * r - 3) := by
  rw [← pow_add]
  congr 1
  omega

private theorem pow_regularized_product (n r : ℕ) (hr : 4 ≤ r) :
    n ^ (r - 2) * n ^ (r - 2) = n ^ (2 * r - 4) := by
  rw [← pow_add]
  congr 1
  omega

private theorem pow_square_rminus3 (n r : ℕ) (hr : 4 ≤ r) :
    n ^ 2 * n ^ (r - 3) = n ^ (r - 1) := by
  rw [← pow_add]
  congr 1
  omega

private theorem pow_square_rminus4 (n r : ℕ) (hr : 4 ≤ r) :
    n ^ 2 * n ^ (r - 4) = n ^ (r - 2) := by
  rw [← pow_add]
  congr 1
  omega

private theorem choose_card_le_power
    (u n t : ℕ) (hu : u ≤ n) :
    u.choose t ≤ n ^ t :=
  (Nat.choose_le_pow u t).trans (Nat.pow_le_pow_left hu t)

/-- The collision coefficient under ambient codegree bounds
 D₂ ≤ n^(r-2) and D₃ ≤ n^(r-3) is at most C_r n^(r-1). -/
private theorem coarse_collision_bracket
    (n r D₂ D₃ u : ℕ) (hr : 4 ≤ r) (hn : 1 ≤ n) (hu : u ≤ n)
    (hD₂ : D₂ ≤ n ^ (r - 2)) (hD₃ : D₃ ≤ n ^ (r - 3)) :
    (r - 1) * (r - 1) * D₂ + u * (u - 1) * (r - 2) * D₃ ≤
      starCollisionConstant r * n ^ (r - 1) := by
  have hpow := pow_rminus2_le_pow_rminus1 n r (by omega) hn
  have hpair : u * (u - 1) ≤ n ^ 2 := by
    have h₁ : u * (u - 1) ≤ n * (u - 1) :=
      Nat.mul_le_mul_right (u - 1) hu
    have h₂ : n * (u - 1) ≤ n * n :=
      Nat.mul_le_mul_left n (Nat.sub_le u 1 |>.trans hu)
    calc
      u * (u - 1) ≤ n * (u - 1) := h₁
      _ ≤ n * n := h₂
      _ = n ^ 2 := by simp [pow_two]
  have hD₂term :
      (r - 1) * (r - 1) * D₂ ≤
        ((r - 1) * (r - 1)) * n ^ (r - 1) := by
    calc
      (r - 1) * (r - 1) * D₂ ≤
          ((r - 1) * (r - 1)) * n ^ (r - 2) :=
        Nat.mul_le_mul_left ((r - 1) * (r - 1)) hD₂
      _ ≤ ((r - 1) * (r - 1)) * n ^ (r - 1) :=
        Nat.mul_le_mul_left _ hpow
  have hD₃term :
      u * (u - 1) * (r - 2) * D₃ ≤ (r - 2) * n ^ (r - 1) := by
    have hprod := Nat.mul_le_mul hpair hD₃
    calc
      u * (u - 1) * (r - 2) * D₃ =
          (r - 2) * (u * (u - 1) * D₃) := by ac_rfl
      _ ≤ (r - 2) * (n ^ 2 * n ^ (r - 3)) :=
        Nat.mul_le_mul_left (r - 2) hprod
      _ = (r - 2) * n ^ (r - 1) := by
        rw [pow_square_rminus3 n r hr]
  calc
    _ ≤ ((r - 1) * (r - 1)) * n ^ (r - 1) +
        (r - 2) * n ^ (r - 1) := Nat.add_le_add hD₂term hD₃term
    _ = starCollisionConstant r * n ^ (r - 1) := by
      dsimp [starCollisionConstant]
      rw [← Nat.add_mul]

/-- At the ambient codegree scale, the actual number of deleted colored
members is bounded in square by C_r h² n^(2r-3), the finite form of the
manuscript's O_r(h n^(r-3/2)) estimate. -/
theorem actual_star_layer_deletion_coarse_scale
    [Inhabited α] {H : Family α} {U Centers : Edge α} {r n D₂ D₃ : ℕ}
    (hH : Admissible H)
    (hCenters : ∀ z ∈ Centers, z ∉ U)
    (hr : 4 ≤ r) (hn : 1 ≤ n) (hu : U.card ≤ n)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₂)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₂scale : D₂ ≤ n ^ (r - 2))
    (hD₃scale : D₃ ≤ n ^ (r - 3)) :
    ∃ owner : Edge α → α,
      ((actualStarLayerObjects H U Centers r).filter fun zT : α × Edge α =>
        ∃ P ∈ actualStarLayerFacets U zT.2 r,
          P ∈ U.powersetCard (r - 2) ∧ owner P ≠ zT.1).card ^ 2 ≤
        starCollisionConstant r * Centers.card ^ 2 * n ^ (2 * r - 3) := by
  obtain ⟨owner, hDeletion⟩ :=
    actual_star_layer_ownership_deletion_card_sq_le_exists_max
      hH hCenters hr hD₂ hD₃
  refine ⟨owner, ?_⟩
  have hP : (U.powersetCard (r - 2)).card ≤ n ^ (r - 2) := by
    rw [Finset.card_powersetCard]
    exact choose_card_le_power U.card n (r - 2) hu
  have hPair := pair_card_le_square Centers.card
  have hBracket := coarse_collision_bracket n r D₂ D₃ U.card hr hn hu
    hD₂scale hD₃scale
  calc
    _ ≤ (U.powersetCard (r - 2)).card *
        (Centers.card * (Centers.card - 1) *
          (starCollisionConstant r * n ^ (r - 1))) := by
        have hInner := Nat.mul_le_mul_left
          (Centers.card * (Centers.card - 1)) hBracket
        exact hDeletion.trans
          (Nat.mul_le_mul_left (U.powersetCard (r - 2)).card hInner)
    _ ≤ n ^ (r - 2) *
        (Centers.card ^ 2 * (starCollisionConstant r * n ^ (r - 1))) :=
      Nat.mul_le_mul hP (Nat.mul_le_mul_right _ hPair)
    _ = starCollisionConstant r * Centers.card ^ 2 * n ^ (2 * r - 3) := by
      calc
        n ^ (r - 2) * (Centers.card ^ 2 * (starCollisionConstant r * n ^ (r - 1))) =
            starCollisionConstant r * Centers.card ^ 2 *
              (n ^ (r - 2) * n ^ (r - 1)) := by ac_rfl
        _ = starCollisionConstant r * Centers.card ^ 2 * n ^ (2 * r - 3) := by
            rw [pow_coarse_product n r hr]

/-- Under the regularized caps D_j ≤ R n^(r-j-1), the actual deletion
cost is bounded in square by C_r h² R n^(2r-4), the finite form of
O_r(h sqrt(R) n^(r-2)). -/
theorem actual_star_layer_deletion_regularized_scale
    [Inhabited α] {H : Family α} {U Centers : Edge α}
    {r n R D₂ D₃ : ℕ}
    (hH : Admissible H)
    (hCenters : ∀ z ∈ Centers, z ∉ U)
    (hr : 4 ≤ r) (hn : 1 ≤ n) (hu : U.card ≤ n)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₂)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₂scale : D₂ ≤ R * n ^ (r - 3))
    (hD₃scale : D₃ ≤ R * n ^ (r - 4)) :
    ∃ owner : Edge α → α,
      ((actualStarLayerObjects H U Centers r).filter fun zT : α × Edge α =>
        ∃ P ∈ actualStarLayerFacets U zT.2 r,
          P ∈ U.powersetCard (r - 2) ∧ owner P ≠ zT.1).card ^ 2 ≤
        starCollisionConstant r * Centers.card ^ 2 * R *
          n ^ (2 * r - 4) := by
  obtain ⟨owner, hDeletion⟩ :=
    actual_star_layer_ownership_deletion_card_sq_le_exists_max
      hH hCenters hr hD₂ hD₃
  refine ⟨owner, ?_⟩
  have hP : (U.powersetCard (r - 2)).card ≤ n ^ (r - 2) := by
    rw [Finset.card_powersetCard]
    exact choose_card_le_power U.card n (r - 2) hu
  have hpow := pow_rminus3_le_pow_rminus2 n r hr hn
  have hpair : U.card * (U.card - 1) ≤ n ^ 2 := by
    have h₁ : U.card * (U.card - 1) ≤ n * (U.card - 1) :=
      Nat.mul_le_mul_right (U.card - 1) hu
    have h₂ : n * (U.card - 1) ≤ n * n :=
      Nat.mul_le_mul_left n (Nat.sub_le U.card 1 |>.trans hu)
    calc
      U.card * (U.card - 1) ≤ n * (U.card - 1) := h₁
      _ ≤ n * n := h₂
      _ = n ^ 2 := by simp [pow_two]
  have hD₂term :
      (r - 1) * (r - 1) * D₂ ≤
        ((r - 1) * (r - 1)) * (R * n ^ (r - 2)) := by
    calc
      (r - 1) * (r - 1) * D₂ ≤
          ((r - 1) * (r - 1)) * (R * n ^ (r - 3)) :=
        Nat.mul_le_mul_left ((r - 1) * (r - 1)) hD₂scale
      _ ≤ ((r - 1) * (r - 1)) * (R * n ^ (r - 2)) := by
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul_left R hpow
  have hD₃prod := Nat.mul_le_mul hpair hD₃scale
  have hD₃term :
      U.card * (U.card - 1) * (r - 2) * D₃ ≤
        (r - 2) * (R * n ^ (r - 2)) := by
    calc
      U.card * (U.card - 1) * (r - 2) * D₃ =
          (r - 2) * (U.card * (U.card - 1) * D₃) := by ac_rfl
      _ ≤ (r - 2) * (n ^ 2 * (R * n ^ (r - 4))) :=
        Nat.mul_le_mul_left (r - 2) hD₃prod
      _ = (r - 2) * (R * n ^ (r - 2)) := by
        congr 1
        calc
          n ^ 2 * (R * n ^ (r - 4)) = R * (n ^ 2 * n ^ (r - 4)) := by ac_rfl
          _ = R * n ^ (r - 2) := by rw [pow_square_rminus4 n r hr]
  have hBracket :
      (r - 1) * (r - 1) * D₂ +
          U.card * (U.card - 1) * (r - 2) * D₃ ≤
        starCollisionConstant r * (R * n ^ (r - 2)) := by
    calc
      _ ≤ ((r - 1) * (r - 1)) * (R * n ^ (r - 2)) +
          (r - 2) * (R * n ^ (r - 2)) := Nat.add_le_add hD₂term hD₃term
      _ = starCollisionConstant r * (R * n ^ (r - 2)) := by
        dsimp [starCollisionConstant]
        rw [← Nat.add_mul]
  have hPair := pair_card_le_square Centers.card
  calc
    _ ≤ (U.powersetCard (r - 2)).card *
        (Centers.card * (Centers.card - 1) *
          (starCollisionConstant r * (R * n ^ (r - 2)))) := by
        have hInner := Nat.mul_le_mul_left
          (Centers.card * (Centers.card - 1)) hBracket
        exact hDeletion.trans
          (Nat.mul_le_mul_left (U.powersetCard (r - 2)).card hInner)
    _ ≤ n ^ (r - 2) *
        (Centers.card ^ 2 * (starCollisionConstant r *
          (R * n ^ (r - 2)))) :=
      Nat.mul_le_mul hP (Nat.mul_le_mul_right _ hPair)
    _ = starCollisionConstant r * Centers.card ^ 2 * R *
          n ^ (2 * r - 4) := by
      calc
        n ^ (r - 2) * (Centers.card ^ 2 *
            (starCollisionConstant r * (R * n ^ (r - 2)))) =
            starCollisionConstant r * Centers.card ^ 2 * R *
              (n ^ (r - 2) * n ^ (r - 2)) := by ac_rfl
        _ = starCollisionConstant r * Centers.card ^ 2 * R *
              n ^ (2 * r - 4) := by rw [pow_regularized_product n r hr]

end JSP523.Rank5
