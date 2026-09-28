import JSP523.Rank5.StarLayerLoss
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Finite far-star tail from an actual vertex-degree bound

Uniformity bounds the pair and triple codegrees needed by the star-layer
theorem. The maximum vertex degree bounds the link radius. Integer roots
choose the radius and collision budget, so the conclusion has no auxiliary
geometric hypotheses.
-/

namespace JSP523.Rank5

open Finset

/-- A finite radius for links whose centers have degree at most `M`. -/
def farStarRadius (r M : ℕ) : ℕ :=
  Nat.nthRoot (r - 1) ((r - 1).factorial * M) + 1

/-- The collision expression using the exact ambient pair and triple
codegree bounds. -/
def farStarCollision (n r h : ℕ) : ℕ :=
  n.choose (r - 2) * (h * (h - 1) *
    ((r - 1) * (r - 1) * (n - 2).choose (r - 2) +
      n * (n - 1) * (r - 2) * (n - 3).choose (r - 3)))

/-- A concrete integer budget for the ownership deletions. -/
def farStarDeletion (n r h : ℕ) : ℕ :=
  Nat.nthRoot 2 (farStarCollision n r h) + 1

/-- Rank-only coefficient in the collision estimate. -/
def farStarCollisionConstant (r : ℕ) : ℕ :=
  (r - 1) * (r - 1) + (r - 2)

/-- The collision expression has the manuscript's `h² n^(2r-3)` scale.
This bound is independent of the family and keeps the rank coefficient
visible for subsequent finite-rate or asymptotic arguments. -/
theorem far_star_collision_power_bound
    (n r h : ℕ) (hr : 4 ≤ r) (hn : 1 ≤ n) :
    farStarCollision n r h ≤
      farStarCollisionConstant r * h ^ 2 * n ^ (2 * r - 3) := by
  have hChooseOuter : n.choose (r - 2) ≤ n ^ (r - 2) := Nat.choose_le_pow n _
  have hChoosePair : (n - 2).choose (r - 2) ≤ n ^ (r - 2) :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
  have hChooseTriple : (n - 3).choose (r - 3) ≤ n ^ (r - 3) :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
  have hPowStep : n ^ (r - 2) ≤ n ^ (r - 1) := by
    have he : r - 2 + 1 = r - 1 := by omega
    rw [← he, pow_succ]
    calc
      n ^ (r - 2) = n ^ (r - 2) * 1 := by simp
      _ ≤ n ^ (r - 2) * n := Nat.mul_le_mul_left _ hn
  have hTripleTerm :
      n * (n - 1) * (r - 2) * ((n - 3).choose (r - 3)) ≤
        (r - 2) * n ^ (r - 1) := by
    calc
      n * (n - 1) * (r - 2) * ((n - 3).choose (r - 3)) ≤
          n * n * (r - 2) * n ^ (r - 3) := by
            gcongr
            exact Nat.sub_le n 1
      _ = (r - 2) * n ^ (r - 1) := by
        have he : 2 + (r - 3) = r - 1 := by omega
        rw [← he, pow_add]
        ring
  have hPairTerm :
      (r - 1) * (r - 1) * ((n - 2).choose (r - 2)) ≤
        ((r - 1) * (r - 1)) * n ^ (r - 1) := by
    calc
      _ ≤ ((r - 1) * (r - 1)) * n ^ (r - 2) := by
        simpa only [mul_assoc] using
          Nat.mul_le_mul_left ((r - 1) * (r - 1)) hChoosePair
      _ ≤ _ := Nat.mul_le_mul_left _ hPowStep
  have hBracket :
      (r - 1) * (r - 1) * ((n - 2).choose (r - 2)) +
        n * (n - 1) * (r - 2) * ((n - 3).choose (r - 3)) ≤
      farStarCollisionConstant r * n ^ (r - 1) := by
    unfold farStarCollisionConstant
    calc
      _ ≤ ((r - 1) * (r - 1)) * n ^ (r - 1) +
          (r - 2) * n ^ (r - 1) := Nat.add_le_add hPairTerm hTripleTerm
      _ = _ := by rw [add_mul]
  have hH : h * (h - 1) ≤ h ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul_left h (Nat.sub_le h 1)
  unfold farStarCollision
  calc
    _ ≤ n ^ (r - 2) * (h ^ 2 *
          (farStarCollisionConstant r * n ^ (r - 1))) := by
      gcongr
    _ = farStarCollisionConstant r * h ^ 2 * n ^ (2 * r - 3) := by
      have he : (r - 2) + (r - 1) = 2 * r - 3 := by omega
      rw [← he, pow_add]
      ring

/-- A finite-rate version of the statement that ownership deletions are
`o(n^(r-1))` whenever `h² = o(n)`. For rational error `p/q`, the sole
scale condition is `C_r q² h² ≤ p² n`. -/
theorem far_star_deletion_rate
    (n r h p q : ℕ) (hr : 4 ≤ r) (hn : 1 ≤ n)
    (hScale : farStarCollisionConstant r * q ^ 2 * h ^ 2 ≤ p ^ 2 * n) :
    q * farStarDeletion n r h ≤ p * n ^ (r - 1) + q := by
  let c := farStarCollision n r h
  let u := Nat.nthRoot 2 c
  have hRoot : u ^ 2 ≤ c := Nat.pow_nthRoot_le (Or.inl (by norm_num))
  have hCollision := far_star_collision_power_bound n r h hr hn
  have hExponent : 1 + (2 * r - 3) = 2 * r - 2 := by omega
  have hPower : q ^ 2 * c ≤ (p * n ^ (r - 1)) ^ 2 := by
    calc
      q ^ 2 * c ≤ q ^ 2 *
          (farStarCollisionConstant r * h ^ 2 * n ^ (2 * r - 3)) :=
        Nat.mul_le_mul_left _ hCollision
      _ = (farStarCollisionConstant r * q ^ 2 * h ^ 2) *
          n ^ (2 * r - 3) := by ring
      _ ≤ (p ^ 2 * n) * n ^ (2 * r - 3) :=
        Nat.mul_le_mul_right _ hScale
      _ = (p * n ^ (r - 1)) ^ 2 := by
        have he : (r - 1) * 2 = 2 * r - 2 := by omega
        calc
          p ^ 2 * n * n ^ (2 * r - 3) =
              p ^ 2 * (n ^ 1 * n ^ (2 * r - 3)) := by simp [mul_assoc]
          _ = p ^ 2 * n ^ (2 * r - 2) := by rw [← pow_add, hExponent]
          _ = (p * n ^ (r - 1)) ^ 2 := by rw [mul_pow, ← pow_mul, he]
  have hRootPower : (q * u) ^ 2 ≤ (p * n ^ (r - 1)) ^ 2 := by
    calc
      (q * u) ^ 2 = q ^ 2 * u ^ 2 := by ring
      _ ≤ q ^ 2 * c := Nat.mul_le_mul_left _ hRoot
      _ ≤ _ := hPower
  have hLinear : q * u ≤ p * n ^ (r - 1) :=
    (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hRootPower
  change q * (u + 1) ≤ p * n ^ (r - 1) + q
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- A factorial-normalized maximum-degree bound gives a rational bound on
the star-link radius, with only the one-unit integer-rounding cost. -/
theorem far_star_radius_rate
    (n r M p q : ℕ) (hr : 4 ≤ r)
    (hDegree : q ^ (r - 1) * ((r - 1).factorial * M) ≤
      p ^ (r - 1) * n ^ (r - 1)) :
    q * farStarRadius r M ≤ p * n + q := by
  let k := r - 1
  let c := k.factorial * M
  let u := Nat.nthRoot k c
  have hk : k ≠ 0 := by omega
  have hRoot : u ^ k ≤ c := Nat.pow_nthRoot_le (Or.inl hk)
  have hPower : (q * u) ^ k ≤ (p * n) ^ k := by
    calc
      (q * u) ^ k = q ^ k * u ^ k := by rw [mul_pow]
      _ ≤ q ^ k * c := Nat.mul_le_mul_left _ hRoot
      _ ≤ p ^ k * n ^ k := hDegree
      _ = (p * n) ^ k := by rw [mul_pow]
  have hLinear : q * u ≤ p * n :=
    (Nat.pow_le_pow_iff_left hk).mp hPower
  change q * (u + 1) ≤ p * n + q
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- The multiple-hit term has the `h² n^(r-2)` scale used in IV.3.3. -/
theorem far_star_multihit_power_bound
    (n r h : ℕ) :
    h.choose 2 * (n - 2).choose (r - 2) ≤ h ^ 2 * n ^ (r - 2) := by
  have hChooseH : h.choose 2 ≤ h ^ 2 := Nat.choose_le_pow h 2
  have hChooseN : (n - 2).choose (r - 2) ≤ n ^ (r - 2) :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le n 2) _)
  exact Nat.mul_le_mul hChooseH hChooseN

/-- A fixed `j`-set has at most all possible `(r-j)`-completions in the
ambient `n`-set. -/
theorem uniform_codegree_le_ambient_choose
    {n r j : ℕ} (H : Family (Fin n)) (S : Edge (Fin n))
    (hUniform : Uniform r H) (hS : S.card = j) :
    (H.filter (fun E => S ⊆ E)).card ≤ (n - j).choose (r - j) := by
  classical
  let C := H.filter (fun E => S ⊆ E)
  have hMap : ∀ E ∈ C,
      E \ S ∈ (Finset.univ \ S).powersetCard (r - j) := by
    intro E hE
    obtain ⟨hEH, hSE⟩ := Finset.mem_filter.mp hE
    apply Finset.mem_powersetCard.mpr
    constructor
    · exact Finset.sdiff_subset_sdiff_left S (Finset.subset_univ E)
    · rw [Finset.card_sdiff_of_subset hSE, hUniform hEH, hS]
  have hInj : Set.InjOn (fun E : Edge (Fin n) => E \ S) (↑C : Set (Edge (Fin n))) := by
    intro E hE E' hE' hEq
    have hSE := (Finset.mem_filter.mp hE).2
    have hSE' := (Finset.mem_filter.mp hE').2
    have hUnion := congrArg (fun T : Edge (Fin n) => S ∪ T) hEq
    simpa only [Finset.union_sdiff_of_subset hSE,
      Finset.union_sdiff_of_subset hSE'] using hUnion
  have hBound : C.card ≤ ((Finset.univ \ S).powersetCard (r - j)).card :=
    Finset.card_le_card_of_injOn (fun E => E \ S) hMap hInj
  simpa only [C, Finset.card_powersetCard, Finset.card_sdiff_of_subset
    (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin, hS] using hBound

/-- The actual family remaining outside a small set has this fully finite
lower bound. The only family-wide numerical input is its maximum vertex
degree; the other quantities are explicit integer expressions. -/
theorem finite_far_star_tail_from_max_degree
    {n r h M : ℕ} [Inhabited (Fin n)]
    (H : Family (Fin n)) (X : Edge (Fin n))
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 4 ≤ r) (hX : X.card ≤ h)
    (hMax : ∀ z : Fin n, (H.filter (fun E => z ∈ E)).card ≤ M) :
    H.card ≤ (H.filter (fun E => Disjoint E X)).card +
      farStarDeletion n r h +
      ((farStarRadius r M + (r - 1)) * n.choose (r - 2)) / (r - 1) +
      h.choose 2 * (n - 2).choose (r - 2) := by
  classical
  have hPair : ∀ S : Edge (Fin n), S.card = 2 →
      (H.filter (fun E => S ⊆ E)).card ≤ (n - 2).choose (r - 2) := by
    intro S hS
    exact uniform_codegree_le_ambient_choose H S hUniform hS
  have hTriple : ∀ S : Edge (Fin n), S.card = 3 →
      (H.filter (fun E => S ⊆ E)).card ≤ (n - 3).choose (r - 3) := by
    intro S hS
    exact uniform_codegree_le_ambient_choose H S hUniform hS
  have hRadius : (r - 1).factorial * M ≤ (farStarRadius r M) ^ (r - 1) :=
    Nat.le_of_lt (Nat.lt_pow_nthRoot_add_one (by omega : r - 1 ≠ 0) _)
  have hCollision : farStarCollision n r h ≤ (farStarDeletion n r h) ^ 2 :=
    Nat.le_of_lt (Nat.lt_pow_nthRoot_add_one (by norm_num : 2 ≠ 0) _)
  have hLayer := removed_layer_bound_from_codegrees H Finset.univ X
    r h M ((n - 2).choose (r - 2)) ((n - 3).choose (r - 3))
    (farStarRadius r M) (farStarDeletion n r h)
    hAdm hUniform (by intro E hE; exact Finset.subset_univ E)
    hr hX hMax hPair hTriple hRadius hCollision
  omega

/-- A rational finite-density form of the far-star estimate. The two scale
conditions are exactly those needed to make the radius at most
`(p/q)n + 1` and the ownership deletion at most
`(s/q)n^(r-1) + 1`. The remaining terms are lower-order binomial errors.
This form can be applied uniformly to sequences without choosing a real
root or an asymptotic threshold inside the combinatorial argument. -/
theorem finite_far_star_tail_density_rate
    {n r h M p q s : ℕ} [Inhabited (Fin n)]
    (H : Family (Fin n)) (X : Edge (Fin n))
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 4 ≤ r) (hn : 1 ≤ n) (hX : X.card ≤ h)
    (hMax : ∀ z : Fin n, (H.filter (fun E => z ∈ E)).card ≤ M)
    (hDegree : q ^ (r - 1) * ((r - 1).factorial * M) ≤
      p ^ (r - 1) * n ^ (r - 1))
    (hSmallX : farStarCollisionConstant r * q ^ 2 * h ^ 2 ≤ s ^ 2 * n) :
    q * (r - 1) * H.card ≤
      q * (r - 1) * (H.filter (fun E => Disjoint E X)).card +
      (r - 1) * (s * n ^ (r - 1) + q) +
      (p * n + q + q * (r - 1)) * n.choose (r - 2) +
      q * (r - 1) * (h.choose 2 * (n - 2).choose (r - 2)) := by
  let k := r - 1
  let L := farStarRadius r M
  let D := farStarDeletion n r h
  let B := n.choose (r - 2)
  let Q := h.choose 2 * (n - 2).choose (r - 2)
  let T := (H.filter (fun E => Disjoint E X)).card
  have hk : 0 < k := by omega
  have hTail : H.card ≤ T + D + ((L + k) * B) / k + Q :=
    finite_far_star_tail_from_max_degree H X hAdm hUniform hr hX hMax
  have hRadius := far_star_radius_rate n r M p q hr hDegree
  have hDeletion := far_star_deletion_rate n r h s q hr hn hSmallX
  have hDiv : k * (((L + k) * B) / k) ≤ (L + k) * B :=
    Nat.mul_div_le _ _
  have hWeighted := Nat.mul_le_mul_left (q * k) hTail
  have hRadiusWeighted : q * (L + k) * B ≤
      (p * n + q + q * k) * B := by
    apply Nat.mul_le_mul_right
    calc
      q * (L + k) = q * L + q * k := by ring
      _ ≤ (p * n + q) + q * k := Nat.add_le_add_right hRadius _
      _ = p * n + q + q * k := by omega
  have hDeletionWeighted : k * (q * D) ≤ k * (s * n ^ (r - 1) + q) :=
    Nat.mul_le_mul_left _ hDeletion
  change q * k * H.card ≤ q * k * T +
      k * (s * n ^ (r - 1) + q) +
      (p * n + q + q * k) * B + q * k * Q
  nlinarith [Nat.mul_le_mul_left q hDiv, hWeighted,
    hRadiusWeighted, hDeletionWeighted]

end JSP523.Rank5
