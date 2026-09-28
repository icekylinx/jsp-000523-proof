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

/-- Exact ratio between the shadow-allocation binomial and the extremal
star size `choose(n-1,k)`. The two factors in the denominator explain why
the leading coefficient of the shadow term is one. -/
theorem far_star_choose_ratio_exact
    (n k : ℕ) (hk : 1 ≤ k) (hn : k + 1 ≤ n) :
    (n - k + 1) * (n - k) * n.choose (k - 1) =
      n * k * (n - 1).choose k := by
  have hFirst := Nat.choose_mul_succ_eq (n - 1) (k - 1)
  have hSecond := Nat.choose_succ_right_eq (n - 1) (k - 1)
  have hN : n - 1 + 1 = n := by omega
  have hK : k - 1 + 1 = k := by omega
  have hDiff₁ : n - (k - 1) = n - k + 1 := by omega
  have hDiff₂ : n - 1 - (k - 1) = n - k := by omega
  rw [hN, hDiff₁] at hFirst
  rw [hK, hDiff₂] at hSecond
  calc
    (n - k + 1) * (n - k) * n.choose (k - 1) =
        ((n - 1).choose (k - 1) * n) * (n - k) := by
      rw [hFirst]
      ring
    _ = n * ((n - 1).choose (k - 1) * (n - k)) := by ring
    _ = n * ((n - 1).choose k * k) := by rw [← hSecond]
    _ = n * k * (n - 1).choose k := by ring

/-- The exact binomial denominator differs from `n²` by at most `2kn`.
This crude polynomial inequality is enough to turn a fixed rational
coefficient margin into an explicit ground-set threshold. -/
theorem far_star_choose_denominator_bound
    (n k : ℕ) (hkn : k ≤ n) :
    n ^ 2 ≤ (n - k + 1) * (n - k) + 2 * k * n := by
  have hnk : n - k + k = n := Nat.sub_add_cancel hkn
  nlinarith

/-- A uniform lower bound for the extremal star size once `n ≥ 2k+1`.
It turns every fixed multiple of `n^k` into a fixed multiple of
`choose(n-1,k)` without invoking asymptotic equivalence. -/
theorem far_star_power_le_choose_multiple
    (n k : ℕ) (hLarge : 2 * k + 1 ≤ n) :
    n ^ k ≤ 2 ^ k * k.factorial * (n - 1).choose k := by
  have hnk : n ≤ 2 * (n - k) := by omega
  have hPow : n ^ k ≤ 2 ^ k * (n - k) ^ k := by
    calc
      n ^ k ≤ (2 * (n - k)) ^ k := Nat.pow_le_pow_left hnk _
      _ = 2 ^ k * (n - k) ^ k := by rw [mul_pow]
  have hDesc : (n - k) ^ k ≤ (n - 1).descFactorial k := by
    have hEq : n - 1 + 1 - k = n - k := by omega
    simpa only [hEq] using Nat.pow_sub_le_descFactorial (n - 1) k
  calc
    n ^ k ≤ 2 ^ k * (n - k) ^ k := hPow
    _ ≤ 2 ^ k * (n - 1).descFactorial k :=
      Nat.mul_le_mul_left _ hDesc
    _ = 2 ^ k * k.factorial * (n - 1).choose k := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      ring

/-- A rational maximum-degree gap relative to the extremal star size
implies the factorial-normalized radius condition directly. -/
theorem far_star_degree_rate_of_star_ratio
    (n k M p q : ℕ)
    (hRatio : q ^ k * M ≤ p ^ k * (n - 1).choose k) :
    q ^ k * (k.factorial * M) ≤ p ^ k * n ^ k := by
  have hStar : k.factorial * (n - 1).choose k ≤ n ^ k := by
    calc
      k.factorial * (n - 1).choose k =
          (n - 1).descFactorial k :=
        (Nat.descFactorial_eq_factorial_mul_choose _ _).symm
      _ ≤ (n - 1) ^ k := Nat.descFactorial_le_pow _ _
      _ ≤ n ^ k := Nat.pow_le_pow_left (Nat.sub_le n 1) _
  calc
    q ^ k * (k.factorial * M) = k.factorial * (q ^ k * M) := by ring
    _ ≤ k.factorial * (p ^ k * (n - 1).choose k) :=
      Nat.mul_le_mul_left _ hRatio
    _ = p ^ k * (k.factorial * (n - 1).choose k) := by ring
    _ ≤ p ^ k * n ^ k := Nat.mul_le_mul_left _ hStar

/-- Linear upper bound on the difference of two powers. This is the
integer form of the Bernoulli estimate needed to choose rational degree
coefficients from a fixed positive gap. -/
theorem power_gap_linear_bound (p d k : ℕ) :
    (p + d) ^ k ≤ p ^ k + k * d * (p + d) ^ (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      by_cases hk : k = 0
      · subst k
        simp
      · have hPow : p ^ k ≤ (p + d) ^ k :=
          Nat.pow_le_pow_left (Nat.le_add_right p d) _
        have hExp : k + 1 - 1 = k := by omega
        rw [hExp, pow_succ, pow_succ p]
        have hPrev : k - 1 + 1 = k := by omega
        have hQ : (p + d) ^ (k - 1) * (p + d) = (p + d) ^ k := by
          rw [← pow_succ, hPrev]
        calc
          (p + d) ^ k * (p + d) ≤
              (p ^ k + k * d * (p + d) ^ (k - 1)) * (p + d) :=
            Nat.mul_le_mul_right _ ih
          _ = p ^ k * p + d * p ^ k + k * d * (p + d) ^ k := by
            calc
              (p ^ k + k * d * (p + d) ^ (k - 1)) * (p + d) =
                  p ^ k * (p + d) +
                    k * d * ((p + d) ^ (k - 1) * (p + d)) := by ring
              _ = _ := by rw [hQ]; ring
          _ ≤ p ^ k * p + d * (p + d) ^ k + k * d * (p + d) ^ k := by
            exact Nat.add_le_add_right
              (Nat.add_le_add_left (Nat.mul_le_mul_left d hPow) _) _
          _ = p ^ k * p + (k + 1) * d * (p + d) ^ k := by ring

/-- A radius coefficient `p/q` is promoted to any larger coefficient
`p'/q` by an explicit linear ground-set threshold. The conclusion is the
sharp finite comparison with `choose(n-1,k)`, with no division. -/
theorem far_star_shadow_main_term_rate
    (n k L p p' q : ℕ)
    (hk : 1 ≤ k) (hn : k + 1 ≤ n) (hpp' : p ≤ p')
    (hRadius : q * L ≤ p * n + q)
    (hThreshold : q * (k + 1) + 2 * p' * k ≤ (p' - p) * n) :
    q * (L + k) * n.choose (k - 1) ≤
      p' * k * (n - 1).choose k := by
  let den := (n - k + 1) * (n - k)
  let B := n.choose (k - 1)
  let M := (n - 1).choose k
  have hExact : den * B = n * k * M :=
    far_star_choose_ratio_exact n k hk hn
  have hDen : n ^ 2 ≤ den + 2 * k * n :=
    far_star_choose_denominator_bound n k (by omega)
  have hR : q * (L + k) + 2 * p' * k ≤ p' * n := by
    have hR' : q * (L + k) ≤ p * n + q * (k + 1) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      omega
    have hSub : p * n + (p' - p) * n = p' * n := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hpp']
    omega
  have hScale : q * (L + k) * n ≤ p' * den := by
    have hMul := Nat.mul_le_mul_right n hR
    have hDenMul := Nat.mul_le_mul_left p' hDen
    nlinarith
  have hScaled := Nat.mul_le_mul_right B hScale
  calc
    q * (L + k) * B ≤ p' * k * M := by
      have hNpos : 0 < n := by omega
      have hCompare : q * (L + k) * B * n ≤ p' * k * M * n := by
        calc
          q * (L + k) * B * n = q * (L + k) * n * B := by ring
          _ ≤ p' * den * B := hScaled
          _ = p' * k * M * n := by
            calc
              p' * den * B = p' * (den * B) := by ring
              _ = p' * (n * k * M) := by rw [hExact]
              _ = p' * k * M * n := by ring
      exact (Nat.mul_le_mul_right_iff hNpos).mp (by simpa only [Nat.mul_assoc] using hCompare)

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

/-- Coefficient-sharp finite version of IV.3.3. The exact choose ratio
converts the separated-shadow allocation into `p'/q` times the extremal
star size. The remaining errors are displayed at their true power scales. -/
theorem finite_far_star_tail_extremal_rate
    {n r h M p p' q s : ℕ} [Inhabited (Fin n)]
    (H : Family (Fin n)) (X : Edge (Fin n))
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 4 ≤ r) (hn : r ≤ n) (hX : X.card ≤ h)
    (hMax : ∀ z : Fin n, (H.filter (fun E => z ∈ E)).card ≤ M)
    (hpp' : p ≤ p')
    (hDegree : q ^ (r - 1) * ((r - 1).factorial * M) ≤
      p ^ (r - 1) * n ^ (r - 1))
    (hSmallX : farStarCollisionConstant r * q ^ 2 * h ^ 2 ≤ s ^ 2 * n)
    (hThreshold : q * r + 2 * p' * (r - 1) ≤
      (p' - p) * n) :
    q * (r - 1) * H.card ≤
      q * (r - 1) * (H.filter (fun E => Disjoint E X)).card +
      (r - 1) * (s * n ^ (r - 1) + q) +
      p' * (r - 1) * (n - 1).choose (r - 1) +
      q * (r - 1) * (h ^ 2 * n ^ (r - 2)) := by
  let k := r - 1
  let L := farStarRadius r M
  let D := farStarDeletion n r h
  let B := n.choose (r - 2)
  let Q := h.choose 2 * (n - 2).choose (r - 2)
  let T := (H.filter (fun E => Disjoint E X)).card
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hkn : k + 1 ≤ n := by dsimp [k]; omega
  have hD := far_star_deletion_rate n r h s q hr (by omega : 1 ≤ n) hSmallX
  have hL := far_star_radius_rate n r M p q hr hDegree
  have hShadow : q * (L + k) * B ≤
      p' * k * (n - 1).choose k := by
    have hExp : k - 1 = r - 2 := by dsimp [k]; omega
    have hThresh : q * (k + 1) + 2 * p' * k ≤ (p' - p) * n := by
      simpa only [k, show r - 1 + 1 = r by omega] using hThreshold
    simpa only [B, hExp] using
      far_star_shadow_main_term_rate n k L p p' q hk hkn hpp' hL hThresh
  have hMulti := far_star_multihit_power_bound n r h
  have hTail : H.card ≤ T + D + ((L + k) * B) / k + Q :=
    finite_far_star_tail_from_max_degree H X hAdm hUniform hr hX hMax
  have hDiv : k * (((L + k) * B) / k) ≤ (L + k) * B :=
    Nat.mul_div_le _ _
  have hWeighted := Nat.mul_le_mul_left (q * k) hTail
  change q * k * H.card ≤ q * k * T +
      k * (s * n ^ k + q) +
      p' * k * (n - 1).choose k +
      q * k * (h ^ 2 * n ^ (k - 1))
  have hMulti' : Q ≤ h ^ 2 * n ^ (k - 1) := by
    simpa only [Q, k, show r - 1 - 1 = r - 2 by omega] using hMulti
  nlinarith [Nat.mul_le_mul_left q hDiv,
    Nat.mul_le_mul_left k hD,
    Nat.mul_le_mul_left (q * k) hMulti', hWeighted, hShadow]

/-- A positive-mass far-star tail with an explicit finite error absorption
condition. The retained mass is a fixed rational fraction of the extremal
star size whenever `p' < q`. -/
theorem finite_far_star_tail_positive_mass
    {n r h M p p' q s : ℕ} [Inhabited (Fin n)]
    (H : Family (Fin n)) (X : Edge (Fin n))
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 4 ≤ r) (hn : r ≤ n) (hX : X.card ≤ h)
    (hMax : ∀ z : Fin n, (H.filter (fun E => z ∈ E)).card ≤ M)
    (hpp' : p ≤ p') (hp'q : p' < q)
    (hDegree : q ^ (r - 1) * ((r - 1).factorial * M) ≤
      p ^ (r - 1) * n ^ (r - 1))
    (hSmallX : farStarCollisionConstant r * q ^ 2 * h ^ 2 ≤ s ^ 2 * n)
    (hThreshold : q * r + 2 * p' * (r - 1) ≤
      (p' - p) * n)
    (hMass : (n - 1).choose (r - 1) ≤ H.card)
    (hAbsorb : 2 *
      (s * n ^ (r - 1) + q + q * h ^ 2 * n ^ (r - 2)) ≤
        (q - p') * (n - 1).choose (r - 1)) :
    (q - p') * (n - 1).choose (r - 1) ≤
      2 * q * (H.filter (fun E => Disjoint E X)).card := by
  let k := r - 1
  let B := (n - 1).choose k
  let T := (H.filter (fun E => Disjoint E X)).card
  let Err := s * n ^ k + q + q * h ^ 2 * n ^ (k - 1)
  have hk : 0 < k := by dsimp [k]; omega
  have hRate := finite_far_star_tail_extremal_rate H X hAdm hUniform
    hr hn hX hMax hpp' hDegree hSmallX hThreshold
  have hRate' : q * k * H.card ≤ q * k * T + k * Err + p' * k * B := by
    dsimp [k, B, T, Err] at *
    rw [show r - 1 - 1 = r - 2 by omega]
    nlinarith [hRate]
  have hMass' : B ≤ H.card := hMass
  have hAbsorb' : 2 * Err ≤ (q - p') * B := by
    simpa only [Err, k, B, show r - 1 - 1 = r - 2 by omega] using hAbsorb
  have hSub : p' + (q - p') = q := Nat.add_sub_of_le hp'q.le
  have hCoef : q * k * B = p' * k * B + (q - p') * k * B := by
    conv_lhs => rw [← hSub]
    ring
  have hMassScaled : q * k * B ≤ q * k * H.card :=
    Nat.mul_le_mul_left _ hMass'
  have hCore : (q - p') * k * B ≤ q * k * T + k * Err := by
    omega
  have hErrScaled := Nat.mul_le_mul_left k hAbsorb'
  have hFinal : k * ((q - p') * B) ≤ k * (2 * q * T) := by
    nlinarith [Nat.mul_le_mul_left 2 hCore, hErrScaled]
  have hResult : (q - p') * B ≤ 2 * q * T :=
    (Nat.mul_le_mul_left_iff hk).mp hFinal
  exact hResult

/-- A simpler positive-mass criterion with a single small-set condition
`q h² ≤ n`. The remaining hypotheses involve fixed rank and rational
coefficients, plus the sharp maximum-degree bound and a linear threshold
on `n`. Hence every sequence with `h² = o(n)` eventually meets the
small-set condition for any fixed `q`. -/
theorem finite_far_star_tail_positive_from_small_set
    {n r h M p p' q s : ℕ} [Inhabited (Fin n)]
    (H : Family (Fin n)) (X : Edge (Fin n))
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 4 ≤ r) (hn : 2 * (r - 1) + 1 ≤ n) (hX : X.card ≤ h)
    (hMax : ∀ z : Fin n, (H.filter (fun E => z ∈ E)).card ≤ M)
    (hpp' : p ≤ p') (hp'q : p' < q)
    (hDegree : q ^ (r - 1) * ((r - 1).factorial * M) ≤
      p ^ (r - 1) * n ^ (r - 1))
    (hThreshold : q * r + 2 * p' * (r - 1) ≤
      (p' - p) * n)
    (hMass : (n - 1).choose (r - 1) ≤ H.card)
    (hTiny : q * h ^ 2 ≤ n)
    (hQ : q ≤ n ^ (r - 1))
    (hCollisionCoeff : farStarCollisionConstant r * q ≤ s ^ 2)
    (hErrorCoeff : 2 * (s + 2) *
      (2 ^ (r - 1) * (r - 1).factorial) ≤ q - p') :
    (q - p') * (n - 1).choose (r - 1) ≤
      2 * q * (H.filter (fun E => Disjoint E X)).card := by
  let k := r - 1
  let B := (n - 1).choose k
  let C := 2 ^ k * k.factorial
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hn' : r ≤ n := by omega
  have hSmallX : farStarCollisionConstant r * q ^ 2 * h ^ 2 ≤ s ^ 2 * n := by
    calc
      farStarCollisionConstant r * q ^ 2 * h ^ 2 =
          (farStarCollisionConstant r * q) * (q * h ^ 2) := by ring
      _ ≤ (farStarCollisionConstant r * q) * n :=
        Nat.mul_le_mul_left _ hTiny
      _ ≤ s ^ 2 * n := Nat.mul_le_mul_right _ hCollisionCoeff
  have hPower : n ^ k ≤ C * B :=
    far_star_power_le_choose_multiple n k hn
  have hTinyTerm : q * h ^ 2 * n ^ (k - 1) ≤ n ^ k := by
    have hPow : n * n ^ (k - 1) = n ^ k := by
      have he : k - 1 + 1 = k := by omega
      rw [Nat.mul_comm, ← pow_succ, he]
    calc
      q * h ^ 2 * n ^ (k - 1) = (q * h ^ 2) * n ^ (k - 1) := by ring
      _ ≤ n * n ^ (k - 1) := Nat.mul_le_mul_right _ hTiny
      _ = n ^ k := hPow
  have hError :
      s * n ^ k + q + q * h ^ 2 * n ^ (k - 1) ≤
        (s + 2) * n ^ k := by
    nlinarith [hTinyTerm, hQ]
  have hAbsorb : 2 *
      (s * n ^ (r - 1) + q + q * h ^ 2 * n ^ (r - 2)) ≤
        (q - p') * (n - 1).choose (r - 1) := by
    have hCoeff : 2 * (s + 2) * C ≤ q - p' := hErrorCoeff
    have hError' := Nat.mul_le_mul_left 2 hError
    have hPower' := Nat.mul_le_mul_left (2 * (s + 2)) hPower
    have hCoeff' := Nat.mul_le_mul_right B hCoeff
    dsimp [k, B, C] at *
    have he : r - 1 - 1 = r - 2 := by omega
    rw [he] at hError'
    nlinarith
  exact finite_far_star_tail_positive_mass H X hAdm hUniform
    hr hn' hX hMax hpp' hp'q hDegree hSmallX hThreshold hMass hAbsorb

end JSP523.Rank5
