import JSP523.Rank5.ActualHigherBadRoot
import JSP523.Counting.BinomialThresholdBounds

/-!
# Explicit `q / w` bound for higher bad-root deletions

For roots of size at least three, the tail-packing exponent is one less
than the missing-facet incidence exponent. We retain the finite sum of
rank-only coefficients instead of introducing `O_r` notation.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- The tail packing factor for a root of size `k ≥ 3` costs at most one
power of `w` relative to the bad-root incidence threshold. -/
theorem higher_bad_root_tail_power_bound
    (r k w : ℕ) (hr : 5 ≤ r) (hk : 3 ≤ k) (hkr : k ≤ r - 2)
    (hw : 4 * r ≤ w) :
    w * (if k ≤ r - k then w.choose (r - k - k + 1) else 1) ≤
      w ^ (r - 1 - k) := by
  have hwPos : 1 ≤ w := by omega
  by_cases hPack : k ≤ r - k
  · let e := r - k - k + 1
    have he : e + 1 ≤ r - 1 - k := by dsimp [e]; omega
    have hChoose := Counting.choose_le_ground_power w e
    have hPow := pow_le_pow_right' hwPos he
    simp only [hPack, ↓reduceIte]
    calc
      w * w.choose e ≤ w * w ^ e := Nat.mul_le_mul_left w hChoose
      _ = w ^ (e + 1) := by
        conv_rhs => rw [pow_succ]
        ac_rfl
      _ ≤ w ^ (r - 1 - k) := hPow
  · have ht : 1 ≤ r - 1 - k := by omega
    have hPow := pow_le_pow_right' hwPos ht
    simpa [hPack] using hPow

/-- One actual higher-root stratum has deletion cost at most a rank-only
constant times `q/w`, in denominator-free form. -/
theorem actual_higher_bad_root_stratum_power_bound
    (H : Family α) (W : Edge α) (v : α) (r k : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hvW : v ∉ W) (hr : 5 ≤ r) (hk : 3 ≤ k)
    (hkr : k ≤ r - 2) (hw : 4 * r ≤ W.card) :
    W.card *
      (edgesMeetingBadRoot (outsideNoSmallerBadRoot H W v r k)
        (badMissingSets H W v r k
          ((W.card - r - k).choose (r - 1 - k)))).card ≤
      2 * (4 * r) ^ (r - 1) * (r - 1).choose k *
        (missingStarFacets H W v r).card := by
  let w := W.card
  let q := (missingStarFacets H W v r).card
  let C := (4 * r) ^ (r - 1)
  let Λ := (w - r - k).choose (r - 1 - k)
  let N := 2 * (r - 1).choose k * q
  let Tail := if k ≤ r - k then w.choose (r - k - k + 1) else 1
  let X := edgesMeetingBadRoot (outsideNoSmallerBadRoot H W v r k)
    (badMissingSets H W v r k Λ)
  have hLambda : 0 < Λ := Nat.choose_pos (by dsimp [Λ, w]; omega)
  have hStratum := actual_higher_bad_root_stratum_bound H W v r k
    hAdm hUniform hvW hk hkr hLambda
  change X.card ≤ (N / Λ) * Tail at hStratum
  have hTail := higher_bad_root_tail_power_bound r k w hr hk hkr hw
  change w * Tail ≤ w ^ (r - 1 - k) at hTail
  have hThreshold := Counting.fixed_rank_choose_lower_bound
    r k w (by omega) (by omega) hkr hw
  change w ^ (r - 1 - k) ≤ C * Λ at hThreshold
  change w * X.card ≤ 2 * C * (r - 1).choose k * q
  calc
    w * X.card ≤ w * ((N / Λ) * Tail) :=
      Nat.mul_le_mul_left w hStratum
    _ = (N / Λ) * (w * Tail) := by ac_rfl
    _ ≤ (N / Λ) * (C * Λ) :=
      Nat.mul_le_mul_left _ (hTail.trans hThreshold)
    _ = C * ((N / Λ) * Λ) := by ac_rfl
    _ ≤ C * N := Nat.mul_le_mul_left C (Nat.div_mul_le_self N Λ)
    _ = 2 * C * (r - 1).choose k * q := by
      dsimp [N]
      ac_rfl

/-- The whole higher-root deletion family has the promised `O_r(q/w)`
scale, with an explicit coefficient depending only on `r`. -/
theorem actual_higher_bad_root_edges_power_bound
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hvW : v ∉ W) (hr : 5 ≤ r) (hw : 4 * r ≤ W.card) :
    W.card * (actualHigherBadRootEdges H W v r).card ≤
      (∑ k ∈ Finset.Icc 3 (r - 2),
        2 * (4 * r) ^ (r - 1) * (r - 1).choose k) *
          (missingStarFacets H W v r).card := by
  classical
  let K := Finset.Icc 3 (r - 2)
  let q := (missingStarFacets H W v r).card
  let A := fun k => edgesMeetingBadRoot
    (outsideNoSmallerBadRoot H W v r k)
    (badMissingSets H W v r k
      ((W.card - r - k).choose (r - 1 - k)))
  have hUnion : (actualHigherBadRootEdges H W v r).card ≤
      ∑ k ∈ K, (A k).card := by
    unfold actualHigherBadRootEdges
    exact Finset.card_biUnion_le
  have hEach : ∀ k ∈ K,
      W.card * (A k).card ≤
        (2 * (4 * r) ^ (r - 1) * (r - 1).choose k) * q := by
    intro k hk
    obtain ⟨hk₁, hk₂⟩ := Finset.mem_Icc.mp hk
    exact actual_higher_bad_root_stratum_power_bound H W v r k
      hAdm hUniform hvW hr hk₁ hk₂ hw
  calc
    W.card * (actualHigherBadRootEdges H W v r).card ≤
        W.card * ∑ k ∈ K, (A k).card :=
      Nat.mul_le_mul_left W.card hUnion
    _ = ∑ k ∈ K, W.card * (A k).card := by rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ K,
          (2 * (4 * r) ^ (r - 1) * (r - 1).choose k) * q :=
      Finset.sum_le_sum hEach
    _ = (∑ k ∈ K,
          2 * (4 * r) ^ (r - 1) * (r - 1).choose k) * q := by
      rw [Finset.sum_mul]

end JSP523
