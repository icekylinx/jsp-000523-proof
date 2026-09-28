import JSP523.Counting.BinomialThresholdBounds
import JSP523.Counting.BadSetIncidence

/-!
# Polynomial-scale bounds for actual bad roots

The finite incidence estimate (IV.2.3) and an explicit binomial lower
bound give denominator-free polynomial estimates for every bad-root
size. The constant is deliberately coarse and depends only on the fixed
rank. These are the arithmetic inputs to the `O_r` deletion estimate
in §IV.2.1 of `jsp-000523-proof/paper/proof.md`.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Explicit polynomial form of (IV.2.3) for the actual bad `k`-sets. -/
theorem actual_bad_root_power_bound
    (H : Family α) (W : Edge α) (v : α) (r k : ℕ)
    (hr : 3 ≤ r) (hk₁ : 1 ≤ k) (hk₂ : k ≤ r - 2)
    (hw : 4 * r ≤ W.card) :
    (badMissingSets H W v r k
      ((W.card - r - k).choose (r - 1 - k))).card *
        W.card ^ (r - 1 - k) ≤
      2 * (4 * r) ^ (r - 1) * (r - 1).choose k *
        (missingStarFacets H W v r).card := by
  let Bad := badMissingSets H W v r k
    ((W.card - r - k).choose (r - 1 - k))
  let Λ := (W.card - r - k).choose (r - 1 - k)
  let C := (4 * r) ^ (r - 1)
  let q := (missingStarFacets H W v r).card
  have hThreshold := Counting.fixed_rank_choose_lower_bound
    r k W.card hr hk₁ hk₂ hw
  change W.card ^ (r - 1 - k) ≤ C * Λ at hThreshold
  have hIncidence := badMissingSets_card_bound H W v r k Λ
  change Λ * Bad.card ≤ 2 * (r - 1).choose k * q at hIncidence
  change Bad.card * W.card ^ (r - 1 - k) ≤
    2 * C * (r - 1).choose k * q
  calc
    Bad.card * W.card ^ (r - 1 - k) ≤ Bad.card * (C * Λ) :=
      Nat.mul_le_mul_left Bad.card hThreshold
    _ = C * (Λ * Bad.card) := by ac_rfl
    _ ≤ C * (2 * (r - 1).choose k * q) :=
      Nat.mul_le_mul_left C hIncidence
    _ = 2 * C * (r - 1).choose k * q := by ac_rfl

/-- In particular the number `d` of exceptional vertices has the
polynomial scale stated in (IV.2.4), with an explicit rank constant. -/
theorem actual_bad_singleton_power_bound
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hr : 3 ≤ r) (hw : 4 * r ≤ W.card) :
    (badSingletonVertices H W v r).card * W.card ^ (r - 2) ≤
      2 * (4 * r) ^ (r - 1) * (r - 1) *
        (missingStarFacets H W v r).card := by
  let D := badSingletonVertices H W v r
  let Λ := (W.card - r - 1).choose (r - 2)
  let C := (4 * r) ^ (r - 1)
  let q := (missingStarFacets H W v r).card
  have hThreshold := Counting.fixed_rank_choose_lower_bound
    r 1 W.card hr (by omega) (by omega) hw
  have hIncidence := badSingletonVertices_card_bound H W v r
  change Λ * D.card ≤ 2 * (r - 1) * q at hIncidence
  have hThreshold' : W.card ^ (r - 2) ≤ C * Λ := by
    simpa [C, Λ, Nat.sub_sub] using hThreshold
  change D.card * W.card ^ (r - 2) ≤ 2 * C * (r - 1) * q
  calc
    D.card * W.card ^ (r - 2) ≤ D.card * (C * Λ) :=
      Nat.mul_le_mul_left D.card hThreshold'
    _ = C * (Λ * D.card) := by ac_rfl
    _ ≤ C * (2 * (r - 1) * q) :=
      Nat.mul_le_mul_left C hIncidence
    _ = 2 * C * (r - 1) * q := by ac_rfl

end JSP523
