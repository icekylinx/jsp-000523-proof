import Mathlib.Tactic

/-!
# Reciprocal pair averaging

A finite involution allows a pairwise receiver-capacity estimate to be
summed without selecting representatives of its orbits. This applies to
the reciprocal two-core receiver cells in Part II.
-/

namespace JSP523.Rank3

theorem sum_le_two_card_of_reciprocal_involution
    {β : Type*} [DecidableEq β]
    (S : Finset β) (R : β → β) (f : β → ℚ)
    (hMap : ∀ q ∈ S, R q ∈ S)
    (hInv : ∀ q ∈ S, R (R q) = q)
    (hPair : ∀ q ∈ S, f q + f (R q) ≤ 4) :
    ∑ q ∈ S, f q ≤ 2 * (S.card : ℚ) := by
  have hSwap : (∑ q ∈ S, f (R q)) = ∑ q ∈ S, f q := by
    apply Finset.sum_bij (fun q _ => R q)
    · intro q hq
      exact hMap q hq
    · intro q hq r hr heq
      calc
        q = R (R q) := (hInv q hq).symm
        _ = R (R r) := by rw [heq]
        _ = r := hInv r hr
    · intro r hr
      exact ⟨R r, hMap r hr, hInv r hr⟩
    · intro q hq
      rfl
  have hSum : (∑ q ∈ S, (f q + f (R q))) ≤
      ∑ q ∈ S, (4 : ℚ) := by
    apply Finset.sum_le_sum
    intro q hq
    exact hPair q hq
  rw [Finset.sum_add_distrib, hSwap] at hSum
  simp only [Finset.sum_const, nsmul_eq_mul] at hSum
  nlinarith

end JSP523.Rank3
