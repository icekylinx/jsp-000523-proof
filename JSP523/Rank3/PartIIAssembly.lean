import JSP523.Rank3.NearCompleteBlocks
import JSP523.Rank3.LocalPaymentLedger
import JSP523.Rank3.LocalDefectActual
import JSP523.Rank3.GlobalSourceLedger
import Mathlib.Tactic.Linarith

/-!
# The Part II ledger interface

The statements below isolate two geometric inputs:
the actual global receiver-capacity estimate (II.8), and payment of its
exceptional excess by local defects (II.11)–(II.12). All other terms are the
actual supports, rooted weights, and local defects of the same family.
`PartIIClosure` discharges both inputs for every admissible triple family.
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

/-- Algebraic form of (II.9), conditional exactly on (II.8). -/
theorem actual_support_defect_le_exceptional_excess
    (H : Family α) (V : Edge α) (Ξ : ℚ)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hCapacity :
      orientedPositiveWeightTotal H V / 2 ≤
        2 * ((singletonCompletionPairs H V).card : ℚ) +
        4 * ((singletonLinkCells H V).card : ℚ) +
        2 * ((doubleLinkCells H V).card : ℚ) + Ξ) :
    6 * (2 * (H.card : ℚ) -
      ((usedPairs H V).card : ℚ) -
      ((usedCells H V).card : ℚ)) ≤
      Ξ - ∑ E ∈ H, localSignedDefect H V E := by
  have hLedger := actual_support_ledger H V hU hGround
  have hPayment := signed_payment_identity_on_actual_supports
    V hAdm hU hGround
  linarith

/-- (II.8) plus payment of every exceptional demand closes the support
inequality on the actual family. -/
theorem actual_support_of_capacity_and_bridge_payment
    (H : Family α) (V : Edge α) (Ξ : ℚ)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hCapacity :
      orientedPositiveWeightTotal H V / 2 ≤
        2 * ((singletonCompletionPairs H V).card : ℚ) +
        4 * ((singletonLinkCells H V).card : ℚ) +
        2 * ((doubleLinkCells H V).card : ℚ) + Ξ)
    (hPaid : Ξ ≤ ∑ E ∈ H, localSignedDefect H V E) :
    2 * H.card ≤
      (usedPairs H V).card + (usedCells H V).card := by
  have hDefect := actual_support_defect_le_exceptional_excess
    H V Ξ hU hAdm hGround hCapacity
  have hRational : 2 * (H.card : ℚ) ≤
      ((usedPairs H V).card : ℚ) +
      ((usedCells H V).card : ℚ) := by
    linarith
  exact_mod_cast hRational

/-- Reduction of Theorem II.1 to the two remaining estimates on
block-free admissible triple systems. -/
theorem rank_three_bound_of_block_free_capacity_and_payment
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hRemaining : ∀ K : Family α,
      Uniform 3 K → Admissible K →
      (∀ E ∈ K, E ⊆ V) →
      (∀ A : Edge α, A ⊆ V → ¬ nearCompleteBlock K A) →
      ∃ Ξ : ℚ,
        orientedPositiveWeightTotal K V / 2 ≤
          2 * ((singletonCompletionPairs K V).card : ℚ) +
          4 * ((singletonLinkCells K V).card : ℚ) +
          2 * ((doubleLinkCells K V).card : ℚ) + Ξ ∧
        Ξ ≤ ∑ E ∈ K, localSignedDefect K V E) :
    H.card ≤ V.card.choose 2 := by
  apply triple_family_card_le_choose_two_of_block_free_case
    H V hU hAdm hGround
  intro K hUK hAdmK hGroundK hFreeK
  obtain ⟨Ξ, hCapacity, hPaid⟩ :=
    hRemaining K hUK hAdmK hGroundK hFreeK
  exact actual_support_of_capacity_and_bridge_payment
    K V Ξ hUK hAdmK hGroundK hCapacity hPaid

/-- A conditional interface from global source conservation to the
rank-three bound. `PartIIClosure` supplies these actual-charge and
exception-payment hypotheses without extra assumptions. -/
theorem rank_three_bound_of_incoming_capacity_and_exception_payment
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hRemaining : ∀ K : Family α,
      Uniform 3 K → Admissible K →
      (∀ E ∈ K, E ⊆ V) →
      (∀ A : Edge α, A ⊆ V → ¬ nearCompleteBlock K A) →
      incomingCommonLinkChargeTotal K V ≤
        4 * ((singletonLinkCells K V).card : ℚ) +
        2 * ((doubleLinkCells K V).card : ℚ) +
        actualXi K V ∧
      actualXi K V ≤ ∑ E ∈ K, localSignedDefect K V E) :
    H.card ≤ V.card.choose 2 := by
  apply rank_three_bound_of_block_free_capacity_and_payment
    H V hU hAdm hGround
  intro K hUK hAdmK hGroundK hFreeK
  obtain ⟨hIncoming, hPaid⟩ :=
    hRemaining K hUK hAdmK hGroundK hFreeK
  exact ⟨actualXi K V,
    positive_total_le_capacity_of_incoming_bound
      K V hUK hGroundK hIncoming,
    hPaid⟩

end JSP523.Rank3
