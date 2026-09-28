import JSP523.Rank3.BridgeExcessAccounting
import JSP523.Rank3.LocalDefectActual

/-!
# Finite bridge-demand payment ledger

The two geometric claims of §§II.C–II.D enter only through `hUnique` and
`hPaid`. The finite sum below then turns those claims and the actual local
defect nonnegativity into the manuscript's global Xi payment.
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

/-- When positive demands on one triple have a unique receiving cell, local
payment of that demand bounds the entire actual demand on the triple. -/
theorem bridge_demand_on_triple_le_local_signed_defect
    (H : Family α) (V : Edge α)
    (hH : Admissible H) (hU : Uniform 3 H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hUnique : ∀ E ∈ H, ∀ q₁ ∈ usedCells H V, ∀ q₂ ∈ usedCells H V,
      0 < bridgeDemand H V q₁ E →
      0 < bridgeDemand H V q₂ E → q₁ = q₂)
    (hPaid : ∀ E ∈ H, ∀ q ∈ usedCells H V,
      0 < bridgeDemand H V q E →
      bridgeDemand H V q E ≤ localSignedDefect H V E)
    {E : Edge α} (hE : E ∈ H) :
    bridgeDemandOnTriple H V E ≤ localSignedDefect H V E := by
  classical
  by_cases hSome : ∃ q ∈ usedCells H V, 0 < bridgeDemand H V q E
  · obtain ⟨q, hq, hpos⟩ := hSome
    have hOthers (q' : Edge α) (hq' : q' ∈ usedCells H V)
        (hneq : q' ≠ q) : bridgeDemand H V q' E = 0 := by
      have hnon := bridge_demand_nonneg H V q' E hH
      have hnot : ¬ 0 < bridgeDemand H V q' E := by
        intro hpos'
        exact hneq (hUnique E hE q' hq' q hq hpos' hpos)
      linarith
    have hSingle : bridgeDemandOnTriple H V E =
        bridgeDemand H V q E := by
      unfold bridgeDemandOnTriple
      exact Finset.sum_eq_single_of_mem q hq
        (fun q' hq' hneq => hOthers q' hq' hneq)
    rw [hSingle]
    exact hPaid E hE q hq hpos
  · have hZero (q : Edge α) (hq : q ∈ usedCells H V) :
        bridgeDemand H V q E = 0 := by
      have hnon := bridge_demand_nonneg H V q E hH
      have hnot : ¬ 0 < bridgeDemand H V q E := by
        intro hp
        exact hSome ⟨q, hq, hp⟩
      linarith
    have hDemandZero : bridgeDemandOnTriple H V E = 0 := by
      unfold bridgeDemandOnTriple
      exact Finset.sum_eq_zero (fun q hq => hZero q hq)
    rw [hDemandZero]
    exact local_signed_defect_nonneg hH hU hGround hE

/-- Once §§II.C–II.D give uniqueness and local payment, the actual Xi
excess is paid by the actual local defects. -/
theorem actual_xi_le_local_signed_defect_sum_of_bridge_geometry
    (H : Family α) (V : Edge α)
    (hH : Admissible H) (hU : Uniform 3 H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hUnique : ∀ E ∈ H, ∀ q₁ ∈ usedCells H V, ∀ q₂ ∈ usedCells H V,
      0 < bridgeDemand H V q₁ E →
      0 < bridgeDemand H V q₂ E → q₁ = q₂)
    (hPaid : ∀ E ∈ H, ∀ q ∈ usedCells H V,
      0 < bridgeDemand H V q E →
      bridgeDemand H V q E ≤ localSignedDefect H V E) :
    actualXi H V ≤ ∑ E ∈ H, localSignedDefect H V E := by
  calc
    actualXi H V ≤ bridgeDemandTotal H V :=
      actual_xi_le_bridge_demand_total H V hH
    _ ≤ ∑ E ∈ H, localSignedDefect H V E := by
      unfold bridgeDemandTotal
      apply Finset.sum_le_sum
      intro E hE
      exact bridge_demand_on_triple_le_local_signed_defect
        H V hH hU hGround hUnique hPaid hE

end JSP523.Rank3
