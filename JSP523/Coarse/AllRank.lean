import JSP523.Coarse.AlignmentTriples
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Theorem I.1: finite coarse bound in every rank

This proves Theorem I.1 of `paper/proof.pdf`, §I.1. The proof uses the graph
deletion and rainbow triple-system lemmas from that section. In the final
alignment step, write the paper's rank as `r = s₀ + 2` for the first `s₀`
classes. Here
the Lean offset is `s = r - 3`, so those classes are `s+1` and a difference
vector has `s` coordinates.  The manuscript averages over bijections and
gets alignment probability `n⁻ˢ`; this development instead partitions the
crossing family into `nˢ` difference fibers, each bounded by `3 n²`.
Summing gives `3 n^(s+2) = 3 n^(r-1)`, the same estimate as (I.7).
This is an equivalent deterministic proof of the alignment count, not a
formalization of the manuscript's bijection average itself.
-/

namespace JSP523.Coarse

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Theorem I.1 with the rank written as s+3. -/
theorem coarse_bound_offset
    (H : Family α) (s : ℕ)
    (hU : Uniform (s + 3) H)
    (hAdm : Admissible H) :
    (s + 3).factorial * H.card ≤
      3 * (s + 3) ^ (s + 3) * (Fintype.card α) ^ (s + 2) := by
  classical
  by_cases hNonempty : H.Nonempty
  · obtain ⟨E, hE⟩ := hNonempty
    have hle : s + 3 ≤ Fintype.card α := by
      rw [← hU hE]
      simpa using Finset.card_le_card (Finset.subset_univ E)
    have hpos : 0 < Fintype.card α := by omega
    let : NeZero (Fintype.card α) := ⟨Nat.ne_of_gt hpos⟩
    let e : α ≃ ZMod (Fintype.card α) :=
      (Fintype.equivFin α).trans
        (ZMod.finEquiv (Fintype.card α)).toEquiv
    obtain ⟨κ, hAvg⟩ :=
      exists_crossing_subfamily_uniform H (s + 3) (by omega) hU
    let F := crossingSubfamily H (s + 3) κ
    have hFU : Uniform (s + 3) F := by
      intro A hA
      exact hU (crossing_subfamily_subset H (s + 3) κ hA)
    have hFC : ∀ A ∈ F, CrossingOn (s + 3) κ A := by
      intro A hA
      exact ((mem_crossing_subfamily_iff H (s + 3) κ A).mp hA).2
    have hFAdm : Admissible F :=
      admissible_mono (crossing_subfamily_subset H (s + 3) κ) hAdm
    have hFbound :=
      crossing_family_card_le_three_power F s κ hFU hFC hFAdm e
    calc
      (s + 3).factorial * H.card ≤
          (s + 3) ^ (s + 3) * F.card := hAvg
      _ ≤ (s + 3) ^ (s + 3) *
          (3 * (Fintype.card α) ^ (s + 2)) :=
        Nat.mul_le_mul_left _ hFbound
      _ = 3 * (s + 3) ^ (s + 3) *
          (Fintype.card α) ^ (s + 2) := by ac_rfl
  · have hEmpty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hNonempty
    simp [hEmpty]

/-- Theorem I.1 in the manuscript's rank notation. -/
theorem coarse_bound_all_rank
    (H : Family α) (r : ℕ) (hr : 3 ≤ r)
    (hU : Uniform r H) (hAdm : Admissible H) :
    r.factorial * H.card ≤
      3 * r ^ r * (Fintype.card α) ^ (r - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 3 :=
    ⟨r - 3, by omega⟩
  have hExp : (s + 3) - 1 = s + 2 := by omega
  simpa only [hExp] using coarse_bound_offset H s hU hAdm

/-- Equation (I.2), the rank-four consequence used later. -/
theorem coarse_rank_four
    (H : Family α) (hU : Uniform 4 H) (hAdm : Admissible H) :
    H.card ≤ 32 * (Fintype.card α) ^ 3 := by
  have h := coarse_bound_all_rank H 4 (by omega) hU hAdm
  norm_num [Nat.factorial] at h
  omega

end JSP523.Coarse
