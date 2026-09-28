import JSP523.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Finite multilevel cleanup from actual parent links

The link and deletion sets refer to a fixed parent family. The aggregate bad
partner incidence premise is the input supplied by quantitative coloring.
-/
namespace JSP523.Rank5
open JSP523 Finset BigOperators
variable {α : Type*} [DecidableEq α]

/-- Actual `s`-link of a core in the fixed parent family. -/
noncomputable def actualCoreLink (H : Family α) (V A : Edge α) (s : ℕ) : Family α := by
  classical
  exact (V.powersetCard s).filter fun P => Disjoint P A ∧ A ∪ P ∈ H

theorem mem_actualCoreLink {H : Family α} {V A P : Edge α} {s : ℕ} :
    P ∈ actualCoreLink H V A s ↔
      P ⊆ V ∧ P.card = s ∧ Disjoint P A ∧ A ∪ P ∈ H := by
  simp only [actualCoreLink, Finset.mem_filter, Finset.mem_powersetCard]
  tauto

/-- Exceptional partner degree in an actual parent link. -/
noncomputable def actualBadPartnerDegree
    (H : Family α) (V A : Edge α) (s : ℕ)
    (bad : Edge α → Edge α → Edge α → Prop) (P : Edge α) : ℕ := by
  classical
  exact ((actualCoreLink H V A s).filter fun Q => bad A P Q).card

/-- Nonexception partners other than the selected link vertex. -/
noncomputable def actualGoodOtherPartners
    (H : Family α) (V A P : Edge α) (s : ℕ)
    (bad : Edge α → Edge α → Edge α → Prop) : Family α := by
  classical
  exact ((actualCoreLink H V A s).erase P).filter fun Q => ¬ bad A P Q

/-- Delete every link vertex for a low-degree core, and only high-exception
vertices otherwise. -/
noncomputable def cleanupTails
    (H : Family α) (V A : Edge α) (s u q : ℕ)
    (bad : Edge α → Edge α → Edge α → Prop) : Family α := by
  classical
  let L := actualCoreLink H V A s
  if L.card < u then exact L
  else exact L.filter fun P => q < actualBadPartnerDegree H V A s bad P

/-- Actual parent edges deleted through the finite set of occurring cores. -/
noncomputable def multilevelDeletedEdges
    (H : Family α) (V : Edge α) (C : Family α) (s u q : ℕ)
    (bad : Edge α → Edge α → Edge α → Prop) : Family α := by
  classical
  exact C.biUnion fun A => (cleanupTails H V A s u q bad).image (fun P => A ∪ P)

/-- Every deleted edge is an edge of the fixed parent family. -/
theorem multilevelDeletedEdges_subset_parent
    {H : Family α} {V : Edge α} {C : Family α} {s u q : ℕ}
    {bad : Edge α → Edge α → Edge α → Prop} :
    multilevelDeletedEdges H V C s u q bad ⊆ H := by
  classical
  intro E hE
  rcases Finset.mem_biUnion.mp hE with ⟨A, hA, hImg⟩
  rcases Finset.mem_image.mp hImg with ⟨P, hP, rfl⟩
  have hPLink : P ∈ actualCoreLink H V A s := by
    by_cases hLow : (actualCoreLink H V A s).card < u
    · simpa [cleanupTails, hLow] using hP
    · have hP' := hP
      simp [cleanupTails, hLow] at hP'
      exact hP'.1
  exact (mem_actualCoreLink.mp hPLink).2.2.2

/-- High fibers in a finite incidence system have total size controlled by
its total number of incidences. -/
theorem high_fiber_sum_bound {ι : Type*} [DecidableEq ι]
    (L : Finset ι) (f : ι → ℕ) (q : ℕ) :
    q * (L.filter fun x => q < f x).card ≤ ∑ x ∈ L, f x := by
  classical
  let B := L.filter fun x => q < f x
  calc
    q * B.card = ∑ x ∈ B, q := by simp [B, Finset.sum_const, mul_comm]
    _ ≤ ∑ x ∈ B, f x :=
      Finset.sum_le_sum fun x hx => Nat.le_of_lt (Finset.mem_filter.mp hx).2
    _ ≤ ∑ x ∈ L, f x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)

/-- Per-core scaled cleanup estimate. -/
theorem cleanup_core_scaled_bound
    (H : Family α) (V A : Edge α) (s u q : ℕ)
    (bad : Edge α → Edge α → Edge α → Prop) :
    q * (cleanupTails H V A s u q bad).card ≤
      q * u + ∑ P ∈ actualCoreLink H V A s,
        actualBadPartnerDegree H V A s bad P := by
  classical
  let L := actualCoreLink H V A s
  by_cases hLow : L.card < u
  · calc
      q * (cleanupTails H V A s u q bad).card = q * L.card := by
        simp [cleanupTails, L, hLow]
      _ ≤ q * u := Nat.mul_le_mul_left q (Nat.le_of_lt hLow)
      _ ≤ q * u + ∑ P ∈ L, actualBadPartnerDegree H V A s bad P :=
        Nat.le_add_right _ _
  · have hHeavy := high_fiber_sum_bound L
      (actualBadPartnerDegree H V A s bad) q
    simpa [cleanupTails, L, hLow] using
      hHeavy.trans (Nat.le_add_left _ _)

/-- A retained parent-link vertex at a core of size at least `u` has no more
than `q` exceptional partners in the parent link. -/
theorem retained_tail_exception_degree_le
    (H : Family α) (V A P : Edge α) (s u q : ℕ)
    (bad : Edge α → Edge α → Edge α → Prop)
    (hPL : P ∈ actualCoreLink H V A s)
    (hLarge : u ≤ (actualCoreLink H V A s).card)
    (hKeep : P ∉ cleanupTails H V A s u q bad) :
    actualBadPartnerDegree H V A s bad P ≤ q := by
  classical
  have hNotLow : ¬ (actualCoreLink H V A s).card < u := by omega
  have hKeep' : ¬ (P ∈ actualCoreLink H V A s ∧
      q < actualBadPartnerDegree H V A s bad P) := by
    simpa [cleanupTails, hNotLow] using hKeep
  have hbad : ¬ q < actualBadPartnerDegree H V A s bad P := by
    intro hbad
    exact hKeep' ⟨hPL, hbad⟩
  omega

/-- Among the other link vertices of a retained high-degree tail, at least
`m - 1 - q` are nonexceptional, where `m` is the parent link degree. -/
theorem retained_tail_good_partner_count
    (H : Family α) (V A P : Edge α) (s u q : ℕ)
    (bad : Edge α → Edge α → Edge α → Prop)
    (hPL : P ∈ actualCoreLink H V A s)
    (hLarge : u ≤ (actualCoreLink H V A s).card)
    (hKeep : P ∉ cleanupTails H V A s u q bad) :
    (actualCoreLink H V A s).card ≤ 1 + q +
      (actualGoodOtherPartners H V A P s bad).card := by
  classical
  let L := actualCoreLink H V A s
  let badQ := L.filter fun Q => bad A P Q
  let goodQ := actualGoodOtherPartners H V A P s bad
  have hd := retained_tail_exception_degree_le H V A P s u q bad hPL hLarge hKeep
  have hCover : L.erase P ⊆ badQ ∪ goodQ := by
    intro Q hQ
    by_cases hb : bad A P Q
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_of_mem_erase hQ, hb⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hQ, hb⟩)
  have hErase : (L.erase P).card + 1 = L.card := Finset.card_erase_add_one hPL
  have hCard : (L.erase P).card ≤ badQ.card + goodQ.card :=
    (Finset.card_le_card hCover).trans (Finset.card_union_le ..)
  have hBadQ : badQ.card = actualBadPartnerDegree H V A s bad P := by
    simp [badQ, actualBadPartnerDegree, L]
  rw [hBadQ] at hCard
  change L.card ≤ 1 + q + goodQ.card
  omega

/-- IV.7.3 finite multilevel deletion bound in scaled form. The premise is
an aggregate count of ordered exceptional partner incidences, supplied by
IV.6.2 from the uncolored-edge and bicolored-triangle totals. -/
theorem multilevel_cleanup_scaled_budget
    (H : Family α) (V : Edge α) (C : Family α) (s u q exceptionBudget : ℕ)
    (bad : Edge α → Edge α → Edge α → Prop)
    (hAggregate :
      ∑ A ∈ C,
        (∑ P ∈ actualCoreLink H V A s,
          actualBadPartnerDegree H V A s bad P) ≤ exceptionBudget) :
    q * (multilevelDeletedEdges H V C s u q bad).card ≤
      q * C.card * u + exceptionBudget := by
  classical
  let tails := fun A => cleanupTails H V A s u q bad
  let edgeSets := fun A => (tails A).image (fun P => A ∪ P)
  have hUnion : (C.biUnion edgeSets).card ≤ ∑ A ∈ C, (edgeSets A).card :=
    Finset.card_biUnion_le
  have hCore A : q * (tails A).card ≤
      q * u + ∑ P ∈ actualCoreLink H V A s,
        actualBadPartnerDegree H V A s bad P :=
    cleanup_core_scaled_bound H V A s u q bad
  have hSum : q * (∑ A ∈ C, (tails A).card) ≤
      q * C.card * u + exceptionBudget := by
    calc
      q * (∑ A ∈ C, (tails A).card) = ∑ A ∈ C, q * (tails A).card := by
        simp [Finset.mul_sum]
      _ ≤ ∑ A ∈ C,
          (q * u + ∑ P ∈ actualCoreLink H V A s,
            actualBadPartnerDegree H V A s bad P) :=
        Finset.sum_le_sum fun A hA => hCore A
      _ = q * C.card * u +
          ∑ A ∈ C, (∑ P ∈ actualCoreLink H V A s,
            actualBadPartnerDegree H V A s bad P) := by
          simp [Finset.sum_add_distrib, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ q * C.card * u + exceptionBudget := Nat.add_le_add_left hAggregate _
  calc
    q * (multilevelDeletedEdges H V C s u q bad).card
        ≤ q * (C.biUnion edgeSets).card := by
          simp [multilevelDeletedEdges, edgeSets, tails]
    _ ≤ q * ∑ A ∈ C, (edgeSets A).card := Nat.mul_le_mul_left q hUnion
    _ ≤ q * ∑ A ∈ C, (tails A).card :=
      Nat.mul_le_mul_left q (Finset.sum_le_sum fun A hA => Finset.card_image_le)
    _ ≤ q * C.card * u + exceptionBudget := hSum

/-- IV.7.3 budget with aggregate uncolored and bicolored-triangle counts.
The premise is the cross-multiplied form of the IV.6.2 exception estimate:
the total directed bad-partner incidence is at most
`C * (B + T / (u - 2))`. -/
theorem multilevel_cleanup_from_exception_aggregate
    (H : Family α) (V : Edge α) (Cores : Family α)
    (s u q B T C₀ : ℕ)
    (bad : Edge α → Edge α → Edge α → Prop) (_hu : 2 ≤ u)
    (hAggregate :
      (u - 2) *
          (∑ A ∈ Cores,
            ∑ P ∈ actualCoreLink H V A s,
              actualBadPartnerDegree H V A s bad P) ≤
        C₀ * ((u - 2) * B + T)) :
    (u - 2) *
        (q * (multilevelDeletedEdges H V Cores s u q bad).card) ≤
      (u - 2) * (q * Cores.card * u) + C₀ * ((u - 2) * B + T) := by
  have hCore := multilevel_cleanup_scaled_budget H V Cores s u q
    (∑ A ∈ Cores,
      ∑ P ∈ actualCoreLink H V A s,
        actualBadPartnerDegree H V A s bad P) bad (le_rfl)
  have h := Nat.mul_le_mul_left (u - 2) hCore
  calc
    (u - 2) *
        (q * (multilevelDeletedEdges H V Cores s u q bad).card)
        ≤ (u - 2) * (q * Cores.card * u) +
            (u - 2) *
              (∑ A ∈ Cores,
                ∑ P ∈ actualCoreLink H V A s,
                  actualBadPartnerDegree H V A s bad P) := by
          simpa [Nat.mul_add] using h
    _ ≤ (u - 2) * (q * Cores.card * u) +
          C₀ * ((u - 2) * B + T) := Nat.add_le_add_left hAggregate _

end JSP523.Rank5
