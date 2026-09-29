import JSP523.Rank4.PreprocessStarAllocation
import JSP523.Rank4.GlobalNearStarThreshold
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-! # Extracting one original center from the actual cleaned star mass

The integer allocation theorem loses only a quadratic term. A cubic Young
inequality removes the cube root from the final stability estimate.
-/
namespace JSP523.Rank4

private theorem cubic_young_nat (q N : ℕ) : 3 * q * N ^ 2 ≤ q ^ 3 + 2 * N ^ 3 := by
  have h : (0 : ℤ) ≤ ((q : ℤ) - N) ^ 2 * ((q : ℤ) + 2 * N) := by positivity
  have hR : 3 * (q : ℤ) * (N : ℤ) ^ 2 ≤ (q : ℤ) ^ 3 + 2 * (N : ℤ) ^ 3 := by
    nlinarith only [h]
  exact_mod_cast hR

/-- Near saturation of the separated pair shadows forces a large original
link. The index belongs to the original center set. -/
theorem actual_cleaned_star_single_large_link
    {n : ℕ} {ι : Type*} [DecidableEq ι]
    (V : Edge (Fin n)) (I : Finset ι) (L : ι → Family (Fin n))
    (owner : Edge (Fin n) → ι) (hI : I.Nonempty)
    (hGround : ∀ i ∈ I, ∀ T ∈ L i, T ∈ V.powersetCard 3) :
    ∃ i ∈ I, 18 * (∑ j ∈ I, (pairOwnerCleanedLink L owner j).card) ≤
      6 * (L i).card + 2 * V.card ^ 3 + 12 * V.card ^ 2 := by
  classical
  obtain ⟨i, hi, hMax⟩ := Finset.exists_max_image I (fun j => (L j).card) hI
  let q := Nat.nthRoot 3 (6 * (L i).card)
  have hRoot : q ^ 3 ≤ 6 * (L i).card := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hNext : 6 * (L i).card < (q + 1) ^ 3 := Nat.lt_pow_nthRoot_add_one (by decide) _
  have hSize : ∀ j ∈ I, 6 * (L j).card ≤ (q + 1) ^ 3 := by
    intro j hj
    exact (Nat.mul_le_mul_left 6 (hMax j hj)).trans hNext.le
  have hAlloc := actual_cleaned_star_allocation V I L owner (q + 1) hGround hSize
  have hPairs : 2 * V.card.choose 2 ≤ V.card ^ 2 := by
    have h := Nat.descFactorial_le_pow V.card 2
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h
    simpa only [Nat.factorial] using h
  have hScale := Nat.mul_le_mul_left (q + 4) hPairs
  have hMass : 6 * (∑ j ∈ I, (pairOwnerCleanedLink L owner j).card) ≤
      (q + 4) * V.card ^ 2 := by nlinarith only [hAlloc, hScale]
  refine ⟨i, hi, ?_⟩
  have hYoung := cubic_young_nat q V.card
  nlinarith only [hMass, hYoung, hRoot]

/-- Every original link injects into the original star at its own center. -/
theorem actual_original_link_plus_outside_le_parent
    {n : ℕ} (H : Family (Fin n)) (V : Edge (Fin n)) (c : Fin n)
    (L : Family (Fin n)) (hc : c ∉ V)
    (hGround : ∀ T ∈ L, T ∈ V.powersetCard 3)
    (hEdges : ∀ T ∈ L, insert c T ∈ H) :
    L.card + (outsideEdges H (Finset.univ.erase c)).card ≤ H.card := by
  classical
  have hInject : L.card ≤ (H.filter fun E => c ∈ E).card := by
    apply Finset.card_le_card_of_injOn (fun T => insert c T)
    · intro T hT
      exact Finset.mem_filter.mpr ⟨hEdges T hT, Finset.mem_insert_self ..⟩
    · intro T hT S hS hEq
      have hcT : c ∉ T := fun hh => hc ((Finset.mem_powersetCard.mp (hGround T hT)).1 hh)
      have hcS : c ∉ S := fun hh => hc ((Finset.mem_powersetCard.mp (hGround S hS)).1 hh)
      have hErase := congrArg (Finset.erase · c) hEq
      simpa only [Finset.erase_insert hcT, Finset.erase_insert hcS] using hErase
  have hOutside : outsideEdges H (Finset.univ.erase c) = H.filter (fun E => c ∉ E) := by
    ext E
    simp [outsideEdges, Finset.subset_erase]
  rw [hOutside]
  have hPartition := Finset.card_filter_add_card_filter_not (s := H)
    (fun E : Edge (Fin n) => c ∈ E)
  omega

/-- A direct finite III.B.5 stability estimate, referring only to original
centers and original parent edges. -/
theorem actual_original_single_center_outside_bound
    {n : ℕ} (H : Family (Fin n)) (V centers : Edge (Fin n))
    (L : Fin n → Family (Fin n)) (owner : Edge (Fin n) → Fin n)
    (deficit loss : ℕ) (hCenters : centers.Nonempty)
    (hOutside : ∀ c ∈ centers, c ∉ V)
    (hGround : ∀ c ∈ centers, ∀ T ∈ L c, T ∈ V.powersetCard 3)
    (hEdges : ∀ c ∈ centers, ∀ T ∈ L c, insert c T ∈ H)
    (hNear : V.card ^ 3 ≤ 6 * H.card + deficit)
    (hMass : H.card ≤ (∑ c ∈ centers, (pairOwnerCleanedLink L owner c).card) + loss) :
    ∃ c ∈ centers, 6 * (outsideEdges H (Finset.univ.erase c)).card ≤
      2 * deficit + 18 * loss + 12 * V.card ^ 2 := by
  obtain ⟨c, hc, hLarge⟩ := actual_cleaned_star_single_large_link V centers L owner hCenters hGround
  have hStar := actual_original_link_plus_outside_le_parent H V c (L c)
    (hOutside c hc) (hGround c hc) (hEdges c hc)
  exact ⟨c, hc, by omega⟩

/-- The complete-star lower bound differs from the ambient cubic term by
only a fixed quadratic error. -/
theorem star_lower_supplies_cubic_deficit
    (n m N : ℕ) (hn : 2 ≤ n) (hN : N ≤ n + 1) (hLower : n.choose 3 ≤ m) :
    N ^ 3 ≤ 6 * m + 9 * (n + 1) ^ 2 := by
  have hDesc := Nat.pow_sub_le_descFactorial n 3
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hDesc
  have hBase : (n - 2) ^ 3 ≤ 6 * n.choose 3 := by
    simpa only [show n + 1 - 3 = n - 2 by omega, Nat.factorial] using hDesc
  have hShift : n = (n - 2) + 2 := by omega
  have hDiff : (n + 1) ^ 3 ≤ (n - 2) ^ 3 + 9 * (n + 1) ^ 2 := by
    nth_rw 1 [hShift]
    nth_rw 3 [hShift]
    nlinarith
  have hPow := Nat.pow_le_pow_left hN 3
  omega

/-- Above the star lower bound, the single-center error is at most three
times the actual decomposition loss, plus a quadratic term. -/
theorem actual_original_single_center_of_star_lower
    {n : ℕ} (H : Family (Fin (n + 1))) (V centers : Edge (Fin (n + 1)))
    (L : Fin (n + 1) → Family (Fin (n + 1))) (owner : Edge (Fin (n + 1)) → Fin (n + 1))
    (loss : ℕ) (hn : 2 ≤ n) (hCenters : centers.Nonempty)
    (hOutside : ∀ c ∈ centers, c ∉ V)
    (hGround : ∀ c ∈ centers, ∀ T ∈ L c, T ∈ V.powersetCard 3)
    (hEdges : ∀ c ∈ centers, ∀ T ∈ L c, insert c T ∈ H)
    (hLower : n.choose 3 ≤ H.card)
    (hMass : H.card ≤ (∑ c ∈ centers, (pairOwnerCleanedLink L owner c).card) + loss) :
    ∃ c ∈ centers, (outsideEdges H (Finset.univ.erase c)).card ≤
      3 * loss + 5 * (n + 1) ^ 2 := by
  have hV : V.card ≤ n + 1 := by simpa only [Fintype.card_fin] using Finset.card_le_univ V
  have hNear := star_lower_supplies_cubic_deficit n H.card V.card hn hV hLower
  obtain ⟨c, hc, hBound⟩ := actual_original_single_center_outside_bound H V centers L owner
    (9 * (n + 1) ^ 2) loss hCenters hOutside hGround hEdges hNear hMass
  have hSq := Nat.pow_le_pow_left hV 2
  exact ⟨c, hc, by nlinarith only [hBound, hSq]⟩

/-- The same original-center conclusion holds for genuinely near-extremal
families below the complete-star lower bound by a controlled deficit. -/
theorem actual_original_single_center_of_near_star_lower
    {n : ℕ} (H : Family (Fin (n + 1))) (V centers : Edge (Fin (n + 1)))
    (L : Fin (n + 1) → Family (Fin (n + 1))) (owner : Edge (Fin (n + 1)) → Fin (n + 1))
    (missing loss : ℕ) (hn : 2 ≤ n) (hCenters : centers.Nonempty)
    (hOutside : ∀ c ∈ centers, c ∉ V)
    (hGround : ∀ c ∈ centers, ∀ T ∈ L c, T ∈ V.powersetCard 3)
    (hEdges : ∀ c ∈ centers, ∀ T ∈ L c, insert c T ∈ H)
    (hLower : n.choose 3 ≤ H.card + missing)
    (hMass : H.card ≤ (∑ c ∈ centers, (pairOwnerCleanedLink L owner c).card) + loss) :
    ∃ c ∈ centers, (outsideEdges H (Finset.univ.erase c)).card ≤
      2 * missing + 3 * loss + 5 * (n + 1) ^ 2 := by
  have hV : V.card ≤ n + 1 := by simpa only [Fintype.card_fin] using Finset.card_le_univ V
  have hRaw := star_lower_supplies_cubic_deficit n (H.card + missing) V.card hn hV hLower
  have hNear : V.card ^ 3 ≤ 6 * H.card + (6 * missing + 9 * (n + 1) ^ 2) := by omega
  obtain ⟨c, hc, hBound⟩ := actual_original_single_center_outside_bound H V centers L owner
    (6 * missing + 9 * (n + 1) ^ 2) loss hCenters hOutside hGround hEdges hNear hMass
  have hSq := Nat.pow_le_pow_left hV 2
  exact ⟨c, hc, by nlinarith only [hBound, hSq]⟩

end JSP523.Rank4
