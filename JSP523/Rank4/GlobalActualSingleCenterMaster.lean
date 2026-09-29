import JSP523.Rank4.GlobalActualSingleCenterEndpoint
import JSP523.Rank4.GlobalActualParentStability

/-! # The actual master surplus pays for single-center stability -/
namespace JSP523.Rank4

/-- Combine the actual parent-stability master with the original star
allocation. No independent small-core or single-center premise is supplied. -/
theorem actual_global_center_outside_of_master
    {n : ℕ} (H : Family (Fin (n + 1))) (V centers : Edge (Fin (n + 1)))
    (L : Fin (n + 1) → Family (Fin (n + 1))) (owner : Edge (Fin (n + 1)) → Fin (n + 1))
    (K B₁ : Family (Fin (n + 1))) (M N masterError highError outerLoss : ℕ)
    (hn : 2 ≤ n) (hUniform : Uniform 4 H)
    (hOutside : ∀ c ∈ centers, c ∉ V)
    (hGround : ∀ c ∈ centers, ∀ T ∈ L c, T ∈ V.powersetCard 3)
    (hEdges : ∀ c ∈ centers, ∀ T ∈ L c, insert c T ∈ H)
    (hLower : n.choose 3 ≤ H.card)
    (hOriginal : H.card ≤ (centers.biUnion (pairOwnerCleanedLink L owner)).card +
      (fixedDecompositionCore H V).card + outerLoss)
    (hK : K ⊆ fixedDecompositionCore H V) (hB₁ : B₁ ⊆ fixedDecompositionCore H V)
    (hM : 1 ≤ M)
    (hCap : ∀ T ∈ V.powersetCard 3, 2 * (facetCompletions B₁ V T).card ≤ M)
    (hMaster : 10 * H.card + (rankFourNonprivateFacets K V).card +
      6 * (rankFourAllPrivateEdges K V).card ≤ 10 * N + masterError)
    (hNearMaster : N ≤ H.card + highError) :
    (outsideEdges H (Finset.univ.erase (actualGlobalMainCenter H))).card ≤
      3 * M * (masterError + 10 * highError) +
      24 * (fixedDecompositionCore H V \ B₁).card +
      3 * (fixedDecompositionCore H V \ K).card + 3 * outerLoss + 5 * (n + 1) ^ 2 := by
  have hParent := actual_parent_stability_of_master (fixedDecompositionCore H V) K B₁ V
    M H.card N masterError highError hK hB₁
    (fun E hE => hUniform (Finset.mem_filter.mp hE).1)
    (fun _ hE => (Finset.mem_filter.mp hE).2) hM hCap hMaster hNearMaster
  have hCenter := actual_global_center_of_master_decomposition H V centers L owner outerLoss hn
    hOutside hGround hEdges hLower hOriginal
  have hScaled := Nat.mul_le_mul_left 3 hParent
  nlinarith only [hScaled, hCenter]

end JSP523.Rank4
