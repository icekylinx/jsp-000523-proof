import JSP523.Rank5.HigherRankConditionalGlobalEndpoint
import JSP523.Rank5.FinalNearStarBridge

/-!
# The global extremal theorem for every fixed rank at least five
-/

namespace JSP523.Rank5

open Filter

/-- For every fixed rank at least five, the exact maximum is the
complete-star size plus an outside matching. -/
theorem eventually_rank_at_least_five_extremal_exact
    (r : ℕ) (hr : 5 ≤ r) :
    ∀ᶠ n : ℕ in atTop,
      (∃ H : Family (Fin n), Admissible H ∧ Uniform r H ∧
        H.card = (n - 1).choose (r - 1) + (n - 1) / r) ∧
      (∀ H : Family (Fin n), Admissible H → Uniform r H →
        H.card ≤ (n - 1).choose (r - 1) + (n - 1) / r) := by
  have hδ := local_exact_density_pos r hr
  exact eventually_fixed_rank_extremal_exact_of_degree_concentration
    r hr (eventually_uniform_rank_at_least_five_degree_concentration
      r hr (localExactDensity r) hδ)


/-- The two equality patterns at a chosen center for any rank at least
five. -/
def rank_r_equality_form
    {n : ℕ} (H : Family (Fin n)) (v : Fin n) (r : ℕ) : Prop :=
  let W : Edge (Fin n) := Finset.univ.erase v
  ((missingStarFacets H W v r).card = 0 ∧
    IsMatching (outsideFamily H W) ∧
    (outsideFamily H W).card = W.card / r) ∨
  (∃ (P : Edge (Fin n)) (x : Fin n) (Q : Edge (Fin n))
      (M : Family (Fin n)),
    missingStarFacets H W v r = {P} ∧ P.card = r - 1 ∧
    W.card % r = r - 1 ∧
    x ∈ W ∧ x ∉ P ∧ Q.card = r - 1 ∧
    Disjoint P Q ∧ x ∉ Q ∧
    outsideFamily H W =
      insert (insert x P) (insert (insert x Q) M) ∧
    IsMatching M ∧
    (∀ E ∈ M, Disjoint E (insert x P ∪ insert x Q)) ∧
    M.biUnion (fun E => E) =
      W \ (insert x P ∪ insert x Q))

/-- Every sufficiently large extremizer has one of the two equality
forms in the exact local theorem. -/
theorem eventually_rank_at_least_five_extremal_classification
    (r : ℕ) (hr : 5 ≤ r) :
    ∀ᶠ n : ℕ in atTop, ∀ H : Family (Fin n),
      Admissible H → Uniform r H →
      H.card = (n - 1).choose (r - 1) + (n - 1) / r →
      ∃ v : Fin n, rank_r_equality_form H v r := by
  have hδ := local_exact_density_pos r hr
  have hCenter := eventually_uniform_rank_at_least_five_degree_concentration
    r hr (localExactDensity r) hδ
  filter_upwards [hCenter,
    eventually_ge_atTop (localExactGroundThreshold r + 1)]
    with n hCenterN hn
  intro H hAdm hUniform hEquality
  have hMass : (n - 1).choose (r - 1) ≤ H.card := by
    rw [hEquality]
    exact Nat.le_add_right _ _
  obtain ⟨v, hv⟩ := hCenterN H hAdm hUniform hMass
  let W : Edge (Fin n) := Finset.univ.erase v
  have hWcard : W.card = n - 1 := by simp [W]
  have hvW : v ∉ W := by simp [W]
  have hSupport : ∀ E ∈ H, E ⊆ insert v W := by
    intro E _ x hx
    by_cases hxv : x = v
    · exact hxv ▸ Finset.mem_insert_self v W
    · exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ x⟩)
  have hDensity := missing_star_density_of_high_vertex_degree
    H v hUniform hr hv.le
  have hw : localExactGroundThreshold r ≤ W.card := by
    rw [hWcard]
    omega
  have hEqualityW : H.card = W.card.choose (r - 1) + W.card / r := by
    simpa only [hWcard] using hEquality
  have hForms := quantitative_local_equality_classification
    H W v r hAdm hUniform hSupport hvW hr hw hDensity hEqualityW
  exact ⟨v, by simpa only [rank_r_equality_form, W] using hForms⟩

end JSP523.Rank5
