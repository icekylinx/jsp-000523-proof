import JSP523.Rank5.UniformDegreeGap
import JSP523.Rank5.FinalNearStarBridge
import JSP523.LowerConstruction

/-!
# The rank-five global upper bound

Uniform degree concentration puts every star-sized family in the
quantitative neighborhood of one vertex. The exact local theorem then
gives the sharp integer bound.
-/

namespace JSP523.Rank5

open Filter

/-- Every sufficiently large admissible five-uniform family obeys the
sharp star-plus-matching upper bound. -/
theorem eventually_rank_five_global_upper :
    ∀ᶠ n : ℕ in atTop, ∀ H : Family (Fin n),
      Admissible H → Uniform 5 H →
      H.card ≤ (n - 1).choose 4 + (n - 1) / 5 := by
  have hδ := local_exact_density_pos 5 (by omega)
  have hCenter := eventually_uniform_rank_five_degree_concentration
    (localExactDensity 5) hδ
  filter_upwards [hCenter,
    eventually_ge_atTop (localExactGroundThreshold 5 + 1)]
    with n hCenterN hn
  intro H hAdm hUniform
  by_cases hMass : (n - 1).choose 4 ≤ H.card
  · obtain ⟨v, hv⟩ := hCenterN H hAdm hUniform hMass
    exact near_star_exact_of_high_vertex_degree H v
      hAdm hUniform (by omega) hn hv.le
  · omega

/-- The exact extremal value is attained by a complete star together
with an outside matching. -/
theorem eventually_rank_five_extremal_exact :
    ∀ᶠ n : ℕ in atTop,
      (∃ H : Family (Fin n),
        Admissible H ∧ Uniform 5 H ∧
          H.card = (n - 1).choose 4 + (n - 1) / 5) ∧
      (∀ H : Family (Fin n), Admissible H → Uniform 5 H →
        H.card ≤ (n - 1).choose 4 + (n - 1) / 5) := by
  filter_upwards [eventually_rank_five_global_upper,
    eventually_ge_atTop 1] with n hUpper hn
  let v : Fin n := ⟨0, by omega⟩
  obtain ⟨H, hUniform, hAdm, hCard⟩ :=
    JSP523.exists_star_plus_matching_exact v 5 (by omega)
  refine ⟨⟨H, hAdm, hUniform, ?_⟩, hUpper⟩
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ v),
    Finset.card_univ, Fintype.card_fin,
    show 5 - 1 = 4 by omega] using hCard


/-- The two equality forms, relative to a center. -/
def rank_five_equality_form
    {n : ℕ} (H : Family (Fin n)) (v : Fin n) : Prop :=
  let W : Edge (Fin n) := Finset.univ.erase v
  ((missingStarFacets H W v 5).card = 0 ∧
    IsMatching (outsideFamily H W) ∧
    (outsideFamily H W).card = W.card / 5) ∨
  (∃ (P : Edge (Fin n)) (x : Fin n) (Q : Edge (Fin n))
      (M : Family (Fin n)),
    missingStarFacets H W v 5 = {P} ∧ P.card = 4 ∧
    W.card % 5 = 4 ∧
    x ∈ W ∧ x ∉ P ∧ Q.card = 4 ∧
    Disjoint P Q ∧ x ∉ Q ∧
    outsideFamily H W =
      insert (insert x P) (insert (insert x Q) M) ∧
    IsMatching M ∧
    (∀ E ∈ M, Disjoint E (insert x P ∪ insert x Q)) ∧
    M.biUnion (fun E => E) =
      W \ (insert x P ∪ insert x Q))

/-- Every sufficiently large extremizer has one of the two local
equality forms at some center. -/
theorem eventually_rank_five_extremal_classification :
    ∀ᶠ n : ℕ in atTop, ∀ H : Family (Fin n),
      Admissible H → Uniform 5 H →
      H.card = (n - 1).choose 4 + (n - 1) / 5 →
      ∃ v : Fin n, rank_five_equality_form H v := by
  have hδ := local_exact_density_pos 5 (by omega)
  have hCenter := eventually_uniform_rank_five_degree_concentration
    (localExactDensity 5) hδ
  filter_upwards [hCenter,
    eventually_ge_atTop (localExactGroundThreshold 5 + 1)]
    with n hCenterN hn
  intro H hAdm hUniform hEquality
  have hMass : (n - 1).choose 4 ≤ H.card := by omega
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
    H v hUniform (by omega : 5 ≤ 5) hv.le
  have hw : localExactGroundThreshold 5 ≤ W.card := by
    rw [hWcard]
    omega
  have hEqualityW : H.card = W.card.choose 4 + W.card / 5 := by
    simpa only [hWcard] using hEquality
  have hForms := quantitative_local_equality_classification
    H W v 5 hAdm hUniform hSupport hvW (by omega) hw hDensity hEqualityW
  exact ⟨v, by simpa only [rank_five_equality_form, W,
    show 5 - 1 = 4 by omega] using hForms⟩

end JSP523.Rank5
