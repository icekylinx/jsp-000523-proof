import JSP523.Rank5.LocalEqualityExact
import JSP523.LowerConstruction

/-!
# From a high-degree vertex to the local exact theorem

This is the finite interface between degree stability and the exact
near-star bound.
-/

namespace JSP523.Rank5

/-- The present star facets at a vertex are exactly its edge link. -/
theorem present_star_facets_card_eq_vertex_degree
    {n r : ℕ} (H : Family (Fin n)) (v : Fin n)
    (hUniform : Uniform r H) :
    (presentStarFacets H (Finset.univ.erase v) v r).card =
      (H.filter fun E => v ∈ E).card := by
  classical
  let W : Edge (Fin n) := Finset.univ.erase v
  have hvW : v ∉ W := by simp [W]
  have hSupport : ∀ E ∈ H, E ⊆ insert v W := by
    intro E _ x hx
    by_cases hxv : x = v
    · exact hxv ▸ Finset.mem_insert_self v W
    · exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ x⟩)
  have hOutsideEq : outsideFamily H W =
      H.filter (fun E => v ∉ E) := by
    ext E
    simp only [outsideFamily, Finset.mem_filter]
    constructor
    · rintro ⟨hEH, hEW⟩
      refine ⟨hEH, ?_⟩
      intro hv
      exact (Finset.mem_erase.mp (hEW hv)).1 rfl
    · rintro ⟨hEH, hv⟩
      refine ⟨hEH, ?_⟩
      intro x hx
      exact Finset.mem_erase.mpr
        ⟨fun hxv => hv (hxv ▸ hx), Finset.mem_univ x⟩
  have hSplit := star_outside_card hUniform hSupport hvW
  have hPartition :=
    H.card_filter_add_card_filter_not (fun E => v ∈ E)
  have hSplit' : H.card =
      (presentStarFacets H W v r).card +
        (H.filter fun E => v ∉ E).card := by
    simpa only [hOutsideEq] using hSplit
  have hPartition' :
      (H.filter fun E => v ∈ E).card +
        (H.filter fun E => v ∉ E).card = H.card := by
    simpa only using hPartition
  exact Nat.add_right_cancel (hSplit'.symm.trans hPartition'.symm)

/-- A high-degree vertex has the required small missing-star density. -/
theorem missing_star_density_of_high_vertex_degree
    {n r : ℕ} (H : Family (Fin n)) (v : Fin n)
    (hUniform : Uniform r H)
    (hr : 5 ≤ r)
    (hDegree :
      (1 - localExactDensity r) *
        ((n - 1).choose (r - 1) : ℝ) ≤
          ((H.filter fun E => v ∈ E).card : ℝ)) :
    ((missingStarFacets H (Finset.univ.erase v) v r).card : ℝ) ≤
      localExactDensity r * ((Finset.univ.erase v : Edge (Fin n)).card : ℝ) ^
        (r - 1) := by
  classical
  let W : Edge (Fin n) := Finset.univ.erase v
  have hWcard : W.card = n - 1 := by simp [W]
  have hvW : v ∉ W := by simp [W]
  have hSupport : ∀ E ∈ H, E ⊆ insert v W := by
    intro E _ x hx
    by_cases hxv : x = v
    · exact hxv ▸ Finset.mem_insert_self v W
    · exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ x⟩)
  have hPresent := present_star_facets_card_eq_vertex_degree H v hUniform
  have hPresentW : (presentStarFacets H W v r).card =
      (H.filter fun E => v ∈ E).card := by
    simpa only [W] using hPresent
  have hFacet := present_add_missing_star_facets H W v r
  have hFacetR : ((presentStarFacets H W v r).card : ℝ) +
      ((missingStarFacets H W v r).card : ℝ) =
        (W.card.choose (r - 1) : ℝ) := by exact_mod_cast hFacet
  have hPow : (W.card.choose (r - 1) : ℝ) ≤
      (W.card : ℝ) ^ (r - 1) := by
    exact_mod_cast Nat.choose_le_pow W.card (r - 1)
  have hδpos := local_exact_density_pos r hr
  have hδnonneg : 0 ≤ localExactDensity r := hδpos.le
  have hDegree' :
      (1 - localExactDensity r) * (W.card.choose (r - 1) : ℝ) ≤
        ((presentStarFacets H W v r).card : ℝ) := by
    simpa only [hWcard, hPresentW] using hDegree
  have hMult := mul_le_mul_of_nonneg_left hPow hδnonneg
  nlinarith [hFacetR, hDegree', hMult]

/-- A vertex whose degree is within the explicit local density of the
complete star forces the sharp near-star cardinal bound. -/
theorem near_star_exact_of_high_vertex_degree
    {n r : ℕ} (H : Family (Fin n)) (v : Fin n)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 5 ≤ r)
    (hn : localExactGroundThreshold r + 1 ≤ n)
    (hDegree :
      (1 - localExactDensity r) *
        ((n - 1).choose (r - 1) : ℝ) ≤
          ((H.filter fun E => v ∈ E).card : ℝ)) :
    H.card ≤ (n - 1).choose (r - 1) + (n - 1) / r := by
  classical
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
    H v hUniform hr hDegree
  have hw : localExactGroundThreshold r ≤ W.card := by
    rw [hWcard]
    omega
  have hFinal := quantitative_near_star_exact H W v r
    hAdm hUniform hSupport hvW hr hw hDensity
  simpa only [hWcard] using hFinal


/-- A uniform high-degree conclusion at a fixed rank closes the global
upper bound through the finite local theorem. -/
theorem eventually_fixed_rank_global_upper_of_degree_concentration
    (r : ℕ) (hr : 5 ≤ r)
    (hCenter :
      ∀ᶠ n : ℕ in Filter.atTop, ∀ H : Family (Fin n),
        Admissible H → Uniform r H →
        (n - 1).choose (r - 1) ≤ H.card →
        ∃ v : Fin n,
          (1 - localExactDensity r) *
              ((n - 1).choose (r - 1) : ℝ) <
            ((H.filter fun E => v ∈ E).card : ℝ)) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ H : Family (Fin n),
      Admissible H → Uniform r H →
      H.card ≤ (n - 1).choose (r - 1) + (n - 1) / r := by
  filter_upwards [hCenter,
    Filter.eventually_ge_atTop (localExactGroundThreshold r + 1)]
    with n hCenterN hn
  intro H hAdm hUniform
  by_cases hMass : (n - 1).choose (r - 1) ≤ H.card
  · obtain ⟨v, hv⟩ := hCenterN H hAdm hUniform hMass
    exact near_star_exact_of_high_vertex_degree H v
      hAdm hUniform hr hn hv.le
  · exact (Nat.lt_of_not_ge hMass).le.trans (Nat.le_add_right _ _)


/-- The star-plus-matching construction and a uniform high-degree
conclusion determine the exact extremal value at any fixed rank. -/
theorem eventually_fixed_rank_extremal_exact_of_degree_concentration
    (r : ℕ) (hr : 5 ≤ r)
    (hCenter :
      ∀ᶠ n : ℕ in Filter.atTop, ∀ H : Family (Fin n),
        Admissible H → Uniform r H →
        (n - 1).choose (r - 1) ≤ H.card →
        ∃ v : Fin n,
          (1 - localExactDensity r) *
              ((n - 1).choose (r - 1) : ℝ) <
            ((H.filter fun E => v ∈ E).card : ℝ)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (∃ H : Family (Fin n), Admissible H ∧ Uniform r H ∧
        H.card = (n - 1).choose (r - 1) + (n - 1) / r) ∧
      (∀ H : Family (Fin n), Admissible H → Uniform r H →
        H.card ≤ (n - 1).choose (r - 1) + (n - 1) / r) := by
  have hUpper := eventually_fixed_rank_global_upper_of_degree_concentration
    r hr hCenter
  filter_upwards [hUpper, Filter.eventually_ge_atTop 1]
    with n hUpperN hn
  let v : Fin n := ⟨0, by omega⟩
  obtain ⟨H, hUniform, hAdm, hCard⟩ :=
    JSP523.exists_star_plus_matching_exact v r (by omega)
  refine ⟨⟨H, hAdm, hUniform, ?_⟩, hUpperN⟩
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ v),
    Finset.card_univ, Fintype.card_fin] using hCard

end JSP523.Rank5
