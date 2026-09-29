import JSP523.Rank5.HigherRankPartnerRetention

/-! # Actual core cleanup retention for arbitrary root size -/
namespace JSP523.Rank5
variable {α : Type*} [DecidableEq α]

theorem retained_core_root_survives_multilevel_cleanup
    (K H : Family α) (V : Edge α) (C : Family α)
    (s u q : ℕ) (bad : Edge α → Edge α → Edge α → Prop)
    (hKH : K ⊆ H)
    (hSurvive : Disjoint K (multilevelDeletedEdges H V C s u q bad))
    {B R : Edge α} (hBC : B ∈ C)
    (hR : R ∈ actualCoreLink K V B s) :
    R ∈ actualCoreLink H V B s ∧
      R ∉ cleanupTails H V B s u q bad := by
  classical
  have hParts := mem_actual_core_link.mp hR
  have hLinkH : R ∈ actualCoreLink H V B s :=
    mem_actual_core_link.mpr
      ⟨hParts.1, hParts.2.1, hParts.2.2.1, hKH hParts.2.2.2⟩
  refine ⟨hLinkH, ?_⟩
  intro hTail
  have hDeleted : B ∪ R ∈ multilevelDeletedEdges H V C s u q bad := by
    unfold multilevelDeletedEdges
    exact Finset.mem_biUnion.mpr
      ⟨B, hBC, Finset.mem_image.mpr ⟨R, hTail, rfl⟩⟩
  exact (Finset.disjoint_left.mp hSurvive) hParts.2.2.2 hDeleted

/-- Low-degree cores lose their entire links, so every surviving root
    certifies the parent degree threshold. -/
theorem retained_core_root_parent_degree_ge
    (K H : Family α) (V : Edge α) (C : Family α)
    (s u q : ℕ) (bad : Edge α → Edge α → Edge α → Prop)
    (hKH : K ⊆ H)
    (hSurvive : Disjoint K (multilevelDeletedEdges H V C s u q bad))
    {B R : Edge α} (hBC : B ∈ C)
    (hR : R ∈ actualCoreLink K V B s) :
    u ≤ (actualCoreLink H V B s).card := by
  classical
  have hKeep := retained_core_root_survives_multilevel_cleanup
    K H V C s u q bad hKH hSurvive hBC hR
  by_contra h
  have hLow : (actualCoreLink H V B s).card < u := Nat.lt_of_not_ge h
  exact hKeep.2 (by simpa [cleanupTails, hLow] using hKeep.1)

theorem actual_rank_labels_of_core_cleanup
    (K H : Family α) (V : Edge α) (n s t u q : ℕ)
    (tripleLabel : Edge α → α)
    (hKH : K ⊆ H) (hUniformK : Uniform (n + s) K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V) (hqu : q < u)
    (hSurvive : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard n) s u q
        (fun B R T => ¬ ActualStrongPartner H V R T s n t
          (tripleLabel B)))) : ActualRankLabels K n tripleLabel := by
  classical
  intro B hB hBcard
  obtain ⟨E, hEK, hBE⟩ := hB
  have hBV : B ⊆ V := hBE.trans (hAmbientK E hEK)
  have hBC : B ∈ V.powersetCard n := Finset.mem_powersetCard.mpr ⟨hBV, hBcard⟩
  let R := E \ B
  have hRcard : R.card = s := by
    dsimp [R]
    rw [Finset.card_sdiff_of_subset hBE, hUniformK hEK, hBcard]
    omega
  have hRecon : B ∪ R = E := Finset.union_sdiff_of_subset hBE
  have hR : R ∈ actualCoreLink K V B s := mem_actual_core_link.mpr
    ⟨Finset.sdiff_subset.trans (hAmbientK E hEK), hRcard,
      Finset.sdiff_disjoint, hRecon.symm ▸ hEK⟩
  let bad := fun B R T => ¬ ActualStrongPartner H V R T s n t (tripleLabel B)
  have hKeep := retained_core_root_survives_multilevel_cleanup K H V
    (V.powersetCard n) s u q bad hKH hSurvive hBC hR
  have hDegree := retained_core_root_parent_degree_ge K H V
    (V.powersetCard n) s u q bad hKH hSurvive hBC hR
  have hBad := retained_tail_exception_degree_le H V B R s u q bad
    hKeep.1 hDegree hKeep.2
  by_contra hz
  have hAll : ∀ T ∈ actualCoreLink H V B s, bad B R T := by
    intro T hT hStrong
    have hp := mem_actual_core_link.mp hKeep.1
    have ht := mem_actual_core_link.mp hT
    have hCell : B ∈ commonPrefixTails H V R T n :=
      mem_common_prefix_tails.mpr ⟨hBV, hBcard,
        Finset.disjoint_union_right.mpr ⟨hp.2.2.1.symm, ht.2.2.1.symm⟩,
        by simpa only [Finset.union_comm] using hp.2.2.2,
        by simpa only [Finset.union_comm] using ht.2.2.2⟩
    exact hz (hStrong.2.2.2.1 B hCell)
  have hBadEq : actualBadPartnerDegree H V B s bad R =
      (actualCoreLink H V B s).card := by
    unfold actualBadPartnerDegree
    congr 1
    ext T
    simp only [Finset.mem_filter]
    exact ⟨And.left, fun hT => ⟨hT, hAll T hT⟩⟩
  rw [hBadEq] at hBad
  omega

end JSP523.Rank5
