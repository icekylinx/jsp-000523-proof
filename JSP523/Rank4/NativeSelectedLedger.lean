import JSP523.Rank4.NativePairLink

/-!
# Selected pair links and native degree excess

This file isolates the local part of (III.B.8): selection can only
decrease pair-link common-neighbor multiplicity, and it preserves all
positive excess at an on-label native vertex when its relevant facets
are selected.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Restrict the ordinary pair link to a finite set of eligible
vertices. -/
def selectedRawPairLinkGraph
    (K : Family α) (U Q : Edge α) (S : Finset α) : SimpleGraph α where
  Adj a b := (rawPairLinkGraph K U Q).Adj a b ∧ a ∈ S ∧ b ∈ S
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by
    intro a h
    exact (rawPairLinkGraph K U Q).loopless.irrefl a h.1⟩

instance selectedRawPairLinkGraphDecidableRel
    (K : Family α) (U Q : Edge α) (S : Finset α) :
    DecidableRel (selectedRawPairLinkGraph K U Q S).Adj :=
  inferInstanceAs (DecidableRel (fun a b : α =>
    (rawPairLinkGraph K U Q).Adj a b ∧ a ∈ S ∧ b ∈ S))

omit [Fintype α] in
@[simp] theorem selectedRawPairLinkGraph_adj
    (K : Family α) (U Q : Edge α) (S : Finset α) (a b : α) :
    (selectedRawPairLinkGraph K U Q S).Adj a b ↔
      (rawPairLinkGraph K U Q).Adj a b ∧ a ∈ S ∧ b ∈ S :=
  Iff.rfl

omit [DecidableEq α] in
/-- Common-neighbor counts depend only on adjacency, even when two
graph presentations use different decidability instances. -/
theorem graph_common_multiplicity_congr
    (F G : SimpleGraph α) [DecidableRel F.Adj]
    [DecidableRel G.Adj]
    (hAdj : ∀ x y, F.Adj x y ↔ G.Adj x y)
    (a b : α) :
    graphCommonMultiplicity F a b =
      graphCommonMultiplicity G a b := by
  classical
  unfold graphCommonMultiplicity
  congr 1
  ext x
  simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  exact and_congr (hAdj a x) (hAdj b x)

/-- Selected pair-link common neighbors form a subset of the ordinary
pair-link common neighbors. -/
theorem selected_raw_pair_common_multiplicity_le
    (K : Family α) (U Q : Edge α) (S : Finset α)
    (a b : α) :
    graphCommonMultiplicity (selectedRawPairLinkGraph K U Q S) a b ≤
      graphCommonMultiplicity (rawPairLinkGraph K U Q) a b := by
  classical
  let F := rawPairLinkGraph K U Q
  let G := selectedRawPairLinkGraph K U Q S
  unfold graphCommonMultiplicity
  apply Finset.card_le_card
  intro x hx
  have hx' := Finset.mem_filter.mp hx
  have hax : G.Adj a x := by
    simpa only [SimpleGraph.mem_neighborFinset] using hx'.1
  have hbx : G.Adj b x := hx'.2
  have haxF : F.Adj a x := hax.1
  have hbxF : F.Adj b x := hbx.1
  exact Finset.mem_filter.mpr
    ⟨by simpa only [SimpleGraph.mem_neighborFinset] using haxF, hbxF⟩

/-- If all ordinary common neighbors survive together with both
endpoints, selection preserves the exact multiplicity. -/
theorem selected_raw_pair_common_multiplicity_eq_of_saturation
    (K : Family α) (U Q : Edge α) (S : Finset α)
    (a b : α)
    (haS : a ∈ S) (hbS : b ∈ S)
    (hNeighbors : ∀ x,
      (rawPairLinkGraph K U Q).Adj a x →
      (rawPairLinkGraph K U Q).Adj b x → x ∈ S) :
    graphCommonMultiplicity (selectedRawPairLinkGraph K U Q S) a b =
      graphCommonMultiplicity (rawPairLinkGraph K U Q) a b := by
  classical
  let F := rawPairLinkGraph K U Q
  let G := selectedRawPairLinkGraph K U Q S
  have hSet :
      (G.neighborFinset a).filter (fun x => G.Adj b x) =
        (F.neighborFinset a).filter (fun x => F.Adj b x) := by
    ext x
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hax, hbx⟩
      exact ⟨hax.1, hbx.1⟩
    · rintro ⟨hax, hbx⟩
      have hxS := hNeighbors x hax hbx
      exact ⟨⟨hax, haS, hxS⟩, ⟨hbx, hbS, hxS⟩⟩
  unfold graphCommonMultiplicity
  exact congrArg Finset.card hSet

/-- The off-label selected multiplicity is at most one when a used
completion pair has a fixed center. -/
theorem selected_raw_pair_common_multiplicity_le_one_off_label
    (K : Family α) (U Q : Edge α) (S : Finset α)
    (hUniform : Uniform 4 K)
    (hQ : Q ∈ U.powersetCard 2)
    (a b z : α)
    (haU : a ∈ U) (hbU : b ∈ U)
    (hab : a ≠ b) (hzQ : z ∉ Q)
    (hCenter : ∀ T ∈ commonRootCell K U ({a, b} : Edge α),
      z ∈ T) :
    graphCommonMultiplicity (selectedRawPairLinkGraph K U Q S) a b ≤ 1 := by
  exact (selected_raw_pair_common_multiplicity_le K U Q S a b).trans
    (raw_pair_common_multiplicity_le_one_off_label
      K U Q hUniform hQ a b z haU hbU hab hzQ hCenter)

/-- On a pair containing the completion-pair label, saturated
selection preserves the precise native vertex degree. -/
theorem selected_raw_pair_common_multiplicity_eq_native_degree
    (K : Family α) (U : Edge α) (S : Finset α)
    (hUniform : Uniform 4 K)
    (a b z w : α)
    (haU : a ∈ U) (hbU : b ∈ U)
    (hzU : z ∈ U) (hwU : w ∈ U)
    (hab : a ≠ b) (hzw : z ≠ w)
    (haQ : a ∉ ({z, w} : Edge α))
    (hbQ : b ∉ ({z, w} : Edge α))
    (haS : a ∈ S) (hbS : b ∈ S)
    (hNeighbors : ∀ x,
      (rawPairLinkGraph K U ({z, w} : Edge α)).Adj a x →
      (rawPairLinkGraph K U ({z, w} : Edge α)).Adj b x → x ∈ S) :
    graphCommonMultiplicity
        (selectedRawPairLinkGraph K U ({z, w} : Edge α) S) a b =
      (nativeTailGraph K U ({a, b} : Edge α) z).degree w := by
  rw [selected_raw_pair_common_multiplicity_eq_of_saturation
    K U ({z, w} : Edge α) S a b haS hbS hNeighbors]
  exact raw_pair_common_multiplicity_eq_native_degree K U hUniform
    a b z w haU hbU hzU hwU hab hzw haQ hbQ

/-- The local positive-excess identity needs selection saturation only
when the native degree is at least two. Degree-zero and degree-one
vertices contribute no excess. -/
theorem selected_raw_pair_common_excess_eq_native_excess
    (K : Family α) (U : Edge α) (S : Finset α)
    (hUniform : Uniform 4 K)
    (a b z w : α)
    (haU : a ∈ U) (hbU : b ∈ U)
    (hzU : z ∈ U) (hwU : w ∈ U)
    (hab : a ≠ b) (hzw : z ≠ w)
    (haQ : a ∉ ({z, w} : Edge α))
    (hbQ : b ∉ ({z, w} : Edge α))
    (hSat : 2 ≤ (nativeTailGraph K U ({a, b} : Edge α) z).degree w →
      a ∈ S ∧ b ∈ S ∧
        ∀ x,
          (rawPairLinkGraph K U ({z, w} : Edge α)).Adj a x →
          (rawPairLinkGraph K U ({z, w} : Edge α)).Adj b x → x ∈ S) :
    graphCommonMultiplicity
        (selectedRawPairLinkGraph K U ({z, w} : Edge α) S) a b - 1 =
      (nativeTailGraph K U ({a, b} : Edge α) z).degree w - 1 := by
  let d := (nativeTailGraph K U ({a, b} : Edge α) z).degree w
  by_cases hHigh : 2 ≤ d
  · obtain ⟨haS, hbS, hNeighbors⟩ := hSat hHigh
    rw [selected_raw_pair_common_multiplicity_eq_native_degree
      K U S hUniform a b z w haU hbU hzU hwU
      hab hzw haQ hbQ haS hbS hNeighbors]
  · have hRaw := raw_pair_common_multiplicity_eq_native_degree
      K U hUniform a b z w haU hbU hzU hwU hab hzw haQ hbQ
    have hSelected := selected_raw_pair_common_multiplicity_le
      K U ({z, w} : Edge α) S a b
    omega

end JSP523.Rank4
