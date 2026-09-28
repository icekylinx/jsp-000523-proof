import JSP523.Rank4.GraphActualExcessSupport
import JSP523.Rank4.NativeOnLabelSum

/-!
# Reindexing actual on-label base pairs

For a used completion pair `P` with unique label `z`, every valid base
pair containing `z` and disjoint from `P` is uniquely `{z,w}` with a
native tail vertex `w`.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- The base pairs containing the chosen label and disjoint from a used
completion pair are precisely the pairs obtained from admissible native
tail vertices. -/
theorem on_label_pair_bases_eq_tail_image
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground)
    (P : Edge α) (hUsed : P ∈ nonemptyCommonRoots D.K D.ground) :
    let z := chosenCommonRootLabel D.K D.ground fallback hCenters P
    (D.ground \ insert z P).image
      (fun w => ({z, w} : Edge α)) =
      (D.ground.powersetCard 2).filter
        (fun Q => z ∈ Q ∧ Disjoint Q P) := by
  classical
  dsimp only
  let z := chosenCommonRootLabel D.K D.ground fallback hCenters P
  change (D.ground \ insert z P).image
      (fun w => ({z, w} : Edge α)) =
    (D.ground.powersetCard 2).filter
      (fun Q => z ∈ Q ∧ Disjoint Q P)
  have hzU : z ∈ D.ground :=
    (chosen_common_root_label_valid
      D.K D.ground fallback hCenters P hUsed).1
  have hzP : z ∉ P :=
    (chosen_common_root_label_valid
      D.K D.ground fallback hCenters P hUsed).2
  ext Q
  constructor
  · intro hQ
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hQ
    have hw' := Finset.mem_sdiff.mp hw
    have hwU : w ∈ D.ground := hw'.1
    have hwz : w ≠ z := by
      intro h
      subst w
      exact hw'.2 (Finset.mem_insert_self z P)
    have hwP : w ∉ P := by
      intro h
      exact hw'.2 (Finset.mem_insert_of_mem h)
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      refine ⟨?_, Finset.card_pair hwz.symm⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hzU
      · exact (Finset.mem_singleton.mp ht) ▸ hwU
    · constructor
      · exact Finset.mem_insert_self z _
      · apply Finset.disjoint_left.mpr
        intro t ht htP
        rcases Finset.mem_insert.mp ht with htz | htw
        · exact hzP (htz ▸ htP)
        · exact hwP ((Finset.mem_singleton.mp htw) ▸ htP)
  · intro hQ
    obtain ⟨hQpair, hzQ, hDisj⟩ := Finset.mem_filter.mp hQ
    have hQ' := Finset.mem_powersetCard.mp hQpair
    have hEraseCard : (Q.erase z).card = 1 := by
      rw [Finset.card_erase_of_mem hzQ, hQ'.2]
    obtain ⟨w, hwEq⟩ := Finset.card_eq_one.mp hEraseCard
    have hwErase : w ∈ Q.erase z := by simp [hwEq]
    have hwQ : w ∈ Q := (Finset.mem_erase.mp hwErase).2
    have hwz : w ≠ z := (Finset.mem_erase.mp hwErase).1
    have hwU : w ∈ D.ground := hQ'.1 hwQ
    have hwP : w ∉ P := by
      intro hwP
      exact (Finset.disjoint_left.mp hDisj) hwQ hwP
    have hwTail : w ∈ D.ground \ insert z P :=
      Finset.mem_sdiff.mpr
        ⟨hwU, by
          intro hIns
          rcases Finset.mem_insert.mp hIns with hwz' | hwP'
          · exact hwz hwz'
          · exact hwP hwP'⟩
    have hQeq : Q = ({z, w} : Edge α) := by
      calc
        Q = insert z (Q.erase z) := (Finset.insert_erase hzQ).symm
        _ = {z, w} := by rw [hwEq]
    apply Finset.mem_image.mpr
    exact ⟨w, hwTail, hQeq.symm⟩

omit [Fintype α] in
/-- The map from an admissible tail vertex to its on-label base pair is
injective on the finite tail set. -/
theorem on_label_tail_pair_map_inj_on
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground)
    (P : Edge α) :
    let z := chosenCommonRootLabel D.K D.ground fallback hCenters P
    Set.InjOn (fun w => ({z, w} : Edge α))
      ((D.ground \ insert z P : Finset α) : Set α) := by
  classical
  dsimp only
  let z := chosenCommonRootLabel D.K D.ground fallback hCenters P
  change Set.InjOn (fun w => ({z, w} : Edge α))
    ((D.ground \ insert z P : Finset α) : Set α)
  intro w hw w' hw' hPairs
  have hwz : z ∉ ({w} : Edge α) := by
    intro h
    have hzw : z = w := Finset.mem_singleton.mp h
    exact (Finset.mem_sdiff.mp hw).2 (by simp [hzw])
  have hwz' : z ∉ ({w'} : Edge α) := by
    intro h
    have hzw' : z = w' := Finset.mem_singleton.mp h
    exact (Finset.mem_sdiff.mp hw').2 (by simp [hzw'])
  have hErase := congrArg (fun Q : Edge α => Q.erase z) hPairs
  simpa [Finset.erase_insert hwz, Finset.erase_insert hwz'] using hErase

end JSP523.Rank4
