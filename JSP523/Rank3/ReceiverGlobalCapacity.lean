import JSP523.Rank3.GlobalSourceLedger
import JSP523.Rank3.ReceiverCapacityExtended
import JSP523.Rank3.ReciprocalSumLedger
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.SymmDiff

open scoped symmDiff

set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace JSP523.Rank3

section ReceiverGlobalCapacity

variable {α : Type*} [DecidableEq α]

theorem actual_receiver_charge_nonneg_of_source
    {H : Family α} {V : Edge α} {z v x y : α}
    (hzV : z ∈ V) (hsource : ({x, y} : Edge α) ∈ rootLink H V z)
    (hrecv : v ∈ (completionVertices H V ({x, y} : Edge α)).erase z) :
    0 ≤ actualReceiverCharge H V z x y v := by
  have hzcomp := root_mem_source_completion H V hzV hsource
  have hrecv' := (Finset.mem_erase.mp hrecv).2
  have hne := (Finset.mem_erase.mp hrecv).1
  have hsub : ({z, v} : Edge α) ⊆ completionVertices H V ({x, y} : Edge α) := by
    intro a ha
    rcases Finset.mem_insert.mp ha with haz | hav
    · exact haz ▸ hzcomp
    · exact (Finset.mem_singleton.mp hav) ▸ hrecv'
  have hdegree := Finset.card_le_card hsub
  have htwo : 2 ≤ ({z, v} : Edge α).card := by simp [Ne.symm hne]
  have hdegree' : 2 ≤ (completionVertices H V ({x, y} : Edge α)).card := htwo.trans hdegree
  have hden : (0 : ℚ) < ((completionVertices H V ({x, y} : Edge α)).card : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (completionVertices H V ({x, y} : Edge α)).card := by exact_mod_cast hdegree'
    linarith
  simp [actualReceiverCharge, hrecv, chargePerOtherCompletion]
  exact div_nonneg (le_max_right _ _) (le_of_lt hden)

/-- Symmetric difference is determined by a two-element unordered family. -/
theorem symm_diff_eq_of_pair_family_eq
    {p r a b : Edge α} (hpr : p ≠ r) (_hab : a ≠ b)
    (hset : ({p, r} : Family α) = {a, b}) :
    p ∆ r = a ∆ b := by
  have hp : p = a ∨ p = b := by
    have hm : p ∈ ({a, b} : Family α) := by rw [← hset]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hp with hpa | hpb
  · have hr : r = b := by
      have hm : r ∈ ({a, b} : Family α) := by rw [← hset]; simp
      rcases (show r = a ∨ r = b by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm) with h | h
      · exact False.elim (hpr (hpa.trans h.symm))
      · exact h
    simp [hpa, hr]
  · have hr : r = a := by
      have hm : r ∈ ({a, b} : Family α) := by rw [← hset]; simp
      rcases (show r = a ∨ r = b by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm) with h | h
      · exact h
      · exact False.elim (hpr (hpb.trans h.symm))
    ext w
    simp [Finset.mem_symmDiff, hpb, hr, or_comm]

/-- Canonical reciprocal target: symmetric difference of the two common-link
cores, independent of their chosen ordering. -/
noncomputable def reciprocalCellMap (H : Family α) (V : Edge α) (q : Edge α) : Edge α := by
  classical
  if hc : (commonLink H V q).card = 2 then
    let e := corePairRep (commonLink H V q) hc
    exact e.1 ∆ e.2
  else exact ∅

theorem reciprocal_cell_map_eq_pair_symm_diff
    (H : Family α) (V q : Edge α)
    (hc : (commonLink H V q).card = 2)
    {p r : Edge α} (hp : p ∈ commonLink H V q)
    (hr : r ∈ commonLink H V q) (hpr : p ≠ r) :
    reciprocalCellMap H V q = p ∆ r := by
  classical
  have hset : ({p, r} : Family α) = commonLink H V q := by
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      rcases Finset.mem_insert.mp ht with h | h
      · simpa [h] using hp
      · exact (Finset.mem_singleton.mp h) ▸ hr
    · rw [Finset.card_pair hpr, hc]
  let e := corePairRep (commonLink H V q) hc
  have he := core_pair_rep_spec (commonLink H V q) hc
  have hpair : ({p, r} : Family α) = ({e.1, e.2} : Family α) := by
    rw [hset, he.2]
  have hresult := symm_diff_eq_of_pair_family_eq hpr he.1 hpair
  simpa [reciprocalCellMap, hc, e] using hresult.symm

theorem pair_symm_diff_shared_right {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, c} : Edge α) ∆ ({b, c} : Edge α) = {a, b} := by
  ext w
  by_cases hwa : w = a
  · subst w
    simp [Finset.mem_symmDiff, hab, hac]
  · by_cases hwb : w = b
    · subst w
      simp [Finset.mem_symmDiff, hab.symm, hbc]
    · by_cases hwc : w = c
      · subst w
        simp [Finset.mem_symmDiff, hac.symm, hbc.symm]
      · simp [Finset.mem_symmDiff, hwa, hwb, hwc]

/-- Whenever a two-core cell and its canonical reciprocal both have two
cores, the reciprocal map returns to the original cell. The two alternatives
in the local reciprocal witness give the same symmetric-difference identity. -/
theorem reciprocal_cell_map_involutive_of_double
    {H : Family α} {V q : Edge α}
    (hH : Admissible H) (hq : q ∈ doubleLinkCells H V)
    (hrecip : reciprocalCellMap H V q ∈ doubleLinkCells H V) :
    reciprocalCellMap H V (reciprocalCellMap H V q) = q := by
  classical
  have hqUsed := (Finset.mem_filter.mp hq).1
  have hqCard := (Finset.mem_filter.mp hq).2
  have hq2 : q.card = 2 :=
    (Finset.mem_powersetCard.mp (used_cells_subset H V hqUsed)).2
  let e := corePairRep q hq2
  have he := core_pair_rep_spec q hq2
  have hqCardRep :
      (commonLink H V ({e.1, e.2} : Edge α)).card = 2 := by
    rw [← he.2]
    exact hqCard
  have hsub := (Finset.mem_powersetCard.mp (used_cells_subset H V hqUsed)).1
  have hsub' : ({e.1, e.2} : Edge α) ⊆ V := by rw [← he.2]; exact hsub
  have heV : e.1 ∈ V ∧ e.2 ∈ V :=
    ⟨hsub' (by simp), hsub' (by simp)⟩
  have hzv : e.1 ≠ e.2 := he.1
  have hrecipCard := (Finset.mem_filter.mp hrecip).2
  have hrecipUsed := (Finset.mem_filter.mp hrecip).1
  obtain ⟨x, y, u, hxy, hxu, hyu, hyV, huV, hcases⟩ :=
    double_receiver_has_reciprocal_cell hH heV.1 heV.2 hzv
      hqCardRep
  have hcaseMap :
      reciprocalCellMap H V q = ({y, u} : Edge α) ∨
      reciprocalCellMap H V q = ({x, u} : Edge α) := by
    rcases hcases with ⟨hp, hr, _, _⟩ | ⟨hp, hr, _, _⟩
    ·
      have hne : ({x, y} : Edge α) ≠ ({x, u} : Edge α) := by
        intro hh
        have hyMem : y ∈ ({x, u} : Edge α) := by rw [← hh]; simp
        rcases Finset.mem_insert.mp hyMem with hyx | hyu'
        · exact hxy hyx.symm
        · exact hyu (Finset.mem_singleton.mp hyu')
      have hmap := reciprocal_cell_map_eq_pair_symm_diff H V
        ({e.1, e.2} : Edge α) hqCardRep hp hr hne
      left
      rw [he.2, hmap]
      simpa only [Finset.pair_comm] using
        (pair_symm_diff_shared_right hyu (Ne.symm hxy) (Ne.symm hxu))
    ·
      have hne : ({x, y} : Edge α) ≠ ({y, u} : Edge α) := by
        intro hh
        have hxMem : x ∈ ({y, u} : Edge α) := by rw [← hh]; simp
        rcases Finset.mem_insert.mp hxMem with hxy' | hxu'
        · exact hxy hxy'
        · exact hxu (Finset.mem_singleton.mp hxu')
      have hmap := reciprocal_cell_map_eq_pair_symm_diff H V
        ({e.1, e.2} : Edge α) hqCardRep hp hr hne
      right
      rw [he.2, hmap]
      simpa only [Finset.pair_comm] using
        (pair_symm_diff_shared_right hxu hxy (Ne.symm hyu))
  rcases hcaseMap with hq' | hq'
  ·
    have htargetCard : (commonLink H V ({y, u} : Edge α)).card = 2 := by
      rw [← hq']
      exact hrecipCard
    rcases hcases with ⟨_, _, hp, hr⟩ | ⟨hpOther, hrOther, _, _⟩
    · have hpc : ({e.2, x} : Edge α) ∈ commonLink H V ({y, u} : Edge α) := by
        simpa only [Finset.pair_comm] using hp
      have hrc : ({e.1, x} : Edge α) ∈ commonLink H V ({y, u} : Edge α) := by
        simpa only [Finset.pair_comm] using hr
      have hne : ({e.2, x} : Edge α) ≠ ({e.1, x} : Edge α) := by
        intro hh
        have hvMem : e.2 ∈ ({e.1, x} : Edge α) := by rw [← hh]; simp
        rcases Finset.mem_insert.mp hvMem with hvz | hvx
        · exact hzv hvz.symm
        · have hxv : x ≠ e.2 := by
            have hc := (Finset.mem_powersetCard.mp
              (Finset.mem_filter.mp hpc).1).2
            exact Ne.symm (Finset.card_pair_eq_two_iff.mp hc)
          exact hxv (Finset.mem_singleton.mp hvx).symm
      have hback := reciprocal_cell_map_eq_pair_symm_diff H V
        ({y, u} : Edge α) htargetCard hpc hrc hne
      rw [hq', hback]
      have he2x : e.2 ≠ x := Finset.card_pair_eq_two_iff.mp
        ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpc).1).2)
      have he1x : e.1 ≠ x := Finset.card_pair_eq_two_iff.mp
        ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hrc).1).2)
      calc
        ({e.2, x} : Edge α) ∆ {e.1, x} = {e.2, e.1} :=
          pair_symm_diff_shared_right (Ne.symm hzv) he2x he1x
        _ = ({e.1, e.2} : Edge α) := Finset.pair_comm e.2 e.1
        _ = q := he.2.symm

    · have hother : reciprocalCellMap H V q = ({x, u} : Edge α) := by
        have hne' : ({x, y} : Edge α) ≠ ({y, u} : Edge α) := by
          intro hh
          have hxMem : x ∈ ({y, u} : Edge α) := by rw [← hh]; simp
          rcases Finset.mem_insert.mp hxMem with hxy' | hxu'
          · exact hxy hxy'
          · exact hxu (Finset.mem_singleton.mp hxu')
        have hm := reciprocal_cell_map_eq_pair_symm_diff H V
          ({e.1, e.2} : Edge α) hqCardRep hpOther hrOther hne'
        rw [he.2, hm]
        simpa only [Finset.pair_comm] using
          (pair_symm_diff_shared_right hxu hxy (Ne.symm hyu))
      have : False := by
        have htarget : ({x, u} : Edge α) = ({y, u} : Edge α) := hother.symm.trans hq'
        have hxMem : x ∈ ({y, u} : Edge α) := by rw [← htarget]; simp
        rcases Finset.mem_insert.mp hxMem with hxy' | hxu'
        · exact hxy hxy'
        · exact hxu (Finset.mem_singleton.mp hxu')
      exact this.elim
  ·
    have htargetCard : (commonLink H V ({x, u} : Edge α)).card = 2 := by
      rw [← hq']
      exact hrecipCard
    rcases hcases with ⟨hpOther, hrOther, _, _⟩ | ⟨_, _, hp, hr⟩
    · have hother : reciprocalCellMap H V q = ({y, u} : Edge α) := by
        have hne' : ({x, y} : Edge α) ≠ ({x, u} : Edge α) := by
          intro hh
          have hyMem : y ∈ ({x, u} : Edge α) := by rw [← hh]; simp
          rcases Finset.mem_insert.mp hyMem with hxy' | hyu'
          · exact hxy hxy'.symm
          · exact hyu (Finset.mem_singleton.mp hyu')
        have hm := reciprocal_cell_map_eq_pair_symm_diff H V
          ({e.1, e.2} : Edge α) hqCardRep hpOther hrOther hne'
        rw [he.2, hm]
        simpa only [Finset.pair_comm] using
          (pair_symm_diff_shared_right hyu (Ne.symm hxy) (Ne.symm hxu))
      have : False := by
        have htarget : ({y, u} : Edge α) = ({x, u} : Edge α) := hother.symm.trans hq'
        have hyMem : y ∈ ({x, u} : Edge α) := by rw [← htarget]; simp
        rcases Finset.mem_insert.mp hyMem with hxy' | hyu'
        · exact hxy hxy'.symm
        · exact hyu (Finset.mem_singleton.mp hyu')
      exact this.elim
    · have hpc : ({e.2, y} : Edge α) ∈ commonLink H V ({x, u} : Edge α) := by
        simpa only [Finset.pair_comm] using hp
      have hrc : ({e.1, y} : Edge α) ∈ commonLink H V ({x, u} : Edge α) := by
        simpa only [Finset.pair_comm] using hr
      have hne : ({e.2, y} : Edge α) ≠ ({e.1, y} : Edge α) := by
        intro hh
        have hvMem : e.2 ∈ ({e.1, y} : Edge α) := by rw [← hh]; simp
        rcases Finset.mem_insert.mp hvMem with hvz | hvy
        · exact hzv hvz.symm
        · have hyv : y ≠ e.2 := by
            have hc := (Finset.mem_powersetCard.mp
              (Finset.mem_filter.mp hpc).1).2
            exact Ne.symm (Finset.card_pair_eq_two_iff.mp hc)
          exact hyv (Finset.mem_singleton.mp hvy).symm
      have hback := reciprocal_cell_map_eq_pair_symm_diff H V
        ({x, u} : Edge α) htargetCard hpc hrc hne
      rw [hq', hback]
      have he2y : e.2 ≠ y := Finset.card_pair_eq_two_iff.mp
        ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpc).1).2)
      have he1y : e.1 ≠ y := Finset.card_pair_eq_two_iff.mp
        ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hrc).1).2)
      calc
        ({e.2, y} : Edge α) ∆ {e.1, y} = {e.2, e.1} :=
          pair_symm_diff_shared_right (Ne.symm hzv) he2y he1y
        _ = ({e.1, e.2} : Edge α) := Finset.pair_comm e.2 e.1
        _ = q := he.2.symm


theorem reciprocal_cell_map_card_ge_two_of_double
    {H : Family α} {V q : Edge α} (hH : Admissible H)
    (hq : q ∈ doubleLinkCells H V) :
    2 ≤ (commonLink H V (reciprocalCellMap H V q)).card := by
  classical
  have hqUsed := (Finset.mem_filter.mp hq).1
  have hqCard := (Finset.mem_filter.mp hq).2
  have hq2 : q.card = 2 := (Finset.mem_powersetCard.mp
    (used_cells_subset H V hqUsed)).2
  let e := corePairRep q hq2
  have he := core_pair_rep_spec q hq2
  have hqCardRep :
      (commonLink H V ({e.1, e.2} : Edge α)).card = 2 := by
    rw [← he.2]
    exact hqCard
  have hsub := (Finset.mem_powersetCard.mp (used_cells_subset H V hqUsed)).1
  have hsub' : ({e.1, e.2} : Edge α) ⊆ V := by rw [← he.2]; exact hsub
  have heV : e.1 ∈ V ∧ e.2 ∈ V :=
    ⟨hsub' (by simp), hsub' (by simp)⟩
  obtain ⟨x, y, u, hxy, hxu, hyu, hyV, huV, hcases⟩ :=
    double_receiver_has_reciprocal_cell hH heV.1 heV.2 he.1 hqCardRep
  rcases hcases with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
  · have hne : ({x, y} : Edge α) ≠ ({x, u} : Edge α) := by
      intro hh
      have hyMem : y ∈ ({x, u} : Edge α) := by rw [← hh]; simp
      rcases Finset.mem_insert.mp hyMem with hyx | hyu'
      · exact hxy hyx.symm
      · exact hyu (Finset.mem_singleton.mp hyu')
    have hmap := reciprocal_cell_map_eq_pair_symm_diff H V
      ({e.1, e.2} : Edge α) hqCardRep h₁ h₂ hne
    have htarget : reciprocalCellMap H V q = ({y, u} : Edge α) := by
      rw [he.2, hmap]
      simpa only [Finset.pair_comm] using
        (pair_symm_diff_shared_right hyu (Ne.symm hxy) (Ne.symm hxu))
    have hp : ({e.2, x} : Edge α) ∈ commonLink H V ({y, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₃
    have hr : ({e.1, x} : Edge α) ∈ commonLink H V ({y, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₄
    have hne' : ({e.2, x} : Edge α) ≠ ({e.1, x} : Edge α) := by
      intro hh
      have he2mem : e.2 ∈ ({e.1, x} : Edge α) := by rw [← hh]; simp
      rcases Finset.mem_insert.mp he2mem with heq | heq
      · exact he.1 heq.symm
      · have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
        have hxne : x ≠ e.2 := Ne.symm (Finset.card_pair_eq_two_iff.mp hc)
        exact hxne (Finset.mem_singleton.mp heq).symm
    have hcard := finset_card_ge_two_of_distinct_members
      (commonLink H V ({y, u} : Edge α)) hp hr hne'
    rw [htarget]
    exact hcard
  · have hne : ({x, y} : Edge α) ≠ ({y, u} : Edge α) := by
      intro hh
      have hxMem : x ∈ ({y, u} : Edge α) := by rw [← hh]; simp
      rcases Finset.mem_insert.mp hxMem with hxy' | hxu'
      · exact hxy hxy'
      · exact hxu (Finset.mem_singleton.mp hxu')
    have hmap := reciprocal_cell_map_eq_pair_symm_diff H V
      ({e.1, e.2} : Edge α) hqCardRep h₁ h₂ hne
    have htarget : reciprocalCellMap H V q = ({x, u} : Edge α) := by
      rw [he.2, hmap]
      simpa only [Finset.pair_comm] using
        (pair_symm_diff_shared_right hxu hxy (Ne.symm hyu))
    have hp : ({e.2, y} : Edge α) ∈ commonLink H V ({x, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₃
    have hr : ({e.1, y} : Edge α) ∈ commonLink H V ({x, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₄
    have hne' : ({e.2, y} : Edge α) ≠ ({e.1, y} : Edge α) := by
      intro hh
      have he2mem : e.2 ∈ ({e.1, y} : Edge α) := by rw [← hh]; simp
      rcases Finset.mem_insert.mp he2mem with heq | heq
      · exact he.1 heq.symm
      · have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
        have hyne : y ≠ e.2 := Ne.symm (Finset.card_pair_eq_two_iff.mp hc)
        exact hyne (Finset.mem_singleton.mp heq).symm
    have hcard := finset_card_ge_two_of_distinct_members
      (commonLink H V ({x, u} : Edge α)) hp hr hne'
    rw [htarget]
    exact hcard

/-- The c=2 receiver cells whose reciprocal also has c=2. -/
noncomputable def reciprocalRegularDoubleCells
    (H : Family α) (V : Edge α) : Family α := by
  classical
  exact (doubleLinkCells H V).filter
    (fun q => reciprocalCellMap H V q ∈ doubleLinkCells H V)

theorem reciprocal_regular_double_cells_subset
    (H : Family α) (V : Edge α) :
    reciprocalRegularDoubleCells H V ⊆ doubleLinkCells H V := by
  classical
  intro q hq
  exact (Finset.mem_filter.mp hq).1

theorem reciprocal_regular_map_mem
    {H : Family α} {V : Edge α} (hH : Admissible H) (q : Edge α)
    (hq : q ∈ reciprocalRegularDoubleCells H V) :
    reciprocalCellMap H V q ∈ reciprocalRegularDoubleCells H V := by
  classical
  have hdouble := (Finset.mem_filter.mp hq).1
  have htarget := (Finset.mem_filter.mp hq).2
  have hback := reciprocal_cell_map_involutive_of_double hH hdouble htarget
  apply Finset.mem_filter.mpr
  exact ⟨htarget, hback.symm ▸ hdouble⟩

theorem reciprocal_regular_map_involutive
    {H : Family α} {V : Edge α} (hH : Admissible H) (q : Edge α)
    (hq : q ∈ reciprocalRegularDoubleCells H V) :
    reciprocalCellMap H V (reciprocalCellMap H V q) = q := by
  classical
  exact reciprocal_cell_map_involutive_of_double
    hH (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2

theorem actual_regular_pair_capacity_le_four
    {H : Family α} {V q : Edge α} (hH : Admissible H)
    (hq : q ∈ reciprocalRegularDoubleCells H V) :
    actualCellChargeForPair H V q +
      actualCellChargeForPair H V (reciprocalCellMap H V q) ≤ 4 := by
  classical
  have hdouble := (Finset.mem_filter.mp hq).1
  have hrecipDouble := (Finset.mem_filter.mp hq).2
  have hqUsed := (Finset.mem_filter.mp hdouble).1
  have hqCard := (Finset.mem_filter.mp hdouble).2
  have hq2 : q.card = 2 := (Finset.mem_powersetCard.mp
    (used_cells_subset H V hqUsed)).2
  let e := corePairRep q hq2
  have he := core_pair_rep_spec q hq2
  have hqCardRep :
      (commonLink H V ({e.1, e.2} : Edge α)).card = 2 := by
    rw [← he.2]
    exact hqCard
  have hsub := (Finset.mem_powersetCard.mp (used_cells_subset H V hqUsed)).1
  have hsub' : ({e.1, e.2} : Edge α) ⊆ V := by rw [← he.2]; exact hsub
  have heV : e.1 ∈ V ∧ e.2 ∈ V :=
    ⟨hsub' (by simp), hsub' (by simp)⟩
  have hchargeQ : actualCellChargeForPair H V q =
      actualCellChargeTotal H V e.1 e.2 := by
    rw [he.2]
    exact actual_cell_charge_for_pair_eq_displayed H V he.1
  have hrecipCard := (Finset.mem_filter.mp hrecipDouble).2
  obtain ⟨x, y, u, hxy, hxu, hyu, hyV, huV, hcases⟩ :=
    double_receiver_has_reciprocal_cell hH heV.1 heV.2 he.1 hqCardRep
  rcases hcases with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
  · have hne : ({x, y} : Edge α) ≠ ({x, u} : Edge α) := by
      intro hh
      have hyMem : y ∈ ({x, u} : Edge α) := by rw [← hh]; simp
      rcases Finset.mem_insert.mp hyMem with hyx | hyu'
      · exact hxy hyx.symm
      · exact hyu (Finset.mem_singleton.mp hyu')
    have hmap := reciprocal_cell_map_eq_pair_symm_diff H V
      ({e.1, e.2} : Edge α) hqCardRep h₁ h₂ hne
    have htarget : reciprocalCellMap H V q = ({y, u} : Edge α) := by
      rw [he.2, hmap]
      simpa only [Finset.pair_comm] using
        (pair_symm_diff_shared_right hyu (Ne.symm hxy) (Ne.symm hxu))
    have htargetCard : (commonLink H V ({y, u} : Edge α)).card = 2 := by
      rw [← htarget]
      exact hrecipCard
    have h₃ : ({x, e.2} : Edge α) ∈ commonLink H V ({y, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₃
    have h₄ : ({x, e.1} : Edge α) ∈ commonLink H V ({y, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₄
    have hxv : x ≠ e.2 := Finset.card_pair_eq_two_iff.mp
      ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₃).1).2)
    have hxz : x ≠ e.1 := Finset.card_pair_eq_two_iff.mp
      ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₄).1).2)
    have hxV : x ∈ V := by
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₁).1).1 (by simp)
    have hcap := actual_reciprocal_double_cell_capacity_le_four hH
      hyV huV heV.1 heV.2 hxy hxu hxv hxz he.1 hyu h₁ h₂ h₃ h₄
      hqCardRep htargetCard
    have hchargeR : actualCellChargeForPair H V (reciprocalCellMap H V q) =
        actualCellChargeTotal H V y u := by
      rw [htarget]
      exact actual_cell_charge_for_pair_eq_displayed H V hyu
    rw [hchargeQ, hchargeR]
    exact hcap
  · have hne : ({x, y} : Edge α) ≠ ({y, u} : Edge α) := by
      intro hh
      have hxMem : x ∈ ({y, u} : Edge α) := by rw [← hh]; simp
      rcases Finset.mem_insert.mp hxMem with hxy' | hxu'
      · exact hxy hxy'
      · exact hxu (Finset.mem_singleton.mp hxu')
    have hmap := reciprocal_cell_map_eq_pair_symm_diff H V
      ({e.1, e.2} : Edge α) hqCardRep h₁ h₂ hne
    have htarget : reciprocalCellMap H V q = ({x, u} : Edge α) := by
      rw [he.2, hmap]
      simpa only [Finset.pair_comm] using
        (pair_symm_diff_shared_right hxu hxy (Ne.symm hyu))
    have htargetCard : (commonLink H V ({x, u} : Edge α)).card = 2 := by
      rw [← htarget]
      exact hrecipCard
    have h₃ : ({y, e.2} : Edge α) ∈ commonLink H V ({x, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₃
    have h₄ : ({y, e.1} : Edge α) ∈ commonLink H V ({x, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₄
    have hyv : y ≠ e.2 := Finset.card_pair_eq_two_iff.mp
      ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₃).1).2)
    have hyz : y ≠ e.1 := Finset.card_pair_eq_two_iff.mp
      ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₄).1).2)
    have hxV : x ∈ V := by
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₁).1).1 (by simp)
    have hcap := actual_reciprocal_double_cell_capacity_le_four hH
      hxV huV heV.1 heV.2 (Ne.symm hxy) hyu hyv hyz he.1 hxu
      (by simpa only [Finset.pair_comm] using h₁) h₂
      h₃ h₄ hqCardRep htargetCard
    have hchargeR : actualCellChargeForPair H V (reciprocalCellMap H V q) =
        actualCellChargeTotal H V x u := by
      rw [htarget]
      exact actual_cell_charge_for_pair_eq_displayed H V hxu
    rw [hchargeQ, hchargeR]
    exact hcap

theorem actual_regular_double_cell_sum_le_two_card
    (H : Family α) (V : Edge α) (hH : Admissible H)
    :
    (∑ q ∈ reciprocalRegularDoubleCells H V,
      actualCellChargeForPair H V q) ≤
      2 * ((reciprocalRegularDoubleCells H V).card : ℚ) := by
  apply sum_le_two_card_of_reciprocal_involution
    (reciprocalRegularDoubleCells H V) (reciprocalCellMap H V)
    (actualCellChargeForPair H V)
  · exact reciprocal_regular_map_mem hH
  · exact reciprocal_regular_map_involutive hH
  · intro q hq
    exact actual_regular_pair_capacity_le_four hH hq

/-- Positive charge into a common-link cell forces its multiplicity to at most
 two. This is the support restriction behind vanishing c≥3 receiver cells. -/
theorem actual_receiver_charge_positive_card_le_two
    {H : Family α} {V : Edge α} {z v : α} {p : Edge α}
    (hH : Admissible H) (hzV : z ∈ V) (hvV : v ∈ V) (hzv : z ≠ v)
    (hp : p ∈ commonLink H V ({z, v} : Edge α))
    (hpositive : 0 < coreReceiverCharge H V z v p) :
    (commonLink H V ({z, v} : Edge α)).card ≤ 2 := by
  have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp
    (Finset.mem_filter.mp hp).1).2
  let e := corePairRep p hp2
  have he := core_pair_rep_spec p hp2
  have hpZ : ({e.1, e.2} : Edge α) ∈ rootLink H V z := by
    rw [← he.2]
    exact (common_link_pair_gives_two_sources hzv hp).1
  have hrecv := (source_receiver_iff_common_link H V hzV hvV hzv).2 hp
  have hrecv' : v ∈ (completionVertices H V ({e.1, e.2} : Edge α)).erase z := by
    rw [← he.2]
    exact hrecv.2
  have hcharge : 0 < actualReceiverCharge H V z e.1 e.2 v := by
    simpa [coreReceiverCharge, hp2, e] using hpositive
  have hweight : 0 < positiveRootedWeight H V z e.1 e.2 := by
    have hden : (0 : ℚ) < ((completionVertices H V ({e.1, e.2} : Edge α)).card : ℚ) - 1 := by
      have hzcomp := root_mem_source_completion H V hzV hpZ
      have hvcomp := (Finset.mem_erase.mp hrecv').2
      have hsub : ({z, v} : Edge α) ⊆ completionVertices H V ({e.1, e.2} : Edge α) := by
        intro a ha
        rcases Finset.mem_insert.mp ha with haz | hav
        · exact haz ▸ hzcomp
        · exact (Finset.mem_singleton.mp hav) ▸ hvcomp
      have hdegree := Finset.card_le_card hsub
      have htwo : 2 ≤ ({z, v} : Edge α).card := by simp [hzv]
      have hdegree' : 2 ≤ (completionVertices H V ({e.1, e.2} : Edge α)).card := htwo.trans hdegree
      have hcast : (2 : ℚ) ≤ (completionVertices H V ({e.1, e.2} : Edge α)).card := by
        exact_mod_cast hdegree'
      linarith
    have hcharge' : 0 < chargePerOtherCompletion H V z e.1 e.2 := by
      simpa [actualReceiverCharge, hrecv'] using hcharge
    unfold chargePerOtherCompletion at hcharge'
    rcases (div_pos_iff.mp hcharge') with h | h
    · exact h.1
    · linarith
  exact actual_receiver_card_le_two hH hzV hpZ he.1 hrecv' hweight

/-- An actual receiver cell with c≥3 receives no charge. -/
theorem actual_cell_charge_for_pair_eq_zero_of_card_ge_three
    {H : Family α} {V : Edge α} (hH : Admissible H)
    {q : Edge α} (hq : q ∈ usedCells H V)
    (hlarge : 3 ≤ (commonLink H V q).card) :
    actualCellChargeForPair H V q = 0 := by
  classical
  have hq2 : q.card = 2 := (Finset.mem_powersetCard.mp
    (used_cells_subset H V hq)).2
  let e := corePairRep q hq2
  have he := core_pair_rep_spec q hq2
  have heV : e.1 ∈ V ∧ e.2 ∈ V := by
    have hsub := (Finset.mem_powersetCard.mp (used_cells_subset H V hq)).1
    have hsub' : ({e.1, e.2} : Edge α) ⊆ V := by
      rw [← he.2]
      exact hsub
    exact ⟨hsub' (by simp), hsub' (by simp)⟩
  have hcellZero : actualCellChargeTotal H V e.1 e.2 = 0 := by
    unfold actualCellChargeTotal
    apply Finset.sum_eq_zero
    intro p hp
    have h₁ : coreReceiverCharge H V e.1 e.2 p = 0 := by
      by_contra hne
      have hpos : 0 < coreReceiverCharge H V e.1 e.2 p := by
        have hnon : 0 ≤ coreReceiverCharge H V e.1 e.2 p := by
          by_cases hp' : p.card = 2
          · let f := corePairRep p hp'
            have hf := core_pair_rep_spec p hp'
            have hsource : ({f.1, f.2} : Edge α) ∈ rootLink H V e.1 := by
              rw [← hf.2]
              exact (common_link_pair_gives_two_sources he.1 hp).1
            have hrecv := (source_receiver_iff_common_link H V heV.1 heV.2 he.1).2 hp
            have hrecv' : e.2 ∈ (completionVertices H V ({f.1, f.2} : Edge α)).erase e.1 := by
              rw [← hf.2]
              exact hrecv.2
            simpa [coreReceiverCharge, hp', f] using
              actual_receiver_charge_nonneg_of_source heV.1 hsource hrecv'
          · simp [coreReceiverCharge, hp']
        have hpositive' : 0 < coreReceiverCharge H V e.1 e.2 p := lt_of_le_of_ne hnon (Ne.symm hne)
        exact hpositive'
      have hbound := actual_receiver_charge_positive_card_le_two hH
        heV.1 heV.2 he.1 hp hpos
      have hlarge' : 3 ≤ (commonLink H V ({e.1, e.2} : Edge α)).card := by
        rw [← he.2]
        exact hlarge
      omega
    have h₂ : coreReceiverCharge H V e.2 e.1 p = 0 := by
      by_contra hne
      have hpos : 0 < coreReceiverCharge H V e.2 e.1 p := by
        have hnon : 0 ≤ coreReceiverCharge H V e.2 e.1 p := by
          by_cases hp' : p.card = 2
          · let f := corePairRep p hp'
            have hf := core_pair_rep_spec p hp'
            have hsource : ({f.1, f.2} : Edge α) ∈ rootLink H V e.2 := by
              rw [← hf.2]
              exact (common_link_pair_gives_two_sources he.1 hp).2
            have hp'cell : p ∈ commonLink H V ({e.2, e.1} : Edge α) := by
              simpa only [Finset.pair_comm] using hp
            have hrecv := (source_receiver_iff_common_link H V heV.2 heV.1 (Ne.symm he.1)).2 hp'cell
            have hrecv' : e.1 ∈ (completionVertices H V ({f.1, f.2} : Edge α)).erase e.2 := by
              rw [← hf.2]
              exact hrecv.2
            simpa [coreReceiverCharge, hp', f] using
              actual_receiver_charge_nonneg_of_source heV.2 hsource hrecv'
          · simp [coreReceiverCharge, hp']
        have hpositive' : 0 < coreReceiverCharge H V e.2 e.1 p := lt_of_le_of_ne hnon (Ne.symm hne)
        exact hpositive'
      have hp' : p ∈ commonLink H V ({e.2, e.1} : Edge α) := by
        simpa only [Finset.pair_comm] using hp
      have hbound := actual_receiver_charge_positive_card_le_two hH
        heV.2 heV.1 (Ne.symm he.1) hp' hpos
      have hlarge' : 3 ≤ (commonLink H V ({e.2, e.1} : Edge α)).card := by
        calc
          3 ≤ (commonLink H V q).card := hlarge
          _ = (commonLink H V ({e.2, e.1} : Edge α)).card := by
            rw [he.2, Finset.pair_comm]
      omega
    simp [h₁, h₂]
  simpa [actualCellChargeForPair, hq2, e] using hcellZero

/-- A core's receiver charge is nonnegative whenever its core belongs to
the displayed receiving common link. -/
theorem core_receiver_charge_nonneg_of_common_link
    {H : Family α} {V : Edge α} {z v : α} {p : Edge α}
    (hzV : z ∈ V) (hvV : v ∈ V) (hzv : z ≠ v)
    (hp : p ∈ commonLink H V ({z, v} : Edge α)) :
    0 ≤ coreReceiverCharge H V z v p := by
  by_cases hp2 : p.card = 2
  · let e := corePairRep p hp2
    have he := core_pair_rep_spec p hp2
    have hsource : ({e.1, e.2} : Edge α) ∈ rootLink H V z := by
      rw [← he.2]
      exact (common_link_pair_gives_two_sources hzv hp).1
    have hrecv := (source_receiver_iff_common_link H V hzV hvV hzv).2 hp
    have hrecv' : v ∈ (completionVertices H V ({e.1, e.2} : Edge α)).erase z := by
      rw [← he.2]
      exact hrecv.2
    simpa [coreReceiverCharge, hp2, e] using
      actual_receiver_charge_nonneg_of_source hzV hsource hrecv'
  · simp [coreReceiverCharge, hp2]

/-- Each actual unordered receiver-cell total is nonnegative. -/
theorem actual_cell_charge_total_nonneg
    {H : Family α} {V : Edge α} {z v : α}
    (hzV : z ∈ V) (hvV : v ∈ V) (hzv : z ≠ v) :
    0 ≤ actualCellChargeTotal H V z v := by
  unfold actualCellChargeTotal
  apply Finset.sum_nonneg
  intro p hp
  exact add_nonneg
    (core_receiver_charge_nonneg_of_common_link hzV hvV hzv hp)
    (core_receiver_charge_nonneg_of_common_link hvV hzV (Ne.symm hzv)
      (by simpa only [Finset.pair_comm] using hp))

/-- The charge assigned to any actual cell pair is nonnegative. -/
theorem actual_cell_charge_for_pair_nonneg
    {H : Family α} {V q : Edge α}
    (hq : q ∈ usedCells H V) : 0 ≤ actualCellChargeForPair H V q := by
  classical
  have hq2 : q.card = 2 := (Finset.mem_powersetCard.mp (used_cells_subset H V hq)).2
  let e := corePairRep q hq2
  have he := core_pair_rep_spec q hq2
  have hsub := (Finset.mem_powersetCard.mp (used_cells_subset H V hq)).1
  have heV : e.1 ∈ V ∧ e.2 ∈ V := by
    have hsub' : ({e.1, e.2} : Edge α) ⊆ V := by rw [← he.2]; exact hsub
    exact ⟨hsub' (by simp), hsub' (by simp)⟩
  simpa [actualCellChargeForPair, hq2, e] using
    actual_cell_charge_total_nonneg heV.1 heV.2 he.1

/-- Receiver cells with at least three common-link cores. -/
def atLeastThreeReceiverCells (H : Family α) (V : Edge α) : Family α :=
  (usedCells H V).filter (fun q => 3 ≤ (commonLink H V q).card)

theorem actual_cell_charge_for_pair_lt_four_of_singleton
    {H : Family α} {V q : Edge α} (hq : q ∈ singletonLinkCells H V) :
    actualCellChargeForPair H V q < 4 := by
  have hused := (Finset.mem_filter.mp hq).1
  have hc := (Finset.mem_filter.mp hq).2
  have hq2 : q.card = 2 := (Finset.mem_powersetCard.mp
    (used_cells_subset H V hused)).2
  let e := corePairRep q hq2
  have he := core_pair_rep_spec q hq2
  have hsub := (Finset.mem_powersetCard.mp (used_cells_subset H V hused)).1
  have hsub' : ({e.1, e.2} : Edge α) ⊆ V := by rw [← he.2]; exact hsub
  have heV : e.1 ∈ V ∧ e.2 ∈ V :=
    ⟨hsub' (by simp), hsub' (by simp)⟩
  have hdisplay : actualCellChargeForPair H V q =
      actualCellChargeTotal H V e.1 e.2 := by
    rw [he.2]
    exact actual_cell_charge_for_pair_eq_displayed H V he.1
  rw [hdisplay]
  have hc' : (commonLink H V ({e.1, e.2} : Edge α)).card = 1 := by
    rw [← he.2]
    exact hc
  exact singleton_cell_charge_total_lt_four H V heV.1 heV.2 he.1 hc'

theorem actual_cell_singleton_sum_le
    (H : Family α) (V : Edge α) :
    (∑ q ∈ singletonLinkCells H V, actualCellChargeForPair H V q) ≤
      4 * (singletonLinkCells H V).card := by
  calc
    _ ≤ ∑ q ∈ singletonLinkCells H V, (4 : ℚ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact (actual_cell_charge_for_pair_lt_four_of_singleton hq).le
    _ = 4 * (singletonLinkCells H V).card := by
      simp
      ring

theorem actual_cell_threeplus_sum_eq_zero
    (H : Family α) (V : Edge α) (hH : Admissible H) :
    (∑ q ∈ atLeastThreeReceiverCells H V, actualCellChargeForPair H V q) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  exact actual_cell_charge_for_pair_eq_zero_of_card_ge_three hH
    (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2

/-- Finite sum partition of actual cell charges into c=1, c=2, and c≥3. -/
theorem actual_cell_charge_sum_partition
    (H : Family α) (V : Edge α) :
    (∑ q ∈ usedCells H V, actualCellChargeForPair H V q) =
      (∑ q ∈ singletonLinkCells H V, actualCellChargeForPair H V q) +
      (∑ q ∈ doubleLinkCells H V, actualCellChargeForPair H V q) +
      (∑ q ∈ atLeastThreeReceiverCells H V, actualCellChargeForPair H V q) := by
  classical
  have hpoint : ∀ q ∈ usedCells H V,
      actualCellChargeForPair H V q =
        (if (commonLink H V q).card = 1 then actualCellChargeForPair H V q else 0) +
        (if (commonLink H V q).card = 2 then actualCellChargeForPair H V q else 0) +
        (if 3 ≤ (commonLink H V q).card then actualCellChargeForPair H V q else 0) := by
    intro q hq
    have hpos : 0 < (commonLink H V q).card := Finset.card_pos.mpr
      ((mem_used_cells_iff_common_link_nonempty H V q).mp hq).2
    by_cases h1 : (commonLink H V q).card = 1
    · simp [h1]
    · by_cases h2 : (commonLink H V q).card = 2
      · simp [h1, h2]
      · have h3 : 3 ≤ (commonLink H V q).card := by omega
        simp [h1, h2, h3]
  calc
    _ = ∑ q ∈ usedCells H V,
        ((if (commonLink H V q).card = 1 then actualCellChargeForPair H V q else 0) +
         (if (commonLink H V q).card = 2 then actualCellChargeForPair H V q else 0) +
         (if 3 ≤ (commonLink H V q).card then actualCellChargeForPair H V q else 0)) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hpoint q hq
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_filter,
      singletonLinkCells, doubleLinkCells, atLeastThreeReceiverCells]

/-- The per-cell summand defining the actual triangle excess. -/
noncomputable def actualTriangleExcess
    (H : Family α) (V : Edge α) (q : Edge α) : ℚ := by
  classical
  exact if triangleExceptionalReceiverCell H V q then
    max (actualCellChargeForPair H V q - 2) 0 else 0

theorem actual_xi_eq_sum_triangle_excess
    (H : Family α) (V : Edge α) :
    actualXi H V = ∑ q ∈ usedCells H V, actualTriangleExcess H V q := by
  classical
  simp [actualXi, actualTriangleExcess]

theorem actual_triangle_excess_nonneg
    (H : Family α) (V : Edge α) (q : Edge α) :
    0 ≤ actualTriangleExcess H V q := by
  classical
  by_cases hq : triangleExceptionalReceiverCell H V q
  · simp [actualTriangleExcess, hq]
  · simp [actualTriangleExcess, hq]

/-- The cellwise accounting inequality: ordinary cells contribute at most two,
while the exceptional cells' excess is exactly charged to the actual Xi ledger. -/
theorem actual_double_cell_charge_le_two_add_excess
    (H : Family α) (V : Edge α) (q : Edge α)
    (hordinary : ¬ triangleExceptionalReceiverCell H V q →
      actualCellChargeForPair H V q ≤ 2) :
    actualCellChargeForPair H V q ≤ 2 + actualTriangleExcess H V q := by
  classical
  by_cases hq : triangleExceptionalReceiverCell H V q
  · simp [actualTriangleExcess, hq]
    have hmax : actualCellChargeForPair H V q - 2 ≤
        max (actualCellChargeForPair H V q - 2) 0 := le_max_left _ _
    linarith
  · have h := hordinary hq
    simpa [actualTriangleExcess, hq] using h

/-- Finite aggregation of the preceding local estimate over the c=2 cells. -/
theorem actual_double_cell_sum_le_two_card_add_xi
    (H : Family α) (V : Edge α)
    (hordinary : ∀ q ∈ doubleLinkCells H V,
      ¬ triangleExceptionalReceiverCell H V q →
        actualCellChargeForPair H V q ≤ 2) :
    (∑ q ∈ doubleLinkCells H V, actualCellChargeForPair H V q) ≤
      2 * (doubleLinkCells H V).card + actualXi H V := by
  classical
  calc
    _ ≤ ∑ q ∈ doubleLinkCells H V,
        (2 + actualTriangleExcess H V q) := by
      apply Finset.sum_le_sum
      intro q hq
      exact actual_double_cell_charge_le_two_add_excess H V q
        (hordinary q hq)
    _ = 2 * (doubleLinkCells H V).card +
        ∑ q ∈ doubleLinkCells H V, actualTriangleExcess H V q := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 2 * (doubleLinkCells H V).card + actualXi H V := by
      rw [actual_xi_eq_sum_triangle_excess]
      have hsum := Finset.sum_le_sum_of_subset_of_nonneg
        (s := doubleLinkCells H V) (t := usedCells H V)
        (f := actualTriangleExcess H V)
        (by
          intro q hq
          exact (Finset.mem_filter.mp hq).1)
        (by
          intro q hq hnot
          exact actual_triangle_excess_nonneg H V q)
      linarith [hsum]

end ReceiverGlobalCapacity

end JSP523.Rank3
