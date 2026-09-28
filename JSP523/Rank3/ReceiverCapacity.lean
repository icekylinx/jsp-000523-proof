import JSP523.Rank3.ReciprocalCapacityScalar
import JSP523.Rank3.PairGraphClassification
import Mathlib.Tactic.Linarith
set_option maxHeartbeats 300000

/-!
# Actual receiver charges and local capacity bounds

This file records the genuine rooted source and receiver quantities used in
§§II.4–II.5. The reciprocal grouping needed for the full global estimate is
kept separate from these unconditional local facts.
-/

namespace JSP523.Rank3

section ReceiverCapacity

variable {α : Type*} [DecidableEq α]

/-- Positive rooted weight, retained when its source pair has one completion. -/
def retainedPositiveWeight (H : Family α) (V : Edge α) (z x y : α) : ℚ :=
  if (completionVertices H V ({x, y} : Edge α)).card = 1 then
    positiveRootedWeight H V z x y else 0

/-- The actual charge from a rooted source to one other completion vertex. -/
def actualReceiverCharge (H : Family α) (V : Edge α) (z x y v : α) : ℚ :=
  if v ∈ (completionVertices H V ({x, y} : Edge α)).erase z then
    chargePerOtherCompletion H V z x y else 0

/-- A chosen ordered presentation of a two-element core pair. The choice is
used only to evaluate the symmetric rooted weight on an actual pair. -/
noncomputable def corePairRep (p : Edge α) (hp : p.card = 2) : α × α :=
  Classical.choose (show ∃ e : α × α, e.1 ≠ e.2 ∧ p = ({e.1, e.2} : Edge α) from by
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hp
    exact ⟨(x, y), hxy, rfl⟩)

theorem core_pair_rep_spec (p : Edge α) (hp : p.card = 2) :
    (corePairRep p hp).1 ≠ (corePairRep p hp).2 ∧
      p = ({(corePairRep p hp).1, (corePairRep p hp).2} : Edge α) :=
  Classical.choose_spec (show ∃ e : α × α, e.1 ≠ e.2 ∧
    p = ({e.1, e.2} : Edge α) from by
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hp
      exact ⟨(x, y), hxy, rfl⟩)

/-- Charge indexed by an actual core pair, using its chosen two endpoints. -/
noncomputable def coreReceiverCharge
    (H : Family α) (V : Edge α) (z v : α) (p : Edge α) : ℚ := by
  classical
  by_cases hp : p.card = 2
  · let e := corePairRep p hp
    exact actualReceiverCharge H V z e.1 e.2 v
  · exact 0

/-- The charge kernel on actual core pairs. -/
noncomputable def coreChargeKernel
    (H : Family α) (V : Edge α) (z v : α) (p : Edge α) : ℚ := by
  classical
  exact if hp : p ∈ rootLink H V z then
    if hv : v ∈ (completionVertices H V p).erase z then
      coreReceiverCharge H V z v p
    else 0
  else 0

/-- Source ordered total: rooted source pair first, then its receiving
completion vertex. -/
noncomputable def outgoingCoreChargeTotal
    (H : Family α) (V : Edge α) : ℚ := by
  classical
  exact ∑ z ∈ V, ∑ p ∈ rootLink H V z, ∑ v ∈ V.erase z,
    coreChargeKernel H V z v p

/-- Receiver ordered total: receiving vertex first, then rooted source pair. -/
noncomputable def incomingCoreChargeTotal
    (H : Family α) (V : Edge α) : ℚ := by
  classical
  exact ∑ z ∈ V, ∑ v ∈ V.erase z, ∑ p ∈ rootLink H V z,
    coreChargeKernel H V z v p

/-- Finite Fubini reordering of the actual source charges by their receiving
rooted pair `{z,v}`. -/
theorem actual_core_charge_fubini
    (H : Family α) (V : Edge α) :
    outgoingCoreChargeTotal H V = incomingCoreChargeTotal H V := by
  classical
  unfold outgoingCoreChargeTotal incomingCoreChargeTotal
  apply Finset.sum_congr rfl
  intro z hz
  exact Finset.sum_comm

/-- A positive rooted source has weight strictly below two. -/
theorem positive_rooted_weight_lt_two
    (H : Family α) (V : Edge α) {z x y : α}
    (hsource : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxy : x ≠ y) :
    positiveRootedWeight H V z x y < 2 := by
  have hlt := rooted_signed_weight_lt_two H V hsource hxy
  by_cases hnonpos : rootedSignedWeight H V z x y ≤ 0
  · simp [positiveRootedWeight, max_eq_right hnonpos]
  · have hpos : 0 < rootedSignedWeight H V z x y := lt_of_not_ge hnonpos
    simpa [positiveRootedWeight, max_eq_left (le_of_lt hpos)] using hlt

/-- Every actual receiver of a positive source has at most two common-link
base pairs. -/
theorem actual_receiver_card_le_two
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxy : x ≠ y)
    (hv : v ∈ (completionVertices H V ({x, y} : Edge α)).erase z)
    (hpositive : 0 < positiveRootedWeight H V z x y) :
    (commonLink H V ({z, v} : Edge α)).card ≤ 2 :=
  positive_charge_receiver_card_le_two hH hzV hsource hxy hv hpositive

/-- Every actual nonnegative charge is at most its source weight, since a
source distributes across at least one other completion. -/
theorem actual_charge_le_source_weight
    (H : Family α) (V : Edge α) {z v x y : α}
    (hv : v ∈ (completionVertices H V ({x, y} : Edge α)).erase z)
    (hdegree : 2 ≤ (completionVertices H V ({x, y} : Edge α)).card) :
    actualReceiverCharge H V z x y v ≤ positiveRootedWeight H V z x y := by
  have hvN : v ∈ completionVertices H V ({x, y} : Edge α) :=
    (Finset.mem_erase.mp hv).2
  have hcharge := chargePerOtherCompletion H V z x y
  have hden : 1 ≤
      (completionVertices H V ({x, y} : Edge α)).card - 1 := by omega
  have hdenQ : (1 : ℚ) ≤
      ((completionVertices H V ({x, y} : Edge α)).card : ℚ) - 1 := by
    have hcast : (2 : ℚ) ≤
        (completionVertices H V ({x, y} : Edge α)).card := by
      exact_mod_cast hdegree
    linarith
  have hpos : 0 ≤ positiveRootedWeight H V z x y := by
    unfold positiveRootedWeight
    exact le_max_right _ _
  have hdiv : chargePerOtherCompletion H V z x y ≤
      positiveRootedWeight H V z x y := by
    unfold chargePerOtherCompletion
    apply (div_le_iff₀ (by linarith :
      0 < ((completionVertices H V ({x, y} : Edge α)).card : ℚ) - 1)).mpr
    nlinarith
  simp [actualReceiverCharge, hv]
  exact hdiv

/-- Every individual actual receiver charge is below two whenever it comes
from a positive root-link edge whose source has at least two completions. -/
theorem actual_charge_lt_two
    (H : Family α) (V : Edge α) {z v x y : α}
    (hsource : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxy : x ≠ y)
    (hv : v ∈ (completionVertices H V ({x, y} : Edge α)).erase z)
    (hdegree : 2 ≤ (completionVertices H V ({x, y} : Edge α)).card) :
    actualReceiverCharge H V z x y v < 2 := by
  have hle := actual_charge_le_source_weight H V hv hdegree
  have hweight := positive_rooted_weight_lt_two H V hsource hxy
  exact lt_of_le_of_lt hle hweight

/-- A core with at least two completions has reciprocal degree at most one;
if it has degree at least four, the reciprocal is at most one third. -/
theorem reciprocal_completion_degree_bound (d : ℕ) (hd : 2 ≤ d) :
    1 / ((d : ℚ) - 1) ≤ if 4 ≤ d then (1 : ℚ) / 3 else 1 := by
  by_cases hhigh : 4 ≤ d
  · simp [hhigh]
    have hcast : (4 : ℚ) ≤ d := by exact_mod_cast hhigh
    have hden : (3 : ℚ) ≤ (d : ℚ) - 1 := by linarith
    exact (inv_le_inv₀ (by linarith : (0 : ℚ) < (d : ℚ) - 1)
      (by norm_num : (0 : ℚ) < 3)).2 hden
  · have hlow : d = 2 ∨ d = 3 := by omega
    rcases hlow with h | h
    · subst d
      norm_num
    · subst d
      norm_num

/-- If the root-endpoint degree is below four, an actual rooted source has
zero positive weight and sends zero charge. -/
theorem actual_charge_eq_zero_of_low_root_degree
    (H : Family α) (V : Edge α) {z v x y : α}
    (hsource : ({x, y} : Edge α) ∈ rootLink H V z)
    (hv : v ∈ (completionVertices H V ({x, y} : Edge α)).erase z)
    (hlow : (completionVertices H V ({z, x} : Edge α)).card < 4) :
    actualReceiverCharge H V z x y v = 0 := by
  have hxy : x ≠ y := Finset.card_pair_eq_two_iff.mp
    ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hsource).1).2)
  have hnonpos : rootedSignedWeight H V z x y ≤ 0 := by
    by_contra h
    have hpos : 0 < rootedSignedWeight H V z x y := lt_of_not_ge h
    have hhigh := positive_rooted_signed_weight_high_degrees H V
      hsource hxy hpos
    have hdeg : 4 ≤ (completionVertices H V ({z, x} : Edge α)).card := hhigh.1
    omega
  have hzero : positiveRootedWeight H V z x y = 0 := by
    simp [positiveRootedWeight, max_eq_right hnonpos]
  simp [actualReceiverCharge, hv, chargePerOtherCompletion, hzero]

/-- At a double receiver, a source charge is bounded by the reciprocal of
its actual number of other completions. -/
theorem actual_double_charge_lt_inverse_degree
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H) (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxy : x ≠ y)
    (hv : v ∈ (completionVertices H V ({x, y} : Edge α)).erase z)
    (hdouble : (commonLink H V ({z, v} : Edge α)).card = 2) :
    actualReceiverCharge H V z x y v <
      1 / (((completionVertices H V ({x, y} : Edge α)).card : ℚ) - 1) := by
  let N := completionVertices H V ({x, y} : Edge α)
  have hvN : v ∈ N := (Finset.mem_erase.mp hv).2
  have hzv : z ≠ v := Ne.symm (Finset.mem_erase.mp hv).1
  have hvV : v ∈ V := (Finset.mem_filter.mp hvN).1
  have hzN : z ∈ N := root_mem_source_completion H V hzV hsource
  have hpair : ({z, v} : Edge α) ⊆ N := by
    intro t ht
    rcases Finset.mem_insert.mp ht with htz | htv
    · exact htz ▸ hzN
    · exact (Finset.mem_singleton.mp htv) ▸ hvN
  have hdegree : 2 ≤ N.card := by
    have hc := Finset.card_le_card hpair
    rw [Finset.card_pair hzv] at hc
    exact hc
  have hsourceLink := source_pair_mem_receiving_link H V hsource hvN
  have heq : commonLink H V ({z, v} : Edge α) =
      orientedCommonLink H V z v := by
    ext p
    exact mem_common_link_pair_iff_oriented H V hzv p
  have hdoubleOrient : (orientedCommonLink H V z v).card = 2 := by
    rw [← heq]
    exact hdouble
  have hweight := rooted_signed_weight_lt_one_of_double_receiving_link
    hH hzV hvV hzv hxy hsourceLink hdoubleOrient
  have hpositive : positiveRootedWeight H V z x y < 1 := by
    by_cases hw : rootedSignedWeight H V z x y ≤ 0
    · simp [positiveRootedWeight, max_eq_right hw]
    · have hwpos : 0 < rootedSignedWeight H V z x y := lt_of_not_ge hw
      simpa [positiveRootedWeight, max_eq_left (le_of_lt hwpos)] using hweight
  have hden : 0 < (N.card : ℚ) - 1 := by
    have hc : (2 : ℚ) ≤ N.card := by exact_mod_cast hdegree
    linarith
  have hdiv := div_lt_div_of_pos_right hpositive hden
  have hcharge : actualReceiverCharge H V z x y v =
      positiveRootedWeight H V z x y / ((N.card : ℚ) - 1) := by
    simp [actualReceiverCharge, chargePerOtherCompletion, hv, N]
  rw [hcharge]
  exact hdiv

/-- Concrete one-source bound in reciprocal form. A low root-endpoint degree
forces zero charge; otherwise the target core degree supplies the reciprocal
factor used in the c=2 grouping. -/
theorem actual_double_charge_le_reciprocal_indicator
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H) (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxy : x ≠ y)
    (hv : v ∈ (completionVertices H V ({x, y} : Edge α)).erase z)
    (hdouble : (commonLink H V ({z, v} : Edge α)).card = 2) :
    actualReceiverCharge H V z x y v ≤
      (if 4 ≤ (completionVertices H V ({z, x} : Edge α)).card then
        if 4 ≤ (completionVertices H V ({x, y} : Edge α)).card then
          (1 : ℚ) / 3 else 1 else 0) := by
  let N := completionVertices H V ({x, y} : Edge α)
  have hvN : v ∈ N := (Finset.mem_erase.mp hv).2
  have hzv : z ≠ v := Ne.symm (Finset.mem_erase.mp hv).1
  have hzN : z ∈ N := root_mem_source_completion H V hzV hsource
  have hpair : ({z, v} : Edge α) ⊆ N := by
    intro a ha
    rcases Finset.mem_insert.mp ha with haz | hav
    · exact haz ▸ hzN
    · exact (Finset.mem_singleton.mp hav) ▸ hvN
  have hdegree : 2 ≤ N.card := by
    have hc := Finset.card_le_card hpair
    rw [Finset.card_pair hzv] at hc
    exact hc
  have hchargeInv := actual_double_charge_lt_inverse_degree
    hH hzV hsource hxy hv hdouble
  by_cases hroot : 4 ≤ (completionVertices H V ({z, x} : Edge α)).card
  · have hInv := reciprocal_completion_degree_bound N.card hdegree
    have hInv' : 1 / ((N.card : ℚ) - 1) ≤
        if 4 ≤ N.card then (1 : ℚ) / 3 else 1 := hInv
    have hle := (le_of_lt hchargeInv).trans hInv'
    simpa [hroot, N] using hle
  · have hzero := actual_charge_eq_zero_of_low_root_degree
      H V hsource hv (by omega :
        (completionVertices H V ({z, x} : Edge α)).card < 4)
    simp [hzero, hroot]

/-- At a double receiver, the actual charge sent by one positive source is
strictly less than one. -/
theorem actual_charge_lt_one_at_double_receiver
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxy : x ≠ y)
    (hv : v ∈ (completionVertices H V ({x, y} : Edge α)).erase z)
    (hdouble : (commonLink H V ({z, v} : Edge α)).card = 2) :
    actualReceiverCharge H V z x y v < 1 := by
  have hlt := charge_lt_one_of_double_receiver
    hH hzV hsource hxy hv hdouble
  simp [actualReceiverCharge, hv]
  exact hlt

/-- For an actual positive source of completion degree at least two, summing
its charges over all other completion vertices recovers its full weight. -/
theorem actual_source_charge_conservation
    (H : Family α) (V : Edge α) {z x y : α}
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ rootLink H V z)
    (hdegree : 2 ≤ (completionVertices H V ({x, y} : Edge α)).card) :
    (∑ v ∈ (completionVertices H V ({x, y} : Edge α)).erase z,
      actualReceiverCharge H V z x y v) =
      positiveRootedWeight H V z x y := by
  have heq :
      (∑ v ∈ (completionVertices H V ({x, y} : Edge α)).erase z,
        actualReceiverCharge H V z x y v) =
      ∑ v ∈ (completionVertices H V ({x, y} : Edge α)).erase z,
        chargePerOtherCompletion H V z x y := by
    apply Finset.sum_congr rfl
    intro v hv
    simp [actualReceiverCharge, hv]
  rw [heq]
  exact outgoing_charge_conservation H V hzV hsource hdegree

/-- A base pair in the actual common link of `{z,v}` gives genuine rooted
link sources at both roots. -/
theorem common_link_pair_gives_two_sources
    {H : Family α} {V p : Edge α} {z v : α}
    (_hzv : z ≠ v)
    (hp : p ∈ commonLink H V ({z, v} : Edge α)) :
    p ∈ rootLink H V z ∧ p ∈ rootLink H V v := by
  obtain ⟨hpV, a, ha, b, hb, hab, hpq, hpa, hpb⟩ :=
    Finset.mem_filter.mp hp
  have ha' : a = z ∨ a = v := by
    simpa using ha
  have hb' : b = z ∨ b = v := by
    simpa using hb
  have hza : z ∉ p := by
    intro hzp
    have hmeet := (Finset.disjoint_left.mp hpq) hzp (by simp)
    exact hmeet
  have hva : v ∉ p := by
    intro hvp
    have hmeet := (Finset.disjoint_left.mp hpq) hvp (by simp)
    exact hmeet
  have hpz : p ∪ {z} ∈ H := by
    rcases ha' with haZ | haV
    · simpa [haZ] using hpa
    · rcases hb' with hbZ | hbV
      · simpa [hbZ] using hpb
      · exact False.elim (hab (haV.trans hbV.symm))
  have hpv : p ∪ {v} ∈ H := by
    rcases ha' with haZ | haV
    · rcases hb' with hbZ | hbV
      · exact False.elim (hab (haZ.trans hbZ.symm))
      · simpa [hbV] using hpb
    · simpa [haV] using hpa
  exact ⟨Finset.mem_filter.mpr ⟨hpV, hza, hpz⟩,
    Finset.mem_filter.mpr ⟨hpV, hva, hpv⟩⟩

/-- The two actual directions associated with one core pair contribute less
than four in total. This is the local numerical content behind the c=1
capacity bound; identifying this pair with the unique common-link base is a
separate incidence argument. -/
theorem two_root_same_core_charge_lt_four
    (H : Family α) (V : Edge α) {z v x y : α}
    (hzV : z ∈ V) (hvV : v ∈ V) (hzv : z ≠ v) (hxy : x ≠ y)
    (hsourceZ : ({x, y} : Edge α) ∈ rootLink H V z)
    (hsourceV : ({x, y} : Edge α) ∈ rootLink H V v) :
    actualReceiverCharge H V z x y v +
      actualReceiverCharge H V v x y z < 4 := by
  have hvComp : v ∈ completionVertices H V ({x, y} : Edge α) :=
    root_mem_source_completion H V hvV hsourceV
  have hzComp : z ∈ completionVertices H V ({x, y} : Edge α) :=
    root_mem_source_completion H V hzV hsourceZ
  have hvErase : v ∈ (completionVertices H V ({x, y} : Edge α)).erase z :=
    Finset.mem_erase.mpr ⟨Ne.symm hzv, hvComp⟩
  have hzErase : z ∈ (completionVertices H V ({x, y} : Edge α)).erase v :=
    Finset.mem_erase.mpr ⟨hzv, hzComp⟩
  have hdeg : 2 ≤ (completionVertices H V ({x, y} : Edge α)).card := by
    have hp : ({z, v} : Edge α) ⊆ completionVertices H V ({x, y} : Edge α) := by
      intro a ha
      rcases Finset.mem_insert.mp ha with h | h
      · exact h ▸ hzComp
      · exact (Finset.mem_singleton.mp h) ▸ hvComp
    have hc := Finset.card_le_card hp
    rw [Finset.card_pair hzv] at hc
    exact hc
  have hfirst := actual_charge_lt_two H V hsourceZ hxy hvErase hdeg
  have hsecond := actual_charge_lt_two H V hsourceV hxy hzErase hdeg
  linarith

/-- A rooted core can send charge from `z` to `v` exactly when it is a
base pair in the actual common link of `{z,v}`. -/
theorem source_receiver_iff_common_link
    (H : Family α) (V : Edge α) {p : Edge α} {z v : α}
    (hzV : z ∈ V) (hvV : v ∈ V) (hzv : z ≠ v) :
    (p ∈ rootLink H V z ∧
      v ∈ (completionVertices H V p).erase z) ↔
    p ∈ commonLink H V ({z, v} : Edge α) := by
  constructor
  · rintro ⟨hsource, hv⟩
    have hpV := (Finset.mem_filter.mp hsource).1
    have hzComp : z ∈ completionVertices H V p := by
      obtain ⟨_, hznot, hpz⟩ := Finset.mem_filter.mp hsource
      exact Finset.mem_filter.mpr ⟨hzV, hznot, hpz⟩
    have hvComp := Finset.mem_erase.mp hv |>.2
    have hqV : ({z, v} : Edge α) ∈ V.powersetCard 2 := by
      apply Finset.mem_powersetCard.mpr
      exact ⟨by
        intro a ha
        rcases Finset.mem_insert.mp ha with haz | hav
        · exact haz ▸ hzV
        · exact (Finset.mem_singleton.mp hav) ▸ hvV,
        Finset.card_pair hzv⟩
    have hpCells : ({z, v} : Edge α) ∈ completionCells H V p := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, Finset.card_pair hzv⟩
      intro a ha
      rcases Finset.mem_insert.mp ha with haz | hav
      · exact haz ▸ hzComp
      · exact (Finset.mem_singleton.mp hav) ▸ hvComp
    exact (mem_common_link_iff_mem_completion_cells H V _ _ hqV hpV).2 hpCells
  · intro hp
    have hsrc := common_link_pair_gives_two_sources hzv hp
    have hvComp : v ∈ completionVertices H V p := by
      obtain ⟨_, hvnot, hpv⟩ := Finset.mem_filter.mp hsrc.2
      exact Finset.mem_filter.mpr ⟨hvV, hvnot, hpv⟩
    exact ⟨hsrc.1, Finset.mem_erase.mpr ⟨Ne.symm hzv, hvComp⟩⟩

/-- Charge into one oriented receiver `(z,v)`, indexed by all rooted sources
at `z` which can complete to `v`. -/
noncomputable def oneWayReceiverChargeTotal
    (H : Family α) (V : Edge α) (z v : α) : ℚ := by
  classical
  exact ∑ p ∈ rootLink H V z, coreChargeKernel H V z v p

/-- Reindex one oriented receiver's actual rooted sources by the common-link
base pairs of its cell. -/
theorem one_way_receiver_charge_eq_common_link_sum
    (H : Family α) (V : Edge α) {z v : α}
    (hzV : z ∈ V) (hvV : v ∈ V) (hzv : z ≠ v) :
    oneWayReceiverChargeTotal H V z v =
      ∑ p ∈ commonLink H V ({z, v} : Edge α),
        coreReceiverCharge H V z v p := by
  classical
  let S := rootLink H V z
  let P : Edge α → Prop := fun p =>
    v ∈ (completionVertices H V p).erase z
  have hfilter : S.filter P = commonLink H V ({z, v} : Edge α) := by
    ext p
    simp only [Finset.mem_filter, S, P]
    exact source_receiver_iff_common_link H V hzV hvV hzv
  unfold oneWayReceiverChargeTotal
  change (∑ p ∈ S, coreChargeKernel H V z v p) = _
  calc
    (∑ p ∈ S, coreChargeKernel H V z v p) =
        ∑ p ∈ S, if P p then coreReceiverCharge H V z v p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [coreChargeKernel, S, P, hp]
    _ = ∑ p ∈ S.filter P, coreReceiverCharge H V z v p := by
      rw [← Finset.sum_filter]
    _ = ∑ p ∈ commonLink H V ({z, v} : Edge α),
        coreReceiverCharge H V z v p := by rw [hfilter]

/-- Sum of charges grouped by oriented receiving pair and by actual common-link
base pair. -/
noncomputable def incomingCommonLinkChargeTotal
    (H : Family α) (V : Edge α) : ℚ := by
  classical
  exact ∑ z ∈ V, ∑ v ∈ V.erase z,
    ∑ p ∈ commonLink H V ({z, v} : Edge α),
      coreReceiverCharge H V z v p

/-- The incoming source sum is exactly the sum over actual receiving cells and
their common-link base pairs. -/
theorem incoming_charge_common_link_reindex
    (H : Family α) (V : Edge α) :
    incomingCoreChargeTotal H V = incomingCommonLinkChargeTotal H V := by
  classical
  unfold incomingCoreChargeTotal incomingCommonLinkChargeTotal
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro v hv
  have hvV : v ∈ V := (Finset.mem_erase.mp hv).2
  have hzv : z ≠ v := Ne.symm (Finset.mem_erase.mp hv).1
  exact one_way_receiver_charge_eq_common_link_sum H V hz hvV hzv

/-- Full Fubini identity for actual charges: order first by source core or by
receiving common-link cell. -/
theorem actual_charge_fubini_by_common_link
    (H : Family α) (V : Edge α) :
    outgoingCoreChargeTotal H V = incomingCommonLinkChargeTotal H V := by
  rw [← incoming_charge_common_link_reindex H V]
  exact actual_core_charge_fubini H V

/-- Reversing the two endpoints of an actual core leaves its sent charge
unchanged. -/
theorem actual_receiver_charge_comm
    (H : Family α) (V : Edge α) (z v x y : α) :
    actualReceiverCharge H V z x y v =
      actualReceiverCharge H V z y x v := by
  have hcomp : completionVertices H V ({x, y} : Edge α) =
      completionVertices H V ({y, x} : Edge α) := by
    simp only [Finset.pair_comm]
  simp only [actualReceiverCharge, hcomp, chargePerOtherCompletion,
    positiveRootedWeight, rooted_signed_weight_comm]

/-- A core charge obtained from the chosen endpoint representation agrees
with the charge on any displayed representation of the same pair. -/
theorem core_receiver_charge_eq_displayed_pair
    (H : Family α) (V p : Edge α) (z v x y : α)
    (hp : p.card = 2) (hpair : p = ({x, y} : Edge α)) :
    coreReceiverCharge H V z v p = actualReceiverCharge H V z x y v := by
  classical
  let e := corePairRep p hp
  have he := core_pair_rep_spec p hp
  have heq : ({e.1, e.2} : Edge α) = ({x, y} : Edge α) :=
    he.2.symm.trans hpair
  have he1 : e.1 = x ∨ e.1 = y := by
    have hm : e.1 ∈ ({x, y} : Edge α) := by
      rw [← heq]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hcases : (e.1 = x ∧ e.2 = y) ∨ (e.1 = y ∧ e.2 = x) := by
    rcases he1 with h1 | h1
    · have hm : e.2 ∈ ({x, y} : Edge α) := by
        rw [← heq]
        simp
      rcases (show e.2 = x ∨ e.2 = y by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm) with h2 | h2
      · exact False.elim (he.1 (h1.trans h2.symm))
      · exact Or.inl ⟨h1, h2⟩
    · have hm : e.2 ∈ ({x, y} : Edge α) := by
        rw [← heq]
        simp
      rcases (show e.2 = x ∨ e.2 = y by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm) with h2 | h2
      · exact Or.inr ⟨h1, h2⟩
      · exact False.elim (he.1 (h1.trans h2.symm))
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [coreReceiverCharge, hp, e, h1, h2]
  · rw [actual_receiver_charge_comm]
    simp [coreReceiverCharge, hp, e, h1, h2]

/-- Total charge received at the ordered cell `{z,v}`, grouped by its actual
common-link core pairs and including both choices of root. -/
noncomputable def actualCellChargeTotal
    (H : Family α) (V : Edge α) (z v : α) : ℚ := by
  classical
  exact ∑ p ∈ commonLink H V ({z, v} : Edge α),
    (coreReceiverCharge H V z v p + coreReceiverCharge H V v z p)

/-- Every common link of an admissible family is either a star or has at
most three edges (and hence lies in a triangle). -/
theorem common_link_star_or_card_le_three
    {H : Family α} {V : Edge α} {z v : α}
    (hH : Admissible H) (_hzV : z ∈ V) (_hvV : v ∈ V) (hzv : z ≠ v) :
    (∃ x : α, ∀ p ∈ commonLink H V ({z, v} : Edge α), x ∈ p) ∨
      (commonLink H V ({z, v} : Edge α)).card ≤ 3 := by
  apply intersecting_pair_graph_star_or_small
  · intro p hp
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp q hq
    exact common_link_pair_intersecting hH hzv hp hq

/-- The actual two-root charges over one common-link core pair are below four. -/
theorem common_link_core_bidirectional_charge_lt_four
    {H : Family α} {V p : Edge α} {z v : α}
    (hzV : z ∈ V) (hvV : v ∈ V) (hzv : z ≠ v)
    (hp : p ∈ commonLink H V ({z, v} : Edge α)) :
    coreReceiverCharge H V z v p + coreReceiverCharge H V v z p < 4 := by
  have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp
    (Finset.mem_filter.mp hp).1).2
  let e := corePairRep p hp2
  have he := core_pair_rep_spec p hp2
  have hsrc := common_link_pair_gives_two_sources hzv hp
  have hsrcZ : ({e.1, e.2} : Edge α) ∈ rootLink H V z := by
    rw [← he.2]
    exact hsrc.1
  have hsrcV : ({e.1, e.2} : Edge α) ∈ rootLink H V v := by
    rw [← he.2]
    exact hsrc.2
  have hbound := two_root_same_core_charge_lt_four
    H V hzV hvV hzv he.1 hsrcZ hsrcV
  simpa [coreReceiverCharge, hp2, e] using hbound

/-- With exactly two known bases, the actual cell total expands to the four
rooted charges on those bases. -/
theorem actual_cell_charge_total_eq_two_cores
    (H : Family α) (V : Edge α) {z v : α} {p₁ p₂ : Edge α}
    (hp₁ : p₁ ∈ commonLink H V ({z, v} : Edge α))
    (hp₂ : p₂ ∈ commonLink H V ({z, v} : Edge α))
    (hne : p₁ ≠ p₂)
    (hcard : (commonLink H V ({z, v} : Edge α)).card = 2) :
    actualCellChargeTotal H V z v =
      (coreReceiverCharge H V z v p₁ + coreReceiverCharge H V v z p₁) +
      (coreReceiverCharge H V z v p₂ + coreReceiverCharge H V v z p₂) := by
  classical
  have hsub : ({p₁, p₂} : Finset (Edge α)) ⊆
      commonLink H V ({z, v} : Edge α) := by
    intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · simpa [h] using hp₁
    · exact (Finset.mem_singleton.mp h) ▸ hp₂
  have hpairCard : ({p₁, p₂} : Finset (Edge α)).card = 2 :=
    Finset.card_pair hne
  have hset' : ({p₁, p₂} : Finset (Edge α)) =
      commonLink H V ({z, v} : Edge α) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hpairCard])
  have hset : commonLink H V ({z, v} : Edge α) = {p₁, p₂} := hset'.symm
  unfold actualCellChargeTotal
  rw [hset]
  simp [hne]

/-- A one-core receiving cell has total actual charge below four. -/
theorem singleton_cell_charge_total_lt_four
    (H : Family α) (V : Edge α) {z v : α}
    (hzV : z ∈ V) (hvV : v ∈ V) (hzv : z ≠ v)
    (hcard : (commonLink H V ({z, v} : Edge α)).card = 1) :
    actualCellChargeTotal H V z v < 4 := by
  classical
  unfold actualCellChargeTotal
  obtain ⟨p₀, hp₀⟩ := Finset.card_eq_one.mp hcard
  have hp₀mem : p₀ ∈ commonLink H V ({z, v} : Edge α) := by
    rw [hp₀]
    exact Finset.mem_singleton_self _
  rw [hp₀]
  simp only [Finset.sum_singleton]
  exact common_link_core_bidirectional_charge_lt_four hzV hvV hzv hp₀mem

/-- If a common-link cell has exactly one core pair, the two actual rooted
sources for that core have total charge below four. This proves the numerical
c=1 bound on its unique core; a separate incidence sum accounts for the whole
cell charge. -/
theorem singleton_common_link_core_charge_lt_four
    {H : Family α} {V q p : Edge α} {z v : α}
    (hzV : z ∈ V) (hvV : v ∈ V) (hzv : z ≠ v)
    (hq : q = ({z, v} : Edge α))
    (_hcard : (commonLink H V q).card = 1)
    (hp : p ∈ commonLink H V q) :
    ∃ x y : α, x ≠ y ∧ p = ({x, y} : Edge α) ∧
      actualReceiverCharge H V z x y v +
        actualReceiverCharge H V v x y z < 4 := by
  have hpV := (Finset.mem_filter.mp hp).1
  obtain ⟨x, y, hxy, hpEq⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hpV).2
  subst p
  subst q
  have hsrc := common_link_pair_gives_two_sources hzv hp
  refine ⟨x, y, hxy, rfl, ?_⟩
  exact two_root_same_core_charge_lt_four H V hzV hvV hzv hxy hsrc.1 hsrc.2

/-- Every admissible two-core receiver has a reciprocal common-link cell.
The two possible outcomes correspond to the two ways its cores can intersect. -/
theorem double_receiver_has_reciprocal_cell
    {H : Family α} {V : Edge α} {z v : α}
    (hH : Admissible H) (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v)
    (hcard : (commonLink H V ({z, v} : Edge α)).card = 2) :
    ∃ x y u : α, x ≠ y ∧ x ≠ u ∧ y ≠ u ∧ y ∈ V ∧ u ∈ V ∧
      ((({x, y} : Edge α) ∈ commonLink H V ({z, v} : Edge α) ∧
       ({x, u} : Edge α) ∈ commonLink H V ({z, v} : Edge α) ∧
       ({v, x} : Edge α) ∈ commonLink H V ({y, u} : Edge α) ∧
       ({z, x} : Edge α) ∈ commonLink H V ({y, u} : Edge α)) ∨
       (({x, y} : Edge α) ∈ commonLink H V ({z, v} : Edge α) ∧
       ({y, u} : Edge α) ∈ commonLink H V ({z, v} : Edge α) ∧
       ({v, y} : Edge α) ∈ commonLink H V ({x, u} : Edge α) ∧
       ({z, y} : Edge α) ∈ commonLink H V ({x, u} : Edge α))) := by
  have htwo := Finset.card_eq_two.mp hcard
  obtain ⟨p, t, hpt, hcells⟩ := htwo
  have hp : p ∈ commonLink H V ({z, v} : Edge α) := by
    rw [hcells]
    simp
  have ht : t ∈ commonLink H V ({z, v} : Edge α) := by
    rw [hcells]
    simp
  have hpOrient := (mem_common_link_pair_iff_oriented H V hzv p).mp hp
  have htOrient := (mem_common_link_pair_iff_oriented H V hzv t).mp ht
  have hpSwap : p ∈ commonLink H V ({v, z} : Edge α) := by
    simpa only [Finset.pair_comm] using hp
  have htSwap : t ∈ commonLink H V ({v, z} : Edge α) := by
    simpa only [Finset.pair_comm] using ht
  have hpRev := (mem_common_link_pair_iff_oriented H V (Ne.symm hzv) p).mp hpSwap
  have htRev := (mem_common_link_pair_iff_oriented H V (Ne.symm hzv) t).mp htSwap
  have hp2 : p.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpOrient).1).2
  obtain ⟨x, y, hxy, hpEq⟩ := Finset.card_eq_two.mp hp2
  subst p
  have hyV : y ∈ V := by
    have hsubset := (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hpOrient).1).1
    exact hsubset (by simp)
  have htErase : t ∈ (orientedCommonLink H V z v).erase ({x, y} : Edge α) :=
    Finset.mem_erase.mpr ⟨by
      intro heq
      exact hpt heq.symm, htOrient⟩
  have hcovered := other_receiving_pairs_covered_by_weak_alternatives
    hH hzV hvV hzv hxy hpOrient htErase
  rcases Finset.mem_union.mp hcovered with hright | hleft
  · obtain ⟨u, huWeak, htu⟩ := Finset.mem_image.mp hright
    change u ∈ ((rootNeighbors H V z x).erase y).filter _ at huWeak
    have huMem := (Finset.mem_filter.mp huWeak).1
    have huy : u ≠ y := (Finset.mem_erase.mp huMem).1
    have hxu : x ≠ u := by
      intro h
      subst u
      exact root_neighbors_not_self H V z x (Finset.mem_erase.mp huMem).2
    have h_yu : y ≠ u := Ne.symm huy
    have huV : u ∈ V := root_neighbors_subset_ground H V z x
      (Finset.mem_erase.mp huMem).2
    have hxuLink : ({x, u} : Edge α) ∈ orientedCommonLink H V z v := by
      rw [htu]
      exact htOrient
    have hrecip := reciprocal_pair_in_common_link H V hvV
      hxy hxu h_yu hpOrient hxuLink
    have hxuLinkRev : ({x, u} : Edge α) ∈ orientedCommonLink H V v z := by
      rw [htu]
      exact htRev
    have hrecipRev := reciprocal_pair_in_common_link H V hzV
      hxy hxu h_yu hpRev hxuLinkRev
    have hxuCore : ({x, u} : Edge α) ∈ commonLink H V ({z, v} : Edge α) := by
      rw [htu]
      exact ht
    exact ⟨x, y, u, hxy, hxu, h_yu, hyV, huV,
      Or.inl ⟨hp, hxuCore, hrecip, hrecipRev⟩⟩
  · obtain ⟨u, huWeak, htu⟩ := Finset.mem_image.mp hleft
    change u ∈ ((rootNeighbors H V z y).erase x).filter _ at huWeak
    have huMem := (Finset.mem_filter.mp huWeak).1
    have hux : u ≠ x := (Finset.mem_erase.mp huMem).1
    have hyu : y ≠ u := by
      intro h
      subst u
      exact root_neighbors_not_self H V z y (Finset.mem_erase.mp huMem).2
    have hxu : x ≠ u := Ne.symm hux
    have huV : u ∈ V := root_neighbors_subset_ground H V z y
      (Finset.mem_erase.mp huMem).2
    have hyxSource : ({y, x} : Edge α) ∈ orientedCommonLink H V z v := by
      simpa only [Finset.pair_comm] using hpOrient
    have hyuLink : ({y, u} : Edge α) ∈ orientedCommonLink H V z v := by
      rw [htu]
      exact htOrient
    have hrecip := reciprocal_pair_in_common_link H V hvV
      (Ne.symm hxy) hyu hxu hyxSource hyuLink
    have hyxSourceRev : ({y, x} : Edge α) ∈ orientedCommonLink H V v z := by
      simpa only [Finset.pair_comm] using hpRev
    have hyuLinkRev : ({y, u} : Edge α) ∈ orientedCommonLink H V v z := by
      rw [htu]
      exact htRev
    have hrecipRev := reciprocal_pair_in_common_link H V hzV
      (Ne.symm hxy) hyu hxu hyxSourceRev hyuLinkRev
    have hyuCore : ({y, u} : Edge α) ∈ commonLink H V ({z, v} : Edge α) := by
      rw [htu]
      exact ht
    exact ⟨x, y, u, hxy, hxu, hyu, hyV, huV,
      Or.inr ⟨hp, hyuCore, hrecip, hrecipRev⟩⟩

/-- Applying the reciprocal construction at the reciprocal cell returns to
the original receiving pair, with its second core. -/
theorem double_receiver_reciprocal_returns
    {H : Family α} {V : Edge α} {z v : α}
    (hH : Admissible H) (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v)
    (hcard : (commonLink H V ({z, v} : Edge α)).card = 2) :
    ∃ x y u : α, x ≠ y ∧ x ≠ u ∧ y ≠ u ∧
      ({u, x} : Edge α) ∈ commonLink H V ({z, v} : Edge α) := by
  obtain ⟨x, y, u, hxy, hxu, hyu, hyV, huV, hreciprocal⟩ :=
    double_receiver_has_reciprocal_cell hH hzV hvV hzv hcard
  rcases hreciprocal with ⟨_, _, hvx, hzx⟩ | ⟨_, _, hvy, hzy⟩
  · have hvx' : ({x, v} : Edge α) ∈ commonLink H V ({y, u} : Edge α) := by
      simpa only [Finset.pair_comm] using hvx
    have hzx' : ({x, z} : Edge α) ∈ commonLink H V ({y, u} : Edge α) := by
      simpa only [Finset.pair_comm] using hzx
    have hxvLink : ({x, v} : Edge α) ∈ orientedCommonLink H V y u :=
      (mem_common_link_pair_iff_oriented H V hyu _).mp hvx'
    have hxzLink : ({x, z} : Edge α) ∈ orientedCommonLink H V y u :=
      (mem_common_link_pair_iff_oriented H V hyu _).mp hzx'
    have hxvNe : x ≠ v := by
      have hc := (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp hvx).1).2
      exact Ne.symm (Finset.card_pair_eq_two_iff.mp hc)
    have hxzNe : x ≠ z := by
      have hc := (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp hzx).1).2
      exact Ne.symm (Finset.card_pair_eq_two_iff.mp hc)
    have hvzNe : v ≠ z := Ne.symm hzv
    have hback := reciprocal_pair_in_common_link H V huV
      hxvNe hxzNe hvzNe hxvLink hxzLink
    have hback' : ({u, x} : Edge α) ∈ commonLink H V ({z, v} : Edge α) := by
      simpa only [Finset.pair_comm] using hback
    exact ⟨x, y, u, hxy, hxu, hyu, hback'⟩
  · have hvy' : ({y, v} : Edge α) ∈ commonLink H V ({x, u} : Edge α) := by
      simpa only [Finset.pair_comm] using hvy
    have hzy' : ({y, z} : Edge α) ∈ commonLink H V ({x, u} : Edge α) := by
      simpa only [Finset.pair_comm] using hzy
    have hyvLink : ({y, v} : Edge α) ∈ orientedCommonLink H V x u :=
      (mem_common_link_pair_iff_oriented H V hxu _).mp hvy'
    have hyzLink : ({y, z} : Edge α) ∈ orientedCommonLink H V x u :=
      (mem_common_link_pair_iff_oriented H V hxu _).mp hzy'
    have hyvNe : y ≠ v := by
      have hc := (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp hvy).1).2
      exact Ne.symm (Finset.card_pair_eq_two_iff.mp hc)
    have hyzNe : y ≠ z := by
      have hc := (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp hzy).1).2
      exact Ne.symm (Finset.card_pair_eq_two_iff.mp hc)
    have hvzNe : v ≠ z := Ne.symm hzv
    have hback := reciprocal_pair_in_common_link H V huV
      hyvNe hyzNe hvzNe hyvLink hyzLink
    have hback' : ({u, y} : Edge α) ∈ commonLink H V ({z, v} : Edge α) := by
      simpa only [Finset.pair_comm] using hback
    exact ⟨y, x, u, Ne.symm hxy, hyu, hxu, hback'⟩

/-- The reciprocal cell produced from a double receiver has at least two
common-link bases, one for each choice of the original root. -/
theorem double_receiver_reciprocal_card_ge_two
    {H : Family α} {V : Edge α} {z v : α}
    (hH : Admissible H) (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v)
    (hcard : (commonLink H V ({z, v} : Edge α)).card = 2) :
    ∃ q : Edge α, 2 ≤ (commonLink H V q).card := by
  obtain ⟨x, y, u, hxy, hxu, hyu, hyV, huV, hreciprocal⟩ :=
    double_receiver_has_reciprocal_cell hH hzV hvV hzv hcard
  rcases hreciprocal with ⟨_, _, hvx, hzx⟩ | ⟨_, _, hvy, hzy⟩
  · let p₁ : Edge α := {v, x}
    let p₂ : Edge α := {z, x}
    have hp₁ : p₁ ∈ commonLink H V ({y, u} : Edge α) := by simpa [p₁] using hvx
    have hp₂ : p₂ ∈ commonLink H V ({y, u} : Edge α) := by simpa [p₂] using hzx
    have hcard₁ := (Finset.card_pair_eq_two_iff.mp
      ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp₁).1).2))
    have hcard₂ := (Finset.card_pair_eq_two_iff.mp
      ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp₂).1).2))
    have hne : p₁ ≠ p₂ := by
      intro heq
      have hmem : v ∈ ({z, x} : Edge α) := by
        change v ∈ p₂
        rw [← heq]
        simp [p₁]
      rcases Finset.mem_insert.mp hmem with hvz | hvx'
      · exact hzv hvz.symm
      · exact hcard₁ (Finset.mem_singleton.mp hvx')
    have hsub : ({p₁, p₂} : Finset (Edge α)) ⊆
        commonLink H V ({y, u} : Edge α) := by
      intro p hp
      rcases Finset.mem_insert.mp hp with h | h
      · simpa [h] using hp₁
      · exact (Finset.mem_singleton.mp h) ▸ hp₂
    have hle := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at hle
    exact ⟨{y, u}, hle⟩
  · let p₁ : Edge α := {v, y}
    let p₂ : Edge α := {z, y}
    have hp₁ : p₁ ∈ commonLink H V ({x, u} : Edge α) := by simpa [p₁] using hvy
    have hp₂ : p₂ ∈ commonLink H V ({x, u} : Edge α) := by simpa [p₂] using hzy
    have hcard₁ := (Finset.card_pair_eq_two_iff.mp
      ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp₁).1).2))
    have hcard₂ := (Finset.card_pair_eq_two_iff.mp
      ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp₂).1).2))
    have hne : p₁ ≠ p₂ := by
      intro heq
      have hmem : v ∈ ({z, y} : Edge α) := by
        change v ∈ p₂
        rw [← heq]
        simp [p₁]
      rcases Finset.mem_insert.mp hmem with hvz | hvy'
      · exact hzv hvz.symm
      · exact hcard₁ (Finset.mem_singleton.mp hvy')
    have hsub : ({p₁, p₂} : Finset (Edge α)) ⊆
        commonLink H V ({x, u} : Edge α) := by
      intro p hp
      rcases Finset.mem_insert.mp hp with h | h
      · simpa [h] using hp₁
      · exact (Finset.mem_singleton.mp h) ▸ hp₂
    have hle := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at hle
    exact ⟨{x, u}, hle⟩

/-- The eight indicator-weighted reciprocal terms from two reciprocal
receivers obey the scalar capacity bound of §II.5. -/
theorem reciprocal_indicator_matrix_le_four
    (d₁ d₂ d₃ d₄ : ℕ) :
    (if 4 ≤ d₁ then (if 4 ≤ d₃ then (1 : ℚ) / 3 else 1) +
        (if 4 ≤ d₄ then (1 : ℚ) / 3 else 1) else 0) +
    (if 4 ≤ d₂ then (if 4 ≤ d₃ then (1 : ℚ) / 3 else 1) +
        (if 4 ≤ d₄ then (1 : ℚ) / 3 else 1) else 0) +
    (if 4 ≤ d₃ then (if 4 ≤ d₁ then (1 : ℚ) / 3 else 1) +
        (if 4 ≤ d₂ then (1 : ℚ) / 3 else 1) else 0) +
    (if 4 ≤ d₄ then (if 4 ≤ d₁ then (1 : ℚ) / 3 else 1) +
        (if 4 ≤ d₂ then (1 : ℚ) / 3 else 1) else 0) ≤ 4 := by
  let h₁ : ℕ := (if 4 ≤ d₁ then 1 else 0) + (if 4 ≤ d₂ then 1 else 0)
  let h₂ : ℕ := (if 4 ≤ d₃ then 1 else 0) + (if 4 ≤ d₄ then 1 else 0)
  have hh₁ : h₁ ≤ 2 := by dsimp [h₁]; split_ifs <;> omega
  have hh₂ : h₂ ≤ 2 := by dsimp [h₂]; split_ifs <;> omega
  have hformula :
      (if 4 ≤ d₁ then (if 4 ≤ d₃ then (1 : ℚ) / 3 else 1) +
          (if 4 ≤ d₄ then (1 : ℚ) / 3 else 1) else 0) +
      (if 4 ≤ d₂ then (if 4 ≤ d₃ then (1 : ℚ) / 3 else 1) +
          (if 4 ≤ d₄ then (1 : ℚ) / 3 else 1) else 0) +
      (if 4 ≤ d₃ then (if 4 ≤ d₁ then (1 : ℚ) / 3 else 1) +
          (if 4 ≤ d₂ then (1 : ℚ) / 3 else 1) else 0) +
      (if 4 ≤ d₄ then (if 4 ≤ d₁ then (1 : ℚ) / 3 else 1) +
          (if 4 ≤ d₂ then (1 : ℚ) / 3 else 1) else 0) =
        (h₁ : ℚ) * (2 - 2 * (h₂ : ℚ) / 3) +
          (h₂ : ℚ) * (2 - 2 * (h₁ : ℚ) / 3) := by
    simp only [h₁, h₂]
    split_ifs <;> norm_num
  rw [hformula]
  exact reciprocal_pair_capacity_le_four h₁ h₂ hh₁ hh₂

/-- Eight actual charge bounds with the reciprocal degree pattern sum to at
most four. The source-specific indicator hypotheses are supplied by
`actual_double_charge_le_reciprocal_indicator`. -/
theorem reciprocal_eight_charge_capacity_le_four
    (d₁ d₂ d₃ d₄ : ℕ)
    (c₁₃ c₁₄ c₂₃ c₂₄ c₃₁ c₃₂ c₄₁ c₄₂ : ℚ)
    (h₁₃ : c₁₃ ≤ if 4 ≤ d₁ then (if 4 ≤ d₃ then (1 : ℚ) / 3 else 1) else 0)
    (h₁₄ : c₁₄ ≤ if 4 ≤ d₁ then (if 4 ≤ d₄ then (1 : ℚ) / 3 else 1) else 0)
    (h₂₃ : c₂₃ ≤ if 4 ≤ d₂ then (if 4 ≤ d₃ then (1 : ℚ) / 3 else 1) else 0)
    (h₂₄ : c₂₄ ≤ if 4 ≤ d₂ then (if 4 ≤ d₄ then (1 : ℚ) / 3 else 1) else 0)
    (h₃₁ : c₃₁ ≤ if 4 ≤ d₃ then (if 4 ≤ d₁ then (1 : ℚ) / 3 else 1) else 0)
    (h₃₂ : c₃₂ ≤ if 4 ≤ d₃ then (if 4 ≤ d₂ then (1 : ℚ) / 3 else 1) else 0)
    (h₄₁ : c₄₁ ≤ if 4 ≤ d₄ then (if 4 ≤ d₁ then (1 : ℚ) / 3 else 1) else 0)
    (h₄₂ : c₄₂ ≤ if 4 ≤ d₄ then (if 4 ≤ d₂ then (1 : ℚ) / 3 else 1) else 0) :
    c₁₃ + c₁₄ + c₂₃ + c₂₄ + c₃₁ + c₃₂ + c₄₁ + c₄₂ ≤ 4 := by
  have hmatrix := reciprocal_indicator_matrix_le_four d₁ d₂ d₃ d₄
  by_cases h₁ : 4 ≤ d₁ <;> by_cases h₂ : 4 ≤ d₂ <;>
    by_cases h₃ : 4 ≤ d₃ <;> by_cases h₄ : 4 ≤ d₄ <;>
    simp_all <;> linarith

/-- Actual capacity of a reciprocal pair of two-core cells. The four source
core pairs and their eight rooted directions are stated explicitly; each term
is then bounded by its actual completion degree and the §II.5 scalar estimate. -/
theorem actual_reciprocal_double_cell_capacity_le_four
    {H : Family α} {V : Edge α} {x y u z v : α}
    (hH : Admissible H)
    (hyV : y ∈ V) (huV : u ∈ V)
    (hzV : z ∈ V) (hvV : v ∈ V)
    (hxy : x ≠ y) (hxu : x ≠ u) (hxv : x ≠ v) (hxz : x ≠ z)
    (hzv : z ≠ v) (hyu : y ≠ u)
    (h₁ : ({x, y} : Edge α) ∈ commonLink H V ({z, v} : Edge α))
    (h₂ : ({x, u} : Edge α) ∈ commonLink H V ({z, v} : Edge α))
    (h₃ : ({x, v} : Edge α) ∈ commonLink H V ({y, u} : Edge α))
    (h₄ : ({x, z} : Edge α) ∈ commonLink H V ({y, u} : Edge α))
    (hc₁ : (commonLink H V ({z, v} : Edge α)).card = 2)
    (hc₂ : (commonLink H V ({y, u} : Edge α)).card = 2) :
    actualCellChargeTotal H V z v + actualCellChargeTotal H V y u ≤ 4 := by
  have hs₁ := common_link_pair_gives_two_sources hzv h₁
  have hs₂ := common_link_pair_gives_two_sources hzv h₂
  have hs₃ := common_link_pair_gives_two_sources hyu h₃
  have hs₄ := common_link_pair_gives_two_sources hyu h₄
  have hne₁ : ({x, y} : Edge α) ≠ {x, u} := by
    intro heq
    have hyMem : y ∈ ({x, u} : Edge α) := by rw [← heq]; simp
    rcases Finset.mem_insert.mp hyMem with h | h
    · exact hxy h.symm
    · exact hyu (Finset.mem_singleton.mp h)
  have hne₂ : ({x, v} : Edge α) ≠ {x, z} := by
    intro heq
    have hvMem : v ∈ ({x, z} : Edge α) := by rw [← heq]; simp
    rcases Finset.mem_insert.mp hvMem with h | h
    · exact hxv h.symm
    · exact hzv (Finset.mem_singleton.mp h).symm
  have hcell₁ := actual_cell_charge_total_eq_two_cores H V h₁ h₂ hne₁ hc₁
  have hcell₂ := actual_cell_charge_total_eq_two_cores H V h₃ h₄ hne₂ hc₂
  have hcard₁ : ({x, y} : Edge α).card = 2 := Finset.card_pair hxy
  have hcard₂ : ({x, u} : Edge α).card = 2 := Finset.card_pair hxu
  have hcard₃ : ({x, v} : Edge α).card = 2 := Finset.card_pair hxv
  have hcard₄ : ({x, z} : Edge α).card = 2 := Finset.card_pair hxz
  have hv₁ : v ∈ (completionVertices H V ({x, y} : Edge α)).erase z :=
    Finset.mem_erase.mpr ⟨Ne.symm hzv,
      root_mem_source_completion H V hvV hs₁.2⟩
  have hz₁ : z ∈ (completionVertices H V ({x, y} : Edge α)).erase v :=
    Finset.mem_erase.mpr ⟨hzv, root_mem_source_completion H V hzV hs₁.1⟩
  have hv₂ : v ∈ (completionVertices H V ({x, u} : Edge α)).erase z :=
    Finset.mem_erase.mpr ⟨Ne.symm hzv,
      root_mem_source_completion H V hvV hs₂.2⟩
  have hz₂ : z ∈ (completionVertices H V ({x, u} : Edge α)).erase v :=
    Finset.mem_erase.mpr ⟨hzv, root_mem_source_completion H V hzV hs₂.1⟩
  have hu₃ : u ∈ (completionVertices H V ({x, v} : Edge α)).erase y :=
    Finset.mem_erase.mpr ⟨Ne.symm hyu,
      root_mem_source_completion H V huV hs₃.2⟩
  have hy₃ : y ∈ (completionVertices H V ({x, v} : Edge α)).erase u :=
    Finset.mem_erase.mpr ⟨hyu, root_mem_source_completion H V hyV hs₃.1⟩
  have hu₄ : u ∈ (completionVertices H V ({x, z} : Edge α)).erase y :=
    Finset.mem_erase.mpr ⟨Ne.symm hyu,
      root_mem_source_completion H V huV hs₄.2⟩
  have hy₄ : y ∈ (completionVertices H V ({x, z} : Edge α)).erase u :=
    Finset.mem_erase.mpr ⟨hyu, root_mem_source_completion H V hyV hs₄.1⟩
  let d₁ := (completionVertices H V ({x, z} : Edge α)).card
  let d₂ := (completionVertices H V ({x, v} : Edge α)).card
  let d₃ := (completionVertices H V ({x, y} : Edge α)).card
  let d₄ := (completionVertices H V ({x, u} : Edge α)).card
  have c₁₃ := actual_double_charge_le_reciprocal_indicator
    hH hzV hs₁.1 hxy hv₁ hc₁
  have c₁₄ := actual_double_charge_le_reciprocal_indicator
    hH hzV hs₂.1 hxu hv₂ hc₁
  have c₂₃ := actual_double_charge_le_reciprocal_indicator
    hH hvV hs₁.2 hxy hz₁ (by simpa [Finset.pair_comm] using hc₁)
  have c₂₄ := actual_double_charge_le_reciprocal_indicator
    hH hvV hs₂.2 hxu hz₂ (by simpa [Finset.pair_comm] using hc₁)
  have c₃₂ := actual_double_charge_le_reciprocal_indicator
    hH hyV hs₃.1 hxv hu₃ hc₂
  have c₃₁ := actual_double_charge_le_reciprocal_indicator
    hH hyV hs₄.1 hxz hu₄ hc₂
  have c₄₂ := actual_double_charge_le_reciprocal_indicator
    hH huV hs₃.2 hxv hy₃ (by simpa [Finset.pair_comm] using hc₂)
  have c₄₁ := actual_double_charge_le_reciprocal_indicator
    hH huV hs₄.2 hxz hy₄ (by simpa [Finset.pair_comm] using hc₂)
  have c₁₃' : actualReceiverCharge H V z x y v ≤
      if 4 ≤ d₁ then (if 4 ≤ d₃ then (1 : ℚ) / 3 else 1) else 0 := by
    simpa [d₁, d₃, Finset.pair_comm] using c₁₃
  have c₁₄' : actualReceiverCharge H V z x u v ≤
      if 4 ≤ d₁ then (if 4 ≤ d₄ then (1 : ℚ) / 3 else 1) else 0 := by
    simpa [d₁, d₄, Finset.pair_comm] using c₁₄
  have c₂₃' : actualReceiverCharge H V v x y z ≤
      if 4 ≤ d₂ then (if 4 ≤ d₃ then (1 : ℚ) / 3 else 1) else 0 := by
    simpa [d₂, d₃, Finset.pair_comm] using c₂₃
  have c₂₄' : actualReceiverCharge H V v x u z ≤
      if 4 ≤ d₂ then (if 4 ≤ d₄ then (1 : ℚ) / 3 else 1) else 0 := by
    simpa [d₂, d₄, Finset.pair_comm] using c₂₄
  have c₃₂' : actualReceiverCharge H V y x v u ≤
      if 4 ≤ d₃ then (if 4 ≤ d₂ then (1 : ℚ) / 3 else 1) else 0 := by
    simpa [d₃, d₂, Finset.pair_comm] using c₃₂
  have c₃₁' : actualReceiverCharge H V y x z u ≤
      if 4 ≤ d₃ then (if 4 ≤ d₁ then (1 : ℚ) / 3 else 1) else 0 := by
    simpa [d₃, d₁, Finset.pair_comm] using c₃₁
  have c₄₂' : actualReceiverCharge H V u x v y ≤
      if 4 ≤ d₄ then (if 4 ≤ d₂ then (1 : ℚ) / 3 else 1) else 0 := by
    simpa [d₄, d₂, Finset.pair_comm] using c₄₂
  have c₄₁' : actualReceiverCharge H V u x z y ≤
      if 4 ≤ d₄ then (if 4 ≤ d₁ then (1 : ℚ) / 3 else 1) else 0 := by
    simpa [d₄, d₁, Finset.pair_comm] using c₄₁
  have hscalar := reciprocal_eight_charge_capacity_le_four
    d₁ d₂ d₃ d₄ _ _ _ _ _ _ _ _ c₁₃' c₁₄' c₂₃' c₂₄' c₃₁' c₃₂' c₄₁' c₄₂'
  have hrep₁ := core_receiver_charge_eq_displayed_pair H V
    ({x, y} : Edge α) z v x y hcard₁ rfl
  have hrep₂ := core_receiver_charge_eq_displayed_pair H V
    ({x, u} : Edge α) z v x u hcard₂ rfl
  have hrep₃ := core_receiver_charge_eq_displayed_pair H V
    ({x, v} : Edge α) y u x v hcard₃ rfl
  have hrep₄ := core_receiver_charge_eq_displayed_pair H V
    ({x, z} : Edge α) y u x z hcard₄ rfl
  have hrep₁b := core_receiver_charge_eq_displayed_pair H V
    ({x, y} : Edge α) v z x y hcard₁ rfl
  have hrep₂b := core_receiver_charge_eq_displayed_pair H V
    ({x, u} : Edge α) v z x u hcard₂ rfl
  have hrep₃b := core_receiver_charge_eq_displayed_pair H V
    ({x, v} : Edge α) u y x v hcard₃ rfl
  have hrep₄b := core_receiver_charge_eq_displayed_pair H V
    ({x, z} : Edge α) u y x z hcard₄ rfl
  rw [hcell₁, hcell₂, hrep₁, hrep₂, hrep₃, hrep₄,
    hrep₁b, hrep₂b, hrep₃b, hrep₄b]
  linarith

/-- The two-root receiver total is independent of which endpoint is listed first. -/
theorem actual_cell_charge_total_comm (H : Family α) (V : Edge α) (z v : α) :
    actualCellChargeTotal H V z v = actualCellChargeTotal H V v z := by
  classical
  unfold actualCellChargeTotal
  simp only [Finset.pair_comm]
  rw [Finset.sum_congr rfl]
  intro p hp
  ring

/-- Evaluate a receiver cell represented as an unordered two-element set. -/
noncomputable def actualCellChargeForPair
    (H : Family α) (V : Edge α) (q : Edge α) : ℚ := by
  classical
  if hq : q.card = 2 then
    let e := corePairRep q hq
    exact actualCellChargeTotal H V e.1 e.2
  else exact 0

/-- The triangle exception in §II.5: a two-core receiver cell whose two
cores share a center, while the reciprocal cell consists of the three edges
of a triangle. This is an actual finite-family predicate. -/
def triangleExceptionalReceiverCell
    (H : Family α) (V : Edge α) (q : Edge α) : Prop :=
  ∃ z v x y u : α, z ∈ V ∧ v ∈ V ∧ x ∈ V ∧ y ∈ V ∧ u ∈ V ∧
    q = ({z, v} : Edge α) ∧
    commonLink H V q = ({({x, y} : Edge α), ({x, u} : Edge α)} : Family α) ∧
    commonLink H V ({y, u} : Edge α) =
      ({({x, z} : Edge α), ({x, v} : Edge α), ({z, v} : Edge α)} : Family α)

/-- Actual excess above the ordinary capacity two, indexed once per
exceptional receiver cell. The sum is over actual used cells, so this is the
finite Xi quantity for the later ledger assembly. -/
noncomputable def actualXi (H : Family α) (V : Edge α) : ℚ := by
  classical
  exact ∑ q ∈ usedCells H V,
    if triangleExceptionalReceiverCell H V q then
      max (actualCellChargeForPair H V q - 2) 0 else 0

/-- Two distinct members force a finite set to have at least two elements. -/
theorem finset_card_ge_two_of_distinct_members {β : Type*} [DecidableEq β]
    (s : Finset β) {a b : β} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    2 ≤ s.card := by
  have hsub : ({a, b} : Finset β) ⊆ s := by
    intro t ht
    rcases Finset.mem_insert.mp ht with h | h
    · simpa [h] using ha
    · exact (Finset.mem_singleton.mp h) ▸ hb
  have hle := Finset.card_le_card hsub
  rw [Finset.card_pair hab] at hle
  exact hle

/-- Pairing a two-core cell with a two-core reciprocal cell has total
actual charge at most four. -/
theorem double_receiver_reciprocal_pair_capacity_le_four
    {H : Family α} {V : Edge α} {z v : α}
    (hH : Admissible H) (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v)
    (hcard : (commonLink H V ({z, v} : Edge α)).card = 2)
    (hrecipCard : ∀ q : Edge α, 2 ≤ (commonLink H V q).card →
      (commonLink H V q).card = 2) :
    ∃ x y u : α, x ≠ y ∧ x ≠ u ∧ y ≠ u ∧ y ∈ V ∧ u ∈ V ∧
      ((({x, y} : Edge α) ∈ commonLink H V ({z, v} : Edge α) ∧
        ({x, u} : Edge α) ∈ commonLink H V ({z, v} : Edge α) ∧
        ({v, x} : Edge α) ∈ commonLink H V ({y, u} : Edge α) ∧
        ({z, x} : Edge α) ∈ commonLink H V ({y, u} : Edge α) ∧
        actualCellChargeTotal H V z v + actualCellChargeTotal H V y u ≤ 4) ∨
       (({x, y} : Edge α) ∈ commonLink H V ({z, v} : Edge α) ∧
        ({y, u} : Edge α) ∈ commonLink H V ({z, v} : Edge α) ∧
        ({v, y} : Edge α) ∈ commonLink H V ({x, u} : Edge α) ∧
        ({z, y} : Edge α) ∈ commonLink H V ({x, u} : Edge α) ∧
        actualCellChargeTotal H V z v + actualCellChargeTotal H V x u ≤ 4)) := by
  obtain ⟨x, y, u, hxy, hxu, hyu, hyV, huV, hcases⟩ :=
    double_receiver_has_reciprocal_cell hH hzV hvV hzv hcard
  rcases hcases with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
  · have hxv : x ≠ v := by
      have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₃).1).2
      exact (Finset.card_pair_eq_two_iff.mp hc).symm
    have hxz : x ≠ z := by
      have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₄).1).2
      exact (Finset.card_pair_eq_two_iff.mp hc).symm
    have p₁ : ({v, x} : Edge α) ∈ commonLink H V ({y, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₃
    have p₂ : ({z, x} : Edge α) ∈ commonLink H V ({y, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₄
    have hne : ({v, x} : Edge α) ≠ ({z, x} : Edge α) := by
      intro he
      have hv : v ∈ ({z, x} : Edge α) := by rw [← he]; simp
      rcases Finset.mem_insert.mp hv with hvz | hvx
      · exact hzv hvz.symm
      · exact hxv (Finset.mem_singleton.mp hvx).symm
    have htwo := finset_card_ge_two_of_distinct_members
      (commonLink H V ({y, u} : Edge α)) p₁ p₂ hne
    have hc₂ := hrecipCard ({y, u} : Edge α) htwo
    have hcap := actual_reciprocal_double_cell_capacity_le_four hH
      hyV huV hzV hvV hxy hxu hxv hxz hzv hyu h₁ h₂
      (by simpa only [Finset.pair_comm] using h₃)
      (by simpa only [Finset.pair_comm] using h₄) hcard hc₂
    exact ⟨x, y, u, hxy, hxu, hyu, hyV, huV,
      Or.inl ⟨h₁, h₂, h₃, h₄, hcap⟩⟩
  · have hyv : y ≠ v := by
      have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₃).1).2
      exact (Finset.card_pair_eq_two_iff.mp hc).symm
    have hyz : y ≠ z := by
      have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₄).1).2
      exact (Finset.card_pair_eq_two_iff.mp hc).symm
    have p₁ : ({v, y} : Edge α) ∈ commonLink H V ({x, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₃
    have p₂ : ({z, y} : Edge α) ∈ commonLink H V ({x, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₄
    have hne : ({v, y} : Edge α) ≠ ({z, y} : Edge α) := by
      intro he
      have hv : v ∈ ({z, y} : Edge α) := by rw [← he]; simp
      rcases Finset.mem_insert.mp hv with hvz | hvy
      · exact hzv hvz.symm
      · exact hyv (Finset.mem_singleton.mp hvy).symm
    have htwo := finset_card_ge_two_of_distinct_members
      (commonLink H V ({x, u} : Edge α)) p₁ p₂ hne
    have hc₂ := hrecipCard ({x, u} : Edge α) htwo
    have hxV : x ∈ V := by
      have hsubset := (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp h₁).1).1
      exact hsubset (by simp)
    have hc₁' : (commonLink H V ({x, u} : Edge α)).card = 2 := hc₂
    have hc₂' : (commonLink H V ({v, z} : Edge α)).card = 2 := by
      simpa only [Finset.pair_comm] using hcard
    have hr₁ : ({y, v} : Edge α) ∈ commonLink H V ({x, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₃
    have hr₂ : ({y, z} : Edge α) ∈ commonLink H V ({x, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₄
    have hs₁ : ({y, x} : Edge α) ∈ commonLink H V ({v, z} : Edge α) := by
      simpa only [Finset.pair_comm] using h₁
    have hs₂ : ({y, u} : Edge α) ∈ commonLink H V ({v, z} : Edge α) := by
      simpa only [Finset.pair_comm] using h₂
    have hcap := actual_reciprocal_double_cell_capacity_le_four hH
      hvV hzV hxV huV hyv hyz hyu (Ne.symm hxy) hxu (Ne.symm hzv)
      hr₁ hr₂ hs₂ hs₁ hc₁' hc₂'
    have hcap' : actualCellChargeTotal H V z v + actualCellChargeTotal H V x u ≤ 4 := by
      rw [← actual_cell_charge_total_comm H V z v] at hcap
      linarith
    exact ⟨x, y, u, hxy, hxu, hyu, hyV, huV,
      Or.inr ⟨h₁, h₂, h₃, h₄, hcap'⟩⟩

/-- A degree-one positive source is retained at its source pair, with weight
strictly below two. -/
theorem retained_positive_weight_lt_two
    (H : Family α) (V : Edge α) {z x y : α}
    (hsource : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxy : x ≠ y)
    (hdegree : (completionVertices H V ({x, y} : Edge α)).card = 1) :
    retainedPositiveWeight H V z x y < 2 := by
  simp [retainedPositiveWeight, hdegree]
  exact positive_rooted_weight_lt_two H V hsource hxy

end ReceiverCapacity

end JSP523.Rank3
