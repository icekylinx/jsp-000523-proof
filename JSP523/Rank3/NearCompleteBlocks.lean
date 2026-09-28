import JSP523.Rank3.ExactSupportLedger
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Removing near-complete five-vertex blocks

The manuscript removes every nine- or ten-triple block at once.  Here we
prepare a sequential version: remove all triples using two vertices of
one block, then repeat.  A local support inequality for one block suffices
because deletion cannot create a new dense block.
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

def blockTriples (H : Family α) (A : Edge α) : Family α :=
  H.filter fun E => E ⊆ A

def missingBlockTriples (H : Family α) (A : Edge α) : Family α :=
  A.powersetCard 3 \ H

def nearCompleteBlock (H : Family α) (A : Edge α) : Prop :=
  A.card = 5 ∧ 9 ≤ (blockTriples H A).card

theorem blockTriples_mono {H K : Family α} (hHK : H ⊆ K)
    (A : Edge α) : blockTriples H A ⊆ blockTriples K A := by
  intro E hE
  exact Finset.mem_filter.mpr
    ⟨hHK (Finset.mem_filter.mp hE).1, (Finset.mem_filter.mp hE).2⟩

theorem blockTriples_eq_inter_powerset
    (H : Family α) (A : Edge α) (hU : Uniform 3 H) :
    blockTriples H A = A.powersetCard 3 ∩ H := by
  ext E
  simp only [blockTriples, Finset.mem_filter, Finset.mem_inter,
    Finset.mem_powersetCard]
  constructor
  · rintro ⟨hEH, hEA⟩
    exact ⟨⟨hEA, hU hEH⟩, hEH⟩
  · rintro ⟨⟨hEA, _⟩, hEH⟩
    exact ⟨hEH, hEA⟩

theorem missingBlockTriples_card_le_one
    (H : Family α) (A : Edge α) (hU : Uniform 3 H)
    (hA : nearCompleteBlock H A) :
    (missingBlockTriples H A).card ≤ 1 := by
  obtain ⟨hAcard, hDense⟩ := hA
  have hAll : (A.powersetCard 3).card = 10 := by
    rw [Finset.card_powersetCard, hAcard]
    decide
  have hPart := Finset.card_sdiff_add_card_inter
    (A.powersetCard 3) H
  rw [← blockTriples_eq_inter_powerset H A hU] at hPart
  change (missingBlockTriples H A).card +
    (blockTriples H A).card = (A.powersetCard 3).card at hPart
  omega

theorem missingBlockTriples_unique
    (H : Family α) (A : Edge α) (hU : Uniform 3 H)
    (hA : nearCompleteBlock H A)
    {S T : Edge α}
    (hS : S ∈ missingBlockTriples H A)
    (hT : T ∈ missingBlockTriples H A) : S = T := by
  exact (Finset.card_le_one.mp
    (missingBlockTriples_card_le_one H A hU hA)) S hS T hT

/-- Distinct candidate triples of a near-complete block cannot both be
missing from the parent family. -/
theorem nearComplete_one_of_two
    (H : Family α) (A : Edge α) (hU : Uniform 3 H)
    (hA : nearCompleteBlock H A)
    {S T : Edge α}
    (hS : S ∈ A.powersetCard 3)
    (hT : T ∈ A.powersetCard 3)
    (hST : S ≠ T) : S ∈ H ∨ T ∈ H := by
  by_contra h
  have hs : S ∈ missingBlockTriples H A :=
    Finset.mem_sdiff.mpr ⟨hS, fun hSH => h (Or.inl hSH)⟩
  have ht : T ∈ missingBlockTriples H A :=
    Finset.mem_sdiff.mpr ⟨hT, fun hTH => h (Or.inr hTH)⟩
  exact hST (missingBlockTriples_unique H A hU hA hs ht)


/-- Pair traces from one outside vertex into a five-point block. -/
def blockTrace (H : Family α) (A : Edge α) (x : α) : Family α :=
  (A.powersetCard 2).filter fun p => p ∪ {x} ∈ H

/-- Internal completions of a pair inside the block. -/
def blockInternalCompleters
    (H : Family α) (A p : Edge α) : Edge α :=
  (A \ p).filter fun y => p ∪ {y} ∈ H

private theorem internal_completion_candidate
    (A p : Edge α) (hp : p ∈ A.powersetCard 2)
    {y : α} (hy : y ∈ A \ p) :
    p ∪ {y} ∈ A.powersetCard 3 := by
  obtain ⟨hpA, hp2⟩ := Finset.mem_powersetCard.mp hp
  obtain ⟨hyA, hyp⟩ := Finset.mem_sdiff.mp hy
  apply Finset.mem_powersetCard.mpr
  constructor
  · exact Finset.union_subset hpA (Finset.singleton_subset_iff.mpr hyA)
  · rw [Finset.union_singleton, Finset.card_insert_of_notMem hyp, hp2]

private theorem internal_completion_injective
    (p : Edge α) {y z : α} (hy : y ∉ p) (_hz : z ∉ p)
    (h : p ∪ {y} = p ∪ {z}) : y = z := by
  have hyMem : y ∈ p ∪ {z} := h ▸ (by simp : y ∈ p ∪ {y})
  rcases Finset.mem_union.mp hyMem with hP | hZ
  · exact False.elim (hy hP)
  · simpa using hZ

theorem blockInternalCompleters_card_ge_two
    (H : Family α) (A p : Edge α)
    (hU : Uniform 3 H)
    (hA : nearCompleteBlock H A)
    (hp : p ∈ A.powersetCard 2) :
    2 ≤ (blockInternalCompleters H A p).card := by
  let C := A \ p
  let Bad := C.filter fun y => p ∪ {y} ∉ H
  have hCcard : C.card = 3 := by
    rw [Finset.card_sdiff_of_subset
      (Finset.mem_powersetCard.mp hp).1,
      hA.1, (Finset.mem_powersetCard.mp hp).2]
  have hBad : Bad.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro y hy z hz
    have hyC : y ∈ C := (Finset.mem_filter.mp hy).1
    have hzC : z ∈ C := (Finset.mem_filter.mp hz).1
    have hyNot : p ∪ {y} ∉ H := (Finset.mem_filter.mp hy).2
    have hzNot : p ∪ {z} ∉ H := (Finset.mem_filter.mp hz).2
    have hyMissing : p ∪ {y} ∈ missingBlockTriples H A :=
      Finset.mem_sdiff.mpr
        ⟨internal_completion_candidate A p hp hyC, hyNot⟩
    have hzMissing : p ∪ {z} ∈ missingBlockTriples H A :=
      Finset.mem_sdiff.mpr
        ⟨internal_completion_candidate A p hp hzC, hzNot⟩
    have hEq := missingBlockTriples_unique H A hU hA hyMissing hzMissing
    exact internal_completion_injective p
      (Finset.mem_sdiff.mp hyC).2
      (Finset.mem_sdiff.mp hzC).2 hEq
  have hPartition := Finset.card_filter_add_card_filter_not
    (s := C) (p := fun y => p ∪ {y} ∈ H)
  change (blockInternalCompleters H A p).card + Bad.card = C.card
    at hPartition
  omega



private theorem complement_pair_injective
    (A p q : Edge α) (hp : p ⊆ A) (hq : q ⊆ A)
    (h : A \ p = A \ q) : p = q := by
  have h' := congrArg (fun S : Edge α => A \ S) h
  simpa [Finset.sdiff_sdiff_eq_self hp,
    Finset.sdiff_sdiff_eq_self hq] using h'

private theorem block_extension_disjoint_complement
    (A p : Edge α) (x : α) (hx : x ∉ A) :
    Disjoint (p ∪ {x}) (A \ p) := by
  apply Finset.disjoint_left.mpr
  intro v hv hComp
  obtain ⟨hvA, hvp⟩ := Finset.mem_sdiff.mp hComp
  rcases Finset.mem_union.mp hv with hP | hX
  · exact hvp hP
  · exact hx ((Finset.mem_singleton.mp hX) ▸ hvA)

private theorem block_extension_union_complement
    (A p : Edge α) (x : α) (hp : p ⊆ A) :
    (p ∪ {x}) ∪ (A \ p) = A ∪ {x} := by
  calc
    (p ∪ {x}) ∪ (A \ p) = (p ∪ (A \ p)) ∪ {x} := by ac_rfl
    _ = A ∪ {x} := by rw [Finset.union_sdiff_of_subset hp]

/-- Two different external traces cannot both have their complementary
internal triples present: they would partition the same six-set twice. -/
theorem block_trace_complements_not_both
    (H : Family α) (A : Edge α) (x : α)
    (hAdm : Admissible H) (hxA : x ∉ A)
    {p q : Edge α}
    (hp : p ∈ blockTrace H A x)
    (hq : q ∈ blockTrace H A x)
    (hpq : p ≠ q)
    (hpComp : A \ p ∈ H)
    (hqComp : A \ q ∈ H) : False := by
  obtain ⟨hpCand, hpEdge⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqCand, hqEdge⟩ := Finset.mem_filter.mp hq
  have hpA := (Finset.mem_powersetCard.mp hpCand).1
  have hqA := (Finset.mem_powersetCard.mp hqCand).1
  have hxp : x ∉ p := fun h => hxA (hpA h)
  have hxq : x ∉ q := fun h => hxA (hqA h)
  have hExtNe : p ∪ {x} ≠ q ∪ {x} := by
    intro h
    have h' := congrArg (fun S : Edge α => S.erase x) h
    rw [Finset.union_singleton, Finset.erase_insert hxp,
      Finset.union_singleton, Finset.erase_insert hxq] at h'
    exact hpq h'
  have hCompNe : A \ p ≠ A \ q :=
    fun h => hpq (complement_pair_injective A p q hpA hqA h)
  have hExtPNeCompP : p ∪ {x} ≠ A \ p := by
    intro h
    have hx : x ∈ A \ p := h ▸ (by simp : x ∈ p ∪ {x})
    exact hxA (Finset.mem_sdiff.mp hx).1
  have hExtPNeCompQ : p ∪ {x} ≠ A \ q := by
    intro h
    have hx : x ∈ A \ q := h ▸ (by simp : x ∈ p ∪ {x})
    exact hxA (Finset.mem_sdiff.mp hx).1
  have hExtQNeCompP : q ∪ {x} ≠ A \ p := by
    intro h
    have hx : x ∈ A \ p := h ▸ (by simp : x ∈ q ∪ {x})
    exact hxA (Finset.mem_sdiff.mp hx).1
  have hExtQNeCompQ : q ∪ {x} ≠ A \ q := by
    intro h
    have hx : x ∈ A \ q := h ▸ (by simp : x ∈ q ∪ {x})
    exact hxA (Finset.mem_sdiff.mp hx).1
  have hEqUnion :
      (p ∪ {x}) ∪ (A \ p) =
        (q ∪ {x}) ∪ (A \ q) := by
    rw [block_extension_union_complement A p x hpA,
      block_extension_union_complement A q x hqA]
  apply hAdm hpEdge hpComp hqEdge hqComp
  refine ⟨?_, block_extension_disjoint_complement A p x hxA,
    block_extension_disjoint_complement A q x hxA, hEqUnion⟩
  exact ⟨hExtPNeCompP, hExtNe, hExtPNeCompQ,
    hExtQNeCompP.symm, hCompNe, hExtQNeCompQ⟩



private theorem block_complement_candidate
    (A p : Edge α)
    (hA : A.card = 5)
    (hp : p ∈ A.powersetCard 2) :
    A \ p ∈ A.powersetCard 3 := by
  obtain ⟨hpA, hp2⟩ := Finset.mem_powersetCard.mp hp
  apply Finset.mem_powersetCard.mpr
  constructor
  · exact Finset.sdiff_subset
  · rw [Finset.card_sdiff_of_subset hpA, hA, hp2]

/-- At a fixed outside vertex, there are at most two pairs of the
near-complete block whose extensions occur in the family. -/
theorem blockTrace_card_le_two
    (H : Family α) (A : Edge α) (x : α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hA : nearCompleteBlock H A) (hxA : x ∉ A) :
    (blockTrace H A x).card ≤ 2 := by
  let T := blockTrace H A x
  let Good := T.filter fun p => A \ p ∈ H
  let Bad := T.filter fun p => A \ p ∉ H
  have hGood : Good.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    by_contra hpq
    have hpT : p ∈ T := (Finset.mem_filter.mp hp).1
    have hqT : q ∈ T := (Finset.mem_filter.mp hq).1
    have hpH : A \ p ∈ H := (Finset.mem_filter.mp hp).2
    have hqH : A \ q ∈ H := (Finset.mem_filter.mp hq).2
    exact block_trace_complements_not_both H A x hAdm hxA
      hpT hqT hpq hpH hqH
  have hBad : Bad.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    have hpT : p ∈ T := (Finset.mem_filter.mp hp).1
    have hqT : q ∈ T := (Finset.mem_filter.mp hq).1
    have hpCand := (Finset.mem_filter.mp hpT).1
    have hqCand := (Finset.mem_filter.mp hqT).1
    have hpMissing : A \ p ∈ missingBlockTriples H A :=
      Finset.mem_sdiff.mpr
        ⟨block_complement_candidate A p hA.1 hpCand,
          (Finset.mem_filter.mp hp).2⟩
    have hqMissing : A \ q ∈ missingBlockTriples H A :=
      Finset.mem_sdiff.mpr
        ⟨block_complement_candidate A q hA.1 hqCand,
          (Finset.mem_filter.mp hq).2⟩
    exact complement_pair_injective A p q
      (Finset.mem_powersetCard.mp hpCand).1
      (Finset.mem_powersetCard.mp hqCand).1
      (missingBlockTriples_unique H A hU hA hpMissing hqMissing)
  have hPart := Finset.card_filter_add_card_filter_not
    (s := T) (p := fun p => A \ p ∈ H)
  change Good.card + Bad.card = T.card at hPart
  change T.card ≤ 2
  omega



/-- If the complementary triple of an internal pair is the one missing
triple, all three completions of the pair are present. -/
theorem blockInternalCompleters_eq_complement
    (H : Family α) (A p : Edge α)
    (hU : Uniform 3 H) (hA : nearCompleteBlock H A)
    (hp : p ∈ A.powersetCard 2)
    (hMissing : A \ p ∉ H) :
    blockInternalCompleters H A p = A \ p := by
  obtain ⟨t, ht⟩ : p.Nonempty := by
    apply Finset.card_pos.mp
    have hp2 := (Finset.mem_powersetCard.mp hp).2
    omega
  have hCompCand := block_complement_candidate A p hA.1 hp
  apply Finset.ext
  intro y
  constructor
  · intro hy
    exact (Finset.mem_filter.mp hy).1
  · intro hy
    apply Finset.mem_filter.mpr
    refine ⟨hy, ?_⟩
    have hCandidate := internal_completion_candidate A p hp hy
    have hneq : p ∪ {y} ≠ A \ p := by
      intro heq
      have htComp : t ∈ A \ p := heq ▸
        (Finset.mem_union_left {y} ht)
      exact (Finset.mem_sdiff.mp htComp).2 ht
    exact (nearComplete_one_of_two H A hU hA hCandidate
      hCompCand hneq).resolve_right hMissing

/-- Two distinct pair traces have at least four different internal
certificate vertices when the first pair has a missing complement. -/
theorem block_two_trace_completers_union_ge_four
    (H : Family α) (A p q : Edge α)
    (hU : Uniform 3 H) (hA : nearCompleteBlock H A)
    (hp : p ∈ A.powersetCard 2)
    (hq : q ∈ A.powersetCard 2)
    (hpq : p ≠ q)
    (hMissing : A \ p ∉ H) :
    4 ≤ (blockInternalCompleters H A p ∪
      blockInternalCompleters H A q).card := by
  obtain ⟨hpA, hp2⟩ := Finset.mem_powersetCard.mp hp
  obtain ⟨hqA, hq2⟩ := Finset.mem_powersetCard.mp hq
  have hNotSub : ¬ p ⊆ q := by
    intro hsub
    exact hpq (Finset.eq_of_subset_of_card_le hsub (by omega))
  have hDiff : (p \ q).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hEmpty
    exact hNotSub (Finset.sdiff_eq_empty_iff_subset.mp hEmpty)
  obtain ⟨y, hyDiff⟩ := hDiff
  obtain ⟨hyP, hyQ⟩ := Finset.mem_sdiff.mp hyDiff
  have hyA : y ∈ A := hpA hyP
  have hyC : y ∈ A \ q := Finset.mem_sdiff.mpr ⟨hyA, hyQ⟩
  have hqCandidate := internal_completion_candidate A q hq hyC
  have hpCompCandidate := block_complement_candidate A p hA.1 hp
  have hneq : q ∪ {y} ≠ A \ p := by
    intro heq
    have hyComp : y ∈ A \ p := heq ▸ (by simp : y ∈ q ∪ {y})
    exact (Finset.mem_sdiff.mp hyComp).2 hyP
  have hqy : q ∪ {y} ∈ H :=
    (nearComplete_one_of_two H A hU hA hqCandidate
      hpCompCandidate hneq).resolve_right hMissing
  have hyNq : y ∈ blockInternalCompleters H A q :=
    Finset.mem_filter.mpr ⟨hyC, hqy⟩
  have hNp := blockInternalCompleters_eq_complement H A p
    hU hA hp hMissing
  have hyNotNp : y ∉ A \ p :=
    fun h => (Finset.mem_sdiff.mp h).2 hyP
  have hsub : insert y (A \ p) ⊆
      blockInternalCompleters H A p ∪
        blockInternalCompleters H A q := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.mem_union_right _ hyNq
    · exact Finset.mem_union_left _ (hNp.symm ▸ hv)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hyNotNp,
    Finset.card_sdiff_of_subset hpA, hA.1, hp2] at hcard
  omega



/-- For each fixed external vertex, internal completions provide at
least two distinct certificate vertices per trace pair. -/
theorem block_trace_certificate_count
    (H : Family α) (A : Edge α) (x : α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hA : nearCompleteBlock H A) (hxA : x ∉ A) :
    2 * (blockTrace H A x).card ≤
      ((blockTrace H A x).biUnion
        (blockInternalCompleters H A)).card := by
  let T := blockTrace H A x
  have hTle := blockTrace_card_le_two H A x hU hAdm hA hxA
  have hCases : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 := by
    change T.card ≤ 2 at hTle
    omega
  rcases hCases with hZero | hOne | hTwo
  · have hEmpty : T = ∅ := Finset.card_eq_zero.mp hZero
    simp [T, hEmpty]
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hOne
    have hpTrace : p ∈ blockTrace H A x := by
      change p ∈ T
      simp [hp]
    have hpCand := (Finset.mem_filter.mp hpTrace).1
    have hN := blockInternalCompleters_card_ge_two H A p hU hA hpCand
    change 2 * T.card ≤
      (T.biUnion (blockInternalCompleters H A)).card
    simp [hp]
    exact hN
  · obtain ⟨p, q, hpq, hT⟩ := Finset.card_eq_two.mp hTwo
    have hpTrace : p ∈ blockTrace H A x := by
      change p ∈ T
      simp [hT]
    have hqTrace : q ∈ blockTrace H A x := by
      change q ∈ T
      simp [hT]
    have hpCand := (Finset.mem_filter.mp hpTrace).1
    have hqCand := (Finset.mem_filter.mp hqTrace).1
    have hUnion : 4 ≤
        (blockInternalCompleters H A p ∪
          blockInternalCompleters H A q).card := by
      by_cases hpPresent : A \ p ∈ H
      · have hqMissing : A \ q ∉ H := by
          intro hqPresent
          exact block_trace_complements_not_both H A x hAdm hxA
            hpTrace hqTrace hpq hpPresent hqPresent
        simpa only [Finset.union_comm] using
          block_two_trace_completers_union_ge_four H A q p
            hU hA hqCand hpCand hpq.symm hqMissing
      · exact block_two_trace_completers_union_ge_four H A p q
          hU hA hpCand hqCand hpq hpPresent
    change 2 * T.card ≤
      (T.biUnion (blockInternalCompleters H A)).card
    rw [hTwo, hT]
    simpa only [Finset.biUnion_insert, Finset.singleton_biUnion,
      Finset.union_empty] using hUnion



/-- Delete every triple containing at least two vertices of one chosen
five-vertex block.  Iterating this operation gives the block-free
reduction used in Part II. -/
def cleanOneBlock (H : Family α) (A : Edge α) : Family α :=
  H.filter fun E => (E ∩ A).card ≤ 1

theorem cleanOneBlock_subset (H : Family α) (A : Edge α) :
    cleanOneBlock H A ⊆ H := by
  intro E hE
  exact (Finset.mem_filter.mp hE).1

theorem cleanOneBlock_admissible
    (H : Family α) (A : Edge α) (hAdm : Admissible H) :
    Admissible (cleanOneBlock H A) :=
  admissible_mono (cleanOneBlock_subset H A) hAdm

theorem cleanOneBlock_uniform
    (H : Family α) (A : Edge α) (hU : Uniform 3 H) :
    Uniform 3 (cleanOneBlock H A) := by
  intro E hE
  exact hU (cleanOneBlock_subset H A hE)

theorem usedPairs_mono
    (H K : Family α) (V : Edge α) (hHK : H ⊆ K) :
    usedPairs H V ⊆ usedPairs K V := by
  intro p hp
  obtain ⟨hpV, E, hEH, hpE⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hpV, ⟨E, hHK hEH, hpE⟩⟩

theorem usedCells_mono
    (H K : Family α) (V : Edge α) (hHK : H ⊆ K) :
    usedCells H V ⊆ usedCells K V := by
  intro q hq
  obtain ⟨hqV, p, hpV, x, hx, y, hy, hxy, hDisj, hpx, hpy⟩ :=
    Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr
    ⟨hqV, ⟨p, hpV, x, hx, y, hy, hxy, hDisj,
      hHK hpx, hHK hpy⟩⟩

/-- Candidate vertices inside A for certificates from an outside x. -/
def blockCertificateVertices
    (H : Family α) (A : Edge α) (x : α) : Edge α :=
  (blockTrace H A x).biUnion (blockInternalCompleters H A)

def blockCertificateCells
    (H : Family α) (V A : Edge α) : Family α :=
  (V \ A).biUnion fun x =>
    (blockCertificateVertices H A x).image fun y => ({x, y} : Edge α)

theorem mem_blockCertificateVertices_iff
    (H : Family α) (A : Edge α) (x y : α) :
    y ∈ blockCertificateVertices H A x ↔
      ∃ p ∈ blockTrace H A x,
        y ∈ blockInternalCompleters H A p := by
  simp [blockCertificateVertices]

theorem blockCertificateVertices_subset
    (H : Family α) (A : Edge α) (x : α) :
    blockCertificateVertices H A x ⊆ A := by
  intro y hy
  obtain ⟨p, _, hyp⟩ := (mem_blockCertificateVertices_iff H A x y).mp hy
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hyp).1).1



theorem certificate_cell_mem_usedCells
    (H : Family α) (V A : Edge α)
    (hAV : A ⊆ V)
    {x y : α}
    (hx : x ∈ V \ A)
    (hy : y ∈ blockCertificateVertices H A x) :
    ({x, y} : Edge α) ∈ usedCells H V := by
  obtain ⟨hxV, hxA⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨p, hpTrace, hyN⟩ :=
    (mem_blockCertificateVertices_iff H A x y).mp hy
  obtain ⟨hpCand, hpx⟩ := Finset.mem_filter.mp hpTrace
  obtain ⟨hpA, hp2⟩ := Finset.mem_powersetCard.mp hpCand
  obtain ⟨hyC, hpy⟩ := Finset.mem_filter.mp hyN
  obtain ⟨hyA, hyp⟩ := Finset.mem_sdiff.mp hyC
  have hxy : x ≠ y := fun h => hxA (h ▸ hyA)
  have hCell : ({x, y} : Edge α) ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hxV
      · exact hAV (Finset.mem_singleton.mp hv ▸ hyA)
    · exact Finset.card_pair hxy
  have hpV : p ∈ V.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨hpA.trans hAV, hp2⟩
  have hDisj : Disjoint p ({x, y} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro v hvp hvCell
    rcases Finset.mem_insert.mp hvCell with hvx | hvy
    · exact hxA (hpA (hvx ▸ hvp))
    · exact hyp (Finset.mem_singleton.mp hvy ▸ hvp)
  exact Finset.mem_filter.mpr
    ⟨hCell, ⟨p, hpV, x, by simp, y, by simp, hxy,
      hDisj, hpx, hpy⟩⟩

theorem blockCertificateCells_subset_usedCells
    (H : Family α) (V A : Edge α) (hAV : A ⊆ V) :
    blockCertificateCells H V A ⊆ usedCells H V := by
  intro q hq
  obtain ⟨x, hx, hqX⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hqX
  exact certificate_cell_mem_usedCells H V A hAV hx hy



private theorem certificate_core_mem_oriented
    (H : Family α) (V A p : Edge α)
    (hAV : A ⊆ V)
    {x y : α}
    (hx : x ∈ V \ A)
    (hp : p ∈ blockTrace H A x)
    (hy : y ∈ blockInternalCompleters H A p) :
    p ∈ orientedCommonLink H V x y := by
  obtain ⟨_, hxA⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hpCand, hpx⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpA, hp2⟩ := Finset.mem_powersetCard.mp hpCand
  obtain ⟨hyC, hpy⟩ := Finset.mem_filter.mp hy
  have hyNotP := (Finset.mem_sdiff.mp hyC).2
  have hDisj : Disjoint p ({x, y} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro v hvp hvPair
    rcases Finset.mem_insert.mp hvPair with hvx | hvy
    · exact hxA (hpA (hvx ▸ hvp))
    · exact hyNotP (Finset.mem_singleton.mp hvy ▸ hvp)
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powersetCard.mpr
      ⟨hpA.trans hAV, hp2⟩, hDisj, hpx, hpy⟩

/-- Each certificate cell vanishes from the common-link support after
cleaning the block.  Any surviving witness would meet the original
internal core and thus create an edge with two block vertices. -/
theorem certificate_cell_not_mem_clean_usedCells
    (H : Family α) (V A : Edge α)
    (hAdm : Admissible H) (hAV : A ⊆ V)
    {x y : α}
    (hx : x ∈ V \ A)
    (hy : y ∈ blockCertificateVertices H A x) :
    ({x, y} : Edge α) ∉ usedCells (cleanOneBlock H A) V := by
  obtain ⟨_, hxA⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨p, hpTrace, hyN⟩ :=
    (mem_blockCertificateVertices_iff H A x y).mp hy
  obtain ⟨hpCand, _⟩ := Finset.mem_filter.mp hpTrace
  have hpA := (Finset.mem_powersetCard.mp hpCand).1
  have hyA : y ∈ A :=
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hyN).1).1
  have hyNotP : y ∉ p :=
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hyN).1).2
  have hxy : x ≠ y := fun h => hxA (h ▸ hyA)
  have hpOrig := certificate_core_mem_oriented H V A p
    hAV hx hpTrace hyN
  intro hCell
  obtain ⟨_, ⟨r, hrClean⟩⟩ :=
    (mem_usedCells_iff_commonLink_nonempty
      (cleanOneBlock H A) V ({x, y} : Edge α)).mp hCell
  have hrClean' := (mem_commonLink_pair_iff_oriented
    (cleanOneBlock H A) V hxy r).mp hrClean
  obtain ⟨hrV, hrDisj, hrxClean, hryClean⟩ :=
    Finset.mem_filter.mp hrClean'
  have hrOrig : r ∈ orientedCommonLink H V x y :=
    Finset.mem_filter.mpr
      ⟨hrV, hrDisj,
        cleanOneBlock_subset H A hrxClean,
        cleanOneBlock_subset H A hryClean⟩
  have hMeet : ¬ Disjoint p r :=
    oriented_common_link_intersecting hAdm hxy hpOrig hrOrig
  have hInter : (p ∩ r).Nonempty := by
    by_contra h
    exact hMeet (Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp h))
  obtain ⟨t, ht⟩ := hInter
  obtain ⟨htP, htR⟩ := Finset.mem_inter.mp ht
  have htA : t ∈ A := hpA htP
  have hty : t ≠ y := fun h => hyNotP (h ▸ htP)
  have hSub : ({t, y} : Edge α) ⊆ (r ∪ {y}) ∩ A := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_left _ htR, htA⟩
    · have hvy : v = y := Finset.mem_singleton.mp hv
      subst v
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_right _ (by simp), hyA⟩
  have hTwo : 2 ≤ ((r ∪ {y}) ∩ A).card := by
    have h := Finset.card_le_card hSub
    rw [Finset.card_pair hty] at h
    exact h
  have hOne := (Finset.mem_filter.mp hryClean).2
  exact (by omega : False)



private theorem same_extension_injective
    (p q : Edge α) (x : α)
    (hxp : x ∉ p) (hxq : x ∉ q)
    (h : p ∪ {x} = q ∪ {x}) : p = q := by
  have he := congrArg (fun S : Edge α => S.erase x) h
  simpa [Finset.union_singleton, Finset.erase_insert hxp,
    Finset.erase_insert hxq] using he

private theorem cross_extension_ne
    (p q : Edge α) {x y : α}
    (hxq : x ∉ q) (hxy : x ≠ y) :
    p ∪ {x} ≠ q ∪ {y} := by
  intro h
  have hx : x ∈ q ∪ {y} := h ▸ (by simp : x ∈ p ∪ {x})
  rcases Finset.mem_union.mp hx with hxq' | hxy'
  · exact hxq hxq'
  · exact hxy (Finset.mem_singleton.mp hxy')

/-- Every pair of a near-complete five-block is a common-link cell
using an internal pair as witness. -/
theorem nearComplete_internal_common_link
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hA : nearCompleteBlock H A)
    (hAV : A ⊆ V)
    {x y : α} (hxy : x ≠ y)
    (hq : ({x, y} : Edge α) ∈ A.powersetCard 2) :
    ∃ p : Edge α,
      p ⊆ A \ ({x, y} : Edge α) ∧
      p ∈ orientedCommonLink H V x y := by
  let B := A \ ({x, y} : Edge α)
  have hqA := (Finset.mem_powersetCard.mp hq).1
  have hBcard : B.card = 3 := by
    rw [Finset.card_sdiff_of_subset hqA, hA.1,
      (Finset.mem_powersetCard.mp hq).2]
  have hPairs : (B.powersetCard 2).card = 3 := by
    rw [Finset.card_powersetCard, hBcard]
    decide
  have hTwo : 1 < (B.powersetCard 2).card := by omega
  obtain ⟨p, hp, r, hr, hpr⟩ := Finset.one_lt_card.mp hTwo
  have hpB := (Finset.mem_powersetCard.mp hp).1
  have hrB := (Finset.mem_powersetCard.mp hr).1
  have hpA : p ∈ A.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨hpB.trans Finset.sdiff_subset,
        (Finset.mem_powersetCard.mp hp).2⟩
  have hrA : r ∈ A.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨hrB.trans Finset.sdiff_subset,
        (Finset.mem_powersetCard.mp hr).2⟩
  have hxA : x ∈ A := hqA (by simp)
  have hyA : y ∈ A := hqA (by simp)
  have hxp : x ∉ p := by
    intro hx
    exact (Finset.mem_sdiff.mp (hpB hx)).2 (by simp)
  have hyp : y ∉ p := by
    intro hy
    exact (Finset.mem_sdiff.mp (hpB hy)).2 (by simp)
  have hxr : x ∉ r := by
    intro hx
    exact (Finset.mem_sdiff.mp (hrB hx)).2 (by simp)
  have hyr : y ∉ r := by
    intro hy
    exact (Finset.mem_sdiff.mp (hrB hy)).2 (by simp)
  have hpxC := internal_completion_candidate A p hpA
    (Finset.mem_sdiff.mpr ⟨hxA, hxp⟩)
  have hpyC := internal_completion_candidate A p hpA
    (Finset.mem_sdiff.mpr ⟨hyA, hyp⟩)
  have hrxC := internal_completion_candidate A r hrA
    (Finset.mem_sdiff.mpr ⟨hxA, hxr⟩)
  have hryC := internal_completion_candidate A r hrA
    (Finset.mem_sdiff.mpr ⟨hyA, hyr⟩)
  have hrxNeP : r ∪ {x} ≠ p ∪ {x} :=
    fun h => hpr (same_extension_injective r p x hxr hxp h).symm
  have hryNeP : r ∪ {y} ≠ p ∪ {y} :=
    fun h => hpr (same_extension_injective r p y hyr hyp h).symm
  have hrxNePY : r ∪ {x} ≠ p ∪ {y} :=
    cross_extension_ne r p hxp hxy
  have hryNePX : r ∪ {y} ≠ p ∪ {x} :=
    cross_extension_ne r p hyp hxy.symm
  have hDisjP : Disjoint p ({x, y} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro a ha haxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at haxy
    rcases haxy with h | h
    · exact hxp (h ▸ ha)
    · exact hyp (h ▸ ha)
  have hDisjR : Disjoint r ({x, y} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro a ha haxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at haxy
    rcases haxy with h | h
    · exact hxr (h ▸ ha)
    · exact hyr (h ▸ ha)
  have hpV : p ∈ V.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨(Finset.mem_powersetCard.mp hpA).1.trans hAV,
        (Finset.mem_powersetCard.mp hpA).2⟩
  have hrV : r ∈ V.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨(Finset.mem_powersetCard.mp hrA).1.trans hAV,
        (Finset.mem_powersetCard.mp hrA).2⟩
  by_cases hPX : p ∪ {x} ∈ H
  · by_cases hPY : p ∪ {y} ∈ H
    · exact ⟨p, hpB, Finset.mem_filter.mpr
        ⟨hpV, hDisjP, hPX, hPY⟩⟩
    · have hRX : r ∪ {x} ∈ H :=
        (nearComplete_one_of_two H A hU hA hrxC hpyC hrxNePY).resolve_right hPY
      have hRY : r ∪ {y} ∈ H :=
        (nearComplete_one_of_two H A hU hA hryC hpyC hryNeP).resolve_right hPY
      exact ⟨r, hrB, Finset.mem_filter.mpr
        ⟨hrV, hDisjR, hRX, hRY⟩⟩
  · have hRX : r ∪ {x} ∈ H :=
      (nearComplete_one_of_two H A hU hA hrxC hpxC hrxNeP).resolve_right hPX
    have hRY : r ∪ {y} ∈ H :=
      (nearComplete_one_of_two H A hU hA hryC hpxC hryNePX).resolve_right hPX
    exact ⟨r, hrB, Finset.mem_filter.mpr
      ⟨hrV, hDisjR, hRX, hRY⟩⟩



/-- An internal common-link witness prevents its cell from surviving the
deletion of all triples meeting the block twice. -/
theorem internal_core_cell_not_mem_clean_usedCells
    (H : Family α) (V A p : Edge α)
    (hAdm : Admissible H)
    {x y : α} (hxy : x ≠ y)
    (hyA : y ∈ A) (hpA : p ⊆ A) (hyNotP : y ∉ p)
    (hpOrig : p ∈ orientedCommonLink H V x y) :
    ({x, y} : Edge α) ∉ usedCells (cleanOneBlock H A) V := by
  intro hCell
  obtain ⟨_, ⟨r, hrClean⟩⟩ :=
    (mem_usedCells_iff_commonLink_nonempty
      (cleanOneBlock H A) V ({x, y} : Edge α)).mp hCell
  have hrClean' := (mem_commonLink_pair_iff_oriented
    (cleanOneBlock H A) V hxy r).mp hrClean
  obtain ⟨hrV, hrDisj, hrxClean, hryClean⟩ :=
    Finset.mem_filter.mp hrClean'
  have hrOrig : r ∈ orientedCommonLink H V x y :=
    Finset.mem_filter.mpr
      ⟨hrV, hrDisj,
        cleanOneBlock_subset H A hrxClean,
        cleanOneBlock_subset H A hryClean⟩
  have hMeet : ¬ Disjoint p r :=
    oriented_common_link_intersecting hAdm hxy hpOrig hrOrig
  have hInter : (p ∩ r).Nonempty := by
    by_contra h
    exact hMeet (Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp h))
  obtain ⟨t, ht⟩ := hInter
  obtain ⟨htP, htR⟩ := Finset.mem_inter.mp ht
  have htA : t ∈ A := hpA htP
  have hty : t ≠ y := fun h => hyNotP (h ▸ htP)
  have hSub : ({t, y} : Edge α) ⊆ (r ∪ {y}) ∩ A := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_left _ htR, htA⟩
    · have hvy : v = y := Finset.mem_singleton.mp hv
      subst v
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_right _ (by simp), hyA⟩
  have hTwo : 2 ≤ ((r ∪ {y}) ∩ A).card := by
    have h := Finset.card_le_card hSub
    rw [Finset.card_pair hty] at h
    exact h
  have hOne := (Finset.mem_filter.mp hryClean).2
  omega

theorem nearComplete_pair_not_mem_clean_usedCells
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hA : nearCompleteBlock H A) (hAV : A ⊆ V)
    {x y : α} (hxy : x ≠ y)
    (hq : ({x, y} : Edge α) ∈ A.powersetCard 2) :
    ({x, y} : Edge α) ∉ usedCells (cleanOneBlock H A) V := by
  obtain ⟨p, hpB, hpLink⟩ :=
    nearComplete_internal_common_link H V A hU hA hAV hxy hq
  have hqA := (Finset.mem_powersetCard.mp hq).1
  have hyA : y ∈ A := hqA (by simp)
  have hpA : p ⊆ A := hpB.trans Finset.sdiff_subset
  have hyNotP : y ∉ p := by
    intro hy
    exact (Finset.mem_sdiff.mp (hpB hy)).2 (by simp)
  exact internal_core_cell_not_mem_clean_usedCells H V A p
    hAdm hxy hyA hpA hyNotP hpLink

theorem nearComplete_pair_mem_usedCells
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hA : nearCompleteBlock H A)
    (hAV : A ⊆ V)
    {x y : α} (hxy : x ≠ y)
    (hq : ({x, y} : Edge α) ∈ A.powersetCard 2) :
    ({x, y} : Edge α) ∈ usedCells H V := by
  obtain ⟨p, _, hpLink⟩ :=
    nearComplete_internal_common_link H V A hU hA hAV hxy hq
  exact (mem_usedCells_iff_commonLink_nonempty H V ({x, y} : Edge α)).mpr
    ⟨Finset.mem_powersetCard.mpr
      ⟨(Finset.mem_powersetCard.mp hq).1.trans hAV,
        (Finset.mem_powersetCard.mp hq).2⟩,
      ⟨p, (mem_commonLink_pair_iff_oriented H V hxy p).mpr hpLink⟩⟩


theorem nearComplete_blockPairs_subset_usedCells
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hA : nearCompleteBlock H A)
    (hAV : A ⊆ V) :
    A.powersetCard 2 ⊆ usedCells H V := by
  intro q hq
  obtain ⟨x, y, hxy, rfl⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hq).2
  exact nearComplete_pair_mem_usedCells H V A hU hA hAV hxy hq

theorem nearComplete_blockPairs_not_mem_clean_usedCells
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hA : nearCompleteBlock H A) (hAV : A ⊆ V)
    {q : Edge α} (hq : q ∈ A.powersetCard 2) :
    q ∉ usedCells (cleanOneBlock H A) V := by
  obtain ⟨x, y, hxy, rfl⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hq).2
  exact nearComplete_pair_not_mem_clean_usedCells H V A
    hU hAdm hA hAV hxy hq

theorem nearComplete_blockPairs_subset_usedPairs
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hA : nearCompleteBlock H A)
    (hAV : A ⊆ V) :
    A.powersetCard 2 ⊆ usedPairs H V := by
  intro q hq
  have hN := blockInternalCompleters_card_ge_two H A q hU hA hq
  obtain ⟨z, hz⟩ : (blockInternalCompleters H A q).Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hzH : q ∪ {z} ∈ H := (Finset.mem_filter.mp hz).2
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powersetCard.mpr
      ⟨(Finset.mem_powersetCard.mp hq).1.trans hAV,
        (Finset.mem_powersetCard.mp hq).2⟩,
      ⟨q ∪ {z}, hzH, Finset.subset_union_left⟩⟩

theorem nearComplete_blockPairs_not_mem_clean_usedPairs
    (H : Family α) (V A : Edge α)
    {q : Edge α} (hq : q ∈ A.powersetCard 2) :
    q ∉ usedPairs (cleanOneBlock H A) V := by
  intro hqClean
  obtain ⟨_, E, hEClean, hqE⟩ := Finset.mem_filter.mp hqClean
  have hqA := (Finset.mem_powersetCard.mp hq).1
  have hqSub : q ⊆ E ∩ A := Finset.subset_inter hqE hqA
  have hTwo : 2 ≤ (E ∩ A).card := by
    have h := Finset.card_le_card hqSub
    rw [(Finset.mem_powersetCard.mp hq).2] at h
    exact h
  have hOne := (Finset.mem_filter.mp hEClean).2
  omega


private theorem outside_pair_injOn
    (A : Edge α) {x : α} (hxA : x ∉ A) :
    Set.InjOn (fun y : α => ({x, y} : Edge α)) A := by
  intro y hy z hz h
  change ({x, y} : Edge α) = ({x, z} : Edge α) at h
  have hyx : y ≠ x := fun e => hxA (e ▸ hy)
  have hymem : y ∈ ({x, z} : Edge α) := h ▸ (by simp)
  rcases Finset.mem_insert.mp hymem with e | e
  · exact False.elim (hyx e)
  · exact Finset.mem_singleton.mp e

private theorem outside_pair_images_disjoint
    (A : Edge α) {x x' : α}
    (hx : x ∉ A) (hxx' : x ≠ x')
    (Y Z : Edge α) (hZA : Z ⊆ A) :
    Disjoint (Y.image fun y => ({x, y} : Edge α))
      (Z.image fun z => ({x', z} : Edge α)) := by
  apply Finset.disjoint_left.mpr
  intro q hqY hqZ
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hqY
  obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hqZ
  have hxmem : x ∈ ({x', z} : Edge α) := heq ▸ (by simp)
  rcases Finset.mem_insert.mp hxmem with e | e
  · exact hxx' e
  · have hxz : x = z := Finset.mem_singleton.mp e
    exact hx (hxz.symm ▸ hZA hz)

theorem blockCertificateCells_card_eq_sum
    (H : Family α) (V A : Edge α) :
    (blockCertificateCells H V A).card =
      ∑ x ∈ V \ A, (blockCertificateVertices H A x).card := by
  unfold blockCertificateCells
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro x hx
    apply Finset.card_image_of_injOn
    intro y hy z hz heq
    exact outside_pair_injOn A (Finset.mem_sdiff.mp hx).2
      (blockCertificateVertices_subset H A x hy)
      (blockCertificateVertices_subset H A x hz) heq
  · intro x hx x' hx' hxx'
    exact outside_pair_images_disjoint A
      (Finset.mem_sdiff.mp hx).2 hxx'
      (blockCertificateVertices H A x)
      (blockCertificateVertices H A x')
      (blockCertificateVertices_subset H A x')


theorem blockCertificateCells_card_ge_two_trace_sum
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hA : nearCompleteBlock H A) :
    2 * (∑ x ∈ V \ A, (blockTrace H A x).card) ≤
      (blockCertificateCells H V A).card := by
  rw [blockCertificateCells_card_eq_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  exact block_trace_certificate_count H A x hU hAdm hA
    (Finset.mem_sdiff.mp hx).2

theorem blockCertificateCells_disjoint_blockPairs
    (H : Family α) (V A : Edge α) :
    Disjoint (blockCertificateCells H V A) (A.powersetCard 2) := by
  apply Finset.disjoint_left.mpr
  intro q hq hqA
  obtain ⟨x, hx, hqX⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hqX
  exact (Finset.mem_sdiff.mp hx).2
    ((Finset.mem_powersetCard.mp hqA).1 (by simp))

private theorem cardinal_support_loss
    {β : Type*} [DecidableEq β]
    (S T B : Finset β) (hT : T ⊆ S) (hB : B ⊆ S)
    (hDisj : Disjoint B T) :
    B.card + T.card ≤ S.card := by
  rw [← Finset.card_union_of_disjoint hDisj]
  exact Finset.card_le_card (Finset.union_subset hB hT)

theorem nearComplete_block_pair_support_loss
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hA : nearCompleteBlock H A)
    (hAV : A ⊆ V) :
    10 + (usedPairs (cleanOneBlock H A) V).card ≤
      (usedPairs H V).card := by
  have hCount : (A.powersetCard 2).card = 10 := by
    rw [Finset.card_powersetCard, hA.1]
    decide
  rw [← hCount]
  apply cardinal_support_loss
  · exact usedPairs_mono _ _ V (cleanOneBlock_subset H A)
  · exact nearComplete_blockPairs_subset_usedPairs H V A hU hA hAV
  · apply Finset.disjoint_left.mpr
    intro q hq
    exact nearComplete_blockPairs_not_mem_clean_usedPairs H V A hq

theorem nearComplete_block_cell_support_loss
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hA : nearCompleteBlock H A) (hAV : A ⊆ V) :
    10 + (blockCertificateCells H V A).card +
        (usedCells (cleanOneBlock H A) V).card ≤
      (usedCells H V).card := by
  have hCount : (A.powersetCard 2).card = 10 := by
    rw [Finset.card_powersetCard, hA.1]
    decide
  have hDisj :=
    blockCertificateCells_disjoint_blockPairs H V A
  have hUnionCard :
      (A.powersetCard 2 ∪ blockCertificateCells H V A).card =
        10 + (blockCertificateCells H V A).card := by
    rw [Finset.card_union_of_disjoint hDisj.symm, hCount]
  rw [← hUnionCard]
  apply cardinal_support_loss
  · exact usedCells_mono _ _ V (cleanOneBlock_subset H A)
  · exact Finset.union_subset
      (nearComplete_blockPairs_subset_usedCells H V A hU hA hAV)
      (blockCertificateCells_subset_usedCells H V A hAV)
  · apply Finset.disjoint_left.mpr
    intro q hq
    rcases Finset.mem_union.mp hq with hqA | hqCert
    · exact nearComplete_blockPairs_not_mem_clean_usedCells
        H V A hU hAdm hA hAV hqA
    · obtain ⟨x, hx, hqX⟩ := Finset.mem_biUnion.mp hqCert
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hqX
      exact certificate_cell_not_mem_clean_usedCells
        H V A hAdm hAV hx hy


def blockExternalEdges
    (H : Family α) (V A : Edge α) : Family α :=
  (V \ A).biUnion fun x =>
    (blockTrace H A x).image fun p => p ∪ {x}

theorem removedBlockEdges_cover
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H)
    (hGround : ∀ E ∈ H, E ⊆ V) :
    H \ cleanOneBlock H A ⊆
      blockTriples H A ∪ blockExternalEdges H V A := by
  intro E hRemoved
  obtain ⟨hEH, hNotClean⟩ := Finset.mem_sdiff.mp hRemoved
  have hAtLeast : 2 ≤ (E ∩ A).card := by
    by_contra h
    have hOne : (E ∩ A).card ≤ 1 := by omega
    exact hNotClean (Finset.mem_filter.mpr ⟨hEH, hOne⟩)
  by_cases hEA : E ⊆ A
  · exact Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hEH, hEA⟩)
  · have hOutNonempty : (E \ A).Nonempty := by
      by_contra h
      exact hEA (Finset.sdiff_eq_empty_iff_subset.mp
        (Finset.not_nonempty_iff_eq_empty.mp h))
    have hCardSplit := Finset.card_sdiff_add_card_inter E A
    have hCardE := hU hEH
    have hOutCard : (E \ A).card = 1 := by
      have hPos := Finset.card_pos.mpr hOutNonempty
      omega
    obtain ⟨x, hOutEq⟩ := Finset.card_eq_one.mp hOutCard
    have hxOut : x ∈ E \ A := hOutEq.symm ▸ (by simp)
    have hxV : x ∈ V \ A :=
      Finset.mem_sdiff.mpr
        ⟨hGround E hEH (Finset.mem_sdiff.mp hxOut).1,
          (Finset.mem_sdiff.mp hxOut).2⟩
    have hCoreCard : (E ∩ A).card = 2 := by omega
    have hCore : E ∩ A ∈ A.powersetCard 2 :=
      Finset.mem_powersetCard.mpr
        ⟨Finset.inter_subset_right, hCoreCard⟩
    have hEdgeEq : E = (E ∩ A) ∪ {x} := by
      calc
        E = (E \ A) ∪ (E ∩ A) :=
          (Finset.sdiff_union_inter E A).symm
        _ = (E ∩ A) ∪ {x} := by rw [hOutEq]; ac_rfl
    have hTrace : E ∩ A ∈ blockTrace H A x :=
      Finset.mem_filter.mpr ⟨hCore, hEdgeEq ▸ hEH⟩
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr
        ⟨x, hxV, Finset.mem_image.mpr
          ⟨E ∩ A, hTrace, hEdgeEq.symm⟩⟩)


theorem blockTriples_card_le_ten
    (H : Family α) (A : Edge α)
    (hU : Uniform 3 H) (hA : A.card = 5) :
    (blockTriples H A).card ≤ 10 := by
  have hSub : blockTriples H A ⊆ A.powersetCard 3 := by
    intro E hE
    obtain ⟨hEH, hEA⟩ := Finset.mem_filter.mp hE
    exact Finset.mem_powersetCard.mpr ⟨hEA, hU hEH⟩
  have hCard := Finset.card_le_card hSub
  rwa [Finset.card_powersetCard, hA] at hCard

theorem blockExternalEdges_card_le_trace_sum
    (H : Family α) (V A : Edge α) :
    (blockExternalEdges H V A).card ≤
      ∑ x ∈ V \ A, (blockTrace H A x).card := by
  unfold blockExternalEdges
  calc
    ((V \ A).biUnion fun x =>
        (blockTrace H A x).image fun p => p ∪ {x}).card
      ≤ ∑ x ∈ V \ A,
          ((blockTrace H A x).image fun p => p ∪ {x}).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ x ∈ V \ A, (blockTrace H A x).card := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.card_image_le

theorem removedBlockEdges_card_le
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hA : A.card = 5) :
    (H \ cleanOneBlock H A).card ≤
      10 + ∑ x ∈ V \ A, (blockTrace H A x).card := by
  have hCover := removedBlockEdges_cover H V A hU hGround
  have hInternal := blockTriples_card_le_ten H A hU hA
  have hExternal := blockExternalEdges_card_le_trace_sum H V A
  calc
    (H \ cleanOneBlock H A).card
      ≤ (blockTriples H A ∪ blockExternalEdges H V A).card :=
        Finset.card_le_card hCover
    _ ≤ (blockTriples H A).card +
        (blockExternalEdges H V A).card := Finset.card_union_le _ _
    _ ≤ 10 + ∑ x ∈ V \ A, (blockTrace H A x).card := by omega

theorem nearComplete_block_deletion_card_bound
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hA : A.card = 5) :
    H.card ≤ (cleanOneBlock H A).card +
      10 + ∑ x ∈ V \ A, (blockTrace H A x).card := by
  have hRemoved := removedBlockEdges_card_le H V A hU hGround hA
  have hPartition := Finset.card_sdiff_add_card_eq_card
    (cleanOneBlock_subset H A)
  omega

/-- Sequential one-block deletion does not decrease the exact support
defect. This is the local alternative to the manuscript's simultaneous
removal of all dense blocks. -/
theorem nearComplete_block_deletion_support_balance
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hA : nearCompleteBlock H A) (hAV : A ⊆ V) :
    2 * H.card +
        (usedPairs (cleanOneBlock H A) V).card +
        (usedCells (cleanOneBlock H A) V).card ≤
      2 * (cleanOneBlock H A).card +
        (usedPairs H V).card + (usedCells H V).card := by
  have hEdges := nearComplete_block_deletion_card_bound H V A
    hU hGround hA.1
  have hPairs := nearComplete_block_pair_support_loss H V A
    hU hA hAV
  have hCells := nearComplete_block_cell_support_loss H V A
    hU hAdm hA hAV
  have hCert := blockCertificateCells_card_ge_two_trace_sum
    H V A hU hAdm hA
  omega


theorem cleanOneBlock_card_lt
    (H : Family α) (A : Edge α)
    (hU : Uniform 3 H)
    (hA : nearCompleteBlock H A) :
    (cleanOneBlock H A).card < H.card := by
  have hPos : 0 < (blockTriples H A).card := by
    have hDense := hA.2
    omega
  obtain ⟨E, hE⟩ := Finset.card_pos.mp hPos
  obtain ⟨hEH, hEA⟩ := Finset.mem_filter.mp hE
  have hNotClean : E ∉ cleanOneBlock H A := by
    intro hEClean
    have hOne := (Finset.mem_filter.mp hEClean).2
    have hInter : E ∩ A = E := Finset.inter_eq_left.mpr hEA
    rw [hInter, hU hEH] at hOne
    omega
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset
    (cleanOneBlock_subset H A)).mpr
  exact ⟨E, hEH, hNotClean⟩

/-- A finite iteration of one-block deletions yields a block-free
subfamily while preserving the exact support balance. -/
private theorem blockFree_reduction_aux
    (V : Edge α) (n : ℕ) :
    ∀ H : Family α, H.card = n →
      Uniform 3 H → Admissible H →
      (∀ E ∈ H, E ⊆ V) →
      ∃ H₀ : Family α,
        H₀ ⊆ H ∧
        (∀ A : Edge α, A ⊆ V → ¬ nearCompleteBlock H₀ A) ∧
        2 * H.card + (usedPairs H₀ V).card +
            (usedCells H₀ V).card ≤
          2 * H₀.card + (usedPairs H V).card +
            (usedCells H V).card := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H hCard hU hAdm hGround
    by_cases hExists : ∃ A : Edge α, A ⊆ V ∧ nearCompleteBlock H A
    · obtain ⟨A, hAV, hA⟩ := hExists
      let H₁ := cleanOneBlock H A
      have hH₁sub : H₁ ⊆ H := cleanOneBlock_subset H A
      have hH₁lt : H₁.card < n := by
        change (cleanOneBlock H A).card < n
        rw [← hCard]
        exact cleanOneBlock_card_lt H A hU hA
      have hH₁ground : ∀ E ∈ H₁, E ⊆ V := by
        intro E hEH₁
        exact hGround E (hH₁sub hEH₁)
      obtain ⟨H₀, hH₀sub, hFree, hBal₁⟩ :=
        ih H₁.card hH₁lt H₁ rfl
          (cleanOneBlock_uniform H A hU)
          (cleanOneBlock_admissible H A hAdm)
          hH₁ground
      have hBal₀ :=
        nearComplete_block_deletion_support_balance
          H V A hU hAdm hGround hA hAV
      change 2 * H.card + (usedPairs H₁ V).card +
          (usedCells H₁ V).card ≤
        2 * H₁.card + (usedPairs H V).card +
          (usedCells H V).card at hBal₀
      refine ⟨H₀, hH₀sub.trans hH₁sub, hFree, ?_⟩
      omega
    · refine ⟨H, Finset.Subset.refl H, ?_, ?_⟩
      · intro A hAV hNear
        exact hExists ⟨A, hAV, hNear⟩
      · omega

theorem exists_blockFree_reduction
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V) :
    ∃ H₀ : Family α,
      H₀ ⊆ H ∧
      (∀ A : Edge α, A ⊆ V → ¬ nearCompleteBlock H₀ A) ∧
      2 * H.card + (usedPairs H₀ V).card +
          (usedCells H₀ V).card ≤
        2 * H₀.card + (usedPairs H V).card +
          (usedCells H V).card :=
  blockFree_reduction_aux V H.card H rfl hU hAdm hGround


/-- It suffices to establish the actual rank-three support inequality
for admissible systems without near-complete five-blocks in the ambient
vertex set. -/
theorem actual_support_of_blockFree_case
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hBase : ∀ K : Family α,
      Uniform 3 K → Admissible K →
      (∀ E ∈ K, E ⊆ V) →
      (∀ A : Edge α, A ⊆ V → ¬ nearCompleteBlock K A) →
      2 * K.card ≤ (usedPairs K V).card + (usedCells K V).card) :
    2 * H.card ≤ (usedPairs H V).card + (usedCells H V).card := by
  obtain ⟨H₀, hSub, hFree, hBalance⟩ :=
    exists_blockFree_reduction H V hU hAdm hGround
  have hBase₀ := hBase H₀
    (fun E hE => hU (hSub hE))
    (admissible_mono hSub hAdm)
    (fun E hE => hGround E (hSub hE))
    hFree
  omega

theorem triple_family_card_le_choose_two_of_blockFree_case
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hBase : ∀ K : Family α,
      Uniform 3 K → Admissible K →
      (∀ E ∈ K, E ⊆ V) →
      (∀ A : Edge α, A ⊆ V → ¬ nearCompleteBlock K A) →
      2 * K.card ≤ (usedPairs K V).card + (usedCells K V).card) :
    H.card ≤ V.card.choose 2 := by
  apply triple_family_card_le_choose_two_of_actual_supports H V
  exact actual_support_of_blockFree_case H V hU hAdm hGround hBase

end JSP523.Rank3
