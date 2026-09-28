import JSP523.Rank5.PrivateFacetExistence
import JSP523.Rank5.PrivateFacetInjection
import Mathlib.Data.Finset.Powerset

/-!
# Assemble private four-faces into the actual shadow bound

The local existence theorem supplies two private deletion faces on each
unrooted edge.  Finite choice selects a pair for each edge; privacy makes
the resulting edge-and-Boolean map injective.  This module then applies the
previously checked cardinal injection to the actual four-shadow.
-/

namespace JSP523.Rank5

section PrivateFacetAssembly

variable {α : Type*} [DecidableEq α]

/-- Data needed to charge two distinct private faces of one edge. -/
def PrivateFacetPair
    (all shadow : Family α) (E : Edge α)
    (P : Edge α × Edge α) : Prop :=
  P.1 ∈ shadow ∧ P.2 ∈ shadow ∧
    P.1 ⊆ E ∧ P.2 ⊆ E ∧ P.1 ≠ P.2 ∧
    (∀ F ∈ all, P.1 ⊆ F → F = E) ∧
    (∀ F ∈ all, P.2 ⊆ F → F = E)

/-- Any private pair for each unrooted edge supplies the finite rank-five
    shadow ledger; the choices are made in the proof, not in a new axiom. -/
theorem shadow_bound_of_private_pairs
    {all rooted unrooted shadow : Family α}
    (hdecomp : all.card = rooted.card + unrooted.card)
    (hsub : unrooted ⊆ all)
    (hpairs : ∀ E ∈ unrooted,
      ∃ P : Edge α × Edge α, PrivateFacetPair all shadow E P) :
    2 * all.card ≤ shadow.card + 2 * rooted.card := by
  classical
  let chosen : Edge α → Edge α × Edge α := fun E =>
    if h : E ∈ unrooted then Classical.choose (hpairs E h)
    else (∅, ∅)
  have hchosen : ∀ E ∈ unrooted,
      PrivateFacetPair all shadow E (chosen E) := by
    intro E hE
    simpa only [chosen, dite_eq_left hE] using
      (Classical.choose_spec (hpairs E hE))
  let facet : Edge α → Bool → Edge α := fun E b =>
    match b with
    | false => (chosen E).1
    | true => (chosen E).2
  have hmem : ∀ E ∈ unrooted, ∀ b : Bool,
      facet E b ∈ shadow := by
    intro E hE b
    obtain ⟨hA, hB, _, _, _, _, _⟩ := hchosen E hE
    cases b with
    | false => exact hA
    | true => exact hB
  have hface : ∀ E ∈ unrooted, ∀ b : Bool,
      facet E b ⊆ E := by
    intro E hE b
    obtain ⟨_, _, hA, hB, _, _, _⟩ := hchosen E hE
    cases b with
    | false => exact hA
    | true => exact hB
  have hprivate : ∀ E ∈ unrooted, ∀ b : Bool,
      ∀ F ∈ all, facet E b ⊆ F → F = E := by
    intro E hE b F hF hsubface
    obtain ⟨_, _, _, _, _, hA, hB⟩ := hchosen E hE
    cases b with
    | false => exact hA F hF hsubface
    | true => exact hB F hF hsubface
  have hchoice : ∀ E ∈ unrooted, ∀ b b' : Bool,
      facet E b = facet E b' → b = b' := by
    intro E hE b b' heq
    obtain ⟨_, _, _, _, hne, _, _⟩ := hchosen E hE
    cases b with
    | false =>
      cases b' with
      | false => rfl
      | true =>
        have hbad : (chosen E).1 = (chosen E).2 := heq
        exact False.elim (hne hbad)
    | true =>
      cases b' with
      | false =>
        have hbad : (chosen E).2 = (chosen E).1 := heq
        exact False.elim (hne hbad.symm)
      | true => rfl
  exact shadow_bound_of_private_certificates facet hdecomp hsub
    hmem hface hprivate hchoice

/-- The actual four-shadow is the union of the four-faces of all edges. -/
def fourShadow (all : Family α) : Family α :=
  all.biUnion (fun E => E.powersetCard 4)

theorem erase_mem_fourShadow
    {all : Family α} {E : Edge α} {a : α}
    (hE : E ∈ all) (hcard : E.card = 5) (ha : a ∈ E) :
    E.erase a ∈ fourShadow all := by
  apply Finset.mem_biUnion.mpr
  refine ⟨E, hE, ?_⟩
  apply Finset.mem_powersetCard.mpr
  constructor
  · exact Finset.erase_subset a E
  · have h := Finset.card_erase_of_mem ha
    omega

/-- The private-pair source comes from the rootless-edge theorem once a
    shared face is known to be coherent and each face is in the shadow. -/
theorem shadow_bound_of_rootless_coherence
    {all rooted unrooted shadow : Family α}
    (z : Edge α → α)
    (hdecomp : all.card = rooted.card + unrooted.card)
    (hsub : unrooted ⊆ all)
    (hEcard : ∀ E ∈ unrooted, E.card = 5)
    (hnoroot : ∀ E ∈ unrooted,
      ¬ ∃ v ∈ E, ∀ S : Edge α,
        S ⊆ E → S.card = 3 → v ∈ S → z S = v)
    (hshared : ∀ E ∈ unrooted, ∀ a ∈ E,
      (∃ F ∈ all, F ≠ E ∧ E.erase a ⊆ F) →
      CoherentDeletedFace E z a)
    (hshadow : ∀ E ∈ unrooted, ∀ a ∈ E,
      E.erase a ∈ shadow) :
    2 * all.card ≤ shadow.card + 2 * rooted.card := by
  apply shadow_bound_of_private_pairs hdecomp hsub
  intro E hE
  obtain ⟨a, ha, b, hb, _, hne, _, _, hprivA, hprivB⟩ :=
    two_private_facets_of_rootless_edge
      (hEcard E hE) (hnoroot E hE) (hshared E hE)
  refine ⟨⟨E.erase a, E.erase b⟩, ?_⟩
  exact ⟨hshadow E hE a ha, hshadow E hE b hb,
    Finset.erase_subset a E, Finset.erase_subset b E,
    hne, hprivA, hprivB⟩

/-- A concrete finite rank-five shadow inequality with no abstract shadow
    membership hypothesis.  Only the structural shared-face coherence and
    rootless partition inputs remain. -/
theorem actual_four_shadow_bound_of_rootless_coherence
    {all rooted unrooted : Family α}
    (z : Edge α → α)
    (hdecomp : all.card = rooted.card + unrooted.card)
    (hsub : unrooted ⊆ all)
    (hEcard : ∀ E ∈ unrooted, E.card = 5)
    (hnoroot : ∀ E ∈ unrooted,
      ¬ ∃ v ∈ E, ∀ S : Edge α,
        S ⊆ E → S.card = 3 → v ∈ S → z S = v)
    (hshared : ∀ E ∈ unrooted, ∀ a ∈ E,
      (∃ F ∈ all, F ≠ E ∧ E.erase a ⊆ F) →
      CoherentDeletedFace E z a) :
    2 * all.card ≤ (fourShadow all).card + 2 * rooted.card := by
  apply shadow_bound_of_rootless_coherence z hdecomp hsub
    hEcard hnoroot hshared
  intro E hE a ha
  exact erase_mem_fourShadow (hsub hE) (hEcard E hE) ha

end PrivateFacetAssembly

end JSP523.Rank5
