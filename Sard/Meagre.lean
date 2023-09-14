-- Nowhere dense and meagre sets. Probably should belong elsewhere in mathlib.
import Mathlib.Topology.MetricSpace.Baire -- xxx can be minimised?

open Function TopologicalSpace Set
set_option autoImplicit false

-- prerequisites, probably all in mathlib
-- interior commutes with finite intersection
-- interior commutes with arbitrary unions
-- closure commutes with finite unions
-- closure commutes with arbitrary intersections

variable {α : Type*} [TopologicalSpace α]

/-- A set is nowhere dense iff its closure has empty interior. -/
def IsNowhereDense (s : Set α) := IsEmpty (interior (closure s))

/-- A closed set is nowhere dense iff its interior is empty. -/
lemma closed_nowhere_dense_iff {s : Set α} (hs : IsClosed s) : IsNowhereDense s ↔ IsEmpty (interior s) := by
  rw [IsNowhereDense, IsClosed.closure_eq hs]

/-- If a set `s` is nowhere dense, so is its closure.-/
lemma closure_nowhere_dense {s : Set α} (hs : IsNowhereDense s) : IsNowhereDense (closure s) := by
  rw [IsNowhereDense, closure_closure]
  exact hs

/-- A nowhere dense set `s` is contained in a closed nowhere dense set (namely, its closure). -/
lemma nowhere_dense_contained_in_closed_nowhere_dense {s : Set α} (hs : IsNowhereDense s) :
    ∃ t : Set α, s ⊆ t ∧ IsNowhereDense t ∧ IsClosed t := by
  use closure s
  exact ⟨subset_closure, ⟨closure_nowhere_dense hs, isClosed_closure⟩⟩

/-- A set `s` is closed and nowhere dense iff its complement `sᶜ` is open and dense. -/
lemma closed_nowhere_dense_iff_complement {s : Set α} :
    IsClosed s ∧ IsNowhereDense s ↔ IsOpen sᶜ ∧ Dense sᶜ := by
  constructor
  · rintro ⟨hclosed, hNowhereDense⟩
    constructor
    · exact Iff.mpr isOpen_compl_iff hclosed
    · rw [← interior_eq_empty_iff_dense_compl]
      rw [closed_nowhere_dense_iff hclosed] at hNowhereDense
      exact Iff.mp isEmpty_coe_sort hNowhereDense
  · rintro ⟨hopen, hdense⟩
    constructor
    · exact { isOpen_compl := hopen }
    · have : IsClosed s := by exact { isOpen_compl := hopen }
      rw [closed_nowhere_dense_iff this, isEmpty_coe_sort, interior_eq_empty_iff_dense_compl]
      exact hdense

/-- A set is **meagre** iff it is contained in the countable union of nowhere dense sets. -/
def IsMeagre (s : Set α) := ∃ S : Set (Set α), (∀ t ∈ S, IsNowhereDense t) ∧ S.Countable ∧ s ⊆ sInter S

/-- A set is meagre iff its complement is residual (or comeagre). -/
lemma meagre_iff_complement_comeagre (s : Set α) : IsMeagre s ↔ sᶜ ∈ residual α := by
  constructor
  · intro hs -- suppose s is meagre
    rcases hs with ⟨s', ⟨hnowhereDense, hcountable, hss'⟩⟩
    -- Passing to closure, assume all U_i are closed nowhere dense.
    -- there's another such set, namely the closures of all subsets
    -- TODO: how to write this nicely? set builder notation??
    have hclosure : ∀ (t : Set α), t ∈ s' → IsClosed t := by sorry
    -- Then each U_i^c is open and dense, and we compute sᶜ ⊇ ⋂ U_iᶜ, done.
    sorry
  · intro hs -- suppose s is comeagre
    rw [mem_residual_iff] at hs
    rcases hs with ⟨s', ⟨hopen, hdense, hcountable, hss'⟩⟩
    rw [← compl_compl s]
    -- Then have s ⊇ ⋂ U i for open dense sets U_i. Thus, sᶜ ⊆ (⋂ U_i)ᶜ = ⋃ u_iᶜ.
    -- Each u_iᶜ is closed and nowhere dense, hence nowhere dense itself, thus sᶜ is meagre.
    sorry

/-- The empty set is meagre. -/
lemma meagre_empty : IsMeagre (∅ : Set α) := by
  rw [meagre_iff_complement_comeagre, compl_empty, ← Filter.eventuallyEq_univ]

/-- Subsets of meagre sets are meagre. -/
lemma meagre_mono {s t: Set α} (hs : IsMeagre s) (hts: t ⊆ s) : IsMeagre t := by
  rw [← compl_subset_compl] at hts
  rw [meagre_iff_complement_comeagre] at *
  exact Filter.mem_of_superset hs hts

/-- A finite intersection of meagre sets is meagre. -/ -- xxx is this superfluous?
lemma meagre_inter {s t : Set α} (hs : IsMeagre s) (ht : IsMeagre t) : IsMeagre (s ∩ t) := by sorry

/-- A countable union of meagre sets is meagre. -/
lemma meagre_iUnion (s : ℕ → Set α)
    (hs : ∀ n : ℕ, IsMeagre (s n)) : IsMeagre (⋃ (n : ℕ), (s n)) := by
  simp only [meagre_iff_complement_comeagre, compl_iUnion] at *
  exact Iff.mpr countable_iInter_mem hs
