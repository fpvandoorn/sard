-- Nowhere dense and meagre sets. Probably should belong elsewhere in mathlib.
import Mathlib.Topology.MetricSpace.Baire -- xxx can be minimised?

open Function TopologicalSpace Set
set_option autoImplicit false

-- prerequisites, probably all in mathlib
-- interior commutes with finite intersection
-- interior commutes with arbitrary unions
-- closure commutes with finite unions
-- closure commutes with arbitrary intersections

variable {α : Type*} [TopologicalSpace α] [HasCompl α]

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
    · sorry -- topology exercise using the pre-requisites above
  · rintro ⟨hopen, hdense⟩
    constructor
    · exact { isOpen_compl := hopen }
    · sorry -- topology exercise using the pre-requisites above

/-- A set is **meagre** iff it is contained in the countable union of nowhere dense sets. -/
def IsMeagre (s : Set α) := ---
    ∃ S : Set (Set α), (∀ t ∈ S, IsNowhereDense t) ∧ S.Countable ∧ s ⊆ sInter S

-- xxx: this errors, `failed to synthesize instance HasCompl (Type u_1)`
-- /-- A set is meagre iff its complement is residual (or comeagre). -/
-- lemma meagre_iff_complement_comeagre (s : Set α) : IsMeagre s ↔ residual (sᶜ) :=
  -- -- compute s = ⋂ U_i => sᶜ = ⋃ u_iᶜ
  -- -- "=>" If s is comeagre, have s ⊇ ⋂ U i for open dense sets U_i. Thus, sᶜ ⊆ (⋂ U_i)ᶜ = ⋃ u_iᶜ.
  -- --   Each u_iᶜ is closed and nowhere dense, hence nowhere dense itself, thus sᶜ is meagre.
  -- -- "<=" If s is meagre, have s ⊆ ⋃ U_i for nowhere dense sets U_i.
  -- --   Passing to closure, assume all U_i are closed nowhere dense.
  -- --   Then U_i^c is open and dense, and we compute sᶜ ⊇ ⋂ U_iᶜ, done.
  -- sorry


-- TODO: prove the following properties, by using `meagre_iff_complement_comeagre`, taking complements
-- and applying the dual properties of residual sets
/-- The empty set is meagre. -/
lemma meagre_empty : IsMeagre (∅ : Set α) := by sorry

/-- Subsets of meagre sets are meagre. -/
lemma meagure_mono {s t: Set α} (hs : IsMeagre s) (hts: t ⊆ s) : IsMeagre t := by sorry

/-- A finite intersection of meagre sets is meagre. -/ -- xxx is this superfluous?
lemma meagre_inter {s t : Set α} (hs : IsMeagre s) (ht : IsMeagre t) : IsMeagre (s ∩ t) := by sorry

/-- A countable union of meagre sets is meagre. -/
lemma meagre_iUnion (s : ℕ → Set α)
    (hs : ∀ n : ℕ, IsMeagre (s n)) : IsMeagre (⋃ (n : ℕ), (s n)) := by sorry
