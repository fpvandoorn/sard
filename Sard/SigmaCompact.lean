import Mathlib.Topology.SubsetProperties
/-!
σ-compact subsets of a topological space, elementary properties and relation to σ-compact spaces
-/
-- merge into SubsetProperties, probably

open Set
set_option autoImplicit false
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A subset `A ⊆ X` is called **σ-compact** iff it is the union of countably many compact sets. --/
def IsSigmaCompact (A : Set X) : Prop :=
  ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = A

/-- A topological space is σ-compact iff `univ` is σ-compact. --/
lemma isSigmaCompact_univ_iff : IsSigmaCompact (univ : Set X) ↔ SigmaCompactSpace X := by
  constructor
  · intro h
    exact { exists_compact_covering := h }
  · intro h
    exact SigmaCompactSpace.exists_compact_covering

lemma isSigmaCompact_univ [h : SigmaCompactSpace X] : IsSigmaCompact (univ : Set X) :=
  Iff.mpr isSigmaCompact_univ_iff h

/-- Compact sets are σ-compact. -/
lemma SigmaCompact_of_compact {s : Set X} (hs : IsCompact s) : IsSigmaCompact s := by sorry -- -> go via spaces?

-- /-- Countable unions of σ-compact sets are compact. -/

-- A closed subset of a σ-compact set is σ-compact.
lemma SigmaCompact_of_isClosed_subset {s t : Set X} (hs : IsSigmaCompact s)
    (ht : IsClosed t) (h : t ⊆ s) : IsSigmaCompact t := by sorry

/-- If `s` is σ-compact and `f` continuous, `f(A)` is σ-compact. -/
lemma SigmaCompact_image {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsSigmaCompact s) :
    IsSigmaCompact (f '' s) := by sorry

/-- If `X` is σ-compact, `im f` is σ-compact. -/
lemma SigmaCompact_image' {f : X → Y} (hf : Continuous f) [i : SigmaCompactSpace X] :
    IsSigmaCompact (range f) := by
  rw [← image_univ]
  apply SigmaCompact_image hf (Iff.mpr isSigmaCompact_univ_iff i)
