import Mathlib.Topology.SubsetProperties
/-!
σ-compact subsets of a topological space, elementary properties and relation to σ-compact spaces
-/
-- merge into SubsetProperties, probably
-- proofs are mostly copied/adapted from SigmaCompactSpace; not sure if this can be avoided
-- it's only short proofs though, so perhaps that's ok :-)

open Set
set_option autoImplicit false
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A subset `A ⊆ X` is called **σ-compact** iff it is the union of countably many compact sets. --/
def IsSigmaCompact (A : Set X) : Prop :=
  ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = A

/-- A topological space is σ-compact iff `univ` is σ-compact. --/
lemma isSigmaCompact_univ_iff : IsSigmaCompact (univ : Set X) ↔ SigmaCompactSpace X :=
  ⟨fun h ↦ { exists_compact_covering := h }, fun _ ↦ SigmaCompactSpace.exists_compact_covering⟩

lemma isSigmaCompact_univ [h : SigmaCompactSpace X] : IsSigmaCompact (univ : Set X) :=
  Iff.mpr isSigmaCompact_univ_iff h

/-- Compact sets are σ-compact. -/
lemma SigmaCompact_of_compact {s : Set X} (hs : IsCompact s) : IsSigmaCompact s := by
  use fun _ => s
  exact ⟨fun _ => hs, iUnion_const _⟩

-- countable unions of compact sets are compact
lemma SigmaCompact_of_countable_compact (S : Set (Set X)) (hc : Set.Countable S) (hcomp : ∀ (s : Set X), s ∈ S → IsCompact s) :
  IsSigmaCompact (⋃₀ S) := by
  -- easy "in principle": S is countable, so get a bijection, that yields the covering
  have h : ∃ t : Set X, IsCompact t := by sorry -- pick one element S; if empty, we're good
  -- this does almost what we want: except it's for a cover of univ, whereas we want just S
  let lem := Iff.mpr (exists_seq_cover_iff_countable h)
  have hyp : ∃ S, Set.Countable S ∧ (∀ (s : Set X), s ∈ S → IsCompact s) ∧ ⋃₀ S = univ := by
    use S
    exact ⟨hc, ⟨hcomp, sorry⟩⟩
  -- in particular, lem does not fully match what I need!
  specialize lem hyp
  simp [IsSigmaCompact] at *
  sorry

/-- Countable unions of σ-compact sets are compact. -/
lemma SigmaCompact_of_countable_sigma_compact (S : Set (Set X)) (hc : Countable S) (hcomp : ∀ (s : Set X), s ∈ S → IsSigmaCompact s) :
  IsSigmaCompact (⋃₀ S) := by sorry -- TODO: renumbering the sequences, how?

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
