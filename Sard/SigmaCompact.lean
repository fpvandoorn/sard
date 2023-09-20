import Sard.ToSubset
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

/-- The preimage of a compact set under an inducing map is a compact set. -/
-- mathlib only has ClosedEmbedding.isCompact_preimage -> can probably generalise!
theorem Inducing.isCompact_preimage {f : X → Y} (hf : Inducing f) (hf' : IsClosed (range f)) {K : Set Y}
    (hK : IsCompact K) : IsCompact (f ⁻¹' K) := by
  replace hK := hK.inter_right hf'
  rwa [← hf.isCompact_iff, image_preimage_eq_inter_range]

/-- If `f` is an `Inducing` map, the image `f '' s` of a set `s` is σ-compact if and only if `s` is. -/
lemma Inducing.isSigmaCompact_iff {f : X → Y} (hf : Inducing f) {s : Set X} :
    IsSigmaCompact s ↔ IsSigmaCompact (f '' s) := by
  -- Proof is a relative easy reduction to the compact case.
  simp [IsSigmaCompact] at *
  constructor
  · rintro ⟨K, hcompact, hcov⟩
    use (fun n ↦ f '' (K n))
    constructor
    · intro n
      exact Iff.mpr (isCompact_iff hf) (hcompact n)
    · rw [← hcov, image_iUnion]
  · sorry -- TODO: solve this for embeddings first; then see if this generalizes.

/-- If `f : X → Y` is an `Embedding`, the image `f '' s` of a set `s` is σ-compact
if and only `s`` is σ-compact. -/
lemma Embedding.isSigmaCompact_iff_isSigmaCompact_image {f : X → Y} {s : Set X} (hf : Embedding f) :
    IsSigmaCompact s ↔ IsSigmaCompact (f '' s) := by
  -- exact hf.toInducing.isSigmaCompact_iff, if that generality holds
  constructor
  · rintro ⟨K, hcompact, hcov⟩
    use (fun n ↦ f '' (K n))
    constructor
    · intro n
      exact Iff.mp (isCompact_iff_isCompact_image hf) (hcompact n)
    · rw [← hcov, image_iUnion]
  · rintro ⟨K, hcompact, hcov⟩
    use (fun n ↦ f ⁻¹' (K n))
    constructor
    · intro n
      let S := f ⁻¹' K n
      let f' := S.restrict f
      have : ClosedEmbedding f' := sorry
      have : IsCompact (f' ⁻¹' K n) := ClosedEmbedding.isCompact_preimage this (K := K n) (hcompact n)
      have h : (f' ⁻¹' K n) = toSubset (f ⁻¹' K n) S := sorry
      have : IsClosed S := sorry -- uses Hausdorff or so?
      sorry
    · have : f ⁻¹' (f '' s) = s := by apply preimage_image_eq s hf.inj
      rw [← preimage_iUnion, hcov, this]

-- basically: the inclusion is inducing; being sigma-compact is preserved under such maps
lemma isSigmaCompact_iff_isSigmaCompact_in_subtype {p : X → Prop} {s : Set { a // p a }} :
    IsSigmaCompact s ↔ IsSigmaCompact (((↑) : _ → X) '' s) :=
  embedding_subtype_val.isSigmaCompact_iff_isSigmaCompact_image

/-- A subset `s` is σ-compact iff `s` (with the subspace topology) is a σ-compact space. -/
lemma isSigmaCompact_iff_isSigmaCompact_univ {s : Set X} :
    IsSigmaCompact s ↔ IsSigmaCompact (univ : Set s) := by
  rw [isSigmaCompact_iff_isSigmaCompact_in_subtype, image_univ, Subtype.range_coe]

lemma isSigmaCompact_iff_sigmaCompactSpace {s : Set X} : IsSigmaCompact s ↔ SigmaCompactSpace s :=
  isSigmaCompact_iff_isSigmaCompact_univ.trans isSigmaCompact_univ_iff

/-- Compact sets are σ-compact. -/
lemma SigmaCompact_of_compact {s : Set X} (hs : IsCompact s) : IsSigmaCompact s := by
  -- proof 1: show by hand
  -- use fun _ => s
  -- exact ⟨fun _ => hs, iUnion_const _⟩
  -- proof 2: reduce to subspaces. not sure if that's nicer
  rw [isSigmaCompact_iff_sigmaCompactSpace]
  have : CompactSpace ↑s := by exact Iff.mp isCompact_iff_compactSpace hs
  exact CompactSpace.sigma_compact

/-- Countable unions of compact sets are σ-compact. -/
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

/-- Countable unions of σ-compact sets are σ-compact. -/
lemma SigmaCompact_of_countable_sigma_compact (S : Set (Set X)) (hc : Countable S) (hcomp : ∀ (s : Set X), s ∈ S → IsSigmaCompact s) :
  IsSigmaCompact (⋃₀ S) := by sorry -- TODO: renumbering the sequences, how?

-- A closed subset of a σ-compact set is σ-compact.
lemma SigmaCompact_of_isClosed_subset {s t : Set X} (ht : IsSigmaCompact t)
    (hs : IsClosed s) (h : s ⊆ t) : IsSigmaCompact s := by
  rcases ht with ⟨K, hcompact, hcov⟩
  use (fun n ↦ s ∩ (K n))
  constructor
  · intro n
    exact IsCompact.inter_left (hcompact n) hs
  · rw [← inter_iUnion, hcov]
    exact Iff.mpr inter_eq_left_iff_subset h

/-- If `s` is σ-compact and `f` continuous, `f(A)` is σ-compact. -/
lemma SigmaCompact_image {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsSigmaCompact s) :
    IsSigmaCompact (f '' s) := by
  rcases hs with ⟨K, hcompact, hcov⟩
  use (fun n ↦ f '' (K n))
  exact ⟨fun n ↦ IsCompact.image (hcompact n) hf, by rw [← hcov, image_iUnion]⟩

/-- If `X` is σ-compact, `im f` is σ-compact. -/
lemma SigmaCompact_image' {f : X → Y} (hf : Continuous f) [i : SigmaCompactSpace X] :
    IsSigmaCompact (range f) := by
  rw [← image_univ]
  apply SigmaCompact_image hf (Iff.mpr isSigmaCompact_univ_iff i)
