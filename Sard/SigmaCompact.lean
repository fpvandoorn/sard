import Sard.ToSubset
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Separation
import Mathlib.Topology.SubsetProperties
/-!
We define σ-compact subsets of a topological space, show their elementary properties
and relate them to σ-compact spaces.
-/
-- probably, this also should go into `Mathlib.Topology.SubsetPropertes`
-- TODO: finish proving that σ-compact sets are spaces are related
-- TODO: finish proving that σ-compact spaces are closed under countable unions
--   (and transfer this to σ-compact spaces)
-- FIXME: are these proofs easier in terms of that reduction? didn't feel like it,
--   at least there was missing API in terms of relating properties to the subspace

open Set
set_option autoImplicit false
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The preimage of a compact set under an inducing map is a compact set. -/
-- PRed and merged in mathlib; remove when updating mathlib!
theorem Inducing.isCompact_preimage {f : X → Y} (hf : Inducing f) (hf' : IsClosed (range f)) {K : Set Y}
    (hK : IsCompact K) : IsCompact (f ⁻¹' K) := by
  replace hK := hK.inter_right hf'
  rwa [← hf.isCompact_iff, image_preimage_eq_inter_range]

/-- A subset `s ⊆ X` is called **σ-compact** if it is the union of countably many compact sets. -/
def IsSigmaCompact (s : Set X) : Prop :=
  ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = s

/-- A topological space is σ-compact iff `univ` is σ-compact. -/
lemma isSigmaCompact_univ_iff : IsSigmaCompact (univ : Set X) ↔ SigmaCompactSpace X :=
  ⟨fun h ↦ { exists_compact_covering := h }, fun _ ↦ SigmaCompactSpace.exists_compact_covering⟩

lemma isSigmaCompact_univ [h : SigmaCompactSpace X] : IsSigmaCompact (univ : Set X) :=
  isSigmaCompact_univ_iff.mpr h

/-- If `s` is σ-compact and `f` continuous on a set `w` containing `s`, `f(s)` is σ-compact.-/
lemma IsSigmaCompact.image_of_continuousOn {f : X → Y} {s : Set X} (hs : IsSigmaCompact s)
    (hf : ContinuousOn f s) : IsSigmaCompact (f '' s) := by
  rcases hs with ⟨K, hcompact, hcov⟩
  refine ⟨fun n ↦ f '' K n, ?_, (by rw [← hcov]; exact image_iUnion.symm)⟩
  refine fun n ↦ (hcompact n).image_of_continuousOn (hf.mono ?_)
  calc K n
    _ ⊆ ⋃ n, K n := subset_iUnion K n
    _ = s := by rw [hcov]

/-- If `s` is σ-compact and `f` continuous, `f(s)` is σ-compact. -/
lemma IsSigmaCompact.image {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsSigmaCompact s) :
    IsSigmaCompact (f '' s) := hs.image_of_continuousOn hf.continuousOn

/-- If `X` is σ-compact, `im f` is σ-compact. -/
lemma isSigmaCompact_range {f : X → Y} (hf : Continuous f) [i : SigmaCompactSpace X] :
    IsSigmaCompact (range f) := by
  rw [← image_univ]
  apply IsSigmaCompact.image hf isSigmaCompact_univ

lemma Homeomorph.isSigmaCompact_image {s : Set X} (h : X ≃ₜ Y) : IsSigmaCompact (↑h '' s) ↔ IsSigmaCompact s := by
  constructor <;> intro hyp
  · -- suppose h''s is sigma-compact
    rcases hyp with ⟨K, hcomp, hcov⟩
    let k := h.invFun
    refine ⟨fun n ↦ k '' (K n), fun n ↦ (hcomp n).image (h.continuous_invFun), ?_⟩
    have : k ∘ h = id := by ext x; exact h.left_inv x
    calc ⋃ (n : ℕ), k '' K n
      _ = k '' (⋃ (n : ℕ), K n) := by rw [image_iUnion]
      _ = k '' (h '' s) := by rw [hcov]
      _ = (k ∘ h) '' s := by rw [image_comp]
      _ = id '' s := by rw [this]
      _ = s := by rw [image_id]
  · apply hyp.image h.continuous

lemma Set.image_preimage_eq_subset {f : X → Y} {s : Set Y} (hs : s ⊆ range f) : f '' (f ⁻¹' s) = s := by
  apply Subset.antisymm (image_preimage_subset f s)
  intro x hx
  -- xxx: this can surely be golfed!
  -- choose y such that f y = x
  have : x ∈ range f := by exact hs hx
  rw [mem_range] at this
  obtain ⟨y, hy⟩ := this
  refine ⟨y, ?_, hy⟩
  rw [mem_preimage, hy]
  exact hx

/-- If `f : X → Y` is an `Embedding`, the image `f '' s` of a set `s` is σ-compact
if and only `s`` is σ-compact.
This does not hold for merely inducing maps; direction `←` requires injectivity. -/
lemma Embedding.isSigmaCompact_iff_isSigmaCompact_image {f : X → Y} {s : Set X} (hf : Embedding f) :
    IsSigmaCompact s ↔ IsSigmaCompact (f '' s) := by
  constructor
  · exact fun h ↦ h.image (continuous hf)
  · rintro ⟨L, hcomp, hcov⟩ -- suppose f '' s is σ-compact; we want to show f is σ-compact
    -- write f(s) as a union of compact sets L n,
    -- so s = ⋃ K n with K n := f⁻¹(L n)
    -- since f is an embedding, K n is compact iff L n is.
    refine ⟨fun n ↦ f ⁻¹' (L n), ?_, ?_⟩
    · intro n
      have : f '' (f ⁻¹' (L n)) = L n := by
        apply image_preimage_eq_subset
        have h: L n ⊆ f '' s := by
          rw [← hcov]
          exact subset_iUnion L n
        exact SurjOn.subset_range h
      specialize hcomp n
      rw [← this] at hcomp
      apply hf.toInducing.isCompact_iff.mp (hcomp)
    · calc ⋃ n, f ⁻¹' L n
        _ = f ⁻¹' (⋃ n, L n) := by rw [preimage_iUnion]
        _ = f ⁻¹' (f '' s) := by rw [hcov]
        _ = s := by apply (preimage_image_eq s hf.inj)

lemma isSigmaCompact_iff_isSigmaCompact_in_subtype {p : X → Prop} {s : Set { a // p a }} :
    IsSigmaCompact s ↔ IsSigmaCompact (((↑) : _ → X) '' s) :=
  embedding_subtype_val.isSigmaCompact_iff_isSigmaCompact_image

/-- A subset `s` is σ-compact iff `s` (with the subspace topology) is a σ-compact space. -/
lemma isSigmaCompact_iff_isSigmaCompact_univ {s : Set X} :
    IsSigmaCompact s ↔ IsSigmaCompact (univ : Set s) := by
  rw [isSigmaCompact_iff_isSigmaCompact_in_subtype, image_univ, Subtype.range_coe]

lemma isSigmaCompact_iff_sigmaCompactSpace {s : Set X} :
    IsSigmaCompact s ↔ SigmaCompactSpace s :=
  isSigmaCompact_iff_isSigmaCompact_univ.trans isSigmaCompact_univ_iff

/-- The empty set is σ-compact. -/
@[simp]
lemma isSigmaCompact_empty : IsSigmaCompact (∅ : Set X) := by
  use fun _ ↦ ∅
  simp only [isCompact_empty, forall_const, iUnion_empty, and_self]

/-- Compact sets are σ-compact. -/
lemma isSigmaCompact_of_compact {s : Set X} (hs : IsCompact s) : IsSigmaCompact s := by
  -- proof 1: show by hand
  -- exact ⟨fun _ => s, fun _ => hs, iUnion_const _⟩
  -- proof 2: reduce to subspaces. not sure if that's nicer
  rw [isSigmaCompact_iff_sigmaCompactSpace]
  exact (isCompact_iff_compactSpace.mp hs).sigma_compact

/-- Countable unions of compact sets are σ-compact. -/
lemma isSigmaCompact_of_countable_compact (S : Set (Set X)) (hc : Set.Countable S)
    (hcomp : ∀ (s : Set X), s ∈ S → IsCompact s) : IsSigmaCompact (⋃₀ S) := by
  by_cases S = ∅
  · simp only [h, sUnion_empty, isSigmaCompact_empty]
  · -- If S is non-empty, choose a surjection f : ℕ → S, this yields a map ℕ → Set X.
    obtain ⟨f, hf⟩ := (Set.countable_iff_exists_surjective (nmem_singleton_empty.mp h)).mp hc
    refine ⟨fun n ↦ f n, fun n ↦ hcomp (f n) (Subtype.mem (f n)), ?_⟩
    apply Subset.antisymm
    · -- Suppose x ∈ ⋃ n, f n. Then x ∈ f i for some i.
      intro _ hx
      rw [mem_iUnion] at hx
      rcases hx with ⟨i, hi⟩
      -- But f i is a set in S, so x ∈ ⋃ S as well.
      exact ⟨f i, Subtype.mem (f i), hi⟩
    · -- Suppose x ∈ ⋃ s, then x ∈ s for some s ∈ S.
      intro x hx
      rw [mem_sUnion] at hx
      rcases hx with ⟨s, h, hxs⟩
      -- Choose n with f n = s (using surjectitivity of f).
      have : ∀ s : ↑S, ∃ n : ℕ, f n = s := hf
      -- x has type X, but hs says x ∈ S -> how can I cast x to S?
      have : ∃ n, f n = s := by sorry --exact?
      -- simp [hf] is nice, but doesn't solve this
      rcases this with ⟨n, hn⟩
      exact ⟨f n, mem_range_self n, (by rw [hn]; exact hxs)⟩

/-- Countable unions of σ-compact sets are σ-compact. -/
lemma isSigmaCompact_of_countable_sigma_compact (S : Set (Set X)) (hc : Countable S)
    (hcomp : ∀ s : S, IsSigmaCompact s (X := X)) : IsSigmaCompact (⋃₀ S) := by
  -- Choose a decomposition s = ⋃ s_i for each s ∈ S.
  choose K hcomp hcov using fun s ↦ hcomp s
  -- Then, we have a countable union of countable unions of compact sets, i.e. countably many.
  have : Countable (⋃ s, range (K s)) := by
    have : ∀ s, Countable (range (K s)) := by
      intro s -- should be obvious
      sorry -- N is countable, so the range should be countable also
    sorry --apply Countable.sUnion_iff.mpr this
  sorry

-- A closed subset of a σ-compact set is σ-compact.
lemma IsSigmaCompact.of_isClosed_subset {s t : Set X} (ht : IsSigmaCompact t)
    (hs : IsClosed s) (h : s ⊆ t) : IsSigmaCompact s := by
  rcases ht with ⟨K, hcompact, hcov⟩
  use (fun n ↦ s ∩ (K n))
  constructor
  · exact fun n ↦ (hcompact n).inter_left hs
  · rw [← inter_iUnion, hcov]
    exact inter_eq_left_iff_subset.mpr h
