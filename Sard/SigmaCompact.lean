import Mathlib.Topology.Homeomorph
/-!
We define σ-compact subsets of a topological space, show their elementary properties
and relate them to σ-compact spaces.
-/
-- probably, this also should go into `Mathlib.Topology.SubsetPropertes`

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
  apply isSigmaCompact_univ.image hf

lemma Homeomorph.isSigmaCompact_image {s : Set X} (h : X ≃ₜ Y) :
    IsSigmaCompact (↑h '' s) ↔ IsSigmaCompact s := by
  refine ⟨?_, fun hyp => hyp.image h.continuous⟩
  rintro ⟨K, hcomp, hcov⟩
  refine ⟨fun n ↦ h.invFun '' (K n), fun n ↦ (hcomp n).image (h.continuous_invFun), ?_⟩
  have : h.invFun ∘ h = id := by ext x; exact h.left_inv x
  calc ⋃ (n : ℕ), h.invFun '' K n
    _ = h.invFun '' (⋃ (n : ℕ), K n) := by rw [image_iUnion]
    _ = (h.invFun ∘ h) '' s := by rw [hcov, image_comp]
    _ = id '' s := by rw [this]
    _ = s := by rw [image_id]

lemma Set.image_preimage_eq_subset {f : X → Y} {s : Set Y} (hs : s ⊆ range f) : f '' (f ⁻¹' s) = s := by
  apply Subset.antisymm (image_preimage_subset f s)
  intro x hx
  -- xxx: this can surely be golfed!
  -- Choose y such that f y = x.
  have : x ∈ range f := hs hx
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
  · rintro ⟨L, hcomp, hcov⟩
    -- Suppose f '' s is σ-compact; we want to show f is σ-compact.
    -- Write f(s) as a union of compact sets L n, so s = ⋃ K n with K n := f⁻¹(L n).
    -- Since f is an embedding, K n is compact iff L n is.
    refine ⟨fun n ↦ f ⁻¹' (L n), ?_, ?_⟩
    · intro n
      have : f '' (f ⁻¹' (L n)) = L n := by
        have h: L n ⊆ f '' s := by
          rw [← hcov]
          exact subset_iUnion L n
        exact image_preimage_eq_subset (SurjOn.subset_range h)
      specialize hcomp n
      rw [← this] at hcomp
      apply hf.toInducing.isCompact_iff.mp (hcomp)
    · calc ⋃ n, f ⁻¹' L n
        _ = f ⁻¹' (⋃ n, L n) := by rw [preimage_iUnion]
        _ = f ⁻¹' (f '' s) := by rw [hcov]
        _ = s := preimage_image_eq s hf.inj

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
    -- I presume this part can be golfed/ there are missing lemmas here.
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
      -- Choose n with f n = s (using surjectivity of f).
      have : ∃ n, f n = s := by
        obtain ⟨y, hy⟩ := hf ⟨s, h⟩
        use y
        simp_all only [Subtype.forall]
      rcases this with ⟨n, hn⟩
      exact ⟨f n, mem_range_self n, (by rw [hn]; exact hxs)⟩

-- PRed to mathlib, #7528.
lemma Set.iUnion_prod' {X Y Z : Type*} (f : X × Y → Set Z) :
    ⋃ (x : X) (y : Y), (f ⟨x, y⟩) = ⋃ t : X × Y, (f t) := by
  simp only [iUnion, iSup_eq_iUnion, iSup_prod]

/-- Countable unions of σ-compact sets are σ-compact. -/
lemma isSigmaCompact_of_countable_sigma_compact (S : Set (Set X)) (hc : Set.Countable S)
    (hcomp : ∀ s : S, IsSigmaCompact s (X := X)) : IsSigmaCompact (⋃₀ S) := by
  -- Choose a decomposition s = ⋃ s_i for each s ∈ S.
  choose K hcomp hcov using fun s ↦ hcomp s
  -- Then, we have a countable union of countable unions of compact sets, i.e. countably many.
  have : ⋃₀ S = ⋃₀ range (K.uncurry) := by
    calc ⋃₀ S
      _ = ⋃ s : S, s := by rw [← sUnion_eq_iUnion]
      _ = ⋃ s : S, ⋃ n, (K s n) := by simp_rw [hcov]
      _ = ⋃ s : S, ⋃ n, (K.uncurry ⟨s, n⟩) := by rw [Function.uncurry_def]
      _ = ⋃ (s : S) (n : ℕ), (K.uncurry ⟨s, n⟩) := by rw [iUnion_coe_set]
      _ = ⋃₀ range (K.uncurry) := by rw [iUnion_prod', sUnion_range]
  rw [this]
  rw [← countable_coe_iff] at hc
  refine isSigmaCompact_of_countable_compact _ (countable_range (K.uncurry)) fun s hs ↦ ?_
  obtain ⟨⟨ys, yn⟩, hy⟩ := mem_range.mp hs
  rw [← hy]
  exact hcomp ys yn

/-- A closed subset of a σ-compact set is σ-compact. -/
lemma IsSigmaCompact.of_isClosed_subset {s t : Set X} (ht : IsSigmaCompact t)
    (hs : IsClosed s) (h : s ⊆ t) : IsSigmaCompact s := by
  rcases ht with ⟨K, hcompact, hcov⟩
  refine ⟨(fun n ↦ s ∩ (K n)), fun n ↦ (hcompact n).inter_left hs, ?_⟩
  rw [← inter_iUnion, hcov]
  exact inter_eq_left_iff_subset.mpr h
