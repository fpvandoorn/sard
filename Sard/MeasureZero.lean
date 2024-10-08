/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Michael Rothgang.
-/
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Measure zero subsets of a manifold

Defines the notion of "measure zero" subsets on a finite-dimensional topological manifold.

Let $M$ be a finite-dimensional manifold. While $M$ is a measurable space (for instance, pull back the Lebesgue measure on each chart and use a partition of unity) , it has no canonical measure. However, there is a natural notion of *measure zero* subsets of $M$: a subset $A\subset M$ has measure zero iff for each chart $(\phi, U)$ of $M$ the set $\phi(U\cap A)\subset R^n$ has measure zero (w.r.t. to any additive Haar measure).

Measure zero sets are closed under subsets and countable unions, hence their complement defines the *almost everywhere filter* on a manifold. Measure zero subsets have empty interior, hence closed measure zero sets are nowhere dense.

**TODO**
- show that if $M$ is a normed space with Haar measure $\mu$, a set $A ⊆ M$ has measure zero iff $μ A = 0$.
- show the same if $M$ is a manifold with a suitable measure $\mu$. If `MeasureZero` were defined using `IsOpenPosMeasure` on a chart, that would probably be a suitable class on `M`.
- include manifolds with boundary: in `open_implies_empty`, one needs to show that an open subset of `M` includes an interior point of `M`. (The current definition of manifolds with boundary seems to be too general for that.)


## Main results
- `MeasureZero`: Prop for measure zero subsets in `M`
- `MeasureZero.mono`: measure zero subsets are closed under subsets
- `MeasureZero.union` and `MeasureZero.iUnion`: measure zero subsets are closed under countable unions
- `MeasureZero.ae`: the complements of measure zero sets form a filter, the **almost everywhere filter**.
- `open_implies_empty`: an open measure zero subset is empty
- `MeasureZero_implies_empty_interior`: a measure zero subset has empty interior.

## References
See [Hirsch76], chapter 3.1 for the definition of measure zero subsets in a manifold.
-/

open MeasureTheory Measure Function TopologicalSpace Set

variable
  -- Let `M` be a finite-dimensional (topological) manifold without boundary over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace E]
variable {I}

variable (I) in
/-- A measure zero subset of an n-dimensional manifold $M$ is a subset $S ⊆ M$ such that
for all charts $(φ, U)$ of $M$, $φ(U ∩ S) ⊆ ℝ^n$ has measure zero. -/
-- xxx: show that my spelling implies the same for all charts!
def MeasureZero (s : Set M) : Prop :=
  ∀ (μ : Measure E) [IsAddHaarMeasure μ] (x : M), μ (I ∘ (chartAt H x) '' ((chartAt H x).source ∩ s)) = 0

namespace MeasureZero
/-- Having measure zero is monotone: a subset of a set with measure zero has measure zero. -/
protected lemma mono {s t : Set M} (hst : s ⊆ t) (ht : MeasureZero I t) :
    (MeasureZero I s) := by
  intro μ hμ x
  let e := chartAt H x
  have : I ∘ e '' (e.source ∩ s) ⊆  I ∘ e '' (e.source ∩ t) := by
    apply image_subset
    exact inter_subset_inter_right e.source hst
  exact measure_mono_null this (ht μ x)

/-- The empty set has measure zero. -/
protected lemma empty : MeasureZero I (∅: Set M) := by
  intro μ _ x
  simp only [comp_apply, inter_empty, image_empty, measure_empty]

/-- The countable index union of measure zero sets has measure zero. -/
protected lemma iUnion {ι : Type*} [Encodable ι] {s : ι → Set M}
    (hs : ∀ n : ι, MeasureZero I (s n)) : MeasureZero I (⋃ (n : ι),  s n) := by
  intro μ hμ x
  let e := chartAt H x
  have : I ∘ e '' (e.source ∩ (⋃ (n : ι),  s n)) = ⋃ (n : ι), I ∘ e '' (e.source ∩ s n) := by
    rw [inter_iUnion]
    exact image_iUnion
  -- union of null sets is a null set
  simp_all only [comp_apply, measure_iUnion_null_iff, e]
  intro i
  apply hs

/-- The finite union of measure zero sets has measure zero. -/
protected lemma union {s t : Set M} (hs : MeasureZero I s) (ht : MeasureZero I t) : MeasureZero I (s ∪ t) := by
  let u : Bool → Set M := fun b ↦ cond b s t
  have : ∀ i : Bool, MeasureZero I (u i) := by
    intro i
    cases i
    · exact ht
    · exact hs
  rw [union_eq_iUnion]
  exact MeasureZero.iUnion this

variable [I.Boundaryless] [FiniteDimensional ℝ E] [BorelSpace E]

/-- The “almost everywhere” filter of co-measure zero sets in a manifold. -/
def ModelWithCorners.ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [TopologicalSpace F] (I : ModelWithCorners ℝ E F)
    {M : Type*} [TopologicalSpace M] [ChartedSpace F M] [MeasurableSpace E] : Filter M where
  sets := { s | MeasureZero I sᶜ }
  univ_sets := by
    rw [mem_setOf, compl_univ]
    apply MeasureZero.empty
  inter_sets hx hy:= by
    simp only [mem_setOf_eq] at *
    rw [compl_inter]
    exact hx.union hy
  sets_of_superset hs hst := hs.mono (Iff.mpr compl_subset_compl hst)

/-- An open set of measure zero is empty. -/
protected lemma open_implies_empty {s : Set M} (h₁s : IsOpen s) (h₂s : MeasureZero I s): s = ∅ := by
  suffices ∀ x : M, ((chartAt H x).source ∩ s) = ∅ by
    by_contra h
    obtain ⟨x, hx⟩ : Set.Nonempty s := Iff.mp nmem_singleton_empty h
    specialize this x
    have h₂: x ∈ (chartAt H x).toPartialEquiv.source ∩ s := by
      simp
      exact hx
    rw [this] at h₂
    contradiction

  intro x
  let e := chartAt H x
  -- choose any Haar measure μ
  obtain ⟨K''⟩ : Nonempty (PositiveCompacts E) := PositiveCompacts.nonempty'
  let μ : Measure E := addHaarMeasure K''
  -- by h₂s μ x, we have μ (I∘e '' s) = 0
  specialize h₂s μ x
  by_contra h
  -- in particular, e.source ∩ s is an open subset contained in that, hence has measure zero
  have h' : Set.Nonempty (interior (I ∘ e '' (e.source ∩ s))) := by
    have : Set.Nonempty (I ∘ e '' (e.source ∩ s)) := (Iff.mp Set.nmem_singleton_empty h).image _
    have : IsOpen (I ∘ e '' (e.source ∩ s)) := by
      rw [Set.image_comp]
      exact I.toHomeomorph.isOpenMap _ (e.isOpen_image_source_inter h₁s)
    rwa [this.interior_eq]
  exact (measure_pos_of_nonempty_interior (μ := μ) h').ne' h₂s

/-- A subset of a manifold `M` with measure zero has empty interior.

In particular, a *closed* measure zero subset of M is nowhere dense.
(Closedness is required: there are generalised Cantor sets of positive Lebesgue measure.) -/
protected lemma empty_interior {s : Set M}
    (h₂s : MeasureZero I s) : interior s = ∅ :=
  (h₂s.mono interior_subset).open_implies_empty isOpen_interior
end MeasureZero

---------------------------------------------------------
-- everything above the fold was PRed to mathlib, but not yet merged
---------------------------------------------------------

namespace MeasureZero
variable
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] [FiniteDimensional ℝ E] [SecondCountableTopology M]
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  (J : ModelWithCorners ℝ F G) {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [J.Boundaryless]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- The image `f(s)` of a set `s ⊆ M` under a C¹ map `f : M → N` has measure zero
iff for each preferred chart of $M$, the image $f(U ∩ s)$ has measure zero. -/
-- is the converse useful or just busywork?
-- TODO: also state a version using all charts, not just the preferred ones?
lemma _root_.measure_zero_image_iff_chart_domains {f : M → N} {s : Set M}
    (hs : ∀ x : M, MeasureZero J (f '' ((chartAt H x).source ∩ s))) : MeasureZero J (f '' s) := by
  -- The charts of M form an open cover.
  let U : M → Set M := fun x ↦ (ChartedSpace.chartAt x : PartialHomeomorph M H).source
  have hcovering : univ ⊆ ⋃ (x : M), U x := by
    intro x _
    rw [mem_iUnion]
    exact ⟨x, mem_chart_source H x⟩
  have hopen : ∀ x : M, IsOpen (U x) := fun x => (ChartedSpace.chartAt x).open_source
  -- Since M is second countable, it is Lindelöf: there is a countable subcover U_n of M.
  let ⟨T, ⟨hTCountable, hTcover⟩⟩ := TopologicalSpace.isOpen_iUnion_countable U hopen
  -- Each f(U_n ∩ S) has measure zero.
  have : ∀ i : T, MeasureZero J (f '' ((U i) ∩ s)) := by
    intro i
    let e : PartialHomeomorph M H := ChartedSpace.chartAt i
    have h : MeasureZero J (f '' (e.source ∩ s)) := hs i
    have h₃ : U i = e.source := by rw [← Filter.principal_eq_iff_eq]
    apply h.mono _
    apply image_subset
    rw [h₃]
  -- The countable union of measure zero sets has measure zero.
  have decomp : ⋃ (i : T), f '' ((U i) ∩ s) = f '' s :=
    calc ⋃ (i : T), f '' ((U i) ∩ s)
      _ = f '' (⋃ (i : T), (U i) ∩ s) := by rw [image_iUnion]
      _ = f '' ((⋃ (i : T), (U i)) ∩ s) := by rw [iUnion_inter]
      _ = f '' ((⋃ (i : M) (_ : i ∈ T), U i) ∩ s) := by rw [iUnion_coe_set]
      _ = f '' ((⋃ (i : M), U i) ∩ s) := by rw [hTcover]
      _ = f '' (univ ∩ s) := by rw [subset_antisymm (by simp) (hcovering)]
      _ = f '' s := by rw [univ_inter]
  rw [← decomp]
  have todo : Encodable T := by sorry --infer_instance
  apply MeasureZero.iUnion (ι := T) this

/-- A closed measure zero set is nowhere dense. -/
lemma isNowhereDense_of_isClosed {s : Set N} (h₁ : MeasureZero J s)
    (h₂ : IsClosed s) : IsNowhereDense s :=
  h₂.isNowhereDense_iff.mpr h₁.empty_interior

/-- A σ-compact measure zero set is meagre (the countable union of nowhere dense sets). -/
lemma isMeagre_of_isSigmaCompact [T2Space N] {s : Set N} (h₁s : MeasureZero J s) (h₂s : IsSigmaCompact s) : IsMeagre s := by
  -- Decompose into countably many pieces, using h₂s.
  obtain ⟨K, ⟨hcompact, hcover⟩⟩ := h₂s
  -- The countable union of nowhere dense sets is meagre.
  suffices ∀ n : ℕ, IsNowhereDense (K n) by
    rw [isMeagre_iff_countable_union_isNowhereDense, ← hcover]
    simp [IsMeagre]
    exact ⟨range K, fun t ⟨n, hn⟩ ↦ hn ▸ this n, countable_range K, fun i ↦ subset_iUnion K i⟩
  intro n
  have h : MeasureZero J (K n) := h₁s.mono (hcover ▸ subset_iUnion K n)
  exact MeasureZero.isNowhereDense_of_isClosed J h (IsCompact.isClosed (hcompact n))
end MeasureZero
