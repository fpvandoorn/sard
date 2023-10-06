/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Michael Rothgang.
-/
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Sard.Meagre

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
set_option autoImplicit false

variable
  -- Let `M` be a finite-dimensional (topological) manifold without boundary over the pair `(E, H)`.
  {E : Type*} {𝕂 : Type*} [IsROrC 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕂 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]
  [FiniteDimensional 𝕂 E] [MeasurableSpace E] [BorelSpace E]
variable {I}

variable (I) in
/-- A measure zero subset of an n-dimensional manifold $M$ is a subset $S ⊆ M$ such that
for all charts $(φ, U)$ of $M$, $φ(U ∩ S) ⊆ 𝕂^n$ has measure zero. -/
def MeasureZero (s : Set M) : Prop :=
  ∀ (μ : Measure E) [IsAddHaarMeasure μ], ∀ e ∈ atlas H M, μ (I ∘ e '' (e.source ∩ s)) = 0

namespace MeasureZero
/-- Having measure zero is monotone: a subset of a set with measure zero has measure zero. -/
protected lemma mono {s t : Set M} (hst : s ⊆ t) (ht : MeasureZero I t) :
    (MeasureZero I s) := by
  intro μ hμ e he
  have : I ∘ e '' (e.source ∩ s) ⊆  I ∘ e '' (e.source ∩ t) := by
    apply image_subset
    exact inter_subset_inter_right e.source hst
  exact measure_mono_null this (ht μ e he)

/-- The empty set has measure zero. -/
protected lemma empty : MeasureZero I (∅: Set M) := by
  intro μ _ e _
  simp only [comp_apply, inter_empty, image_empty, OuterMeasure.empty']

/-- The countable index union of measure zero sets has measure zero. -/
protected lemma iUnion {ι : Type*} [Encodable ι] {s : ι → Set M}
  (hs : ∀ n : ι, MeasureZero I (s n)) : MeasureZero I (⋃ (n : ι),  s n) := by
  intro μ hμ e he
  have : I ∘ e '' (e.source ∩ (⋃ (n : ι),  s n)) = ⋃ (n : ι), I ∘ e '' (e.source ∩ s n) := by
    rw [inter_iUnion]
    exact image_iUnion
  -- union of null sets is a null set
  simp_all only [comp_apply, OuterMeasure.iUnion_null_iff]
  intro i
  apply hs
  exact he

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

/-- The “almost everywhere” filter of co-measure zero sets in a manifold. -/
def ModelWithCorners.ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    {F : Type*} [TopologicalSpace F] (I : ModelWithCorners 𝕂 E F)
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
  suffices ∀ e ∈ atlas H M, (e.source ∩ s) = ∅ by
    by_contra h
    obtain ⟨x, hx⟩ : Set.Nonempty s := Iff.mp nmem_singleton_empty h
    specialize this (chartAt H x) (chart_mem_atlas H x)
    have h₂: x ∈ (chartAt H x).toLocalEquiv.source ∩ s := by
      simp
      exact hx
    rw [this] at h₂
    contradiction

  intro e he
  -- choose any Haar measure μ
  have : WeaklyLocallyCompactSpace E := sorry -- TODO: over ℝ, this instance is found, but not over 𝕂
  obtain ⟨K''⟩ : Nonempty (PositiveCompacts E) := PositiveCompacts.nonempty'
  let μ : Measure E := addHaarMeasure K''
  -- by h₂s μ e, we have μ (I∘e '' s) = 0
  specialize h₂s μ e he
  by_contra h
  -- in particular, e.source ∩ s is an open subset contained in that, hence has measure zero
  have h' : Set.Nonempty (interior (I ∘ e '' (e.source ∩ s))) := by
    have : Set.Nonempty (I ∘ e '' (e.source ∩ s)) := by
      exact (Iff.mp Set.nmem_singleton_empty h).image _
    have : IsOpen (e '' (e.source ∩ s)) := by
        apply e.image_open_of_open'
        exact h₁s
    have : IsOpen (I ∘ e '' (e.source ∩ s)) := by
      rw [Set.image_comp]
      apply I.toHomeomorph.isOpenMap _ this
    rwa [this.interior_eq]
  apply (measure_pos_of_nonempty_interior (μ := μ) h').ne' h₂s

/-- A subset of a manifold `M` with measure zero has empty interior.

In particular, a *closed* measure zero subset of M is nowhere dense.
(Closedness is required: there are generalised Cantor sets of positive Lebesgue measure.) -/
protected lemma MeasureZero_implies_empty_interior {s : Set M}
    (h₂s : MeasureZero I s) : interior s = ∅ :=
  (h₂s.mono interior_subset).open_implies_empty isOpen_interior
end MeasureZero

---------------------------------------------------------
-- everything above the fold was already PRed to mathlib
---------------------------------------------------------

namespace MeasureZero
variable
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*} {𝕂 : Type*} [IsROrC 𝕂]
  [NormedAddCommGroup E] [NormedSpace 𝕂 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕂 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] [FiniteDimensional 𝕂 E] [SecondCountableTopology M]
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕂 F] {G : Type*} [TopologicalSpace G]
  (J : ModelWithCorners 𝕂 F G) {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [J.Boundaryless]
  [SmoothManifoldWithCorners J N] [FiniteDimensional 𝕂 F]
  [MeasurableSpace F] [BorelSpace F]

/-- The image `f(s)` of a set `s ⊆ M` under a C¹ map `f : M → N` has measure zero
iff for each chart $(φ, U)$ of $M$, the image $f(U ∩ s)$ has measure zero. -/
-- is the converse useful or just busywork?
lemma measure_zero_image_iff_chart_domains {f : M → N} {s : Set M}
    (hs : ∀ e ∈ atlas H M, MeasureZero J (f '' (e.source ∩ s))) : MeasureZero J (f '' s) := by
  -- The charts of M form an open cover.
  let U : M → Set M := fun x ↦ (ChartedSpace.chartAt x : LocalHomeomorph M H).source
  have hcovering : univ ⊆ ⋃ (x : M), U x := by
    intro x
    have : x ∈ U x := mem_chart_source H x
    rw [mem_iUnion]
    intro _
    use x
  have hopen : ∀ x : M, IsOpen (U x) := fun x => (ChartedSpace.chartAt x).open_source
  -- Since M is second countable, it is Lindelöf: there is a countable subcover U_n of M.
  let ⟨T, ⟨hTCountable, hTcover⟩⟩ := TopologicalSpace.isOpen_iUnion_countable U hopen
  -- Each f(U_n ∩ S) has measure zero.
  have : ∀ i : T, MeasureZero J (f '' ((U i) ∩ s)) := by
    intro i
    let e : LocalHomeomorph M H := ChartedSpace.chartAt i
    have h : MeasureZero J (f '' (e.source ∩ s)) := hs e (chart_mem_atlas H _)
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
lemma MeasureZero.closed_implies_nowhere_dense {s : Set N} (h₁ : MeasureZero J s)
    (h₂ : IsClosed s) : IsNowhereDense s :=
  Iff.mpr (closed_nowhere_dense_iff h₂) (MeasureZero.MeasureZero_implies_empty_interior h₁)

/-- A σ-compact measure zero set is meagre (the countable union of nowhere dense sets). -/
lemma meagre_if_sigma_compact [T2Space N] {s : Set N} (h₁s : MeasureZero J s) (h₂s : IsSigmaCompact s) : IsMeagre s := by
  -- Decompose into countably many pieces, using h₂s.
  obtain ⟨K, ⟨hcompact, hcover⟩⟩ := h₂s
  -- The countable union of nowhere dense sets is meagre.
  suffices ∀ n : ℕ, IsNowhereDense (K n) by
    rw [← hcover]
    use range K
    constructor
    · rintro t ⟨n, hn⟩
      rw [← hn]
      exact this n
    · simp [IsMeagre]
      exact ⟨countable_range K, fun i ↦ subset_iUnion K i⟩
  intro n
  have : K n ⊆ s := by
    rw [← hcover]
    exact subset_iUnion K n
  have h : MeasureZero J (K n) := h₁s.mono this
  exact MeasureZero.closed_implies_nowhere_dense J h (IsCompact.isClosed (hcompact n))
end MeasureZero
