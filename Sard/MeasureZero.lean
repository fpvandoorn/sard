import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

open MeasureTheory Measure Function TopologicalSpace Set
set_option autoImplicit false

variable
  -- Let `M` be a finite-dimensional (topological) manifold without boundary over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {I}

/- A measure zero subset of an n-dimensional manifold $M$ is a subset $S ⊆ M$ such that
for all charts $(φ, U)$ of $M$, $φ(U ∩ S) ⊆ ℝ^n$ has measure zero. -/
variable (I) in
def MeasureZero (s : Set M) : Prop :=
  ∀ (μ : Measure E) [IsAddHaarMeasure μ], ∀ e ∈ atlas H M, μ (I ∘ e '' (e.source ∩ s)) = 0

namespace MeasureZero
/-- Having measure zero is monotone: a subset of a set with measure zero has measure zero. -/
protected lemma mono {s t : Set M} (hst : s ⊆ t) (ht : MeasureZero I t) :
    (MeasureZero I s) := by
  rw [MeasureZero]
  intro μ hμ e he
  have : I ∘ e '' (e.source ∩ s) ⊆  I ∘ e '' (e.source ∩ t) := by
    apply image_subset
    exact inter_subset_inter_right e.source hst
  exact measure_mono_null this (ht μ e he)

/- The empty set has measure zero. -/
protected lemma empty : MeasureZero I (∅: Set M) := by
  intro μ _ e _
  simp only [comp_apply, inter_empty, image_empty, OuterMeasure.empty']

/- The countable index union of measure zero sets has measure zero. -/
protected lemma iUnion { ι : Type* } [Encodable ι] { s : ι → Set M }
  (hs : ∀ n : ι, MeasureZero I (s n)) : MeasureZero I (⋃ (n : ι),  s n) := by
  intro μ hμ e he
  have : I ∘ e '' (e.source ∩ (⋃ (n : ι),  s n)) = ⋃ (n : ι), I ∘ e '' (e.source ∩ s n) := by
    rw [inter_iUnion]
    exact image_iUnion
  -- union of null sets is a null set
  simp_all only [comp_apply, ge_iff_le, gt_iff_lt, OuterMeasure.iUnion_null_iff]
  intro i
  apply hs
  simp_all only [ge_iff_le]

/- The finite union of measure zero sets has measure zero. -/
protected lemma union { s t : Set M } (hs : MeasureZero I s) (ht : MeasureZero I t)
    : MeasureZero I (s ∪ t) := by
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
    { E : Type* } [NormedAddCommGroup E] [NormedSpace ℝ E]
    { F : Type*} [TopologicalSpace F] (I : ModelWithCorners ℝ E F)
    { M : Type* } [TopologicalSpace M] [ChartedSpace F M]
    [SmoothManifoldWithCorners I M] [FiniteDimensional ℝ E]
    [MeasurableSpace E] : Filter M where
  sets := { s | MeasureZero I sᶜ }
  univ_sets := by
    rw [@mem_setOf, compl_univ]
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
      constructor
      simp
      exact hx
    rw [this] at h₂
    contradiction
    -- alternative proof: the atlas forms an open cover -> use interior_zero_iff_open_cover
  intro e he
  simp [MeasureZero] at h₂s
  -- choose any measure μ that's a Haar measure
  obtain ⟨K''⟩ : Nonempty (PositiveCompacts E) := PositiveCompacts.nonempty'
  let μ : Measure E := addHaarMeasure K''
  -- by h₂s μ e, we have μ (I∘e '' s) = 0; that's a set in M
  specialize h₂s μ e he
  by_contra h
  -- in particular, e.source ∩ s is an open subset contained in that -> also has measure zero
  have h' : Set.Nonempty (interior (I ∘ e '' (e.source ∩ s))) := by
    have : Set.Nonempty (I ∘ e '' (e.source ∩ s)) := by
      exact (Iff.mp Set.nmem_singleton_empty h).image _
    have : IsOpen (e '' (e.source ∩ s)) := by
        apply e.image_open_of_open'
        exact h₁s
    have : IsOpen (I ∘ e '' (e.source ∩ s)) := by
      rw [Set.image_comp]
      -- FUTURE: for manifolds with boundary, use open_subset_contains_interior_point above
      apply I.toHomeomorph.isOpenMap
      apply this
    rwa [this.interior_eq]
  apply (measure_pos_of_nonempty_interior (μ := μ) h').ne'
  exact h₂s

/- A subset of a manifold `M` with measure zero has empty interior.

In particular, a *closed* measure zero subset of M is nowhere dense. -/
protected lemma MeasureZero_implies_empty_interior {s : Set M}
    (h₂s : MeasureZero I s) : (interior s) = ∅ := by
  have : MeasureZero I (interior s) := h₂s.mono interior_subset
  apply MeasureZero.open_implies_empty isOpen_interior this
end MeasureZero
