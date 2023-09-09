import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

open Manifold MeasureTheory FiniteDimensional Measure Function TopologicalSpace Set
set_option autoImplicit false

variable
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M] -- I.Boundaryless?
  [SmoothManifoldWithCorners I M] [FiniteDimensional ℝ E]
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  (J : ModelWithCorners ℝ F G) {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [J.Boundaryless]
  [SmoothManifoldWithCorners J N] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

variable {m n r : ℕ} (hm : finrank ℝ E = m) (hn : finrank ℝ F = n) (hr : r > m-n)
variable {J}

/- A measure zero subset of a manifold $N$ is a subset $S ⊆ N$ such that
for all charts $(φ, U)$ of $N$, $φ(U ∩ S) ⊆ ℝ^n$ has measure zero. -/
variable (J) in
def MeasureZero (s : Set N) : Prop :=
  ∀ (μ : Measure F) [IsAddHaarMeasure μ], ∀ e ∈ atlas G N, μ (J ∘ e '' (e.source ∩ s)) = 0

namespace MeasureZero
/-- Having measure zero is monotone: a subset of a set with measure zero has measure zero. -/
protected lemma mono {s t : Set N} (hst : s ⊆ t) (ht : MeasureZero J t) :
    (MeasureZero J s) := by
  rw [MeasureZero]
  intro μ hμ e he
  have : J ∘ e '' (e.source ∩ s) ⊆  J ∘ e '' (e.source ∩ t) := by
    apply image_subset
    exact inter_subset_inter_right e.source hst
  exact measure_mono_null this (ht μ e he)

/- The empty set has measure zero. -/
protected lemma empty : MeasureZero J (∅: Set N) := by
  intro μ _ e _
  simp only [comp_apply, inter_empty, image_empty, OuterMeasure.empty']

/- The countable index union of measure zero sets has measure zero. -/
protected lemma iUnion { ι : Type* } [Encodable ι] { s : ι → Set N }
  (hs : ∀ n : ι, MeasureZero J (s n)) : MeasureZero J (⋃ (n : ι),  s n) := by
  intro μ hμ e he
  have : J ∘ e '' (e.source ∩ (⋃ (n : ι),  s n)) = ⋃ (n : ι), J ∘ e '' (e.source ∩ s n) := by
    rw [inter_iUnion]
    exact image_iUnion
  -- union of null sets is a null set
  simp_all only [comp_apply, ge_iff_le, gt_iff_lt, OuterMeasure.iUnion_null_iff]
  intro i
  apply hs
  simp_all only [ge_iff_le]

/- The finite union of measure zero sets has measure zero. -/
protected lemma union { s t : Set N } (hs : MeasureZero J s) (ht : MeasureZero J t)
    : MeasureZero J (s ∪ t) := by
  let u : Bool → Set N := fun b ↦ cond b s t
  have : ∀ i : Bool, MeasureZero J (u i) := by
    intro i
    cases i
    · exact ht
    · exact hs
  rw [union_eq_iUnion]
  exact MeasureZero.iUnion this

/-- The “almost everywhere” filter of co-measure zero sets in a manifold. -/
def ModelWithCorners.ae
    { E : Type* } [NormedAddCommGroup E] [NormedSpace ℝ E]
    { F : Type*} [TopologicalSpace F] (J : ModelWithCorners ℝ E F)
    { M : Type* } [TopologicalSpace M] [ChartedSpace F M]
    [SmoothManifoldWithCorners J M] [FiniteDimensional ℝ E]
    [MeasurableSpace E] : Filter M where
  sets := { s | MeasureZero J sᶜ }
  univ_sets := by
    rw [@mem_setOf, compl_univ]
    apply MeasureZero.empty
  inter_sets hx hy:= by
    simp only [mem_setOf_eq] at *
    rw [compl_inter]
    exact hx.union hy
  sets_of_superset hs hst := hs.mono (Iff.mpr compl_subset_compl hst)

/-- An open set of measure zero is empty. -/
protected lemma open_implies_empty {s : Set N} (h₁s : IsOpen s) (h₂s : MeasureZero J s): s = ∅ := by
  suffices ∀ e ∈ atlas G N, (e.source ∩ s) = ∅ by
    by_contra h
    obtain ⟨x, hx⟩ : Set.Nonempty s := Iff.mp nmem_singleton_empty h
    specialize this (chartAt G x) (chart_mem_atlas G x)
    have h₂: x ∈ (chartAt G x).toLocalEquiv.source ∩ s := by
      constructor
      simp
      exact hx
    rw [this] at h₂
    contradiction
    -- alternative proof: the atlas forms an open cover -> use interior_zero_iff_open_cover
  intro e he
  simp [MeasureZero] at h₂s
  -- choose any measure μ that's a Haar measure
  obtain ⟨K''⟩ : Nonempty (PositiveCompacts F) := PositiveCompacts.nonempty'
  let μ : Measure F := addHaarMeasure K''
  -- by h₂s μ e, we have μ (J∘e '' s) = 0; that's a set in N
  specialize h₂s μ e he
  by_contra h
  -- in particular, e.source ∩ s is an open subset contained in that -> also has measure zero
  have h' : Set.Nonempty (interior (J ∘ e '' (e.source ∩ s))) := by
    have : Set.Nonempty (J ∘ e '' (e.source ∩ s)) := by
      exact (Iff.mp Set.nmem_singleton_empty h).image _
    have : IsOpen (e '' (e.source ∩ s)) := by
        apply e.image_open_of_open'
        exact h₁s
    have : IsOpen (J ∘ e '' (e.source ∩ s)) := by
      rw [Set.image_comp]
      -- FUTURE: for manifolds with boundary, use open_subset_contains_interior_point above
      apply J.toHomeomorph.isOpenMap
      apply this
    rwa [this.interior_eq]
  apply (measure_pos_of_nonempty_interior (μ := μ) h').ne'
  exact h₂s

/- A subset of a manifold `N` with measure zero has empty interior.

In particular, a *closed* measure zero subset of N is nowhere dense. -/
protected lemma MeasureZero_implies_empty_interior {s : Set N}
    (h₂s : MeasureZero J s) : (interior s) = ∅ := by
  have : MeasureZero J (interior s) := h₂s.mono interior_subset
  apply MeasureZero.open_implies_empty isOpen_interior this
end MeasureZero
