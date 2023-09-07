import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.OpenPos
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

section MeasureZero
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
end MeasureZero

/- Let U c ℝ^n be an open set and f: U → ℝ^n be a C^1 map.
  If $X\subset U$ has measure zero, so has $f(X)$. -/
-- NB: this is false for mere C⁰ maps, the Cantor function f provides a counterexample:
-- the standard Cantor set has measure zero, but its image has measure one
-- (the complement [0,1]\C has countable image by definition of f).
lemma C1_image_null_set_null {f : E → E} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) [MeasurableSpace E] (μ : Measure E) [IsAddHaarMeasure μ]
    {s : Set E} (h₁s: s ⊆ U) (h₂s: μ s = 0) : μ (f '' s) = 0 := by sorry

/-- An open subset of a topological manifold contains an interior point (not on the boundary). -/
-- lemma open_subset_contains_interior_point : (s : Set N) (hs : IsOpen s) :
-- ∃ p ∈ s, p ∈ interior N := by sorry --- how to even state this??
-- is this true or are our local models too wild?

/- Let $(U_α)$ be a cover of a topological space X.
A subset $S ⊆ X$ is empty iff all $S ∩ U_α$ are empty. -/
theorem empty_iff_open_cover {X : Type} [TopologicalSpace X] {I : Type} {U : I → Set X}
    (hcover : ⋃ (α : I), U α = univ) {s : Set X} : s = ∅ ↔ ∀ α : I, s ∩ U α = ∅ := by
  have : ⋃ (α : I), s ∩ U α = s := by rw [←inter_iUnion, hcover, inter_univ s]
  nth_rewrite 1 [← this]
  simp only [iUnion_eq_empty]

/- If M, N are C¹ manifolds with dim M < dim N and f:M → N is C¹, then f(M) has measure zero. -/
lemma image_C1_dimension_increase_image_null {f : M → N} (hf : ContMDiff I J r f)
    (hdim : m < n) : MeasureZero J (Set.range f) := by
  sorry -- use C1_image_null_set_null and MeasureZero_empty_interior

/- Local version of Sard's theorem. If $W ⊆ ℝ^m$ is open and $f: W → ℝ^n$ is $C^r$,
the set of critical values has measure zero. -/
theorem sard_local {s w : Set E} {f : E → F} (hf : ContDiffOn ℝ r f w)
    {f' : E → E →L[ℝ] F} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (h'f' : ∀ x ∈ s, ¬ Surjective (f' x)) (μ : Measure F) [IsAddHaarMeasure μ] :
    μ (f '' s) = 0 := by
  by_cases hyp: m < n
  · sorry -- show f(W) has measure zero; use `C1_image_null_set_null`
  · sorry

/- **Sard's theorem**. Let $M$ and $N$ be real $C^r$ manifolds of dimensions
$m$ and $n$, and $f:M→N$ a $C^r$ map. If $r>\max{0, m-n}$,
the set of regular values of $f$ has full measure. -/
theorem sard {f : M → N} (hf : ContMDiff I J r f)
    {f' : ∀x, TangentSpace I x →L[ℝ] TangentSpace J (f x)} {s : Set M}
    (hf' : ∀ x ∈ s, HasMFDerivWithinAt I J f s x (f' x))
    (h'f' : ∀ x ∈ s, ¬ Surjective (f' x)) : MeasureZero J (f '' s) := by
  sorry

-- Corollary. The set of regular values is residual and therefore dense.
-- note: `ContDiffOn.dense_compl_image_of_dimH_lt_finrank` looks related, I want a version on manifolds
