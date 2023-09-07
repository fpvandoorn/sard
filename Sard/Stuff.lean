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

/- A measure zero subset of a manifold $N$ is a subset $S ⊆ N$ such that
for all charts $(φ, U)$ of $N$, $φ(U ∩ S) ⊆ ℝ^n$ has measure zero. -/
def measure_zero (s : Set N) : Prop :=
  ∀ (μ : Measure F) [IsAddHaarMeasure μ], ∀ e ∈ atlas G N, μ (J ∘ e '' (e.source ∩ s)) = 0

variable {J}
/-- Having measure zero is monotone: a subset of a set with measure zero has measure zero. -/
lemma measure_zero_subset {s t : Set N} (hst : s ⊆ t) (ht : measure_zero J t) :
    (measure_zero J s) := by
  rw [measure_zero]
  intro μ hμ e he
  have : J ∘ e '' (e.source ∩ s) ⊆  J ∘ e '' (e.source ∩ t) := by
    apply image_subset
    exact inter_subset_inter_right e.source hst
  exact measure_mono_null this (ht μ e he)

-- if there's a measure compatible on each chart, that coincides
-- perhaps-cor: if M is a normed space with Haar measure, that also coincides

/- The empty set has measure zero. -/
lemma empty_measure_zero : measure_zero J (∅: Set N) := by
  --rw [measure_zero]
  intro μ _ e _
  simp only [comp_apply, inter_empty, image_empty, OuterMeasure.empty']

/- The finite union of measure zero sets has measure zero. -/
lemma measure_zero_union { s t : Set N } (hs : measure_zero J s) (ht : measure_zero J t)
    : measure_zero J (s ∪ t) := by
  -- FIXME: how to deduce this from `measure_zero_iUnion`?
  intro μ hμ e he
  specialize hs μ e he
  specialize ht μ e he
  have : J ∘ e '' (e.source ∩ (s ∪ t))
      = J ∘ e '' (e.source ∩ s) ∪ J ∘ e  '' (e.source ∩ t) := by
    rw [inter_distrib_left e.source s t]
    exact image_union (↑J ∘ ↑e) (e.source ∩ s) (e.source ∩ t)
  rw [this]
  exact measure_union_null hs ht

/- The countable index union of measure zero sets has measure zero. -/
lemma measure_zero_iUnion { s : ℕ → Set N }
  (hs : ∀ n : ℕ, measure_zero J (s n)) : measure_zero J (⋃ (n : ℕ),  s n) := by
  intro μ hμ e he
  have : J ∘ e '' (e.source ∩ (⋃ (n : ℕ),  s n)) = ⋃ (n : ℕ), J ∘ e '' (e.source ∩ s n) := by
    rw [inter_iUnion]
    exact image_iUnion
  -- union of null sets is a null set
  simp_all only [comp_apply, ge_iff_le, gt_iff_lt, OuterMeasure.iUnion_null_iff]
  intro i
  apply hs
  simp_all only [ge_iff_le]

/-- The “almost everywhere” filter of co-measure zero sets in a manifold. -/
def ModelWithCorners.ae
    { E : Type* } [NormedAddCommGroup E] [NormedSpace ℝ E]
    { F : Type*} [TopologicalSpace F] (J : ModelWithCorners ℝ E F)
    { M : Type* } [TopologicalSpace M] [ChartedSpace F M]
    [SmoothManifoldWithCorners J M] [FiniteDimensional ℝ E]
    [MeasurableSpace E] : Filter M where
  sets := { s | measure_zero J sᶜ }
  univ_sets := by
    rw [@mem_setOf, compl_univ]
    apply empty_measure_zero
  inter_sets hx hy:= by
    simp only [mem_setOf_eq] at *
    rw [compl_inter]
    exact measure_zero_union hx hy
  sets_of_superset hs hst := by
    apply measure_zero_subset (Iff.mpr compl_subset_compl hst)
    exact hs
#exit

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

/-- An open set of measure zero is empty. -/
lemma open_measure_zero_set_is_empty {s : Set N} (h₁s : IsOpen s) (h₂s : measure_zero J s): s = ∅ := by
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
  simp [measure_zero] at h₂s
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
lemma closed_measure_zero_set_empty_interior {s : Set N}
    (h₂s : measure_zero J s) : (interior s) = ∅ := by
  have : measure_zero J (interior s) := measure_zero_subset interior_subset h₂s
  apply open_measure_zero_set_is_empty isOpen_interior this

/- If M, N are C¹ manifolds with dim M < dim N and f:M → N is C¹, then f(M) has measure zero. -/
lemma image_C1_dimension_increase_image_null {f : M → N} (hf : ContMDiff I J r f)
    (hdim : m < n) : measure_zero J (Set.range f) := by
  sorry -- use C1_image_null_set_null and closed_measure_zero_empty_interior

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
    (h'f' : ∀ x ∈ s, ¬ Surjective (f' x)) : measure_zero J (f '' s) := by
  sorry

-- Corollary. The set of regular values is residual and therefore dense.
-- note: `ContDiffOn.dense_compl_image_of_dimH_lt_finrank` looks related, I want a version on manifolds
