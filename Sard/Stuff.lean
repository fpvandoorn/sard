import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

open Manifold MeasureTheory FiniteDimensional
open Measure
open Function

set_option autoImplicit false

variable
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] [FiniteDimensional ℝ E]
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type*}
  -- F is basically R^n, G might be a half-space or so (if corners)
  -- J can be regarded as a map G→F 
  [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  (J : ModelWithCorners ℝ F G) {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [SmoothManifoldWithCorners J N] [FiniteDimensional ℝ F]
  [MeasurableSpace F]

variable {m n r : ℕ} (hm : finrank ℝ E = m) (hn : finrank ℝ F = n) (hr : r > m-n)

/- A measure zero subset of a manifold $N$ is a subset $S⊂N$ such that
for all charts $(φ, U)$ of $N$, $φ(U∩ S) ⊂ ℝ^n$ has measure zero. -/
def measure_zero (s : Set N) : Prop :=
  ∀ (μ : Measure F) [IsAddHaarMeasure μ], ∀ e ∈ atlas G N, μ (J ∘ e '' s) = 0

/- Let U c ℝ^n be an open set and f: U → ℝ^n be a C^1 map.
  If $X\subset U$ has measure zero, so has $f(X)$. -/
lemma C1_image_null_set_null (f : E → E)
  (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
  [MeasurableSpace E] (μ : Measure E) [IsAddHaarMeasure μ]
  (s : Set E) (h₁s: s ⊆ U) (h₂s: μ s = 0) : μ (f '' s) = 0 := by sorry
-- NB: this is false for mere C⁰ maps, the Cantor function f provides a counterexample:
-- the standard Cantor set has measure zero, but its image has measure one
-- (the complement [0,1]\C has countable image by definition of f).

/- A closed measure zero subset of a manifold N is nowhere dense.
  It suffices to show that it has empty interior. -/
lemma closed_measure_zero_empty_interior (s : Set N) (h₁s : IsClosed s) (h₂s : measure_zero J s)
: (interior s) = ∅ := by
  sorry -- use measure_pos_of_non_empty_interior, statement for R^n

/- If M, N are C¹ manifolds with dim M < dim N and f:M → N is C¹, then f(M) has measure zero. -/
lemma image_C1_dimension_increase_image_null (f : M → N) (hf : ContMDiff I J r f)
  (hdim : m < n) : measure_zero J (Set.range f) := by
  sorry -- use C1_image_null_set_null and closed_measure_zero_empty_interior

/- Local version of Sard's theorem. If $W ⊂ ℝ^m$ is open and $f: W → ℝ^n$ is $C^r$,
the set of critical values has measure zero. -/
theorem sard_local (s w : Set E) (f : E → F)
  (μ : Measure F) [IsAddHaarMeasure μ]
  (hf : ContDiffOn ℝ r f w)
  (f' : E → E →L[ℝ] F)
  (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
  (h'f' : ∀ x ∈ s, ¬ Surjective (f' x))
: μ (f '' s) = 0:= by
  by_cases hyp: m < n
  · sorry -- show f(W) has measure zero; use `C1_image_null_set_null`
  · sorry

/- **Sard's theorem**. Let $M$ and $N$ be real $C^r$ manifolds of dimensions
$m$ and $n$, and $f:M→N$ a $C^r$ map. If $r>\max{0, m-n}$,
the set of regular values of $f$ has full measure. -/
theorem sard (f : M → N) (hf : ContMDiff I J r f)
  (f' : ∀x, TangentSpace I x →L[ℝ] TangentSpace J (f x))
  (s : Set M) (hf' : ∀ x ∈ s, HasMFDerivWithinAt I J f s x (f' x))
  (h'f' : ∀ x ∈ s, ¬ Surjective (f' x)) : measure_zero J (f '' s) := by
    sorry

-- Corollary. The set of regular values is residual and therefore dense.
-- note: `ContDiffOn.dense_compl_image_of_dimH_lt_finrank` looks related, I want a version on manifolds
