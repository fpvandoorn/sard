import Sard.MeasureZero
import Mathlib.Geometry.Manifold.MFDeriv
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.Lipschitz

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

section ImageMeasureZeroSet
/-- If $$f : X → Y$$ is a Lipschitz map between metric spaces, then `f` maps null sets
to null sets, w.r.t. the `d`-dimensional Hausdorff measure (for $$d ∈ ℕ$$) on `X` resp. `Y`. -/
-- this is just an auxiliary lemma -> perhaps inline later
lemma lipschitz_image_null_set_is_null_set
    { X Y : Type } [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    { f : X → Y } (hf : ∃ K : NNReal, LipschitzWith K f)
    { d : ℝ } (hd : d ≥ 0) { s : Set X } (hs : μH[d] s = 0) : μH[d] (f '' s) = 0 := by
  obtain ⟨K, hk⟩ := hf
  have aux : μH[d] (f '' s) ≤ (K : ENNReal) ^ d * μH[d] s :=
    LipschitzOnWith.hausdorffMeasure_image_le (LipschitzWith.lipschitzOnWith hk s) hd
  rw [hs] at aux
  simp_all only [ge_iff_le, mul_zero, nonpos_iff_eq_zero, le_refl, hs]

/-- Consider metric spaces `X` and `Y` with the `d`-dimensional Hausdorff measure.
If `X` is $σ$-compact, a locally Lipschitz map $f : X → Y$
maps null sets in `X` to null sets in `Y`. -/
lemma locally_lipschitz_image_of_null_set_is_null_set { X Y : Type }
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SigmaCompactSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] { d : ℕ }
    { f : X → Y } (hf : ∀ x : X, ∃ K : NNReal, ∃ U : Set X, IsOpen U ∧ LipschitzOnWith K f U)
    { s : Set X } (hs : μH[d] s = 0) : μH[d] (f '' s) = 0 :=
  -- Choose a countable cover of X by compact sets K_n.
  let K : ℕ → Set X := compactCovering X
  have hcov : ⋃ (n : ℕ), K n = univ := iUnion_compactCovering X
  have hcompact : ∀ n : ℕ, IsCompact (K n) := isCompact_compactCovering X
  -- It suffices to show the statement for all K_n.
  suffices ass : ∀ n : ℕ, μH[d] (f '' (s ∩ K n)) = 0 by
    have : s = ⋃ (n : ℕ), s ∩ K n := by
      calc s
        _ = s ∩ univ := by exact Eq.symm (inter_univ s)
        _ = s ∩ ⋃ (n : ℕ), K n := by rw [hcov]
        _ = ⋃ (n : ℕ), s ∩ K n := by apply inter_iUnion s
    have hless : μH[d] (f '' s) ≤ 0 := by
      calc μH[d] (f '' s)
        _ = μH[d] (f '' (⋃ (n : ℕ), s ∩ K n)) := by rw [← this]
        _ = μH[d] (⋃ (n : ℕ), f '' (s ∩ K n)) := by rw [@image_iUnion]
        _ ≤ ∑' (n : ℕ), μH[d] (f '' (s ∩ K n)) := by apply OuterMeasure.iUnion_nat
        _ = ∑' (n : ℕ), 0 := by simp_rw [ass]
        _ = 0 := by rw [@tsum_zero]
    have : 0 ≤ μH[d] (f '' s) ∧ μH[d] (f '' s) ≤ 0 → μH[d] (f '' s) = 0 := by
      simp only [zero_le, nonpos_iff_eq_zero, true_and]
      rw [← hs]
      simp only [imp_self]
    have : μH[d] (f '' s) = 0 := by
      apply this
      exact ⟨(by simp only [ge_iff_le, zero_le]), hless⟩
    exact this

  -- Consider the open cover (U_x) of K_n induced by hf: each U_x is an open subset containing x
  -- on which f is Lipschitz, say with constant K_x.
  let U : K n → Set X := by
    intro x
    have hyp := hf x -- there exist K U, s.t. U is open and f is K-Lipschitz on U
    -- FIXME: something is off here: this step errors
    sorry --rcases hyp with ⟨KU, hKU⟩
  have hopen : ∀ x : (K n), IsOpen (U x) := sorry -- almost vacuously true
  have hcovering : K n ⊆ ⋃ (x : (K n)), U x := sorry -- since x ∈ U_x
  -- Since K_n is compact, (U_x) has a finite subcover.
  -- xxx: both of these don't quite do what I think!! the line below doesn't work...
  let subcover := IsCompact.elim_finite_subcover (hcompact n) U hopen hcovering
  have aux : ∃ t : Finset (K n), K n ⊆ ⋃ (i : (K n)) (_ : i ∈ t), U i := by
    exact IsCompact.elim_finite_subcover (hcompact n) (fun i => U i) hopen hcovering
  -- rcases subcover with ⟨t, ht⟩ -- fails!
  --rcases aux with ⟨t, ht⟩
  -- On each U_x, f is Lipschitz by hypothesis.
  -- Hence, the previous lemma `lipschitz_image_null_set_is_null_set` applies.
  sorry

/-- Let $U c ℝ^n$ be an open set and f : U → ℝ^n be a C^1 map.
  If $X\subset U$ has measure zero, so has $f(X)$.
  Note: this is false for merely C⁰ maps, the Cantor function $f$ provides a counterexample:
  the standard Cantor set has measure zero, but its image has measure one
  (as the complement $$[0,1]\setminus C$$ has countable image by definition of $f$). -/
lemma C1_image_null_set_null {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    [MeasurableSpace E] (μ : Measure E) [IsAddHaarMeasure μ]
    [MeasurableSpace F] (ν : Measure F) [IsAddHaarMeasure ν]
    {s : Set E} (h₁s: s ⊆ U) (h₂s: μ s = 0) : ν (f '' s) = 0 := by
  -- C¹ map is locally Lipschitz: use `ContDiffAt.exists_lipschitzOnWith`
  -- argue: Hausdorff measure agrees with Lebesgue measure (that's done)
  -- Lebesgue measure is the Haar measure on R^n -> should follow
  sorry
end ImageMeasureZeroSet

-- An open subset of a topological manifold contains an interior point (not on the boundary). -/
-- lemma open_subset_contains_interior_point : (s : Set N) (hs : IsOpen s) :
-- ∃ p ∈ s, p ∈ interior N := by sorry --- how to even state this??
-- is this true or are our local models too wild?

/-- Let $(U_α)$ be a cover of a topological space X.
A subset $S ⊆ X$ is empty iff all $S ∩ U_α$ are empty. -/
theorem empty_iff_open_cover {X : Type} {I : Type} {U : I → Set X}
    (hcover : ⋃ (α : I), U α = univ) {s : Set X} : s = ∅ ↔ ∀ α : I, s ∩ U α = ∅ := by
  have : ⋃ (α : I), s ∩ U α = s := by rw [←inter_iUnion, hcover, inter_univ s]
  nth_rewrite 1 [← this]
  simp only [iUnion_eq_empty]

/-- If M, N are C¹ manifolds with dim M < dim N and f:M → N is C¹, then f(M) has measure zero. -/
lemma image_C1_dimension_increase_image_null {f : M → N} (hf : ContMDiff I J r f)
    (hdim : m < n) : MeasureZero J (Set.range f) := by
  sorry -- use C1_image_null_set_null and MeasureZero_empty_interior

/-- Local version of Sard's theorem. If $W ⊆ ℝ^m$ is open and $f: W → ℝ^n$ is $C^r$,
the set of critical values has measure zero. -/
theorem sard_local {s w : Set E} {f : E → F} (hf : ContDiffOn ℝ r f w)
    {f' : E → E →L[ℝ] F} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (h'f' : ∀ x ∈ s, ¬ Surjective (f' x)) (μ : Measure F) [IsAddHaarMeasure μ] :
    μ (f '' s) = 0 := by
  by_cases hyp: m < n
  · sorry -- show f(W) has measure zero; use `C1_image_null_set_null`
  · sorry

/-- **Sard's theorem**. Let $M$ and $N$ be real $C^r$ manifolds of dimensions
$m$ and $n$, and $f:M→N$ a $C^r$ map. If $r>\max{0, m-n}$,
the set of regular values of $f$ has full measure.

Note that mathlib already contains a weaker version of Sard's theorem,
as `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` in the file `Mathlib.MeasureTheory.Function.Jacobian.Manifold`.
This local result implies the case $m=n$ for $r\geq 1$ (not hard to show).
However, note that the case $m > n$ requires a different proof: for $m>n$, the condition
$f\in C^1$ is not sufficient any more: Whitney (1957) constructed a C¹ function
$$f : ℝ² → ℝ$$ whose set of critical values contains an open set, thus has positive measure. -/
theorem sard {f : M → N} (hf : ContMDiff I J r f)
    {f' : ∀x, TangentSpace I x →L[ℝ] TangentSpace J (f x)} {s : Set M}
    (hf' : ∀ x ∈ s, HasMFDerivWithinAt I J f s x (f' x))
    (h'f' : ∀ x ∈ s, ¬ Surjective (f' x)) : MeasureZero J (f '' s) := by
  sorry

-- Corollary. The set of regular values is residual and therefore dense.
-- note: `ContDiffOn.dense_compl_image_of_dimH_lt_finrank` looks related, I want a version on manifolds
