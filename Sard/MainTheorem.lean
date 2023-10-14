import Sard.LocallyLipschitz
import Sard.ManifoldAux
import Sard.MeasureZero
import Mathlib.Topology.MetricSpace.HausdorffDimension

open ENNReal NNReal FiniteDimensional Function Manifold MeasureTheory Measure Set
  SmoothManifoldWithCorners TopologicalSpace Topology LocallyLipschitz
set_option autoImplicit false

variable
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]
  [SmoothManifoldWithCorners I M] [FiniteDimensional ℝ E]
  [SecondCountableTopology M] [MeasurableSpace E] [BorelSpace E]
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [J.Boundaryless]
  [SmoothManifoldWithCorners J N] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
variable {m n r : ℕ} (hm : finrank ℝ E = m) (hn : finrank ℝ F = n) (hr : r > m-n)

/-- If $U ⊆ ℝ^m$ is open and $f : U → ℝ^n$ is a $C^1$ map with `m < n`, $f(U)$ has measure zero. -/
lemma image_measure_zero_of_C1_dimension_increase' {g : E → F} {U : Set E} (hU : IsOpen U)
    [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [IsAddHaarMeasure ν]
    (hg : ContDiffOn ℝ 1 g U) (hmn : m < n) : ν (g '' U) = 0 := by
  -- FIXME: once MeasureZero is refactored, replace the Haar measure ν
  -- by the Hausdorff (or Lebesgue) measure, and this step solves itself.
  have h : ν = μH[n] := sorry
  rw [h]
  -- TODO: remove convexity hypothesis from `dimH_image_le`; split into many small pieces.)
  have : Convex ℝ U := sorry
  -- This seems to be missing from mathlib.
  have h : dimH (univ : Set E) = m := sorry
  apply measure_zero_of_dimH_lt (d := n) rfl.absolutelyContinuous
  calc dimH (g '' U)
    _ ≤ dimH U := hg.dimH_image_le this rfl.subset
    _ ≤ m := h ▸ dimH_mono (subset_univ U) -- should this be a separate lemma?
    _ < n := Nat.cast_lt.mpr hmn

/-- Local version of Sard's theorem. If $W ⊆ ℝ^m$ is open and $f: W → ℝ^n$ is $C^r$,
the set of critical values has measure zero. -/
theorem sard_local {s w : Set E} {f : E → F} (hw : IsOpen w) (hsw : s ⊆ w)
    (hf : ContDiffOn ℝ r f w) {f' : E → E →L[ℝ] F} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (h'f' : ∀ x ∈ s, ¬ Surjective (f' x)) (μ : Measure F) [IsAddHaarMeasure μ] :
    μ (f '' s) = 0 := by
  by_cases hyp: m < n
  · have hr : 1 ≤ (r : ℕ∞) := Nat.one_le_cast.mpr (Nat.one_le_of_lt hr)
    have hless: μ (f '' s) ≤ 0 := calc
      μ (f '' s)
      _ ≤ μ (f '' w) := measure_mono (image_subset f hsw)
      _ = 0 := image_measure_zero_of_C1_dimension_increase' hw μ (hf.of_le hr) hyp
    simp only [nonpos_iff_eq_zero, zero_le] at hless ⊢
    exact hless
  · sorry

/-- Local version of Sard's theorem. If $W ⊆ ℝ^m$ is open and $f: W → ℝ^n$ is $C^r$,
the set of critical values of `f` is a meagre set.
We phrase this for any closed set `s` of critical points of `f`; this is fine
as the critical set of `f` is closed. -/
theorem sard_local' {s w : Set E} {f : E → F} (hw : IsOpen w) (hs : IsClosed s) (hsw : s ⊆ w)
    (hf : ContDiffOn ℝ r f w) {f' : E → E →L[ℝ] F} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (h'f' : ∀ x ∈ s, ¬ Surjective (f' x)) : IsMeagre (f '' s) := by
  obtain ⟨K''⟩ : Nonempty (PositiveCompacts F) := PositiveCompacts.nonempty'
  let μ : Measure F := addHaarMeasure K''
  have ass : μ (f '' s) = 0 := sard_local hr hw hsw hf hf' h'f' μ

  -- `s` is closed, hence σ-compact --- thus so is f '' s.
  have : IsSigmaCompact s := isSigmaCompact_univ.of_isClosed_subset hs (subset_univ s)
  have : IsSigmaCompact (f '' s) := this.image_of_continuousOn (hf.continuousOn.mono hsw)
  exact meagre_of_sigma_compact_null this ass

/-- **Sard's theorem**. Let $M$ and $N$ be real $C^r$ manifolds of dimensions
$m$ and $n$, and $f : M → N$ a $C^r$ map. If $r>\max{0, m-n}$,
the set of regular values of `f` has full measure.

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
  suffices hyp : ∀ x : M, MeasureZero J (f '' ((chartAt H x).source ∩ s)) from
    MeasureZero.measure_zero_image_iff_chart_domains (J := J) hyp
  intro x
  let e := chartAt H x

  -- Reduce to images of chart domains, then apply `sard_local`.
  -- Tedious part: check that all hypotheses transfer to their local counterparts.
  intro μ hμ y
  let e' := chartAt G y
  -- Data for the reduction to local coordinates.
  let w := I ∘ e '' (e.source ∩ f ⁻¹' e'.source)
  let s_better := I ∘ e '' (s ∩ e.source ∩ f ⁻¹' e'.source)
  let f_local := (J ∘ e') ∘ f ∘ (e.invFun ∘ I.invFun)
  let f'_local : E → E →L[ℝ] F := fun x ↦ f' ((e.invFun ∘ I.invFun) x)
  -- "Obvious" computations from my data.
  have cor : (e.invFun ∘ I.invFun ∘ I ∘ e) '' (s ∩ e.source ∩ f ⁻¹' e'.source) = s ∩ e.source ∩ f ⁻¹' e'.source := by
    rw [chart_inverse]
    rw [inter_comm s, inter_assoc]
    apply inter_subset_left
  have hsbetter : e.invFun ∘ I.invFun '' s_better = s ∩ e.source ∩ f ⁻¹' e'.source := by
    calc e.invFun ∘ I.invFun '' s_better
      _ = (e.invFun ∘ I.invFun) ∘ I ∘ e '' (s ∩ e.source ∩ f ⁻¹' e'.source) := by
        simp only [comp.assoc, image_comp]
      _ = (e.invFun ∘ I.invFun ∘ I ∘ e) '' (s ∩ e.source ∩ f ⁻¹' e'.source) := by simp only [comp.assoc, image_comp]
      _ = s ∩ e.source ∩ f ⁻¹' e'.source := cor

  have : J ∘ e' '' (e'.source ∩ f '' (e.source ∩ s)) = f_local '' s_better := by
    symm
    calc f_local '' s_better
      _ = (J ∘ e') ∘ f '' ((e.invFun ∘ I.invFun ∘ I ∘ e) '' (s ∩ e.source ∩ f ⁻¹' e'.source)) := by
        simp only [comp.assoc, image_comp]
      _ = J ∘ e' '' (f '' (s ∩ e.source ∩ f ⁻¹' e'.source)) := by rw [cor, image_comp]
      _ = J ∘ e' '' (f '' (e.source ∩ s ∩ f ⁻¹' e'.source)) := by rw [inter_comm s]
      _ = J ∘ e' '' (f '' (e.source ∩ s) ∩ e'.source) := by rw [image_inter_preimage f _ _]
      _ = J ∘ e' '' (e'.source ∩ f '' (e.source ∩ s)) := by rw [inter_comm]
  rw [this]
  apply sard_local hr (w := w) (s := s_better) (f := f_local) (f' := f'_local) (μ := μ)
  · have : IsOpen (e.source ∩ f ⁻¹' e'.source) :=
      IsOpen.inter e.open_source (e'.open_source.preimage hf.continuous)
    apply chartFull_isOpenMapOn_source _ this (inter_subset_left e.source _)
  · apply image_subset (↑I ∘ ↑e)
    rw [inter_assoc]
    exact inter_subset_right s (e.source ∩ f ⁻¹' e'.source)
  · -- ContDiffOn ℝ (↑r) f_local w follows by definition, of ContMDiff f in charts
    have he : e ∈ maximalAtlas I M := by apply subset_maximalAtlas; exact chart_mem_atlas H x
    have he' : e' ∈ maximalAtlas J N := by apply subset_maximalAtlas; exact chart_mem_atlas G y
    have hs : e.source ∩ f ⁻¹' e'.source ⊆ e.source := inter_subset_left _ _
    have h2s : MapsTo f (e.source ∩ f ⁻¹' e'.source) e'.source :=
      (mapsTo_preimage f e'.source).mono_left (inter_subset_right _ _)
    exact (contMDiffOn_iff_of_mem_maximalAtlas' (n := r) he he' hs h2s).mp hf.contMDiffOn
  · -- ∀ x ∈ s_better, HasFDerivWithinAt f_local (f'_local x) s_better x
    -- should be easy, **once** I have the right definition!
    -- seems I've found an API hole (or I'm doing it wrong)
    -- TODO: something like HasFDerivWithAt_iff_of_mem_maximalAtlas' would be super convenient
    intro xnew hx
    let x' := (e.invFun ∘ I.invFun) xnew
    have : x' ∈ s := by
      have : (e.invFun ∘ I.invFun) '' s_better ⊆ s := by
        rw [hsbetter, inter_assoc]
        exact inter_subset_left s _
      refine this (mem_image_of_mem (e.invFun ∘ I.invFun) hx)
    have haux : x' ∈ e.source := by
      have : (e.invFun ∘ I.invFun) '' s_better ⊆ e.source := by
        rw [hsbetter]
        rw [inter_comm s, inter_assoc]
        exact inter_subset_left _ _
      refine this (mem_image_of_mem _ hx)

    specialize hf' x' this
    have : UniqueMDiffWithinAt I s x' := sorry -- obvious, **once** I've found the right setup
    have : mfderivWithin I J f s x' = f' x' := HasMFDerivWithinAt.mfderivWithin hf' this
    -- Rewrite using local charts.
    have h : extChartAt I x' = I ∘ (chartAt H x') := rfl
    rw [MDifferentiableWithinAt.mfderivWithin, h, I.range_eq_univ, inter_univ] at this
    let mye := chartAt H x'
    have this' : fderivWithin ℝ (writtenInExtChartAt I J x' f) (mye.invFun ∘ I.invFun ⁻¹' s) ((I ∘ chartAt H x') x') = f' x' := this
    -- This is *almost* what we want: except that we'd like to have chart e instead of mye.
    sorry
    sorry
    -- -- All the boilerplate: things reduce to a statement about Fréchet derivatives.
    -- -- (0) f is differentiable (obvious; that derivative is even f')
    -- have : MDifferentiableWithinAt I J f s x' := HasMFDerivWithinAt.mdifferentiableWithinAt hf'
    -- -- (1) f_local is differentiable: use charts (after upgrading them to be preferred)
    -- have h2 : f x' ∈ e'.source := by -- FIXME: all these arguments can surely be consolidated!
    --   have : f '' ((e.invFun ∘ I.invFun) '' s_better) ⊆ e'.source := calc
    --     f '' ((e.invFun ∘ I.invFun) '' s_better)
    --     _ = f '' (s ∩ e.source ∩ f ⁻¹' e'.source) := by rw [hsbetter]
    --     _ ⊆ f '' (f ⁻¹' e'.source) := by
    --       apply image_subset
    --       exact inter_subset_right _ _
    --     _ ⊆ e'.source := by exact image_preimage_subset f e'.source
    --   refine this (mem_image_of_mem _ ?_)
    --   exact mem_image_of_mem (e.invFun ∘ I.invFun) hx
    -- obtain ⟨_, real⟩ := (mdifferentiableWithinAt_iff_of_mem_source (M := M) (M' := N) (f := f) haux h2).mp this
    -- -- By defeq, we really have the following statement.
    -- have : DifferentiableWithinAt ℝ f_local ((e.invFun ∘ I.invFun) ⁻¹' s ∩ range I) ((I ∘ e) x') := real
    -- -- Let's rewrite to make more palatable.
    -- have h1 : (I ∘ e) x' = xnew := by
    --   calc (I ∘ e) x'
    --     _ = (I ∘ e ∘ e.invFun ∘ I.invFun) xnew := rfl
    --     _ = xnew := by sorry -- similar to chart_inverse_pointwise; xnew ∈ I∘e'(e.source) by def
    -- have h3 : ((e.invFun ∘ I.invFun) ⁻¹' s) = (I ∘ e) '' s := sorry -- see ManifoldAux.lean, uses that s is contained in the source.
    -- have : DifferentiableWithinAt ℝ f_local ((I ∘ e) '' ((s ∩ e.source ∩ f ⁻¹' e'.source))) xnew := by
    --   rw [I.range_eq_univ, inter_univ, h1, h3] at this
    --   apply this.mono
    --   apply image_subset
    --   rw [inter_assoc]
    --   apply inter_subset_left _ _
    -- -- (2) recover the differential, using fderiv
    -- -- TODO: I don't see how to do this right now! Might mean my setup is wrong!
    -- have goal : fderivWithin ℝ f_local (I ∘ e '' (s ∩ e.source ∩ f ⁻¹' e'.source)) xnew = f'_local xnew := by sorry
    -- rw [← goal]
    -- exact DifferentiableWithinAt.hasFDerivWithinAt this
  · -- ∀ x ∈ s_better, ¬Surjective ↑(f'_local x)
    intro x hx
    apply h'f' ((e.invFun ∘ I.invFun) x)
    have : (e.invFun ∘ I.invFun) x ∈ s ∩ e.source ∩ f ⁻¹' e'.source :=
      hsbetter ▸ mem_image_of_mem (e.invFun ∘ I.invFun) hx
    rw [inter_assoc] at this
    exact mem_of_mem_inter_left this

/-- **Sard's theorem**: let $M$ and $N$ be real $C^r$ manifolds of dimensions $m$ and $n$,
and $f:M→N$ a $C^r$ map. If $r>\max{0, m-n}$, the critical set is meagre. -/
-- FIXME: do I really need N to be Hausdorff? For the local result, I don't...
theorem sard' {f : M → N} (hf : ContMDiff I J r f) [T2Space N]
    {f' : ∀x, TangentSpace I x →L[ℝ] TangentSpace J (f x)} {s : Set M} (hs : IsClosed s)
    (hf' : ∀ x ∈ s, HasMFDerivWithinAt I J f s x (f' x))
    (h'f' : ∀ x ∈ s, ¬ Surjective (f' x)) : IsMeagre (f '' s) := by
  -- M is second countable and locally compact (as finite-dimensional), hence σ-compact.
  have : IsSigmaCompact s := isSigmaCompact_univ.of_isClosed_subset hs (subset_univ s)
  exact MeasureZero.meagre_if_sigma_compact J (sard _ hr hf hf' h'f') (this.image (hf.continuous))

-- Corollary. The set of regular values is residual and therefore dense.

-- most general version: phrased using the Hausdorff dimension
