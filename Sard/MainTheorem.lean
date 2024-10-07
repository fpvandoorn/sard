import Sard.ManifoldAux
import Sard.MeasureZero
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Geometry.Manifold.Diffeomorph

open ENNReal NNReal FiniteDimensional Function Manifold MeasureTheory Measure Set
  SmoothManifoldWithCorners TopologicalSpace Topology LocallyLipschitz

variable
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M] --[I.Boundaryless]
  [SmoothManifoldWithCorners I M] [FiniteDimensional ℝ E]
  [SecondCountableTopology M] [MeasurableSpace E] [BorelSpace E]
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N] --[J.Boundaryless]
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
    (hf : ContDiffOn ℝ r f w) {f' : E → E →L[ℝ] F} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) w x)
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
    (hf : ContDiffOn ℝ r f w) {f' : E → E →L[ℝ] F} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) w x)
    (h'f' : ∀ x ∈ s, ¬ Surjective (f' x)) : IsMeagre (f '' s) := by
  obtain ⟨K''⟩ : Nonempty (PositiveCompacts F) := PositiveCompacts.nonempty'
  let μ : Measure F := addHaarMeasure K''
  have ass : μ (f '' s) = 0 := sard_local hr hw hsw hf hf' h'f' μ

  -- `s` is closed, hence σ-compact --- thus so is f '' s.
  have : IsSigmaCompact s := isSigmaCompact_univ.of_isClosed_subset hs (subset_univ s)
  have : IsSigmaCompact (f '' s) := this.image_of_continuousOn (hf.continuousOn.mono hsw)
  exact IsMeagre.of_isSigmaCompact_null this ass

/-- **Sard's theorem**. Let $M$ and $N$ be real $C^r$ manifolds of dimensions
$m$ and $n$, and $f : M → N$ a $C^r$ map. If $r>\max{0, m-n}$,
the set of regular values of `f` has full measure.

Note that mathlib already contains a weaker version of Sard's theorem,
as `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` in the file `Mathlib.MeasureTheory.Function.Jacobian.Manifold`.
This local result implies the case $m=n$ for $r\geq 1$ (not hard to show).
However, note that the case $m > n$ requires a different proof: for $m>n$, the condition
$f\in C^1$ is not sufficient any more: Whitney (1957) constructed a C¹ function
$$f : ℝ² → ℝ$$ whose set of critical values contains an open set, thus has positive measure. -/
theorem sard_boundaryless {f : M → N} (hf : ContMDiff I J r f) [I.Boundaryless] [J.Boundaryless]
    {f' : ∀x, TangentSpace I x →L[ℝ] TangentSpace J (f x)} {s : Set M}
    (hf' : ∀ x ∈ s, HasMFDerivAt I J f x (f' x))
    (h'f' : ∀ x ∈ s, ¬ Surjective (f' x)) : MeasureZero J (f '' s) := by
  suffices hyp : ∀ x : M, MeasureZero J (f '' ((chartAt H x).source ∩ s)) from
    measure_zero_image_iff_chart_domains (J := J) hyp
  intro x
  let e := chartAt H x

  -- Reduce to images of chart domains, then apply `sard_local`.
  -- Tedious part: check that all hypotheses transfer to their local counterparts.
  intro μ hμ y
  let e' := chartAt G y
  -- Data for the reduction to local coordinates.
  let w := e.extend I '' (e.source ∩ f ⁻¹' e'.source)
  let s_better := (e.extend I) '' (s ∩ e.source ∩ f ⁻¹' e'.source)
  let f_local := (J ∘ e') ∘ f ∘ (e.extend I).symm
  -- "Obvious" computations from my data.
  have hwopen : IsOpen w := by
    refine e.extend_isOpenMapOn_source I ?_ inter_subset_left
    exact e.open_source.inter (e'.open_source.preimage hf.continuous)
  have hsw : s_better ⊆ w := by
    apply image_subset
    rw [inter_assoc]
    exact inter_subset_right
  have hsbetter₀ : s_better ⊆ e.extend I '' e.source := by
    apply image_subset
    rw [inter_comm s, inter_assoc]
    exact inter_subset_left
  have cor : ((e.extend I).symm ∘ e.extend I) '' (s ∩ e.source ∩ f ⁻¹' e'.source) = s ∩ e.source ∩ f ⁻¹' e'.source := by
    have : (s ∩ e.source ∩ f ⁻¹' e'.source) ⊆ e.source := by
      rw [inter_comm s, inter_assoc]
      apply inter_subset_left
    apply e.extend_left_inv' _ this
  have hsbetter : (e.extend I).symm '' s_better = s ∩ e.source ∩ f ⁻¹' e'.source := by
    calc (e.extend I).symm '' s_better
      _ = ((e.extend I).symm ∘ (e.extend I)) '' (s ∩ e.source ∩ f ⁻¹' e'.source) := by simp only [comp.assoc, image_comp]
      _ = s ∩ e.source ∩ f ⁻¹' e'.source := cor
  -- Inclusions about s_better, which are needed at some point in the proofs below.
  have hsbetter₁ : (e.extend I).symm '' s_better ⊆ s := by
    rw [hsbetter, inter_assoc]
    exact inter_subset_left
  have hsbetter₂ : (e.extend I).symm '' s_better ⊆ e.source := by
    rw [hsbetter]
    rw [inter_comm s, inter_assoc]
    exact inter_subset_left

  have hw : (f ∘ (e.extend I).symm) '' w ⊆ e'.source := calc
    (f ∘ (e.extend I).symm) '' w
      = f '' ((e.extend I).symm '' w) := by rw [image_comp]
    _ = f '' (e.source ∩ f ⁻¹' e'.source) := by sorry -- fully analogous to rw [hsbetter]
    _ ⊆ f '' (f ⁻¹' e'.source) := image_subset _ inter_subset_right
    _ ⊆ e'.source := image_preimage_subset f e'.source
  have hsbetter₃ : (f ∘ (e.extend I).symm) '' s_better ⊆ e'.source := calc
    (f ∘ (e.extend I).symm) '' s_better
    _ ⊆ (f ∘ (e.extend I).symm) '' w := image_subset _ hsw
    _ ⊆ e'.source := hw
  have : J ∘ e' '' (e'.source ∩ f '' (e.source ∩ s)) = f_local '' s_better := by
    symm
    calc f_local '' s_better
      _ = ((J ∘ e') ∘ f) '' (((e.extend I).symm ∘ (e.extend I)) '' (s ∩ e.source ∩ f ⁻¹' e'.source)) := by
        simp only [e, e', f_local, s_better, comp.assoc, image_comp]
      _ = J ∘ e' '' (f '' (s ∩ e.source ∩ f ⁻¹' e'.source)) := by rw [cor, image_comp]
      _ = J ∘ e' '' (f '' (e.source ∩ s ∩ f ⁻¹' e'.source)) := by rw [inter_comm s]
      _ = J ∘ e' '' (f '' (e.source ∩ s) ∩ e'.source) := by rw [image_inter_preimage f _ _]
      _ = J ∘ e' '' (e'.source ∩ f '' (e.source ∩ s)) := by rw [inter_comm]
  rw [this]
  apply sard_local hr (w := w) (s := s_better) (f := f_local) (f' := fderiv ℝ f_local) (μ := μ)
  · exact e.extend_isOpenMapOn_source _
      (e.open_source.inter (e'.open_source.preimage hf.continuous)) inter_subset_left
  · apply image_subset
    rw [inter_assoc]
    exact inter_subset_right
  · -- ContDiffOn ℝ (↑r) f_local w follows by definition, of ContMDiff f in charts
    have he : e ∈ maximalAtlas I M := subset_maximalAtlas _ (chart_mem_atlas H x)
    have he' : e' ∈ maximalAtlas J N := subset_maximalAtlas _ (chart_mem_atlas G y)
    have hs : e.source ∩ f ⁻¹' e'.source ⊆ e.source := inter_subset_left
    have h2s : MapsTo f (e.source ∩ f ⁻¹' e'.source) e'.source :=
      (mapsTo_preimage f e'.source).mono_left inter_subset_right
    exact (contMDiffOn_iff_of_mem_maximalAtlas' (n := r) he he' hs h2s).mp hf.contMDiffOn
  · -- ∀ x ∈ s_better, HasFDerivWithinAt f_local (fderiv ℝ f_local x) s_better x
    -- XXX: there's not much happening, surely this can be golfed!
    -- XXX: something like HasFDerivWithAt_iff_of_mem_maximalAtlas' would be super convenient
    intro xnew hx
    let x' := (e.extend I).symm xnew
    have hx'₁ : x' ∈ s := hsbetter₁ (mem_image_of_mem _ hx)
    have hx'₂ : x' ∈ e.source := hsbetter₂ (mem_image_of_mem _ hx)
    have hx'₃ : f x' ∈ e'.source := hsbetter₃ (mem_image_of_mem _ hx)
    specialize hf' x' hx'₁
    -- (1) f_local is differentiable as f is: use charts
    obtain ⟨_, real⟩ := (mdifferentiableAt_iff_of_mem_source hx'₂ hx'₃).mp hf'.mdifferentiableAt
    rw [I.range_eq_univ, differentiableWithinAt_univ] at real
    -- (2) recover the differential, using fderiv
    have : DifferentiableAt ℝ f_local (e.extend I x') := real
    have h : e.extend I x' = xnew := e.extend_right_inv _ (hsbetter₀ hx)
    rw [h] at this
    exact (hasFDerivWithinAt_of_isOpen hwopen (hsw hx)).mpr this.hasFDerivAt
  · -- ∀ x ∈ s_better, ¬Surjective (fderiv ℝ f_local x)
    intro x hx
    -- f_local is a map from E to F, hence its fderiv equals its mfderiv.
    rw [← mfderiv_eq_fderiv]
    set D := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f_local x
    -- By definition, f_local is the composition (J ∘ e') ∘ f ∘ e.invFun ∘ I.invFun.
    -- Hence, by the chain rule, its mfderiv is the composition of those.
    let A := mfderiv 𝓘(ℝ, E) I (e.extend I).symm x
    let B := mfderiv I J f ((e.extend I).symm x)
    let C := mfderiv J 𝓘(ℝ, F) (e'.extend J) ((f ∘ (e.extend I).symm) x)
    -- Technical lemmas needed to apply the chain rule.
    -- **n**eighbourhood lemma for **A**
    have hnA : e.extend I '' e.source ∈ 𝓝 x := by -- this is boring; consolidate these details!
      let x' := (e.extend I).symm x
      have : e.extend I x' = x := e.extend_right_inv _ (hsbetter₀ hx)
      rw [← this]
      have hesource : e.source ∈ 𝓝 x' := by
        have : (e.extend I).symm x = x' := rfl
        have : x' ∈ e.source := by sorry -- tedious busywork
          --rw [← this]
          --apply mem_of_mem_of_subset hx hsbetter₀ --?h--sorry
          --apply inter_subset_left--refine MapsTo.image_subset ?h
        exact e.open_source.mem_nhds this
      exact extendedChart_image_nhds_on I hesource (Eq.subset rfl)
    have hr : 1 ≤ (r : ℕ∞) := Nat.one_le_cast.mpr (Nat.one_le_of_lt hr)
    have he : e ∈ maximalAtlas I M := by sorry -- why doesn't the same proof work?
    have : I '' e.target ∈ 𝓝 x := sorry -- easy
    have hA : MDifferentiableAt 𝓘(ℝ, E) I (e.invFun ∘ I.invFun) x :=
      ((contMDiffOn_extend_symm (𝕜 := ℝ) he).contMDiffAt this).mdifferentiableAt hr
    -- General nonsense: f is ContMDiff, hence also MDifferentiable at each point.
    have hB : MDifferentiableAt I J f ((e.invFun ∘ I.invFun) x) := hf.contMDiffAt.mdifferentiableAt hr
    -- Should be similar. TODO: fix this.
    have hBA : MDifferentiableAt 𝓘(ℝ, E) J (f ∘ (e.invFun ∘ I.invFun)) x := by
      sorry -- exact hB.comp hA (M' := M) (M'' := N)
    -- should be obvious, skipping for now. (open set as w is open)
    have hnC : ((f ∘ e.invFun ∘ I.invFun) '' w) ∈ 𝓝 ((f ∘ e.invFun ∘ I.invFun) x) := sorry
    have hC : MDifferentiableAt J 𝓘(ℝ, F) (J ∘ e') ((f ∘ e.invFun ∘ I.invFun) x) := by
      have : ContMDiffOn J 𝓘(ℝ, F) ∞ (J ∘ e') e'.source := extendedChart_smooth _ (chart_mem_atlas G _)
      exact SmoothAt.mdifferentiableAt ((this.mono hw).contMDiffAt hnC)
    -- By the chain rule, D is the composition of A, B and C.
    let comp := C.comp (B.comp A)
    let r := calc comp
      _ = C.comp (B.comp A) := rfl
      _ = C.comp ((mfderiv I J f ((e.invFun ∘ I.invFun) x)).comp (mfderiv 𝓘(ℝ, E) I (e.invFun ∘ I.invFun) x)) := rfl
      _ = C.comp (mfderiv 𝓘(ℝ, E) J (f ∘ (e.invFun ∘ I.invFun)) x) := by rw [(mfderiv_comp x hB hA)]
      _ = (mfderiv J 𝓘(ℝ, F) (J ∘ e') ((f ∘ e.invFun ∘ I.invFun) x)).comp (mfderiv 𝓘(ℝ, E) J (f ∘ (e.invFun ∘ I.invFun)) x) := rfl
      _ = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) ((J ∘ e') ∘ ((f ∘ e.invFun ∘ I.invFun))) x := by rw [(mfderiv_comp x hC hBA)]
      _ = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f_local x := rfl
      _ = D := rfl

    -- By hypothesis, B is not surjective.
    let x' := (e.extend I).symm x
    have aux : x' ∈ s := hsbetter₁ (mem_image_of_mem _ hx)
    have : f' x' = B := by rw [← (hf' x' aux).mfderiv]
    have hBsurj : ¬ Surjective B := this ▸ h'f' _ aux
    -- The charts e.extend I and e'.extend J are diffeos, hences their differentials are isomorphisms.
    -- Thus, A and C are bijective.
    have hA : Bijective A := extendedChart_symm_differential_bijective I (chart_mem_atlas H _) (hsbetter₀ hx)
    have hC : Bijective C :=
      extendedChart_differential_bijective J (chart_mem_atlas G _) (hsbetter₃ (mem_image_of_mem _ hx))
    -- Thus, B is surjective iff `comp` is.
    -- FUTURE: extract as lemma: df' is {injective,surjective} iff its composition in charts is.
    have : Surjective B ↔ Surjective comp := by
      have : comp = (C ∘ B) ∘ A := rfl
      rw [this]
      rw [hA.surjective.of_comp_iff (C ∘ B)]
      rw [Surjective.of_comp_iff' hC B]
    rw [← r]
    have : ¬Surjective comp := by rw [← this]; exact hBsurj
    exact this

theorem sard {f : M → N} (hf : ContMDiff I J r f)
    {f' : ∀x, TangentSpace I x →L[ℝ] TangentSpace J (f x)} {s : Set M}
    (hf' : ∀ x ∈ s, HasMFDerivAt I J f x (f' x))
    (h'f' : ∀ x ∈ s, ¬ Surjective (f' x)) : MeasureZero J (f '' s) := by
  -- define interior and boundary of a manifold; show they decompose M
  -- show: interior is open, hence is a manifold without boundary
  -- (show: boundary is a one-dimensional submanifold --- not important for this theorem)
  -- show: boundary has measure zero
  -- deduce version this version from `sard_boundaryless`
  sorry

/-- **Sard's theorem**: let $M$ and $N$ be real $C^r$ manifolds of dimensions $m$ and $n$,
and $f:M→N$ a $C^r$ map. If $r>\max{0, m-n}$, the critical set is meagre. -/
-- FIXME: do I really need N to be Hausdorff? For the local result, I don't...
-- FIXME: allow `N` with boundary - will follow once `meagre_if_sigma_compact
theorem sard' {f : M → N} (hf : ContMDiff I J r f) [T2Space N] [J.Boundaryless]
    {f' : ∀x, TangentSpace I x →L[ℝ] TangentSpace J (f x)} {s : Set M} (hs : IsClosed s)
    (hf' : ∀ x ∈ s, HasMFDerivAt I J f x (f' x))
    (h'f' : ∀ x ∈ s, ¬ Surjective (f' x)) : IsMeagre (f '' s) := by
  -- M is second countable and locally compact (as finite-dimensional), hence σ-compact.
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  have : IsSigmaCompact s := isSigmaCompact_univ.of_isClosed_subset hs (subset_univ s)
  exact MeasureZero.isMeagre_of_isSigmaCompact J (sard I hf hf' h'f') (this.image (hf.continuous))

-- Corollary. The set of regular values is residual and therefore dense.

-- most general version: phrased using the Hausdorff dimension
