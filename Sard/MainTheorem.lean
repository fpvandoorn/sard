import Sard.LocallyLipschitz
import Sard.MeasureZero
import Mathlib.Geometry.Manifold.MFDeriv
import Mathlib.Topology.MetricSpace.HausdorffDimension

open ENNReal NNReal FiniteDimensional Function Manifold MeasureTheory Measure Set TopologicalSpace Topology LocallyLipschitz
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

-- generalises statements in Data.Set.Image.lean
theorem image_subset_preimage_of_inverseOn {α β : Type*} {f : α → β} {g : β → α} (s : Set α)
    (I : LeftInvOn g f s) : f '' s ⊆ g ⁻¹' s := by
  sorry -- mathlib proof: fun _ ⟨a, h, e⟩ => e ▸ ((I a).symm ▸ h : g (f a) ∈ s)

theorem preimage_subset_image_of_inverseOn {α β : Type*} {f : α → β} {g : β → α} (t : Set β) (I : RightInvOn g f t)  :
    f ⁻¹' t ⊆ g '' t := sorry -- mathlib proof: fun b h => ⟨f b, h, I b⟩

theorem image_eq_preimage_of_inverseOn {α β : Type*} {f : α → β} {g : β → α} {s : Set α}
  (h₁ : LeftInvOn g f s) /-(h₂ : RightInvOn g f (f '' s))-/ : f '' s = g ⁻¹' s := by
  apply Subset.antisymm (image_subset_preimage_of_inverseOn s h₁)
  · sorry -- apply preimage_subset_image_of_inverseOn h₂ s almost works

/-- Analogous to the funext tactic, but only on a set. -/
-- move to Data.Set.Image
theorem funext_on {α β : Type*} {f : α → β} {g : β → α} {s : Set α} (h : ∀ x : s, (g ∘ f) x = x)
    : g ∘ f '' s = s := by
  simp_all only [comp_apply, Subtype.forall, image_id']

-- add to SmoothManifoldWithCorners.lean
theorem ModelWithCorners.leftInverse' : I.invFun ∘ I = id := funext I.leftInverse

-- If I is boundaryless, it is an open embedding.
-- XXX. there should be a shorter proof, using I.toHomeomorph
theorem ModelWithCorners.openEmbedding : OpenEmbedding I := by
  have h : IsOpen (range I) := by rw [I.range_eq_univ] ; exact isOpen_univ
  have : Embedding I := LeftInverse.embedding I.leftInverse I.continuous_invFun I.continuous_toFun
  exact { toEmbedding := this, open_range := h }

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
  suffices hyp: ∀ e ∈ atlas H M, MeasureZero J (f '' (e.source ∩ s)) from
    MeasureZero.measure_zero_image_iff_chart_domains (J := J) hyp
  intro e he
  -- Reduce to images of chart domains, then apply `sard_local`.
  -- Tedious part: check that all hypotheses transfer to their local counterparts.
  intro μ hμ e' he'
  -- Data for the reduction to local coordinates.
  let w := I ∘ e '' (e.source ∩ f ⁻¹' e'.source)
  let s_better := I ∘ e '' (s ∩ e.source ∩ f ⁻¹' e'.source)
  let f_local := (J ∘ e') ∘ f ∘ (e.invFun ∘ I.invFun)
  let f'_local : E → E →L[ℝ] F := fun x ↦ f' ((e.invFun ∘ I.invFun) x)

  have inv_fixed : ∀ t : Set M, t ⊆ e.source → (e.invFun ∘ I.invFun) ∘ (I ∘ e) '' t = t := by
    intro t ht
    have : e.invFun ∘ e '' t = t := funext_on (fun ⟨x, hxt⟩ ↦ e.left_inv' (ht hxt))
    calc (e.invFun ∘ I.invFun) ∘ (I ∘ e) '' t
      _ = e.invFun ∘ (I.invFun ∘ I) ∘ e '' t := by simp only [comp.assoc]
      _ = e.invFun '' ((I.invFun ∘ I) '' (e '' t)) := by simp only [image_comp]
      _ = e.invFun ∘ e '' t := by rw [I.leftInverse', image_id, image_comp]
      _ = t := by rw [this]
  have cor : (e.invFun ∘ I.invFun) ∘ (I ∘ e) '' (s ∩ e.source ∩ f ⁻¹' e'.source) = s ∩ e.source ∩ f ⁻¹' e'.source := by
    rw [inv_fixed]
    rw [inter_comm s, inter_assoc]
    apply inter_subset_left
  have : J ∘ e' '' (e'.source ∩ f '' (e.source ∩ s)) = f_local '' s_better := by
    symm
    calc f_local '' s_better
      _ = (J ∘ e') ∘ f ∘ (e.invFun ∘ I.invFun) '' (I ∘ e '' (s ∩ e.source ∩ f ⁻¹' e'.source)) := rfl
      _ = (J ∘ e') ∘ f '' (((e.invFun ∘ I.invFun) ∘ (I ∘ e)) '' (s ∩ e.source ∩ f ⁻¹' e'.source)) := by
        simp only [comp.assoc, image_comp]
      _ = J ∘ e' '' (f '' (s ∩ e.source ∩ f ⁻¹' e'.source)) := by rw [cor, image_comp]
      _ = J ∘ e' '' (f '' (e.source ∩ s ∩ f ⁻¹' e'.source)) := by rw [inter_comm s]
      _ = J ∘ e' '' (f '' (e.source ∩ s) ∩ e'.source) := by rw [image_inter_preimage f _ _]
      _ = J ∘ e' '' (e'.source ∩ f '' (e.source ∩ s)) := by rw [inter_comm]
  rw [this]
  apply sard_local hr (w := w) (s := s_better) (f := f_local) (f' := f'_local) (μ := μ)
  · have : IsOpen (e.source ∩ f ⁻¹' e'.source) :=
      IsOpen.inter e.open_source (e'.open_source.preimage hf.continuous)
    have : IsOpen (e '' (e.source ∩ f ⁻¹' e'.source)) := by
      have h : e '' (e.source ∩ f ⁻¹' e'.source) = e.invFun ⁻¹' (e.source ∩ f ⁻¹' e'.source) :=
        image_eq_preimage_of_inverseOn (LeftInvOn.mono (fun x ↦ e.left_inv) (inter_subset_left _ _))
      rw [h]
      refine e.continuous_invFun.isOpen_preimage e.open_target ?_ this
      have : e '' e.source ⊆ e.target := by sorry -- is essentially map_source'
      calc e.invFun ⁻¹' (e.source ∩ f ⁻¹' e'.source)
        _ = e '' (e.source ∩ f ⁻¹' e'.source) := by rw [← h]
        _ ⊆ e '' (e.source) := by apply image_subset; exact inter_subset_left e.source _
        _ ⊆ e.target := this
    -- As M has no boundary, I is a homeomorphism from H to E, hence an open embedding.
    simp only [image_comp I e]
    apply (I.openEmbedding.open_iff_image_open).mp this
  · apply image_subset (↑I ∘ ↑e)
    rw [inter_assoc]
    exact inter_subset_right s (e.source ∩ f ⁻¹' e'.source)
  · sorry -- ContDiffOn ℝ (↑r) f_local w
    -- should follow by definition, of ContDiff f in charts
  · sorry -- ∀ x ∈ s_better, HasFDerivWithinAt f_local (f'_local x) s_better x
    -- should follow almost by definition
  · -- ∀ x ∈ s_better, ¬Surjective ↑(f'_local x)
    intro x hx
    apply h'f' ((e.invFun ∘ I.invFun) x)
    have : e.invFun ∘ I.invFun '' s_better = s ∩ e.source ∩ f ⁻¹' e'.source := by
      calc e.invFun ∘ I.invFun '' s_better
        _ = e.invFun ∘ I.invFun '' (I ∘ e '' (s ∩ e.source ∩ f ⁻¹' e'.source)) := rfl
        _ = (e.invFun ∘ I.invFun) ∘ I ∘ e '' (s ∩ e.source ∩ f ⁻¹' e'.source) := by
          simp only [comp.assoc, image_comp]
        _ = s ∩ e.source ∩ f ⁻¹' e'.source := cor
    have : (e.invFun ∘ I.invFun) x ∈ s ∩ e.source ∩ f ⁻¹' e'.source :=
      this ▸ mem_image_of_mem (e.invFun ∘ I.invFun) hx
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
  have : SigmaCompactSpace M := by
    -- TODO: make an instance, so infer_instance works instead of this argument
    have : LocallyCompactSpace M := by
      suffices aux : ∀ (x : M), ∀ n ∈ 𝓝 x, ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s from
        { local_compact_nhds := aux }
      intro x n hn
      -- Choose a chart around x; e.g. the chart at x.
      let chart := ChartedSpace.chartAt (H := H) x
      -- Intersecting n with the chart source yields a nbhd of x; applying the chart
      -- yields a neighbourhood on E. Then use local compactness of E to find a nbhd,
      -- and transport it back using the chart.
      sorry
    exact sigmaCompactSpace_of_locally_compact_second_countable
  have : IsSigmaCompact s := isSigmaCompact_univ.of_isClosed_subset hs (subset_univ s)
  exact MeasureZero.meagre_if_sigma_compact J (sard _ hr hf hf' h'f') (this.image (hf.continuous))

-- Corollary. The set of regular values is residual and therefore dense.

-- most general version: phrased using the Hausdorff dimension
