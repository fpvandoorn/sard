import Sard.LocallyLipschitz
import Sard.LocallyLipschitzMeasureZero
import Sard.MeasureZero
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.MFDeriv
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

open ENNReal NNReal FiniteDimensional Function Manifold MeasureTheory Measure Set TopologicalSpace Topology LocallyLipschitz
set_option autoImplicit false

variable
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] [FiniteDimensional ℝ E] [SecondCountableTopology M]
  [MeasurableSpace E] [BorelSpace E]
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [J.Boundaryless]
  [SmoothManifoldWithCorners J N] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
variable {m n r : ℕ} (hm : finrank ℝ E = m) (hn : finrank ℝ F = n) (hr : r > m-n)

/-- Let $U ⊆ ℝ^n$ be an open set and f : U → ℝ^n be a C^1 map.
  If $X\subset U$ has measure zero, so has $f(X)$.
  Note: this is false for merely C⁰ maps, the Cantor function $f$ provides a counterexample:
  the standard Cantor set has measure zero, but its image has measure one
  (as the complement $$[0,1]\setminus C$$ has countable image by definition of $f$). -/
lemma image_null_of_C1_of_null {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure F) [IsAddHaarMeasure ν]
    (hd : m = n) {s : Set E} (h₁s: s ⊆ U) (h₂s: μ s = 0) : ν (f '' s) = 0 := by
  -- The m-dimensional Hausdorff measure on E resp. F agrees with the Lebesgue measure.
  have h₁ : μ = μH[m] := by
    -- The m-dimensional Hausdorff measure is the Lebesgue measure on R^m.
    have aux : μH[m] = volume := by
      rw [← Fintype.card_fin m]
      exact hausdorffMeasure_pi_real (ι := Fin m)
    -- The Lebesgue measure is the Haar measure on R^m.
    -- xxx: doesn't typecheck yet, need a measurable equivalence between E and R^m
    -- have : μ = (volume : Measure (Fin m → ℝ)) := by sorry -- MeasureTheory.addHaarMeasure_eq_volume_pi
    -- perhaps https://github.com/leanprover-community/mathlib4/pull/7037 can help
    -- TODO: combining these doesn't work yet
    sorry
  have h₂ : ν = μH[n] := by sorry -- same argument like for μ
  -- Since f is C¹, it's locally Lipschitz on U and we can apply the previous lemma.
  rw [h₁] at h₂s
  have : μH[m] (f '' s) = 0 := by
    -- TODO: split U into convex subsets, e.g. open balls
    have scifi : Convex ℝ U := sorry
    apply locally_lipschitz_image_of_null_set_is_null_set_open (of_C1_on_open hU scifi hf) h₁s h₂s
  rw [h₂, ← hd]
  exact this

/-- If `f : ℝ^n → ℝ^n` is `C^1` and $X\subset ℝ^n$ has measure zero, so does $f(X)$. -/
lemma image_null_of_C1_of_null' {f : E → F} (hf : ContDiff ℝ 1 f)
    (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure F) [IsAddHaarMeasure ν]
    (hd : m = n) {s : Set E} (hs: μ s = 0) : ν (f '' s) = 0 := by
  let hdiff := Iff.mpr contDiffOn_univ hf
  apply image_null_of_C1_of_null isOpen_univ hdiff μ ν hd (subset_univ s) hs

/-- If $U ⊆ ℝ^m$ is open and $f : U → ℝ^n$ is a $C^1$ map with `m < n`, $f(U)$ has measure zero. -/
lemma image_measure_zero_of_C1_dimension_increase {g : E → F} {U : Set E} (hU : IsOpen U)
    [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [IsAddHaarMeasure ν]
    (hg : ContDiffOn ℝ 1 g U) (hmn : m < n) : ν (g '' U) = 0 := by
  -- Since n > m, g factors through the projection R^n → R^m.
  -- We consider the commutative diagram
  --      E ------------------ g --------> F
  --      |                                ^
  --      | incl                           | pi
  --      |                                |
  --      E × ℝ^{n-m}     ---- g' -->   F × ℝ^{n-m}
  let incl : E → E × (Fin (n-m) → ℝ) := fun x ↦ ⟨x, 0⟩
  let g' : E × (Fin (n-m) → ℝ) → F × (Fin (n-m) → ℝ) := fun ⟨y, _⟩ ↦ ⟨g y, 0⟩
  let pi : F × (Fin (n-m) → ℝ) → F := fun ⟨f, _⟩ ↦ f
  have commutes: pi ∘ g' ∘ incl = g := by
     ext y
     rw [comp_apply, comp_apply]
  -- Now, incl U = U × 0 has measure zero in E × ℝ^{n-m}.
  -- Choose a Haar measure on E × ℝ^{n-m}, so we can speak about the measure of U × {0},
  obtain ⟨K''⟩ : Nonempty (PositiveCompacts (E × (Fin (n-m) → ℝ))) := PositiveCompacts.nonempty'
  let μ' : Measure (E × (Fin (n-m) → ℝ)) := addHaarMeasure K''
  have hisHaar: IsAddHaarMeasure μ' := isAddHaarMeasure_addHaarMeasure K''
  -- U × 0 has measure zero in E × ℝ^{n-m}: use Fubini and product measures.
  have aux : μ' (incl '' U) = 0 := by sorry
  -- Hence so does its image pi ∘ g' ∘ incl (U) = g '' U.
  have : ν ((pi ∘ g' ∘ incl) '' U) = 0 := by
    -- XXX: statement doesn't typecheck yet, need some currying.
    -- have : ContDiffOn ℝ 1 (pi ∘ g') (U × (univ: Fin (n-m) → ℝ)) := sorry
    -- refine image_null_of_C1_of_null ?_ ?_ aux ?_ doesn't apply yet
    sorry
  rw [← commutes]
  exact this

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
    apply MeasureZero.mono _ h
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
  apply MeasureZero.iUnion (ι := T)
  exact this

/-- If M, N are C¹ manifolds with dim M < dim N and f:M → N is C¹, then f(M) has measure zero. -/
-- XXX: do I actually use this result?
lemma image_null_of_C1_of_dimension_increase {f : M → N} (hf : ContMDiff I J r f)
    (hdim : m < n) : MeasureZero J (Set.range f) := by
  rw [← image_univ]
  suffices hyp : ∀ e ∈ atlas H M, MeasureZero J (f '' (e.source ∩ univ)) by
    exact measure_zero_image_iff_chart_domains hyp
  -- Fix a chart; we want to show f(U ∩ M) has measure zero.
  intro e he μ hμ e' he'
  -- FIXME. This looks a bit sketchy... adapt proof if necessary!
  have aux : J ∘ e' '' (e'.source ∩ f '' e.source) = (J ∘ e' ∘ f) '' e.source := by sorry
  rw [inter_univ, aux]
  -- Consider the local coordinate expression g : U → ℝ^m of f.
  -- We define g on all of E, taking junk values outside of U.
  let g : E → F := J ∘ e' ∘ f ∘ e.invFun ∘ I.invFun
  have : (J ∘ ↑e' ∘ f '' e.source) = g '' (I '' e.target) := by sorry
  -- g is C¹: suffices on chart domains; there it's by definition.
  have hopen : IsOpen (I '' e.target) := by sorry
  have gdiff : ContDiffOn ℝ 1 g (I '' e.target) := by sorry
  rw [this]
  apply image_measure_zero_of_C1_dimension_increase hopen μ gdiff hdim

/-- Local version of Sard's theorem. If $W ⊆ ℝ^m$ is open and $f: W → ℝ^n$ is $C^r$,
the set of critical values has measure zero. -/
theorem sard_local {s w : Set E} {f : E → F} (hw : IsOpen w) (hsw : s ⊆ w)
    (hf : ContDiffOn ℝ r f w) {f' : E → E →L[ℝ] F} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (h'f' : ∀ x ∈ s, ¬ Surjective (f' x)) (μ : Measure F) [IsAddHaarMeasure μ] :
    μ (f '' s) = 0 := by
  by_cases hyp: m < n
  · have hr : 1 ≤ (r : ℕ∞) := Iff.mpr Nat.one_le_cast (Nat.one_le_of_lt hr)
    have : ContDiffOn ℝ 1 f w := by apply ContDiffOn.of_le hf hr
    have hless: μ (f '' s) ≤ 0 := by calc
      μ (f '' s) ≤ μ (f '' w) := measure_mono (image_subset f hsw)
      _ = 0 := image_measure_zero_of_C1_dimension_increase hw μ this hyp
    simp only [nonpos_iff_eq_zero, zero_le] at hless ⊢
    exact hless
  · sorry

-- TODO: this is missing API for toSubset
lemma toSubset_aux1 {X Y : Type*} (f : X → Y) {s w : Set X} (hsw : s ⊆ w) :
    f '' (s ∩ w) = (w.restrict f) '' (toSubset s w) := sorry

-- TODO: this is missing API for toSubset or rather IsSigmaCompact
lemma toSubset_aux2 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s w : Set X} (hsw : s ⊆ w) (hs : IsSigmaCompact s) : IsSigmaCompact (toSubset s w) := sorry

/-- Local version of Sard's theorem. If $W ⊆ ℝ^m$ is open and $f: W → ℝ^n$ is $C^r$,
the set of critical values of `f` is a meagre set.
We phrase this for any closed set `s` of critical points of `f`; this is fine
as the critical set of `f` is closed. -/
theorem sard_local' {s w : Set E} {f : E → F} (hw : IsOpen w) (hs : IsClosed s) (hsw : s ⊆ w)
    (hf : ContDiffOn ℝ r f w) {f' : E → E →L[ℝ] F} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (h'f' : ∀ x ∈ s, ¬ Surjective (f' x)) : IsMeagre (f '' s) := by
  -- The critical set of `f` is closed: enlarge `s` if needed.
  -- Hence, it's σ-compact, and thus is the set of critical values.
  have h₁: IsSigmaCompact s :=
    SigmaCompact_of_isClosed_subset isSigmaCompact_univ hs (subset_univ s)
  have : IsSigmaCompact (f '' s) := by
    let g := w.restrict f
    have : f '' s = g '' (toSubset s w) := by
      have : s ∩ w = s := Iff.mpr inter_eq_left_iff_subset hsw
      calc f '' s
        _ = f '' (s ∩ w) := by rw [this]
        _ = g '' (toSubset s w) := by rw [(toSubset_aux1 f hsw)]
    rw [this]
    have : IsSigmaCompact (toSubset s w) := toSubset_aux2 hsw h₁ (X := E) (Y := F)
    exact SigmaCompact_image (ContinuousOn.restrict (ContDiffOn.continuousOn hf)) this

  obtain ⟨K''⟩ : Nonempty (PositiveCompacts F) := PositiveCompacts.nonempty'
  let μ : Measure F := addHaarMeasure K''
  have ass : μ (f '' s) = 0 := sard_local hr hw hsw hf hf' h'f' μ
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
  suffices hyp: ∀ e ∈ atlas H M, MeasureZero J (f '' (e.source ∩ s)) by
    exact measure_zero_image_iff_chart_domains hyp
  intro e he
  -- reduce to images of chart domains, then apply `sard_local`
  sorry

/-- **Sard's theorem**: let $M$ and $N$ be real $C^r$ manifolds of dimensions $m$ and $n$,
and $f:M→N$ a $C^r$ map. If $r>\max{0, m-n}$, the critical set is meagre. -/
-- FIXME: do I really need N to be Hausdorff? For the local result, I don't...
theorem sard' {f : M → N} (hf : ContMDiff I J r f) [T2Space N]
    {f' : ∀x, TangentSpace I x →L[ℝ] TangentSpace J (f x)} {s : Set M} (hs : IsClosed s)
    (hf' : ∀ x ∈ s, HasMFDerivWithinAt I J f s x (f' x))
    (h'f' : ∀ x ∈ s, ¬ Surjective (f' x)) : IsMeagre (f '' s) := by

  -- M is second countable and locally compact (as finite-dimensional), hence σ-compact.
  have : SigmaCompactSpace M := by
    have : LocallyCompactSpace M := by sorry -- infer_instance
    exact sigmaCompactSpace_of_locally_compact_second_countable
  have : IsSigmaCompact s :=
    SigmaCompact_of_isClosed_subset isSigmaCompact_univ hs (subset_univ s)
  have : IsSigmaCompact (f '' s) := SigmaCompact_image (ContMDiff.continuous hf) this
  exact MeasureZero.meagre_if_sigma_compact J (sard _ hf hf' h'f') this

-- Corollary. The set of regular values is residual and therefore dense.

-- most general version: phrased using the Hausdorff dimension