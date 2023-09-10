import Sard.MeasureZero
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.MFDeriv
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

open FiniteDimensional Function Manifold MeasureTheory Measure Set TopologicalSpace Topology
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
    { s : Set X } (hs : μH[d] s = 0) : μH[d] (f '' s) = 0 := by
  -- Choose a countable cover of X by compact sets K_n.
  let K : ℕ → Set X := compactCovering X
  have hcov : ⋃ (n : ℕ), K n = univ := iUnion_compactCovering X
  have hcompact : ∀ n : ℕ, IsCompact (K n) := isCompact_compactCovering X

  -- By countable subadditivity, it suffices to show the claim for each K_n.
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
    apply this
    exact ⟨(by simp only [ge_iff_le, zero_le]), hless⟩

  intro n
  -- Consider the open cover (U_x) of K_n induced by hf: each U_x is an open subset containing x
  -- on which f is Lipschitz, say with constant K_x.
  let U : K n → Set X := by
    intro x
    have hyp := hf x -- there exist K U, s.t. U is open and f is K-Lipschitz on U
    -- FIXME: make this step work: rcases hyp with ⟨KU, hKU⟩
    sorry
  have hcovering : K n ⊆ ⋃ (x : (K n)), U x := sorry -- since x ∈ U_x
  have hopen : ∀ x : (K n), IsOpen (U x) := sorry -- almost vacuously true
  have hLipschitz : ∀ x : (K n), ∃ K, LipschitzOnWith K f (U x) := by sorry -- by construction

  -- Since K_n is compact, (U_x) has a finite subcover U_1, ..., U_l.
  let subcover := IsCompact.elim_finite_subcover (hcompact n) U hopen hcovering
  rcases subcover with ⟨t, ht⟩
  -- On each U_j, f is Lipschitz by hypothesis.
  have : ∀ i : t, ∃ K : NNReal, LipschitzOnWith K f (U i) := by sorry
  -- Hence, the previous lemma `lipschitz_image_null_set_is_null_set` applies.
  sorry
end ImageMeasureZeroSet

variable {m n r : ℕ} (hm : finrank ℝ E = m) (hn : finrank ℝ F = n) (hr : r > m-n)
variable {J}

/-- Let $U ⊆ ℝ^n$ be an open set and f : U → ℝ^n be a C^1 map.
  If $X\subset U$ has measure zero, so has $f(X)$.
  Note: this is false for merely C⁰ maps, the Cantor function $f$ provides a counterexample:
  the standard Cantor set has measure zero, but its image has measure one
  (as the complement $$[0,1]\setminus C$$ has countable image by definition of $f$). -/
lemma C1_image_null_set_null {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]
    [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [IsAddHaarMeasure ν]
    (hd : m = n) {s : Set E} (h₁s: s ⊆ U) (h₂s: μ s = 0) : ν (f '' s) = 0 := by
  -- The m-dimensional Hausdorff measure on E resp. F agrees with the Lebesgue measure.
  have h₁ : μ = μH[m] := by
    -- The m-dimensional Hausdorff measure is the Lebesgue measure on R^m.
    have aux : μH[m] = (volume : Measure (Fin m → ℝ)) := by sorry -- apply hausdorffMeasure_pi_real
    -- The Lebesgue measure is the Haar measure on R^m.
    -- xxx: doesn't typecheck yet, need a measurable equivalence between E and R^m
    -- have : μ = (volume : Measure (Fin m → ℝ)) := by sorry -- MeasureTheory.addHaarMeasure_eq_volume_pi
    -- TODO: combining these doesn't work yet
    sorry
  have h₂ : ν = μH[n] := by sorry -- same argument like for μ
  -- Since f is C¹, it's locally Lipschitz and we can apply the previous lemma.
  have : μH[m] (f '' s) = 0 := by
    -- f is locally Lipschitz (xxx: introduce a predicate for this?)
    have hf' : ∀ x : E, ∃ K : NNReal, ∃ U : Set E, IsOpen U ∧ LipschitzOnWith K f U := by
      intro x
      have : ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t := by
        sorry -- somehow, apply ContDiffAt.exists_lipschitzOnWith
      rcases this with ⟨K, ⟨t, ⟨ht, hfloc⟩⟩⟩
      rw [mem_nhds_iff] at ht
      rcases ht with ⟨U, ⟨hUt, hU, hxU⟩⟩
      have : LipschitzOnWith K f U := LipschitzOnWith.mono hfloc hUt
      use K
      use U
    -- TODO: doesn't work, for reasons I don't understand
    -- apply locally_lipschitz_image_of_null_set_is_null_set hf' (X := E) (d := m) hs
    sorry
  rw [h₂, ← hd]
  exact this

/-- If $U ⊆ ℝ^m$ is open and f : U → ℝ^n is a C^1 map with `m < n`, then $f(U)$ has measure zero. -/
lemma image_C1_dimension_increase_null_local {g : E → F} {U : Set E} (hU : IsOpen U)
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]
    [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [IsAddHaarMeasure ν]
    (hg : ContDiffOn ℝ 1 g U) (hmn : m < n) : ν (g '' U) = 0 := by
  -- Since n > m, g factors through the projection R^n → R^m.
  -- We consider the commutative diagram
  --      E ------------------ g --------> F
  --      |                                ^
  --      | incl                           | pi
  --      |                                |
  --      E × ℝ^{n-m}     ---- g' -->   F × ℝ^{n-m}
  -- More precisely: consider the function g' also mapping to the extra factor.
  let incl : E → E × (Fin (n-m) → ℝ) := fun x ↦ ⟨x, 0⟩
  let g' : E × (Fin (n-m) → ℝ) → F × (Fin (n-m) → ℝ) := fun ⟨y, _⟩ ↦ ⟨g y, 0⟩
  let pi : F × (Fin (n-m) → ℝ) → F := fun ⟨f, _⟩ ↦ f
  have commutes: pi ∘ g' ∘ incl = g := by -- can I golf this to one line?
     ext y
     rw [comp_apply, comp_apply]
  -- Now, incl(U)=U × 0 has measure zero in E × ℝ^{n-m}.
  -- Choose a Haar measure on E × ℝ^{n-m}, so we can speak about the measure of U × {0},
  obtain ⟨K''⟩ : Nonempty (PositiveCompacts (E × (Fin (n-m) → ℝ))) := PositiveCompacts.nonempty'
  let μ' : Measure (E × (Fin (n-m) → ℝ)) := addHaarMeasure K''
  have hisHaar: IsAddHaarMeasure μ' := isAddHaarMeasure_addHaarMeasure K''
  -- U × 0 has measure zero in E × ℝ^{n-m}: need to pass to product measures.
  have aux : μ' (incl '' U) = 0 := by sorry
  -- Hence so does its image pi ∘ g' ∘ incl (U) = g '' U.
  have : ν ((pi ∘ g' ∘ incl) '' U) = 0 := by
    -- XXX: statement doesn't typecheck yet. have : ContDiffOn ℝ 1 (pi ∘ g') (U × (Fin (n-m) → ℝ)) := sorry
    -- apply C1_image_null_set_null, XXX doesn't apply yet
    sorry
  rw [← commutes]
  exact this

/-- If M, N are C¹ manifolds with dim M < dim N and f:M → N is C¹, then f(M) has measure zero. -/
-- XXX: why am I proving this? is this result useful anyway?
-- because I think the same argument is used for Sard's theorem locally...
lemma image_C1_dimension_increase_image_measure_zero {f : M → N} (hf : ContMDiff I J r f)
    [SecondCountableTopology M]
    (hdim : m < n) : MeasureZero J (Set.range f) := by
  -- It suffices to show that the image of each chart domain has measure zero.
  suffices ∀ e ∈ atlas H M, MeasureZero J (f '' (e.source)) by
    let s : Set M := univ -- so we can generalise later
    -- The charts of M form an open cover.
    let U : M → Set M := fun x ↦ (ChartedSpace.chartAt x : LocalHomeomorph M H).source
    have hcovering : univ ⊆ ⋃ (x : M), U x := by -- XXX: can golf this??
      intro x
      have : x ∈ U x := mem_chart_source H x
      rw [@mem_iUnion]
      intro _
      use x
    have hopen : ∀ x : M, IsOpen (U x) := fun x => (ChartedSpace.chartAt x).open_source
    -- since M is second countable, it is Lindelöf: there is a countable subcover U_n of M.
    let subcover := TopologicalSpace.isOpen_iUnion_countable U hopen
    rcases subcover with ⟨T, ⟨hTCountable, hTcover⟩⟩
    -- Each f(U_n ∩ S) has measure zero by hypothesis, we have f '' S = ∪ f (U_n ∩ S).
    have : ∀ i : T, MeasureZero J (f '' ((U i) ∩ s)) := by
      intro i
      simp_all only [chart_mem_atlas, ge_iff_le, gt_iff_lt, inter_univ]
    -- The countable union of measure zero sets has measure zero.
    have decomp : ⋃ (i : T), f '' ((U i) ∩ s) = range f := by sorry
      -- calc
      --   range f
      --   _ = f '' univ := by sorry
      --   _ = f '' (⋃ (x : M), U x) := by sorry
      --   _ = f '' (⋃ (i : M) (_ : i ∈ T), U i) := by sorry
      --   --_ = f '' (⋃ (i : T), T i) := by sorry
      --simp only [inter_univ, iUnion_coe_set]
    rw [← decomp]
    have todo : Encodable T := by sorry --infer_instance
    apply @MeasureZero.iUnion (ι := T)
    exact this

  -- Fix a chart; we want to show f(U ∩ M) has measure zero.
  intro e he
  rw [MeasureZero]
  intro μ hμ e' he'
  have aux : J ∘ e' '' (e'.source ∩ f '' e.source) = (J ∘ e' ∘ f) '' e.source := by sorry
  rw [aux]
  -- Consider the function g : U → ℝ^m. Defined on all of E (taking junk values outside of the chart).
  let g : E → F := J ∘ e' ∘ f ∘ e.invFun ∘ I.invFun
  have : (J ∘ ↑e' ∘ f '' e.source) = g '' (I '' e.target) := by sorry
  -- g is C¹: argue that everything is on the chart domains, then by definition
  have gdiff : ContDiffOn ℝ 1 g (I '' e.target) := by sorry
  rw [this]
  -- this is basically image_C1_dimension_increase_null_local
  -- applied to g, with hypotheses gdiff hdim, measure μ... doesn't typecheck yet
  sorry

/-- Local version of Sard's theorem. If $W ⊆ ℝ^m$ is open and $f: W → ℝ^n$ is $C^r$,
the set of critical values has measure zero. -/
theorem sard_local {s w : Set E} {f : E → F} (hf : ContDiffOn ℝ r f w)
    {f' : E → E →L[ℝ] F} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (h'f' : ∀ x ∈ s, ¬ Surjective (f' x)) (μ : Measure F) [IsAddHaarMeasure μ] :
    μ (f '' s) = 0 := by
  by_cases hyp: m < n
  · sorry -- show f(W) has measure zero; use `image_C1_dimension_increase_null_local`
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
  -- It suffices to show that the image of each chart domain has measure zero.
  suffices ∀ e ∈ atlas H M, MeasureZero J (f '' (e.source)) by
    intro μ hμ e he
    -- should be a standard open cover argument: Lindelöf, countable unions etc.
    -- same as for image_C1_dimension_increase_image_measure_zero
    sorry
  sorry-- apply sard_local

-- Corollary. The set of regular values is residual and therefore dense.
-- note: `ContDiffOn.dense_compl_image_of_dimH_lt_finrank` looks related, I want a version on manifolds
