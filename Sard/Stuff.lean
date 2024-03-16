import Sard.LocallyLipschitzMeasureZero
import Sard.MeasureZero
import Mathlib.Geometry.Manifold.ContMDiff.Defs

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

/-- If M, N are C¹ manifolds with dim M < dim N and f:M → N is C¹, then f(M) has measure zero. -/
-- XXX: do I actually use this result?
lemma image_null_of_C1_of_dimension_increase {f : M → N} (hf : ContMDiff I J r f)
    (hdim : m < n) : MeasureZero J (Set.range f) := by
  rw [← image_univ]
  suffices hyp : ∀ x : M, MeasureZero J (f '' ((chartAt H x).source ∩ univ)) by
    apply MeasureZero.measure_zero_image_iff_chart_domains (J := J) hyp
  -- Fix a chart; we want to show f(U ∩ M) has measure zero.
  intro x μ hμ y
  let e := chartAt H x
  let e' := chartAt G y
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
