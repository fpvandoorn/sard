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
  -- F is basically R^n, G might be a half-space or so (if corners)
  -- J can be regarded as a map G→F
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
lemma measure_zero_subset {s t: Set N} (hst : s ⊆ t) (ht : measure_zero J t) :
    (measure_zero J s) := by
  rw [measure_zero]
  intro μ hμ e he
  have : J ∘ e '' (e.source ∩ s) ⊆  J ∘ e '' (e.source ∩ t) := by
    apply image_subset
    exact inter_subset_inter_right e.source hst
  exact measure_mono_null this (ht μ e he)

/- Let U c ℝ^n be an open set and f: U → ℝ^n be a C^1 map.
  If $X\subset U$ has measure zero, so has $f(X)$. -/
-- NB: this is false for mere C⁰ maps, the Cantor function f provides a counterexample:
-- the standard Cantor set has measure zero, but its image has measure one
-- (the complement [0,1]\C has countable image by definition of f).
lemma C1_image_null_set_null {f : E → E} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) [MeasurableSpace E] (μ : Measure E) [IsAddHaarMeasure μ]
    {s : Set E} (h₁s: s ⊆ U) (h₂s: μ s = 0) : μ (f '' s) = 0 := by sorry

-- Helper results in topology which should go in mathlib.
section Topology
-- this lemma is in mathlib, in LocalHomeomorph
-- theorem preimage_interior (s : Set β) :
--     e.source ∩ e ⁻¹' interior s = e.source ∩ interior (e ⁻¹' s) :=
--   (IsImage.of_preimage_eq rfl).interior.preimage_eq

-- the counterpart for image is currently missing
lemma image_interior {α β : Type} [TopologicalSpace α] [TopologicalSpace β]
    (e : LocalHomeomorph α β) (s : Set α) :
    e.target ∩ e '' interior s = e '' (e.source ∩ interior s) := by
  -- idea: restrict the local homeo to the appropriate part; then it's a homeo
  sorry

-- this is the lemma I'm actually interested in, for Homeomorphisms (also not in mathlib)
lemma homeo_preserves_empty_interior {α β : Type} [TopologicalSpace α] [TopologicalSpace β]
    (f : Homeomorph α β) (s : Set α) (h₂s : interior s = ∅) : interior (f '' s) = ∅ := by
  rw [← Homeomorph.image_interior, h₂s]
  exact Set.image_empty ↑f

open Set
lemma local_homeo_preserves_empty_interior {α β : Type}
    [TopologicalSpace α] [TopologicalSpace β] (f : LocalHomeomorph α β)
    (s : Set α) (hs : s ⊆ f.source) (h₂s : interior s = ∅) : interior (f '' s) = ∅ := by
  -- xxx clean up these partial steps
  -- restrict to domain and target: mathematically trivial
  have h₁ : s = s ∩ f.source := by
    rw [← @inter_eq_left_iff_subset α s f.source] at hs
    symm
    exact hs
  have h₂ : interior s = interior (s ∩ f.source) := by
    sorry -- how hard to deduce this?? just redo the proof of h₁?
  rw [h₁] at h₂s
  have h₃ : f '' (interior s ∩ f.source) = ∅ := by sorry

  --rw [← image_interior f] at h₃
  --rw [← h₂]
  -- exact Set.image_empty ↑f
  sorry
end Topology

section local_stuff
/-- Let $(U_α)$ be an open cover of a topological space X.
A subset $S ⊆ X$ has empty interior iff all $S∩U_α$ have empty interior. -/
theorem interior_zero_iff_open_cover {X : Type} [TopologicalSpace X]
    {I : Type} {U : I → Set X} (hU : ∀ α : I,  IsOpen (U α)) (hcover : ⋃ (α : I), U α = X) (s : Set X) :
    interior s = ∅ ↔ ∀ α : I, interior (s ∩ U α) = ∅ := by
  constructor
  · -- suppose interior S = ∅
    intro hs α
    have aux: interior (s ∩ U α) ⊆ interior s := by
      apply interior_mono
      apply Set.inter_subset_left
    -- by hypothesis hs, the rhs is empty, so the lhs also is
    exact Set.subset_eq_empty aux hs
  · intro h -- suppose each s ∩ U_α has empty interior
    -- it suffices to show that each open subset of s is empty
    suffices ∀ V : Set X, (hV : V ⊆ s ∧ IsOpen V) → V = ∅ by sorry
    -- let V ⊆ S be open
    rintro V ⟨hVS, hV⟩

    have h' : ∀ α : I, V ∩ U α = ∅ := by
      intro α
      -- each V ∩ U_α is open and contained in s ∩ U_α
      have h₁ : IsOpen (V ∩ U α) := by exact IsOpen.inter hV (hU α)
      have h₂ : V ∩ U α ⊆ s ∩ U α := by exact Set.inter_subset_inter_left (U α) hVS
      -- by hypothesis, the rhs has empty interior, hence is empty and V ∩ U α = ∅
      have h₃ : V ∩ U α ⊆ interior (s ∩ U α) := by exact interior_maximal h₂ h₁
      exact Set.subset_eq_empty h₃ (h α)

    -- so V=∅ and we're done
    have h'' : V = ⋃ (α : I), (V ∩ U α) := by
      ext i
      rw [Set.mem_iUnion]
      sorry
    rw [h'']
    -- warning for shadowing of hypotheses
    simp [Set.mem_iUnion]
    tauto
end local_stuff

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
