import Mathlib.Geometry.Manifold.MFDeriv

/-!
# Local compactness of manifolds
Finite-dimensional manifolds without boundary are locally compact.

TODO:
- adapt the proof to manifolds with boundary (needs a new argument to handle boundary points),
  possibly also adaptions of the definition of boundary.
- generalise to manifolds on any complete normed fields
(this is merely missing the corresponding instance on normed spaces)
-/

open Function Set TopologicalSpace Topology
set_option autoImplicit false

variable
  -- Let `M` be a manifold over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [HasGroupoid M (contDiffGroupoid 0 I)]

/-- Analogous to the funext tactic, but only on a set. -/
-- add to Data.Set.Image
theorem funext_on {α β : Type*} {f : α → β} {g : β → α} {s : Set α} (h : ∀ x : s, (g ∘ f) x = x)
    : g ∘ f '' s = s := by
  simp_all only [comp_apply, Subtype.forall, image_id']

section LocalHomeo -- add to `LocalHomeomorph.lean`
-- like `e.map_source`, but stated in terms of images
/-- A local homeomorphism maps its source to its target. -/
lemma LocalHomeomorph.map_source'' {e : LocalHomeomorph M H} : e '' e.source ⊆ e.target :=
  fun _ ⟨_, hx, hex⟩ ↦ mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

lemma LocalEquiv.map_source'' {e : LocalEquiv M H} : e '' e.source ⊆ e.target :=
  fun _ ⟨_, hx, hex⟩ ↦ mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

lemma LocalHomeomorph.isOpenMapOn_source {e : LocalHomeomorph M H} {s : Set M}
    (hopen : IsOpen s) (hs : s ⊆ e.source) : IsOpen (e '' s) := by
  rw [(image_eq_target_inter_inv_preimage (e := e) hs)]
  exact e.continuous_invFun.preimage_open_of_open e.open_target hopen

lemma LocalHomeomorph.symm_isOpenMapOn_target {e : LocalHomeomorph M H} {t : Set H}
    (hopen : IsOpen t) (ht : t ⊆ e.target) : IsOpen (e.invFun '' t) := by
  have r : e.invFun '' t = e.source ∩ ↑e ⁻¹' t := symm_image_eq_source_inter_preimage (e := e) ht
  exact r ▸ e.continuous_toFun.preimage_open_of_open e.open_source hopen
end LocalHomeo

section ModelsWithCorners -- add to `SmoothManifoldWithCorners.lean`
theorem ModelWithCorners.leftInverse' : I.invFun ∘ I = id := funext I.leftInverse

/-- If I is boundaryless, it is an open embedding. -/
theorem ModelWithCorners.toOpenEmbedding [I.Boundaryless] : OpenEmbedding I :=
  I.toHomeomorph.openEmbedding

/-- If I is boundaryless, `I.symm` is an open embedding. -/
theorem ModelWithCorners.toOpenEmbedding_symm [I.Boundaryless] : OpenEmbedding I.symm :=
  I.toHomeomorph.symm.openEmbedding

lemma LocalHomeomorph.extend_left_inv' {t : Set M} {e : LocalHomeomorph M H} (ht: t ⊆ e.source) :
    ((e.extend I).symm ∘ (e.extend I)) '' t = t :=
  funext_on (fun ⟨_, hx⟩ ↦ e.extend_left_inv _ (ht hx))

/-- If I has no boundary, `e.extend I` is an open map on its source. -/
lemma LocalHomeomorph.extend_isOpenMapOn_source [I.Boundaryless] {e : LocalHomeomorph M H}
    {s : Set M} (hopen : IsOpen s) (hs : s ⊆ e.source) : IsOpen ((e.extend I) '' s) := by
  simp only [extend_coe, image_comp I e]
  -- As I has no boundary, it is a homeomorphism, hence an open embedding.
  apply (I.toOpenEmbedding.open_iff_image_open).mp (e.isOpenMapOn_source hopen hs)

/-- If I has no boundary, `(e.extend I).symm` is an open map on its source. -/
lemma LocalHomeomorph.extend_symm_isOpenMapOn_target [I.Boundaryless] {e : LocalHomeomorph M H}
    {t : Set E} (hopen : IsOpen t) (ht : t ⊆ (e.extend I).target) : IsOpen ((e.extend I).symm '' t) := by
  have h : IsOpen (I.invFun '' t) := I.toOpenEmbedding_symm.open_iff_image_open.mp hopen
  have : (e.extend I).target = I.symm ⁻¹' e.target := by
    let r := e.extend_target I
    rw [I.range_eq_univ, inter_univ] at r
    exact r
  have : I.symm '' t ⊆ e.target := calc I.symm '' t
    _ ⊆ I.symm '' ((e.extend I).target) := image_subset _ ht
    _ = I.symm '' (I.symm ⁻¹' e.target) := by rw [this]
    _ ⊆ e.target := image_preimage_subset I.symm e.target
  rw [extend_coe_symm, image_comp]
  exact e.symm_isOpenMapOn_target h this

/-- If `I` has no boundary, `(e.extend I).symm` maps neighbourhoods on its source. -/
lemma LocalHomeomorph.extend_image_mem_nhds_symm [I.Boundaryless] {e : LocalHomeomorph M H}
    {x : E} {n : Set E} (hn : n ∈ 𝓝 x) (hn' : n ⊆ (e.extend I).target) :
    (e.extend I).symm '' n ∈ 𝓝 ((e.extend I).symm x) := by
  -- XXX: there ought to be a slicker proof, using that I and e map nhds to nhds
  rcases mem_nhds_iff.mp hn with ⟨t', ht's', ht'open, hxt'⟩
  rw [mem_nhds_iff]
  refine ⟨(e.extend I).symm '' t', image_subset _ ht's', ?_, ?_⟩
  · apply e.extend_symm_isOpenMapOn_target _ ht'open (Subset.trans ht's' hn')
  · exact mem_image_of_mem (e.extend I).symm hxt'

end ModelsWithCorners

/-- Auxiliary lemma for local compactness of `M`. -/
lemma localCompactness_aux [FiniteDimensional ℝ E] (hI : ModelWithCorners.Boundaryless I)
    {x : M} {n : Set M} (hn : n ∈ 𝓝 x) : ∃ s : Set M, s∈ 𝓝 x ∧ s ⊆ n ∧ IsCompact s  := by
  -- Assume `n` is contained in some chart at x. (Choose the distinguished chart from our atlas.)
  let chart := ChartedSpace.chartAt (H := H) x
  let echart := extChartAt I x
  have hn : n ∩ echart.source ∈ 𝓝 x := Filter.inter_mem hn
    (chart.extend_source_mem_nhds _ (mem_chart_source H x))

  -- Apply the chart to obtain a neighbourhood of `echart x ∈ E`.
  let x' := echart x
  let n' := echart '' (n ∩ echart.source)
  have hn' : n' ∈ 𝓝 x' := by
    let r := chart.map_extend_nhds I (mem_chart_source H x)
    rw [I.range_eq_univ, nhdsWithin_univ, ← extChartAt] at r
    exact r ▸ Filter.image_mem_map hn
  -- Since E is locally compact, x' has a compact neighbourhood s' ⊆ n'.
  have h : LocallyCompactSpace E := by infer_instance
  rcases h.local_compact_nhds x' n' hn' with ⟨s', hs', hsn', hscompact⟩
  -- Transport back: s := echart ⁻¹ (s') is a compact neighbourhood of x.
  let s := echart.symm '' s'
  have hsmall : s' ⊆ echart.target := calc s'
    _ ⊆ n' := hsn'
    _ ⊆ echart '' (echart.source) := image_subset _ (inter_subset_right _ _)
    _ ⊆ echart.target := echart.map_source''
  refine ⟨s, ?_, ?_, ?_⟩
  · -- FIXME: (how) to avoid these rewrites?
    let r := chart.extend_image_mem_nhds_symm I hs' hsmall
    have : LocalHomeomorph.extend chart I = echart := rfl
    rw [this, ← image_eta, (extChartAt_to_inv I x)] at r
    apply r
  · calc s
      _ ⊆ echart.symm '' n' := image_subset echart.symm hsn'
      _ = (echart.symm ∘ echart) '' (n ∩ echart.source) := by rw [image_comp]
      _ = n ∩ echart.source := by
        rw [extChartAt_source]
        apply chart.extend_left_inv' _ (inter_subset_right _ _)
      _ ⊆ n := inter_subset_left _ _
  · apply hscompact.image_of_continuousOn ((chart.continuousOn_extend_symm I).mono hsmall)

-- TODO: what's the right way to make this an instance?
/-- A finite-dimensional manifold without boundary is locally compact. -/
lemma Manifold.locallyCompact_of_finiteDimensional_of_boundaryless
    [FiniteDimensional ℝ E] (hI : ModelWithCorners.Boundaryless I) : LocallyCompactSpace M := by
  exact { local_compact_nhds := fun x n hn ↦ localCompactness_aux I hI hn }

-- TODO: add hypotheses, once I figure out the right incantation to add them!
/-- A finite-dimensional second-countable manifold without boundary is σ-compact. -/
instance [SecondCountableTopology M]
  /- [HasGroupoid M (contDiffGroupoid 0 I)] and all the other things -/
  /- [FiniteDimensional ℝ E] (hI : ModelWithCorners.Boundaryless I)-/ : SigmaCompactSpace M := by
  have : LocallyCompactSpace M := by
    sorry -- should be: Manifold.locallyCompact_of_finiteDimensional_of_boundaryless I hI
  apply sigmaCompactSpace_of_locally_compact_second_countable
