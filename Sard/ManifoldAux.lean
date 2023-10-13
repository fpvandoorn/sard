import Mathlib.Geometry.Manifold.MFDeriv

/-!
# Additional lemmas about smooth manifolds
-/

open ENNReal NNReal FiniteDimensional Function Manifold Set TopologicalSpace Topology LocallyLipschitz
set_option autoImplicit false

/-- Analogous to the funext tactic, but only on a set. -/
-- add to Data.Set.Image
theorem funext_on {α β : Type*} {f : α → β} {g : β → α} {s : Set α} (h : ∀ x : s, (g ∘ f) x = x)
    : g ∘ f '' s = s := by
  simp_all only [comp_apply, Subtype.forall, image_id']

variable
  -- Let `M` be a smooth manifold over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]

section LocalHomeomorph -- add to `LocalHomeomorph.lean`
-- like `e.map_source'`, but stated in terms of images
lemma LocalHomeomorph.map_source_image {e : LocalHomeomorph M H} : e '' e.source ⊆ e.target :=
  fun _ ⟨_, hx, hex⟩ ↦ mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

lemma LocalHomeomorph.isOpenMapOn_source {e : LocalHomeomorph M H} {s : Set M}
    (hopen : IsOpen s) (hs : s ⊆ e.source) : IsOpen (e '' s) := by
  have r : e '' s = e.target ∩ e.invFun ⁻¹' s := image_eq_target_inter_inv_preimage (e := e) hs
  rw [r]
  exact e.continuous_invFun.preimage_open_of_open e.open_target hopen

-- xxx: can this be simplified?
lemma LocalHomeomorph.image_mem_nhds_on {e : LocalHomeomorph M H} {x : M} {n : Set M}
    (hn : n ∈ 𝓝 x) (hn₂ : n ⊆ e.source) : e '' n ∈ 𝓝 (e x) := by
  rcases mem_nhds_iff.mp hn with ⟨t, htn, htopen, hxt⟩
  rw [mem_nhds_iff]
  exact ⟨e '' t, image_subset e htn, e.isOpenMapOn_source htopen (Subset.trans htn hn₂),
    mem_image_of_mem _ hxt⟩

lemma LocalHomeomorph.inverse_isOpenMapOn_target {e : LocalHomeomorph M H} {t : Set H}
    (hopen : IsOpen t) (ht : t ⊆ e.target) : IsOpen (e.invFun '' t) := by
  have r : e.invFun '' t = e.source ∩ ↑e ⁻¹' t := symm_image_eq_source_inter_preimage (e := e) ht
  rw [r]
  exact e.continuous_toFun.preimage_open_of_open e.open_source hopen
end LocalHomeomorph

section ModelsWithCorners -- add to `SmoothManifoldWithCorners.lean`
theorem ModelWithCorners.leftInverse' : I.invFun ∘ I = id := funext I.leftInverse

/-- If I is boundaryless, it is an open embedding. -/
theorem ModelWithCorners.openEmbedding [I.Boundaryless] : OpenEmbedding I :=
  I.toHomeomorph.openEmbedding

theorem ModelWithCorners.openEmbedding_symm [I.Boundaryless] : OpenEmbedding I.symm :=
  I.toHomeomorph.symm.openEmbedding
end ModelsWithCorners

-- XXX: this should exist somewhere!
lemma chart_inverse {t : Set M} {e : LocalHomeomorph M H} (ht: t ⊆ e.source) :
    (e.invFun ∘ I.invFun ∘ I ∘ e) '' t = t := by
  calc (e.invFun ∘ I.invFun ∘ I ∘ e) '' t
    _ = e.invFun ∘ (I.invFun ∘ I) ∘ e '' t := by simp only [comp.assoc]
    _ = (e.invFun ∘ e) '' t := by rw [I.leftInverse', left_id]
    _ = t := funext_on (fun ⟨x, hxt⟩ ↦ e.left_inv' (ht hxt))

lemma chart_inverse_point {e : LocalHomeomorph M H} {x : M} (hx: x ∈ e.source) :
    (e.invFun ∘ I.invFun ∘ I ∘ e) x = x := by
  -- xxx: can I golf this?
  simp_all only [LocalEquiv.invFun_as_coe, LocalHomeomorph.coe_coe_symm,
    ModelWithCorners.toLocalEquiv_coe_symm, comp_apply, ModelWithCorners.left_inv, LocalHomeomorph.left_inv]

-- xxx need a better name!
lemma chartFull_isOpenMapOn_source [I.Boundaryless] {e : LocalHomeomorph M H}
    {s : Set M} (hopen : IsOpen s) (hs : s ⊆ e.source) : IsOpen (I ∘ e '' s) := by
  -- As M has no boundary, I is a homeomorphism from H to E, hence an open embedding.
  simp only [image_comp I e]
  apply (I.openEmbedding.open_iff_image_open).mp (e.isOpenMapOn_source hopen hs)

lemma chartFull_image_nhds_on [I.Boundaryless] {e : LocalHomeomorph M H} {x : M} {n : Set M}
    (hn : n ∈ 𝓝 x) (hn₂ : n ⊆ e.source) : I ∘ e '' n ∈ 𝓝 ((I ∘ e) x) := by
  rw [image_comp]
  exact IsOpenMap.image_mem_nhds I.openEmbedding.isOpenMap (e.image_mem_nhds_on hn hn₂)

lemma chartFull_isOpenMapOn_target [I.Boundaryless] {e : LocalHomeomorph M H} {t : Set E}
    (hopen : IsOpen t) (ht : t ⊆ I '' (e.target)) : IsOpen (e.invFun ∘ I.invFun '' t) := by
  have h : IsOpen (I.invFun '' t) := I.openEmbedding_symm.open_iff_image_open.mp hopen
  have : I.invFun '' t ⊆ e.target := by
    calc I.invFun '' t
      _ ⊆ I.invFun '' (I '' (e.target)) := by apply image_subset _ ht
      _ = (I.invFun ∘ I) '' e.target := by rw [image_comp]
      _ = e.target := by rw [I.leftInverse', image_id]
  rw [image_comp]
  exact e.inverse_isOpenMapOn_target h this

lemma localCompactness_aux [FiniteDimensional ℝ E] (hI : ModelWithCorners.Boundaryless I) {x : M} {n : Set M} (hn : n ∈ 𝓝 x) :
    ∃ s : Set M, s∈ 𝓝 x ∧ s ⊆ n ∧ IsCompact s  := by
  -- Assume `n` is contained in some chart at x. (Choose the distinguished chart from our atlas.)
  let chart := ChartedSpace.chartAt (H := H) x
  have hn : n ∩ chart.source ∈ 𝓝 x := by
    apply Filter.inter_mem hn
    rw [mem_nhds_iff]
    exact ⟨chart.source, rfl.subset, chart.open_source, mem_chart_source H x⟩
  -- Apply the chart to obtain a neighbourhood of (I∘e)(x) ∈ E.
  let x' : E := (I ∘ chart) x
  let n' := (I ∘ chart) '' (n ∩ chart.source)
  have hn' : n' ∈ 𝓝 x' := chartFull_image_nhds_on _ hn (inter_subset_right n chart.source)
  -- Since E is locally compact, x' has a compact neighbourhood s' ⊆ n'.
  have h : LocallyCompactSpace E := by infer_instance
  rcases h.local_compact_nhds x' n' hn' with ⟨s', hs', hsn', hscompact⟩
  -- Transport back: s := (I∘e)⁻¹ (s') is a compact neighbourhood of x.
  let s := chart.invFun ∘ I.invFun '' s'
  have hsmall : s' ⊆ I '' chart.target := by calc s'
    _ ⊆ n' := hsn'
    _ = (I ∘ chart) '' (n ∩ chart.source) := rfl
    _ ⊆ (I ∘ chart) '' (chart.source) := image_subset _ (inter_subset_right _ _)
    _ ⊆ I '' (chart '' chart.source) := by rw [image_comp]
    _ ⊆ I '' (chart.target) := image_subset _ chart.map_source_image
  refine ⟨s, ?_, ?_, ?_⟩
  · rcases mem_nhds_iff.mp hs' with ⟨t', ht's', ht'open, hxt'⟩
    rw [mem_nhds_iff]
    refine ⟨(chart.invFun ∘ I.invFun) '' t', image_subset _ ht's', ?_, ?_⟩
    · apply chartFull_isOpenMapOn_target _ ht'open (Subset.trans ht's' hsmall)
    · have : (chart.invFun ∘ I.invFun) x' = x := chart_inverse_point _ (mem_chart_source H x)
      exact this ▸ mem_image_of_mem (chart.invFun ∘ I.invFun) hxt'
  · calc s
      _ ⊆ chart.invFun ∘ I.invFun '' n' := image_subset (chart.invFun ∘ I.invFun) hsn'
      _ = (chart.invFun ∘ I.invFun ∘ I ∘ chart) '' (n ∩ chart.source) := by simp only [image_comp, comp.assoc]
      _ = n ∩ chart.source := chart_inverse _ (inter_subset_right n chart.source)
      _ ⊆ n := inter_subset_left n chart.source
  · apply IsCompact.image_of_continuousOn hscompact
    have : ContinuousOn chart.invFun (I.invFun '' s') := by
      apply chart.continuous_invFun.mono
      calc I.invFun '' s'
        _ ⊆ I.invFun '' (I '' chart.target) := image_subset I.invFun hsmall
        _ = (I.invFun ∘ I) '' chart.target := by rw [image_comp]
        _ = chart.target := by rw [I.leftInverse', image_id]
    apply this.comp I.continuous_invFun.continuousOn (mapsTo_image I.invFun s')

-- TODO: what's the right way to make this an instance?
/-- A finite-dimensional manifold without boundary is locally compact. -/
-- TODO: allow boundary; needs a new argument for the boundary points.
lemma SmoothManifoldWithCorners.locallyCompact_ofFiniteDimensional_boundaryless
    [FiniteDimensional ℝ E] (hI : ModelWithCorners.Boundaryless I) : LocallyCompactSpace M := by
  exact { local_compact_nhds := fun x n hn ↦ localCompactness_aux I hI hn }

-- TODO: add hypotheses, once I figure out the right incantation to add them!
/-- A finite-dimensional second-countable manifold without boundary is σ-compact. -/
instance [SecondCountableTopology M]
  /- [FiniteDimensional ℝ E] (hI : ModelWithCorners.Boundaryless I)-/ : SigmaCompactSpace M := by
  have : LocallyCompactSpace M := by
    sorry -- should be: SmoothManifoldWithCorners.locallyCompact_ofFiniteDimensional_boundaryless I hI
  apply sigmaCompactSpace_of_locally_compact_second_countable
