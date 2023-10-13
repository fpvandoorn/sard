import Mathlib.Geometry.Manifold.MFDeriv

/-!
# Additional lemmas about smooth manifolds
-/

open ENNReal NNReal FiniteDimensional Function Manifold Set TopologicalSpace Topology LocallyLipschitz
set_option autoImplicit false

variable
  -- Let `M` be a smooth manifold over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]

-- add to SmoothManifoldWithCorners.lean
theorem ModelWithCorners.leftInverse' : I.invFun ∘ I = id := funext I.leftInverse

/-- If I is boundaryless, it is an open embedding. -/
-- add to SmoothManifoldWithCorners.lean
-- XXX. there should be a shorter proof, using I.toHomeomorph
theorem ModelWithCorners.openEmbedding [I.Boundaryless] : OpenEmbedding I := by
  have h : IsOpen (range I) := by rw [I.range_eq_univ] ; exact isOpen_univ
  have : Embedding I := LeftInverse.embedding I.leftInverse I.continuous_invFun I.continuous_toFun
  exact { toEmbedding := this, open_range := h }

/-- Analogous to the funext tactic, but only on a set. -/
-- move to Data.Set.Image
theorem funext_on {α β : Type*} {f : α → β} {g : β → α} {s : Set α} (h : ∀ x : s, (g ∘ f) x = x)
    : g ∘ f '' s = s := by
  simp_all only [comp_apply, Subtype.forall, image_id']

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

lemma chart_isOpenMapOn_source {e : LocalHomeomorph M H} {s : Set M}
    (hopen : IsOpen s) (hs : s ⊆ e.source) : IsOpen (e '' s) := by
  have h : e '' s = e.invFun ⁻¹' s :=
    image_eq_preimage_of_inverseOn (LeftInvOn.mono (fun x ↦ e.left_inv) hs)
  rw [h]
  refine e.continuous_invFun.isOpen_preimage e.open_target ?_ hopen
  have : e '' e.source ⊆ e.target := by sorry -- this is essentially map_source'; omitted
  calc e.invFun ⁻¹' s
    _ = e '' s := by rw [← h]
    _ ⊆ e '' (e.source) := image_subset _ hs
    _ ⊆ e.target := this

lemma chartInverse_isOpenMapOn_target {e : LocalHomeomorph M H} {t : Set H}
  (hopen : IsOpen t) (ht : t ⊆ e.target) : IsOpen (e.invFun '' t) := sorry

-- xxx need a better name!
lemma chartFull_isOpenMapOn_source [I.Boundaryless] {e : LocalHomeomorph M H}
    {s : Set M} (hopen : IsOpen s) (hs : s ⊆ e.source) : IsOpen (I ∘ e '' s) := by
  -- As M has no boundary, I is a homeomorphism from H to E, hence an open embedding.
  simp only [image_comp I e]
  apply (I.openEmbedding.open_iff_image_open).mp (chart_isOpenMapOn_source hopen hs)

lemma localCompactness_aux [FiniteDimensional ℝ E] (hI : ModelWithCorners.Boundaryless I) {x : M} {n : Set M} (hn : n ∈ 𝓝 x) :
    ∃ s : Set M, s∈ 𝓝 x ∧ s ⊆ n ∧ IsCompact s  := by
  -- Assume `n` is contained in some chart at x. (Choose the distinguished chart from our atlas.)
  let chart := ChartedSpace.chartAt (H := H) x
  have hn : n ∩ chart.source ∈ 𝓝 x := by -- FIXME: this should be known/extract to lemma!
    rcases mem_nhds_iff.mp hn with ⟨t, htn, htopen, hxt⟩
    rw [mem_nhds_iff]
    exact ⟨t ∩ chart.source, inter_subset_inter_left chart.source htn,
          htopen.inter chart.open_source, mem_inter hxt (mem_chart_source H x)⟩
  -- Apply the chart to obtain a neighbourhood of (I∘e)(x) ∈ E.
  let x' : E := (I ∘ chart) x
  let n' : Set E := (I ∘ chart) '' (n ∩ chart.source)
  have hn' : n' ∈ 𝓝 x' := by
    -- Not fully true: need a version on an open subset.
    have scifi : IsOpenMap chart := sorry
    exact IsOpenMap.image_mem_nhds (I.openEmbedding.isOpenMap.comp scifi) hn
  -- Since E is locally compact, x' has a compact neighbourhood s' ⊆ n'.
  have h : LocallyCompactSpace E := by infer_instance
  rcases h.local_compact_nhds x' n' hn' with ⟨s', hs', hsn', hscompact⟩
  -- Transport back: s := (I∘e)⁻¹ (s') is a compact neighbourhood of x.
  let s := chart.invFun ∘ I.invFun '' s'

  have : s' ⊆ (I ∘ chart) '' chart.source :=
        calc s'
          _ ⊆ n' := hsn'
          _ = (I ∘ chart) '' (n ∩ chart.source) := rfl
          _ ⊆ (I ∘ chart) '' (chart.source) :=
            image_subset (↑I ∘ ↑chart) (inter_subset_right n chart.source)
  have hs'small : I.invFun '' s' ⊆ chart.target := calc I.invFun '' s'
          _ ⊆ I.invFun '' n' := image_subset I.invFun hsn'
          _ = I.invFun '' ((I ∘ chart) '' (n ∩ chart.source)) := rfl
          _ = (I.invFun ∘ I ∘ chart) '' (n ∩ chart.source) := by rw [← image_comp]
          _ = chart '' (n ∩ chart.source) := by rw [← comp.assoc, ModelWithCorners.leftInverse', left_id]
          _ ⊆ chart.target := sorry -- TODO: shrink n to make this true!!
  refine ⟨s, ?_, ?_, ?_⟩
  · rcases mem_nhds_iff.mp hs' with ⟨t', ht's', ht'open, hxt'⟩
    rw [mem_nhds_iff]
    refine ⟨(chart.invFun ∘ I.invFun) '' t', image_subset _ ht's', ?_, ?_⟩
    · let t := I.invFun '' t'
      have : IsOpen (I.invFun '' t') := by
        have : I.invFun '' t' = I ⁻¹' t' := by sorry -- use I.leftInverse; details skipped
        rw [this]
        exact ht'open.preimage I.continuous
      rw [image_comp]
      apply chartInverse_isOpenMapOn_target this
      calc t
        _ = I.invFun '' t' := rfl
        _ ⊆ I.invFun '' s' := image_subset (I.invFun) ht's'
        _ ⊆ chart.target := hs'small
    · have : (chart.invFun ∘ I.invFun) x' = x := chart_inverse_point _ (mem_chart_source H x)
      exact this ▸ mem_image_of_mem (chart.invFun ∘ I.invFun) hxt'
  · calc s
      _ ⊆ chart.invFun ∘ I.invFun '' n' := image_subset (chart.invFun ∘ I.invFun) hsn'
      _ = (chart.invFun ∘ I.invFun ∘ I ∘ chart) '' (n ∩ chart.source) := by simp only [image_comp, comp.assoc]
      _ = n ∩ chart.source := chart_inverse _ (inter_subset_right n chart.source)
      _ ⊆ n := inter_subset_left n chart.source
  · apply IsCompact.image_of_continuousOn hscompact
    have : ContinuousOn chart.invFun (I.invFun '' s') :=
          chart.continuous_invFun.mono hs'small
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
