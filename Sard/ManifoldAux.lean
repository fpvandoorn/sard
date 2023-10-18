import Mathlib.Geometry.Manifold.MFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Additional lemmas about smooth manifolds
-/

open Function Manifold Set SmoothManifoldWithCorners TopologicalSpace Topology
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

lemma LocalHomeomorph.symm_isOpenMapOn_target {e : LocalHomeomorph M H} {t : Set H}
    (hopen : IsOpen t) (ht : t ⊆ e.target) : IsOpen (e.invFun '' t) := by
  have r : e.invFun '' t = e.source ∩ ↑e ⁻¹' t := symm_image_eq_source_inter_preimage (e := e) ht
  rw [r]
  exact e.continuous_toFun.preimage_open_of_open e.open_source hopen
end LocalHomeomorph

section ModelsWithCorners -- add to `SmoothManifoldWithCorners.lean`
theorem ModelWithCorners.leftInverse' : I.invFun ∘ I = id := funext I.leftInverse

/-- If I is boundaryless, it is an open embedding. -/
theorem ModelWithCorners.toOpenEmbedding [I.Boundaryless] : OpenEmbedding I :=
  I.toHomeomorph.openEmbedding

theorem ModelWithCorners.toOpenEmbedding_symm [I.Boundaryless] : OpenEmbedding I.symm :=
  I.toHomeomorph.symm.openEmbedding
end ModelsWithCorners

lemma extendedChart_leftInverse [I.Boundaryless] {e : LocalHomeomorph M H}
    {x : E} (hx: x ∈ I ∘ e '' e.source) : (I ∘ e ∘ e.invFun ∘ I.invFun) x = x := by
  have : I.invFun x ∈ e.target := by aesop
  have aux : ∀ y : H, y ∈ e.target → (e ∘ e.invFun) y = y := by -- XXX: nicer proof?
    intro y hy
    simp_all only [comp_apply, mem_image, LocalEquiv.invFun_as_coe,
      ModelWithCorners.toLocalEquiv_coe_symm, LocalHomeomorph.coe_coe_symm, LocalHomeomorph.right_inv]
  have aux2 : ∀ x : E, (I ∘ I.invFun) x = x := by -- extract into separate lemma?
    intro x
    refine ModelWithCorners.right_inv I ?hx
    rw [I.range_eq_univ]
    exact trivial
  calc (I ∘ e ∘ e.invFun ∘ I.invFun) x
    _ = I ((e ∘ e.invFun) (I.invFun x)) := rfl
    _ = I (I.invFun x) := by simp_rw [aux (I.invFun x) this]
    _ = (I ∘ I.invFun) x := rfl
    _ = x := aux2 x

-- might be useful for completeness; proof skipped; the above contains all necessary ingredients
lemma unused_extendedChart_leftInverse' {e : LocalHomeomorph M H} {t : Set E} (ht: t ⊆ (I ∘ e) '' e.source) :
    (I ∘ e ∘ e.invFun ∘ I.invFun) '' t = t := by sorry

/-- If `I ∘ e` is an extended chart, `(I ∘ e).symm` is a left inverse to `I ∘ e` on `e.source`. -/
lemma extendedChart_symm_leftInverse {e : LocalHomeomorph M H} {x : M} (hx: x ∈ e.source) :
    (e.invFun ∘ I.invFun ∘ I ∘ e) x = x := by
  -- what's the best proof? I know two options!
  -- have : e.invFun ∘ I.invFun ∘ I ∘ e = e.invFun ∘ e := by calc
  --   e.invFun ∘ I.invFun ∘ I ∘ e = e.invFun ∘ (I.invFun ∘ I) ∘ e := by simp only [comp.assoc]
  --     _ = e.invFun ∘ e := by rw [I.leftInverse', left_id]
  -- rw [this]
  -- exact LocalHomeomorph.left_inv e hx
  simp_all only [LocalEquiv.invFun_as_coe, LocalHomeomorph.coe_coe_symm,
    ModelWithCorners.toLocalEquiv_coe_symm, comp_apply, ModelWithCorners.left_inv,
    LocalHomeomorph.left_inv]

-- XXX: can this be golfed?
/-- If `I ∘ e` is an extended chart, `(I ∘ e).symm` is a left inverse to `I ∘ e`:
  stated for subsets of `e.source`. -/
lemma extendedChart_symm_leftInverse' {t : Set M} {e : LocalHomeomorph M H} (ht: t ⊆ e.source) :
    (e.invFun ∘ I.invFun ∘ I ∘ e) '' t = t := by
  calc (e.invFun ∘ I.invFun ∘ I ∘ e) '' t
    _ = e.invFun ∘ (I.invFun ∘ I) ∘ e '' t := by simp only [comp.assoc]
    _ = (e.invFun ∘ e) '' t := by rw [I.leftInverse', left_id]
    _ = t := funext_on (fun ⟨x, hxt⟩ ↦ e.left_inv' (ht hxt))

lemma extendedChart_LeftInvOn (e : LocalHomeomorph M H) :
    LeftInvOn (e.invFun ∘ I.invFun) (I ∘ e) e.source :=
  fun _ hx ↦ extendedChart_symm_leftInverse I hx

lemma extendedChart_RightInvOn [I.Boundaryless] (e : LocalHomeomorph M H) :
    RightInvOn (e.invFun ∘ I.invFun) (I ∘ e) (I ∘ e '' e.source) :=
  fun _ hx ↦ extendedChart_leftInverse I hx

lemma extendedChart_isOpenMapOn_source [I.Boundaryless] {e : LocalHomeomorph M H}
    {s : Set M} (hopen : IsOpen s) (hs : s ⊆ e.source) : IsOpen (I ∘ e '' s) := by
  -- As M has no boundary, I is a homeomorphism from H to E, hence an open embedding.
  simp only [image_comp I e]
  apply (I.toOpenEmbedding.open_iff_image_open).mp (e.isOpenMapOn_source hopen hs)

lemma extendedChart_image_nhds_on [I.Boundaryless] {e : LocalHomeomorph M H} {x : M} {n : Set M}
    (hn : n ∈ 𝓝 x) (hn₂ : n ⊆ e.source) : I ∘ e '' n ∈ 𝓝 ((I ∘ e) x) := by
  rw [image_comp]
  exact IsOpenMap.image_mem_nhds I.toOpenEmbedding.isOpenMap (e.image_mem_nhds_on hn hn₂)

lemma extendedChart_symm_isOpenMapOn_target [I.Boundaryless] {e : LocalHomeomorph M H} {t : Set E}
    (hopen : IsOpen t) (ht : t ⊆ I '' (e.target)) : IsOpen (e.invFun ∘ I.invFun '' t) := by
  have h : IsOpen (I.invFun '' t) := I.toOpenEmbedding_symm.open_iff_image_open.mp hopen
  have : I.invFun '' t ⊆ e.target := by
    calc I.invFun '' t
      _ ⊆ I.invFun '' (I '' (e.target)) := by apply image_subset _ ht
      _ = (I.invFun ∘ I) '' e.target := by rw [image_comp]
      _ = e.target := by rw [I.leftInverse', image_id]
  rw [image_comp]
  exact e.symm_isOpenMapOn_target h this

/-- Auxiliary lemma for local compactness of `M`. -/
lemma localCompactness_aux [FiniteDimensional ℝ E] (hI : ModelWithCorners.Boundaryless I)
    {x : M} {n : Set M} (hn : n ∈ 𝓝 x) : ∃ s : Set M, s∈ 𝓝 x ∧ s ⊆ n ∧ IsCompact s  := by
  -- Assume `n` is contained in some chart at x. (Choose the distinguished chart from our atlas.)
  let chart := ChartedSpace.chartAt (H := H) x
  have hn : n ∩ chart.source ∈ 𝓝 x := by
    apply Filter.inter_mem hn
    rw [mem_nhds_iff]
    exact ⟨chart.source, rfl.subset, chart.open_source, mem_chart_source H x⟩
  -- Apply the chart to obtain a neighbourhood of (I∘e)(x) ∈ E.
  let x' : E := (I ∘ chart) x
  let n' := (I ∘ chart) '' (n ∩ chart.source)
  have hn' : n' ∈ 𝓝 x' := extendedChart_image_nhds_on _ hn (inter_subset_right n chart.source)
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
    · apply extendedChart_symm_isOpenMapOn_target _ ht'open (Subset.trans ht's' hsmall)
    · have : (chart.invFun ∘ I.invFun) x' = x := extendedChart_symm_leftInverse _ (mem_chart_source H x)
      exact this ▸ mem_image_of_mem (chart.invFun ∘ I.invFun) hxt'
  · calc s
      _ ⊆ chart.invFun ∘ I.invFun '' n' := image_subset (chart.invFun ∘ I.invFun) hsn'
      _ = (chart.invFun ∘ I.invFun ∘ I ∘ chart) '' (n ∩ chart.source) := by
        simp only [image_comp, comp.assoc]
      _ = n ∩ chart.source := extendedChart_symm_leftInverse' _ (inter_subset_right n chart.source)
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
lemma SmoothManifoldWithCorners.locallyCompact_of_finiteDimensional_of_boundaryless
    [FiniteDimensional ℝ E] (hI : ModelWithCorners.Boundaryless I) : LocallyCompactSpace M := by
  exact { local_compact_nhds := fun x n hn ↦ localCompactness_aux I hI hn }

-- TODO: add hypotheses, once I figure out the right incantation to add them!
/-- A finite-dimensional second-countable manifold without boundary is σ-compact. -/
instance [SecondCountableTopology M]
  /- [SmoothManifoldWithCorners I M] and all the other things -/
  /- [FiniteDimensional ℝ E] (hI : ModelWithCorners.Boundaryless I)-/ : SigmaCompactSpace M := by
  have : LocallyCompactSpace M := by
    sorry -- should be: SmoothManifoldWithCorners.locallyCompact_of_finiteDimensional_of_boundaryless I hI
  apply sigmaCompactSpace_of_locally_compact_second_countable

section ChartsLocalDiffeos
-- Let `N` be a smooth manifold over the pair `(F, G)`.
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  (J : ModelWithCorners ℝ F G) {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [SmoothManifoldWithCorners J N]

-- similar to `fderivWithin_of_open`; seems missing
lemma hasFDerivWithinAt_of_open {s : Set E} {x : E} (h : IsOpen s) (hx : x ∈ s) {f : E → F} {f' : E →L[ℝ] F}:
    HasFDerivWithinAt f f' s x ↔ HasFDerivAt f f' x := by
  simp only [HasFDerivAt, HasFDerivWithinAt]
  rw [IsOpen.nhdsWithin_eq h hx]

-- I have not compared FDeriv.Basic to MFDeriv and added all analogous lemmas.
-- analogous to `fderivWithin_of_mem_nhds`
theorem mfderivWithin_of_mem_nhds {f : M → N} {s : Set M} {x : M} (h : s ∈ 𝓝 x) :
    mfderivWithin I J f s x = mfderiv I J f x := by
  rw [← mfderivWithin_univ, ← univ_inter s, mfderivWithin_inter h]

-- similar to `fderivWith_of_open`
lemma mfderivWithin_of_open {s : Set M} {x : M} (hs : IsOpen s) (hx : x ∈ s) {f : M → N} :
    mfderivWithin I J f s x = mfderiv I J f x :=
  mfderivWithin_of_mem_nhds I J (hs.mem_nhds hx)

-- analogous to `mfderivWithin_eq_mfderiv`
theorem mfderivWithin_eq_mfderiv {s : Set M} {x : M} {f : M → N}
    (hs : UniqueMDiffWithinAt I s x) (h : MDifferentiableAt I J f x) :
    mfderivWithin I J f s x = mfderiv I J f x := by
  rw [← mfderivWithin_univ]
  exact mfderivWithin_subset (subset_univ _) hs h.mdifferentiableWithinAt

-----------------------------------------------

lemma bijective_iff_inverses {X Y : Type*} {f : X → Y} {g : Y → X} (h1 : g ∘ f = id) (h2 : f ∘ g = id) :
    Bijective f :=
  ⟨LeftInverse.injective (congrFun h1), LeftInverse.surjective (congrFun h2)⟩

-- FIXME: surely this can be golfed?
lemma bijective_iff_inverses' {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X →L[ℝ] Y} {g : Y →L[ℝ] X}
    (h1 : g.comp f = ContinuousLinearMap.id ℝ X) (h2 : f.comp g = ContinuousLinearMap.id ℝ Y) : Bijective f := by
  have h : f.toFun ∘ g.toFun = id := calc f.toFun ∘ g.toFun
    _ = (f.comp g).toFun := rfl
    _ = (ContinuousLinearMap.id ℝ Y).toFun := by rw [h2]
    _ = id := rfl
  have : g.toFun ∘ f.toFun = id := by calc g.toFun ∘ f.toFun
    _ = (g.comp f).toFun := rfl
    _ = (ContinuousLinearMap.id ℝ X).toFun := by rw [h1]
    _ = id := rfl
  exact bijective_iff_inverses this h

-- These are needed to apply `bijective_iff_inverses` to differentials:
-- whose are defined an tangent spaces (which are not normed spaces per se).
-- XXX: is there a nicer solution than abusing definitional equality like this?
instance {x : E} : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstanceAs (NormedAddCommGroup E)
instance {x : E} : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstanceAs (NormedSpace ℝ E)
instance {x : M} : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
instance {x : M} : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)

-- TODO: define notion of "linear isomorphism" and add corresponding variants of
-- all the lemmas below!

-- xxx: define local diffeos; diffeos on an open set and refactor conditions accordingly
lemma diffeoOn_differential_bijective {f : M → N} {g : N → M} {r : ℕ} (hr : 1 ≤ r)
    -- morally, s and t are the source and target of my local diffeo
    {s : Set M} (hs : IsOpen s) {t : Set N} (ht : IsOpen t) {x : M} (hx : x ∈ s)
    (hst : MapsTo f s t) (hts : MapsTo g t s)
    (hleft_inv : ∀ x ∈ s, g (f x) = x) (hright_inv : ∀ y ∈ t, f (g y) = y)
    (hf : ContMDiffOn I J r f s) (hg : ContMDiffOn J I r g t) :
    Bijective (mfderiv I J f x) := by
  set A := mfderiv I J f x
  -- Initial observations about x, s and t.
  let y := f x
  have hyx : g y = x := hleft_inv x hx
  have hysource : y ∈ t := hst hx
  have : f '' s = t := subset_antisymm (mapsTo'.mp hst) (fun y hy ↦ ⟨g y, hts hy, hright_inv y hy⟩)
  have : g '' t = s := by
    rw [← this, ← image_comp]
    exact funext_on (fun ⟨x, hx⟩ ↦ hleft_inv x hx)
  have hopen : IsOpen (g '' t) := by rw [this]; exact hs
  have hx2 : x ∈ g '' t := by simp_rw [this]; exact hx

  let A' := mfderiv J I g y
  have hr : 1 ≤ (r : ℕ∞) := Nat.one_le_cast.mpr (Nat.one_le_of_lt hr)
  have hgat : MDifferentiableAt J I g y :=
    (hg.contMDiffAt (ht.mem_nhds (hst hx))).mdifferentiableAt hr
  have hfat : MDifferentiableAt I J f x :=
    (hf.contMDiffAt (hs.mem_nhds hx)).mdifferentiableAt hr
  have inv1 := calc A'.comp A
    _ = mfderiv I I (g ∘ f) x := (mfderiv_comp x hgat hfat).symm
    _ = mfderivWithin I I (g ∘ f) (g '' t) x := (mfderivWithin_of_open I I hopen hx2).symm
    _ = mfderivWithin I I id (g '' t) x :=
      mfderivWithin_congr (hopen.uniqueMDiffWithinAt hx2) (this ▸ hleft_inv) (hleft_inv x (this ▸ hx2))
    _ = mfderiv I I id x := mfderivWithin_of_open I I hopen hx2
    _ = ContinuousLinearMap.id ℝ (TangentSpace I x) := mfderiv_id I
  have inv2 := calc A.comp A'
    _ = mfderiv J J (f ∘ g) y := by
          -- Use the chain rule: rewrite the base point (I ∘ e ∘ e.invFun ∘ I.invFun) x = x, ...
          rw [← (hleft_inv x hx)] at hfat
          -- ... but also the points x and y under the map.
          exact (hyx ▸ (mfderiv_comp (f x) hfat hgat)).symm
    _ = mfderivWithin J J (f ∘ g) t y := (mfderivWithin_of_open J J ht hysource).symm
    _ = mfderivWithin J J id t y :=
          mfderivWithin_congr (ht.uniqueMDiffWithinAt hysource) hright_inv (hright_inv y hysource)
    _ = mfderiv J J id y := mfderivWithin_of_open J J ht hysource
    _ = ContinuousLinearMap.id ℝ (TangentSpace J (f x)) := mfderiv_id J
  exact bijective_iff_inverses' inv1 inv2

/-- A diffeomorphism has bijective differential at each point. -/
lemma diffeo_differential_bijective {r : ℕ} (hr : 1 ≤ r) (f : Diffeomorph I J M N r) {x : M} :
    Bijective (mfderiv I J f x) := by
  refine diffeoOn_differential_bijective I J hr isOpen_univ isOpen_univ trivial (mapsTo_univ f.toFun univ) (mapsTo_univ f.invFun univ) ?_ ?_ ?_ ?_
  · exact fun _ hx ↦ f.toLocalEquiv.left_inv' hx
  · exact fun _ hy ↦ f.toLocalEquiv.right_inv' hy
  · exact contMDiffOn_univ.mpr f.contMDiff_toFun
  · exact contMDiffOn_univ.mpr f.contMDiff_invFun

/-- An extended chart $I ∘ e : M → E$ on a smooth manifold is smooth on `e.source`. -/
-- TODO: can I generalise this to `Structomorph`?
-- TODO: does this hold for manifolds with boundary?
lemma extendedChart_smooth {e : LocalHomeomorph M H} (he : e ∈ atlas H M) [I.Boundaryless] :
    ContMDiffOn I 𝓘(ℝ, E) ∞ (I ∘ e) e.source := by
  let e' : LocalHomeomorph E E := LocalHomeomorph.refl E
  have h₁ : e ∈ maximalAtlas I M := subset_maximalAtlas _ he
  have h₂ : e' ∈ maximalAtlas 𝓘(ℝ, E) E := subset_maximalAtlas _ (by rfl)
  -- Looking closely, we want to show smoothness of f.
  set f := I ∘ e ∘ e.invFun ∘ I.invFun
  -- Since f=id on I ∘ e '' e.source, we're done.
  have h : ∀ x ∈ I ∘ e '' e.source, f x = x := fun _ hx ↦ extendedChart_leftInverse I hx
  apply (contMDiffOn_iff_of_mem_maximalAtlas' h₁ h₂ (Eq.subset rfl) (mapsTo_univ _ _)).mpr
  exact ContMDiffOn.contDiffOn (fun x hx ↦ ContMDiffWithinAt.congr smoothWithinAt_id h (h x hx))

/-- The inverse $e.invFun ∘ I.invFun : E → M$ of an extended chart $I ∘ e : M → E$
on a smooth manifold without boundary is smooth on `I ∘ e '' e.source`. -/
-- TODO: deduce this from a more general result about these being `Structomorph`
-- FIXME: does this hold for manifolds with boundary?
lemma extendedChart_symm_smooth {e : LocalHomeomorph M H} (he : e ∈ atlas H M) [I.Boundaryless] :
    ContMDiffOn 𝓘(ℝ, E) I ∞ (e.invFun ∘ I.invFun) (I ∘ e '' e.source) := by
  have : IsOpen (I ∘ e '' e.source) := extendedChart_isOpenMapOn_source I e.open_source (Eq.subset rfl)
  let e' : LocalHomeomorph E E := LocalHomeomorph.ofSet (I ∘ e '' e.source) this
  have h1 : e ∈ maximalAtlas I M := subset_maximalAtlas _ he
  have h2 : e' ∈ maximalAtlas 𝓘(ℝ, E) E := by -- XXX: extract into separate lemma!
    set gr := (contDiffGroupoid ∞ I)
    rw [maximalAtlas, mem_maximalAtlas_iff]
    intro e' he'
    rw [he']
    simp only [comp_apply, LocalHomeomorph.ofSet_symm, LocalHomeomorph.trans_refl,
      LocalHomeomorph.refl_symm, LocalHomeomorph.refl_trans, and_self]
    apply ofSet_mem_contDiffGroupoid
  -- XXX: this occurs twice -> extract?
  have h3 : MapsTo (e.invFun ∘ I.invFun) (I ∘ e '' e.source) e.source := by
    rintro x ⟨s, hs, hsx⟩
    have : (e.invFun ∘ I.invFun) ((↑I ∘ ↑e) s) = s := extendedChart_symm_leftInverse _ hs
    rw [← hsx, this]
    exact hs
  apply (contMDiffOn_iff_of_mem_maximalAtlas' h2 h1 (Eq.subset rfl) h3).mpr

  apply ContMDiffOn.contDiffOn
  -- We want to show smoothness of this function: locally, that's just the identity.
  set f := (I ∘ e) ∘ (e.invFun ∘ I.invFun) ∘ (LocalEquiv.symm (LocalHomeomorph.extend e' 𝓘(ℝ, E)))
  have cong : ∀ x ∈ I ∘ e '' e.source, f x = x := by
    intro x hx
    calc f x
      _ = ((I ∘ e) ∘ (e.invFun ∘ I.invFun)) (LocalEquiv.symm (LocalHomeomorph.extend e' 𝓘(ℝ, E)) x) := rfl
      _ = ((I ∘ e) ∘ (e.invFun ∘ I.invFun)) x := rfl
      _ = (I ∘ e ∘ e.invFun ∘ I.invFun) x := rfl
      _ = x := extendedChart_leftInverse I hx
  -- Hence, we're done (modulo some rewriting to make this obvious to Lean).
  have : e'.source = I ∘ e '' e.source := rfl
  rw [this]
  have h : (LocalHomeomorph.extend e' 𝓘(ℝ, E)) '' e'.source = I ∘ e '' e.source := by simp
  have : ((LocalHomeomorph.extend e' 𝓘(ℝ, E)) '' (↑I ∘ ↑e '' e.source)) = I ∘ e '' e.source := by
    rw [← this]
    exact h
  rw [this]
  exact fun x hx ↦ ContMDiffWithinAt.congr smoothWithinAt_id cong (cong x (h ▸ hx))

/-- The differential of each inverse extended chart, regarded as a smooth map,
  is bijective at each point in its source. -/
lemma extendedChart_symm_differential_bijective [SmoothManifoldWithCorners I M] [I.Boundaryless]
    {e : LocalHomeomorph M H} (he : e ∈ atlas H M) {x : E} (hx : x ∈ I ∘ e '' e.source):
    Bijective (mfderiv 𝓘(ℝ, E) I (e.invFun ∘ I.invFun) x) := by
  refine diffeoOn_differential_bijective 𝓘(ℝ, E) I (Eq.le rfl) ?_ e.open_source hx ?_ (mapsTo_image (I ∘ e) e.source) ?_ ?_ ?_ ?_
  · exact extendedChart_isOpenMapOn_source I e.open_source (Eq.subset rfl)
  · rintro x ⟨s, hs, hsx⟩
    have : (e.invFun ∘ I.invFun) ((↑I ∘ ↑e) s) = s := extendedChart_symm_leftInverse _ hs
    rw [← hsx, this]
    exact hs
  · exact fun x hx ↦ extendedChart_leftInverse _ hx
  · exact fun x hx ↦ extendedChart_symm_leftInverse _ hx
  · exact SmoothOn.contMDiffOn (extendedChart_symm_smooth I he)
  · exact SmoothOn.contMDiffOn (extendedChart_smooth I he)

/-- The differential of each extended chart, regarded as a smooth map,
  is bijective at each point in its source. -/
lemma extendedChart_differential_bijective [SmoothManifoldWithCorners I M] [I.Boundaryless]
    {e : LocalHomeomorph M H} (he : e ∈ atlas H M) {x : M} (hx : x ∈ e.source):
    Bijective (mfderiv I 𝓘(ℝ, E) (I ∘ e) x) := by
  have diff : ContMDiffOn 𝓘(ℝ, E) I 1 (e.invFun ∘ I.invFun) (I ∘ e '' e.source) :=
    SmoothOn.contMDiffOn (extendedChart_symm_smooth I he)
  refine diffeoOn_differential_bijective I 𝓘(ℝ, E) (Eq.le rfl) e.open_source ?_ hx (mapsTo_image (I ∘ e) e.source) ?_ ?_ ?_ ?_ diff
  · exact extendedChart_isOpenMapOn_source I e.open_source (Eq.subset rfl)
  · rintro x ⟨s, hs, hsx⟩
    have : (e.invFun ∘ I.invFun) ((↑I ∘ ↑e) s) = s := extendedChart_symm_leftInverse _ hs
    rw [← hsx, this]
    exact hs
  · exact fun x hx ↦ extendedChart_symm_leftInverse I hx
  · exact fun x hx ↦ extendedChart_leftInverse _ hx
  · exact SmoothOn.contMDiffOn (extendedChart_smooth I he)
end ChartsLocalDiffeos
