import Mathlib.Geometry.Manifold.Diffeomorph
/-!
# Additional lemmas about smooth manifolds
-/

open Function Manifold Set SmoothManifoldWithCorners TopologicalSpace Topology
set_option autoImplicit false

section new
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
  -- declare a smooth manifold `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M']
  -- declare functions, sets, points and smoothness indices
  {e : PartialHomeomorph M H} {x : M} {m n : ℕ∞}

theorem contMDiffOn_extend (he : e ∈ maximalAtlas I M) : ContMDiffOn I 𝓘(𝕜, E) n (e.extend I) e.source :=
  fun _x' hx' => (contMDiffAt_extend he hx').contMDiffWithinAt
end new

variable
  -- Let `M` be a smooth manifold over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]

section LocalHomeo -- add to `PartialHomeomorph.lean`
lemma PartialHomeomorph.isOpenMapOn_source {e : PartialHomeomorph M H} {s : Set M}
    (hopen : IsOpen s) (hs : s ⊆ e.source) : IsOpen (e '' s) := by
  rw [(image_eq_target_inter_inv_preimage (e := e) hs)]
  exact e.continuousOn_invFun.isOpen_inter_preimage e.open_target hopen

lemma PartialHomeomorph.symm_isOpenMapOn_target {e : PartialHomeomorph M H} {t : Set H}
    (hopen : IsOpen t) (ht : t ⊆ e.target) : IsOpen (e.invFun '' t) := by
  have r : e.invFun '' t = e.source ∩ ↑e ⁻¹' t := symm_image_eq_source_inter_preimage (e := e) ht
  exact r ▸ e.continuousOn_toFun.isOpen_inter_preimage e.open_source hopen
end LocalHomeo

section ModelsWithCorners -- add to `SmoothManifoldWithCorners.lean`

/-- If `I` is boundaryless, it is an open embedding. -/
theorem ModelWithCorners.toOpenEmbedding [I.Boundaryless] : OpenEmbedding I :=
  I.toHomeomorph.openEmbedding

/-- If `I` is boundaryless, `I.symm` is an open embedding. -/
theorem ModelWithCorners.toOpenEmbedding_symm [I.Boundaryless] : OpenEmbedding I.symm :=
  I.toHomeomorph.symm.openEmbedding

/-- If I has no boundary, `e.extend I` is an open map on its source. -/
lemma PartialHomeomorph.extend_isOpenMapOn_source [I.Boundaryless] {e : PartialHomeomorph M H}
    {s : Set M} (hopen : IsOpen s) (hs : s ⊆ e.source) : IsOpen ((e.extend I) '' s) := by
  simp only [extend_coe, image_comp I e]
  -- As I has no boundary, it is a homeomorphism, hence an open embedding.
  apply (I.toOpenEmbedding.open_iff_image_open).mp (e.isOpenMapOn_source hopen hs)

/-- If I has no boundary, `(e.extend I).symm` is an open map on its source. -/
lemma PartialHomeomorph.extend_symm_isOpenMapOn_target [I.Boundaryless] {e : PartialHomeomorph M H}
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
lemma PartialHomeomorph.extend_image_mem_nhds_symm [I.Boundaryless] {e : PartialHomeomorph M H}
    {x : E} {n : Set E} (hn : n ∈ 𝓝 x) (hn' : n ⊆ (e.extend I).target) :
    (e.extend I).symm '' n ∈ 𝓝 ((e.extend I).symm x) := by
  -- XXX: there ought to be a slicker proof, using that I and e map nhds to nhds
  rcases mem_nhds_iff.mp hn with ⟨t', ht's', ht'open, hxt'⟩
  rw [mem_nhds_iff]
  refine ⟨(e.extend I).symm '' t', image_subset _ ht's', ?_, ?_⟩
  · apply e.extend_symm_isOpenMapOn_target _ ht'open (Subset.trans ht's' hn')
  · exact mem_image_of_mem (e.extend I).symm hxt'

end ModelsWithCorners

-- might be useful for completeness; proof skipped; the above contains all necessary ingredients
lemma unused_extendedChart_leftInverse' {e : PartialHomeomorph M H} {t : Set E} (ht: t ⊆ e.extend I '' e.source) :
    e.extend I ∘ (e.extend I).symm '' t = t := by sorry

-- FIXME: remove, in favour of using mathlib lemmas
lemma extendedChart_image_nhds_on [I.Boundaryless] {e : PartialHomeomorph M H} {x : M} {n : Set M}
    (hn : n ∈ 𝓝 x) (hn₂ : n ⊆ e.source) : I ∘ e '' n ∈ 𝓝 (e.extend I x) := by
  rw [image_comp]
  apply I.toOpenEmbedding.isOpenMap.image_mem_nhds (e.image_mem_nhds (hn₂ (mem_of_mem_nhds hn)) hn)

lemma PartialHomeomorph.mapsTo_extend_symm {e : PartialHomeomorph M H} :
    MapsTo (e.extend I).symm (e.extend I '' e.source) e.source := by
  rintro x ⟨s, hs, rfl⟩
  have : (e.extend I).symm (e.extend I s) = s := e.extend_left_inv _ hs
  rw [this]
  exact hs

lemma PartialHomeomorph.extend_LeftInvOn (e : PartialHomeomorph M H) :
    LeftInvOn (e.extend I).symm (e.extend I) e.source :=
  fun _ hx ↦ e.extend_left_inv I hx

lemma ModelWithCorners.right_inv'' [I.Boundaryless] (x : E) : (I ∘ I.invFun) x = x := by
  have : x ∈ range I := by rw [I.range_eq_univ]; exact trivial
  exact I.right_inv this

lemma PartialHomeomorph.extend_right_inv [I.Boundaryless] {e : PartialHomeomorph M H}
    {x : E} (hx: x ∈ (e.extend I) '' e.source) : ((e.extend I) ∘ (e.extend I).symm) x = x := by
  have : I.invFun x ∈ e.target := by aesop
  have aux : ∀ y : H, y ∈ e.target → (e ∘ e.invFun) y = y := by intros; aesop
  calc ((e.extend I) ∘ (e.extend I).symm) x
    _ = I ((e ∘ e.invFun) (I.invFun x)) := rfl
    _ = I (I.invFun x) := by simp_rw [aux (I.invFun x) this]
    _ = x := I.right_inv'' x

lemma PartialHomeomorph.extend_RightInvOn [I.Boundaryless] (e : PartialHomeomorph M H) :
    RightInvOn (e.extend I).symm (e.extend I) (e.extend I '' e.source) :=
  fun _ hx ↦ e.extend_right_inv I hx

section ChartsLocalDiffeos
-- Let `N` be a smooth manifold over the pair `(F, G)`.
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  (J : ModelWithCorners ℝ F G) {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [SmoothManifoldWithCorners J N]

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
-- FIXME: is there a nicer solution than abusing definitional equality like this?
instance {x : E} : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstanceAs (NormedAddCommGroup E)
instance {x : E} : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstanceAs (NormedSpace ℝ E)
instance {x : M} : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
instance {x : M} : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)

-- TODO: upgrade the lemmas below to ContinuousLinearEquiv!
-- TODO: define local diffeos; diffeos on an open set and refactor conditions accordingly
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
    exact EqOn.image_eq_self hleft_inv
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
    _ = mfderivWithin I I (g ∘ f) (g '' t) x := (mfderivWithin_of_isOpen hopen hx2).symm
    _ = mfderivWithin I I id (g '' t) x :=
      mfderivWithin_congr (hopen.uniqueMDiffWithinAt hx2) (this ▸ hleft_inv) (hleft_inv x (this ▸ hx2))
    _ = mfderiv I I id x := mfderivWithin_of_isOpen hopen hx2
    _ = ContinuousLinearMap.id ℝ (TangentSpace I x) := mfderiv_id I
  have inv2 := calc A.comp A'
    _ = mfderiv J J (f ∘ g) y := by
          -- Use the chain rule: rewrite the base point (I ∘ e ∘ e.invFun ∘ I.invFun) x = x, ...
          rw [← (hleft_inv x hx)] at hfat
          -- ... but also the points x and y under the map.
          exact (hyx ▸ (mfderiv_comp (f x) hfat hgat)).symm
    _ = mfderivWithin J J (f ∘ g) t y := (mfderivWithin_of_isOpen ht hysource).symm
    _ = mfderivWithin J J id t y :=
          mfderivWithin_congr (ht.uniqueMDiffWithinAt hysource) hright_inv (hright_inv y hysource)
    _ = mfderiv J J id y := mfderivWithin_of_isOpen ht hysource
    _ = ContinuousLinearMap.id ℝ (TangentSpace J (f x)) := mfderiv_id J
  exact bijective_iff_inverses' inv1 inv2

/-- A diffeomorphism has bijective differential at each point. -/
lemma diffeo_differential_bijective {r : ℕ} (hr : 1 ≤ r) (f : Diffeomorph I J M N r) {x : M} :
    Bijective (mfderiv I J f x) := by
  refine diffeoOn_differential_bijective I J hr isOpen_univ isOpen_univ trivial (mapsTo_univ f.toFun univ) (mapsTo_univ f.invFun univ) ?_ ?_ ?_ ?_
  · exact fun _ hx ↦ f.toPartialEquiv.left_inv' hx
  · exact fun _ hy ↦ f.toPartialEquiv.right_inv' hy
  · exact contMDiffOn_univ.mpr f.contMDiff_toFun
  · exact contMDiffOn_univ.mpr f.contMDiff_invFun

-- `contMDiffOn_of_mem_maximalAtlas` shows this for `e`!
/-- An extended chart $e.extend I : M → E$ on a smooth manifold is smooth on `e.source`. -/
-- TODO: can I generalise this to `Structomorph`?
-- TODO: does this hold for manifolds with boundary?
lemma extendedChart_smooth {e : PartialHomeomorph M H} (he : e ∈ atlas H M) [I.Boundaryless] :
    ContMDiffOn I 𝓘(ℝ, E) ∞ (e.extend I) e.source := by
  let e' : PartialHomeomorph E E := PartialHomeomorph.refl E
  have h₁ : e ∈ maximalAtlas I M := subset_maximalAtlas _ he
  have h₂ : e' ∈ maximalAtlas 𝓘(ℝ, E) E := subset_maximalAtlas _ (by rfl)
  -- Looking closely, we want to show smoothness of f.
  set f := e.extend I ∘ (e.extend I).symm
  -- Since f=id on e.extend I '' e.source, we're done.
  have h : ∀ x ∈ (e.extend I) '' e.source, f x = x := fun _ hx ↦ e.extend_right_inv I hx
  apply (contMDiffOn_iff_of_mem_maximalAtlas' h₁ h₂ (Eq.subset rfl) (mapsTo_univ _ _)).mpr
  exact ContMDiffOn.contDiffOn (fun x hx ↦ ContMDiffWithinAt.congr smoothWithinAt_id h (h x hx))

-- belongs in `SmoothManifoldWithCorners.lean`
/-- An identity local homeomorphism belongs to the maximal atlas on `E`. -/
lemma ofSet_in_maximal_atlas {s : Set E} (hs : IsOpen s) :
    PartialHomeomorph.ofSet s hs ∈ maximalAtlas 𝓘(ℝ, E) E := by
  rw [maximalAtlas, mem_maximalAtlas_iff]
  intro e' he'
  rw [he']
  simp only [mfld_simps]
  apply ofSet_mem_contDiffGroupoid

/-- The inverse of an extended chart `e.extend I : M → E` on a smooth manifold without boundary
  is smooth on its source. -/
-- TODO: deduce this from a more general result about these being `Structomorph`
-- FIXME: does this hold for manifolds with boundary?
lemma extendedChart_symm_smooth {e : PartialHomeomorph M H} (he : e ∈ atlas H M) [I.Boundaryless] :
    ContMDiffOn 𝓘(ℝ, E) I ∞ (e.extend I).symm (e.extend I '' e.source) := by
  have : IsOpen ((e.extend I) '' e.source) := e.extend_isOpenMapOn_source I e.open_source (Eq.subset rfl)
  let e' : PartialHomeomorph E E := PartialHomeomorph.ofSet (e.extend I '' e.source) this
  have h1 : e ∈ maximalAtlas I M := subset_maximalAtlas _ he
  have h2 : e' ∈ maximalAtlas 𝓘(ℝ, E) E := ofSet_in_maximal_atlas this
  apply (contMDiffOn_iff_of_mem_maximalAtlas' h2 h1 (Eq.subset rfl) (e.mapsTo_extend_symm I)).mpr

  apply ContMDiffOn.contDiffOn
  -- We want to show smoothness of this function: locally, that's just the identity.
  set f := e.extend I ∘ (e.extend I).symm ∘ (PartialEquiv.symm (PartialHomeomorph.extend e' 𝓘(ℝ, E)))
  have cong : ∀ x ∈ e.extend I '' e.source, f x = x := fun x hx ↦ e.extend_right_inv I hx
  have h : (e'.extend 𝓘(ℝ, E)) '' e'.source = e.extend I '' e.source := by
    simp only [e', mfld_simps, image_id']
  have : ((e'.extend 𝓘(ℝ, E)) '' (e.extend I '' e.source)) = e.extend I '' e.source := by
    have : e'.source = e.extend I '' e.source := by rw [PartialHomeomorph.ofSet_source]
    exact this ▸ h
  rw [PartialHomeomorph.ofSet_source, this]
  exact fun x hx ↦ ContMDiffWithinAt.congr smoothWithinAt_id cong (cong x (h ▸ hx))

/-- The differential of each inverse extended chart, regarded as a smooth map,
  is bijective at each point in its source. -/
lemma extendedChart_symm_differential_bijective [SmoothManifoldWithCorners I M] [I.Boundaryless]
    {e : PartialHomeomorph M H} (he : e ∈ atlas H M) {x : E} (hx : x ∈ e.extend I '' e.source):
    Bijective (mfderiv 𝓘(ℝ, E) I (e.extend I).symm x) := by
  refine diffeoOn_differential_bijective 𝓘(ℝ, E) I (Eq.le rfl) ?_ e.open_source hx ?_ (mapsTo_image (e.extend I) e.source) ?_ ?_ ?_ ?_
  · exact e.extend_isOpenMapOn_source I e.open_source (Eq.subset rfl)
  · rintro x ⟨s, hs, rfl⟩
    have : (e.extend I).symm (e.extend I s) = s := e.extend_left_inv _ hs
    rw [this]
    exact hs
  · exact fun x hx ↦ e.extend_right_inv _ hx
  · exact fun x hx ↦ e.extend_left_inv _ hx
  · exact SmoothOn.contMDiffOn (extendedChart_symm_smooth I he)
  · exact SmoothOn.contMDiffOn (extendedChart_smooth I he)

/-- The differential of each extended chart, regarded as a smooth map,
  is bijective at each point in its source. -/
lemma extendedChart_differential_bijective [SmoothManifoldWithCorners I M] [I.Boundaryless]
    {e : PartialHomeomorph M H} (he : e ∈ atlas H M) {x : M} (hx : x ∈ e.source):
    Bijective (mfderiv I 𝓘(ℝ, E) (e.extend I) x) := by
  have diff : ContMDiffOn 𝓘(ℝ, E) I 1 (e.extend I).symm (e.extend I '' e.source) :=
    SmoothOn.contMDiffOn (extendedChart_symm_smooth I he)
  refine diffeoOn_differential_bijective I 𝓘(ℝ, E) (Eq.le rfl) e.open_source ?_ hx (mapsTo_image (e.extend I) e.source) ?_ ?_ ?_ ?_ diff
  · exact e.extend_isOpenMapOn_source I e.open_source (Eq.subset rfl)
  · rintro x ⟨s, hs, rfl⟩
    have : (e.extend I).symm (e.extend I s) = s := e.extend_left_inv _ hs
    rw [this]
    exact hs
  · exact fun x hx ↦ e.extend_left_inv I hx
  · exact fun x hx ↦ e.extend_right_inv _ hx
  · exact SmoothOn.contMDiffOn (extendedChart_smooth I he)
end ChartsLocalDiffeos
