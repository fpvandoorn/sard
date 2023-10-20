import Sard.ManifoldLocallyCompact
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Additional lemmas about smooth manifolds
-/

open Function Manifold Set SmoothManifoldWithCorners TopologicalSpace Topology
set_option autoImplicit false

variable
  -- Let `M` be a smooth manifold over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]

-- might be useful for completeness; proof skipped; the above contains all necessary ingredients
lemma unused_extendedChart_leftInverse' {e : LocalHomeomorph M H} {t : Set E} (ht: t ⊆ (I ∘ e) '' e.source) :
    (I ∘ e ∘ e.invFun ∘ I.invFun) '' t = t := by sorry

-- FIXME: remove, in favour of using mathlib lemmas
lemma extendedChart_image_nhds_on [I.Boundaryless] {e : LocalHomeomorph M H} {x : M} {n : Set M}
    (hn : n ∈ 𝓝 x) (hn₂ : n ⊆ e.source) : I ∘ e '' n ∈ 𝓝 ((I ∘ e) x) := by
  rw [image_comp]
  exact IsOpenMap.image_mem_nhds I.toOpenEmbedding.isOpenMap (e.image_mem_nhds_on hn hn₂)

lemma extendedChart_LeftInvOn (e : LocalHomeomorph M H) :
    LeftInvOn (e.invFun ∘ I.invFun) (I ∘ e) e.source :=
  fun _ hx ↦ e.extend_symm_leftInverse I hx

lemma LocalHomeomorph.extend_leftInverse [I.Boundaryless] {e : LocalHomeomorph M H}
    {x : E} (hx: x ∈ (e.extend I) '' e.source) : ((e.extend I) ∘ (e.extend I).symm) x = x := by
  have : I.invFun x ∈ e.target := by aesop
  have aux : ∀ y : H, y ∈ e.target → (e ∘ e.invFun) y = y := by intros; aesop
  have aux2 : ∀ x : E, (I ∘ I.invFun) x = x := by -- extract into separate lemma?
    intro x
    refine I.right_inv ?hx
    rw [I.range_eq_univ]
    exact trivial
  calc (I ∘ e ∘ e.invFun ∘ I.invFun) x
    _ = I ((e ∘ e.invFun) (I.invFun x)) := rfl
    _ = I (I.invFun x) := by simp_rw [aux (I.invFun x) this]
    _ = (I ∘ I.invFun) x := rfl
    _ = x := aux2 x

lemma extendedChart_RightInvOn [I.Boundaryless] (e : LocalHomeomorph M H) :
    RightInvOn (e.invFun ∘ I.invFun) (I ∘ e) (I ∘ e '' e.source) :=
  fun _ hx ↦ e.extend_leftInverse I hx

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

-- `contMDiffOn_of_mem_maximalAtlas` shows this for `e`!
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
  have h : ∀ x ∈ I ∘ e '' e.source, f x = x := fun _ hx ↦ e.extend_leftInverse I hx
  apply (contMDiffOn_iff_of_mem_maximalAtlas' h₁ h₂ (Eq.subset rfl) (mapsTo_univ _ _)).mpr
  exact ContMDiffOn.contDiffOn (fun x hx ↦ ContMDiffWithinAt.congr smoothWithinAt_id h (h x hx))

-- belongs in `SmoothManifoldWithCorners.lean`
/-- An identity local homeomorphism belongs to the maximal atlas on `E`. -/
lemma ofSet_in_maximal_atlas {s : Set E} (hs : IsOpen s) :
    LocalHomeomorph.ofSet s hs ∈ maximalAtlas 𝓘(ℝ, E) E := by
  set e := LocalHomeomorph.ofSet s hs
  set gr := (contDiffGroupoid ∞ I)
  rw [maximalAtlas, mem_maximalAtlas_iff]
  intro e' he'
  rw [he']
  simp only [comp_apply, LocalHomeomorph.ofSet_symm, LocalHomeomorph.trans_refl,
    LocalHomeomorph.refl_symm, LocalHomeomorph.refl_trans, and_self]
  apply ofSet_mem_contDiffGroupoid

/-- The inverse $e.invFun ∘ I.invFun : E → M$ of an extended chart $I ∘ e : M → E$
on a smooth manifold without boundary is smooth on `I ∘ e '' e.source`. -/
-- TODO: deduce this from a more general result about these being `Structomorph`
-- FIXME: does this hold for manifolds with boundary?
lemma extendedChart_symm_smooth {e : LocalHomeomorph M H} (he : e ∈ atlas H M) [I.Boundaryless] :
    ContMDiffOn 𝓘(ℝ, E) I ∞ (e.invFun ∘ I.invFun) (I ∘ e '' e.source) := by
  have : IsOpen (I ∘ e '' e.source) := e.extend_isOpenMapOn_source I e.open_source (Eq.subset rfl)
  let e' : LocalHomeomorph E E := LocalHomeomorph.ofSet (I ∘ e '' e.source) this
  have h1 : e ∈ maximalAtlas I M := subset_maximalAtlas _ he
  have h2 : e' ∈ maximalAtlas 𝓘(ℝ, E) E := ofSet_in_maximal_atlas I this
  -- XXX: this occurs twice -> extract?
  have h3 : MapsTo (e.invFun ∘ I.invFun) (I ∘ e '' e.source) e.source := by
    rintro x ⟨s, hs, rfl⟩
    have : (e.invFun ∘ I.invFun) ((↑I ∘ ↑e) s) = s := e.extend_symm_leftInverse _ hs
    rw [this]
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
      _ = x := e.extend_leftInverse I hx
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
  · exact e.extend_isOpenMapOn_source I e.open_source (Eq.subset rfl)
  · rintro x ⟨s, hs, rfl⟩
    have : (e.invFun ∘ I.invFun) ((↑I ∘ ↑e) s) = s := e.extend_symm_leftInverse _ hs
    rw [this]
    exact hs
  · exact fun x hx ↦ e.extend_leftInverse _ hx
  · exact fun x hx ↦ e.extend_symm_leftInverse _ hx
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
  · exact e.extend_isOpenMapOn_source I e.open_source (Eq.subset rfl)
  · rintro x ⟨s, hs, rfl⟩
    have : (e.invFun ∘ I.invFun) ((↑I ∘ ↑e) s) = s := e.extend_symm_leftInverse _ hs
    rw [this]
    exact hs
  · exact fun x hx ↦ e.extend_symm_leftInverse I hx
  · exact fun x hx ↦ e.extend_leftInverse _ hx
  · exact SmoothOn.contMDiffOn (extendedChart_smooth I he)
end ChartsLocalDiffeos
