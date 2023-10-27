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

open Function Set Topology
set_option autoImplicit false

variable
  -- Let `M` be a manifold over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [HasGroupoid M (contDiffGroupoid 0 I)]

section LocalHomeo -- add to `LocalHomeomorph.lean`
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

/-- If `I` is boundaryless, it is an open embedding. -/
theorem ModelWithCorners.toOpenEmbedding [I.Boundaryless] : OpenEmbedding I :=
  I.toHomeomorph.openEmbedding

/-- If `I` is boundaryless, `I.symm` is an open embedding. -/
theorem ModelWithCorners.toOpenEmbedding_symm [I.Boundaryless] : OpenEmbedding I.symm :=
  I.toHomeomorph.symm.openEmbedding

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
