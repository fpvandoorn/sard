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
  [SmoothManifoldWithCorners I M] [FiniteDimensional ℝ E]
  [SecondCountableTopology M]

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
    (e.invFun ∘ I.invFun) ∘ (I ∘ e) '' t = t := by
  have : e.invFun ∘ e '' t = t := funext_on (fun ⟨x, hxt⟩ ↦ e.left_inv' (ht hxt))
  calc (e.invFun ∘ I.invFun) ∘ (I ∘ e) '' t
    _ = e.invFun ∘ (I.invFun ∘ I) ∘ e '' t := by simp only [comp.assoc]
    _ = e.invFun '' ((I.invFun ∘ I) '' (e '' t)) := by simp only [image_comp]
    _ = e.invFun ∘ e '' t := by rw [I.leftInverse', image_id, image_comp]
    _ = t := by rw [this]

-- I'm sure this exists somewhere!!
lemma chart_inverse_point {e : LocalHomeomorph M H} {x : M} (hx: x ∈ e.source) :
    (e.invFun ∘ I.invFun ∘ I ∘ e) x = x := by sorry -- apply chart_inverse at e.source and specialise

lemma chart_isOpenMapOn_source {e : LocalHomeomorph M H} {s : Set M}
  (hs : IsOpen s) (hs : s ⊆ e.source) : IsOpen (e '' s) := sorry

lemma chartInverse_isOpenMapOn_target {e : LocalHomeomorph M H} {t : Set H}
  (ht : IsOpen t) (ht : t ⊆ e.target) : IsOpen (e.invFun '' t) := sorry

