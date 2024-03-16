import Mathlib.Topology.PartialHomeomorph

open Function TopologicalSpace Set
set_option autoImplicit false

-- Helper results (mostly topological) which I didn't need. Mostly missing from mathlib.
section helpers_obsolete
/-- Let $(U_α)$ be a cover of a topological space X.
A subset $S ⊆ X$ is empty iff all $S ∩ U_α$ are empty. -/
theorem empty_iff_open_cover {X : Type} {I : Type} {U : I → Set X}
    (hcover : ⋃ (α : I), U α = univ) {s : Set X} : s = ∅ ↔ ∀ α : I, s ∩ U α = ∅ := by
  have : ⋃ (α : I), s ∩ U α = s := by rw [←inter_iUnion, hcover, inter_univ s]
  nth_rewrite 1 [← this]
  simp only [iUnion_eq_empty]

-- this lemma is in mathlib, in PartialHomeomorph
-- theorem preimage_interior (s : Set β) :
--     e.source ∩ e ⁻¹' interior s = e.source ∩ interior (e ⁻¹' s) :=
--   (IsImage.of_preimage_eq rfl).interior.preimage_eq

-- this counterpart for image is currently missing
lemma image_interior {α β : Type} [TopologicalSpace α] [TopologicalSpace β]
    (e : PartialHomeomorph α β) (s : Set α) :
    e.target ∩ e '' interior s = e '' (e.source ∩ interior s) := by
  -- idea: restrict the local homeo to the appropriate part; then it's a homeo
  -- have more proof ideas on paper
  sorry

-- I only care about empty interior: homeomorphism version, not in mathlib.
lemma homeo_preserves_empty_interior {α β : Type} [TopologicalSpace α] [TopologicalSpace β]
    (f : Homeomorph α β) (s : Set α) (h₂s : interior s = ∅) : interior (f '' s) = ∅ := by
  rw [← Homeomorph.image_interior, h₂s]
  exact Set.image_empty ↑f

-- and the version for local homeomorphisms
lemma local_homeo_preserves_empty_interior {α β : Type}
    [TopologicalSpace α] [TopologicalSpace β] {f : PartialHomeomorph α β} {s : Set α}
    (hs : s ⊆ f.source) (h₂s : interior s = ∅) : interior (f '' s) = ∅ := by
  -- xxx clean up these partial steps
  -- restrict to domain and target: mathematically trivial
  have h₁ : s = s ∩ f.source := by
    rw [← @inter_eq_left α s f.source] at hs
    symm
    exact hs
  have h₂ : interior s = interior (s ∩ f.source) := by
    sorry -- how hard to deduce this?? just redo the proof of h₁?
  rw [h₁] at h₂s
  have h₃ : f '' (interior s ∩ f.source) = ∅ := by sorry
  sorry

-- /-- Let $(U_α)$ be an open cover of a topological space X.
-- A subset $S ⊆ X$ has empty interior iff all $S∩U_α$ have empty interior. -/
-- XXX I think this should be in mathlib... haven't checked very closely.
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
    simp only [Set.iUnion_eq_empty]
    tauto
end helpers_obsolete
