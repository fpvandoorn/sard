import Sard.ToSubset
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Separation
import Mathlib.Topology.SubsetProperties
/-!
We define σ-compact subsets of a topological space, show their elementary properties
and relate them to σ-compact spaces.
-/
-- probably, this also should go into `Mathlib.Topology.SubsetPropertes`
-- TODO: finish proving that σ-compact sets are spaces are related
-- TODO: finish proving that σ-compact spaces are closed under countable unions
--   (and transfer this to σ-compact spaces)
-- FIXME: are these proofs easier in terms of that reduction? didn't feel like it,
--   at least there was missing API in terms of relating properties to the subspace

open Set
set_option autoImplicit false
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The preimage of a compact set under an inducing map is a compact set. -/
-- Direct PR to mathlib; this removes the injectivity hypothesis from ClosedEmbedding.isCompact_preimage.
theorem Inducing.isCompact_preimage {f : X → Y} (hf : Inducing f) (hf' : IsClosed (range f)) {K : Set Y}
    (hK : IsCompact K) : IsCompact (f ⁻¹' K) := by
  replace hK := hK.inter_right hf'
  rwa [← hf.isCompact_iff, image_preimage_eq_inter_range]

/-- A subset `A ⊆ X` is called **σ-compact** iff it is the union of countably many compact sets. --/
def IsSigmaCompact (A : Set X) : Prop :=
  ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = A

/-- A topological space is σ-compact iff `univ` is σ-compact. --/
lemma isSigmaCompact_univ_iff : IsSigmaCompact (univ : Set X) ↔ SigmaCompactSpace X :=
  ⟨fun h ↦ { exists_compact_covering := h }, fun _ ↦ SigmaCompactSpace.exists_compact_covering⟩

lemma isSigmaCompact_univ [h : SigmaCompactSpace X] : IsSigmaCompact (univ : Set X) :=
  isSigmaCompact_univ_iff.mpr h

lemma toSubset_iUnion {X : Type*} {t : Set X} (S : ℕ → Set X) : toSubset (⋃ n, S n) t = ⋃ n, toSubset (S n) t := by
  ext
  rw [mem_toSubset]
  sorry

/-- If `s ⊆ X` is a compact set and `s ⊆ t`, then `s` is also compact in `t` (with the subspace topology). -/
lemma toSubset_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s t : Set X} (hsw : s ⊆ t) (hs : IsCompact s) : IsCompact (toSubset s t) := by
  -- Let U_i be an open cover of s, in t.
  -- By definition, each U_i is of the form U_i = t ∩ V_i for some V_i ⊆ X open.
  -- Since s is compact in X, it has a finite subcover V_i1, ..., V_in.
  -- But now, s = s ∩ t ⊆ (⋃ V_i1) ∩ t = ⋃ (V_ij ∩ t) = ⋃ U_ij, done.
  sorry
-- non-proof: `s ⊆ t` is the preimage of `s` under the inclusion `t → X`
-- this works *if* `t` is closed (so the inclusion is a closed embedding), but fails in general:
-- for instance, the open unit disc in ℝ² is not compact, but it is the preimage of its closure.

lemma toSubset_sigmaCompact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s w : Set X} (hsw : s ⊆ w) (hs : IsSigmaCompact s) : IsSigmaCompact (toSubset s w) := by
  -- Choose a covering by compact sets. Each is compact on w also, done.
  rcases hs with ⟨K, hcomp, hcov⟩
  have : ∀ n, K n ⊆ w := by
    intro n
    apply Subset.trans _ hsw
    rw [← hcov]
    exact subset_iUnion K n
  exact ⟨fun n ↦ toSubset (K n) w, fun n ↦ toSubset_compact (this n) (Y := Y) (hcomp n), by rw [← toSubset_iUnion, hcov]⟩

-- lemma toSubset_univ {X : Type*} : (toSubset univ univ) = (univ : Set X) := sorry

/-- If `s` is σ-compact and `f` continuous on a set `w` containing `s`, `f(s)` is σ-compact.-/
lemma IsSigmaCompact.image_of_continuousOn {f : X → Y} {s : Set X} (hs : IsSigmaCompact s)
    (hf : ContinuousOn f s) : IsSigmaCompact (f '' s) := by
  rcases hs with ⟨K, hcompact, hcov⟩
  have : ∀ n, IsCompact (f '' (K n)) := by
    intro n
    have : K n ⊆ s := by calc K n
      _ ⊆ ⋃ n, K n := subset_iUnion K n
      _ = s := by rw [hcov]
    exact (hcompact n).image_of_continuousOn (hf.mono this)
  exact ⟨fun n ↦ f '' K n, fun n ↦ this n, (by rw [← hcov]; exact image_iUnion.symm)⟩

/-- If `s` is σ-compact and `f` continuous, `f(s)` is σ-compact. -/
lemma IsSigmaCompact.image {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsSigmaCompact s) :
    IsSigmaCompact (f '' s) := hs.image_of_continuousOn hf.continuousOn

/-- If `X` is σ-compact, `im f` is σ-compact. -/
lemma isSigmaCompact_range {f : X → Y} (hf : Continuous f) [i : SigmaCompactSpace X] :
    IsSigmaCompact (range f) := by
  rw [← image_univ]
  apply IsSigmaCompact.image hf isSigmaCompact_univ

/-- If `f : X → Y` is an `Embedding`, the image `f '' s` of a set `s` is σ-compact
if and only `s`` is σ-compact. -/
-- this proof of <= requires injectivity to conclude s = f ⁻¹' (f '' s)
lemma Embedding.isSigmaCompact_iff_isSigmaCompact_image {f : X → Y} {s : Set X} (hf : Embedding f) :
    IsSigmaCompact s ↔ IsSigmaCompact (f '' s) := by
  constructor
  · intro h
    apply h.image (continuous hf)
  · -- suppose f '' s is σ-compact; we want to show f is σ-compact
    -- a nicer proof: as an embedding, f is a homeomorphism to its image
    -- hence f '' s being σ-compact implies s is
    intro h
    have : IsSigmaCompact (toSubset (f '' s) (f '' s)) :=
      toSubset_sigmaCompact (Eq.subset rfl) h (Y := f '' s)
    have : SigmaCompactSpace (f '' s) := by
      sorry -- apply isSigmaCompact_univ_iff.mp this -- almost there, toSubset univ univ vs univ
    sorry
    #exit
    have : X ≃ₜ range f := by apply Homeomorph.ofEmbedding hf (f := f)
    let g := this.invFun
    have : ↑(g ⁻¹' s) = f '' s := sorry
    -- now, f '' s being σ-compact implies it is σ-compact in the subspace ?!
    -- then, g of that is σ-compact, so we're good
    -- have : s = g '' (ToSubset(f '' s)) := sorry-- have : s ≃ f '' s := by
    --   let g := s.restrict f
    --   have : f '' s = range g := sorry
    --   rw [this]
    --   have : Embedding g := sorry
    --   sorry
      --apply Homeomorph.ofEmbedding this
    sorry
    #exit

    -- xxx: which of this is in mathlib? seems all the building blocks are; can't find the details
    -- consider the inverse (involves choice?) f⁻¹; is well-def'd because injective
    -- as f is inducing, f⁻¹ is continuous -- that should be easy. ask on zulip first!
    rintro ⟨K, hcompact, hcov⟩
    use (fun n ↦ f ⁻¹' (K n))
    constructor
    · intro n
      let S := f ⁻¹' K n
      let f' := S.restrict f
      have : ClosedEmbedding f' := sorry
      have : IsCompact (f' ⁻¹' K n) := ClosedEmbedding.isCompact_preimage this (K := K n) (hcompact n)
      have h : (f' ⁻¹' K n) = toSubset (f ⁻¹' K n) S := sorry
      have : IsClosed S := by -- if Y is T2, this holds. most likely, this is not needed!
        sorry
        -- have hcont : ContinuousOn f univ := Iff.mp continuous_iff_continuousOn_univ (continuous hf)
        -- let h := ContinuousOn.preimage_closed_of_closed hcont isClosed_univ (IsCompact.isClosed (hcompact n))
        -- rw [univ_inter] at h
        -- exact h
      sorry
    · have : f ⁻¹' (f '' s) = s := by apply preimage_image_eq s hf.inj
      rw [← preimage_iUnion, hcov, this]

lemma isSigmaCompact_iff_isSigmaCompact_in_subtype {p : X → Prop} {s : Set { a // p a }} :
    IsSigmaCompact s ↔ IsSigmaCompact (((↑) : _ → X) '' s) :=
  embedding_subtype_val.isSigmaCompact_iff_isSigmaCompact_image

/-- A subset `s` is σ-compact iff `s` (with the subspace topology) is a σ-compact space. -/
lemma isSigmaCompact_iff_isSigmaCompact_univ {s : Set X} :
    IsSigmaCompact s ↔ IsSigmaCompact (univ : Set s) := by
  rw [isSigmaCompact_iff_isSigmaCompact_in_subtype, image_univ, Subtype.range_coe]

lemma isSigmaCompact_iff_sigmaCompactSpace {s : Set X} :
    IsSigmaCompact s ↔ SigmaCompactSpace s :=
  isSigmaCompact_iff_isSigmaCompact_univ.trans isSigmaCompact_univ_iff

/-- The empty set is σ-compact. -/
@[simp]
lemma isSigmaCompact_empty : IsSigmaCompact (∅ : Set X) := by
  use fun _ ↦ ∅
  simp only [isCompact_empty, forall_const, iUnion_empty, and_self]

/-- Compact sets are σ-compact. -/
lemma isSigmaCompact_of_compact {s : Set X} (hs : IsCompact s) : IsSigmaCompact s := by
  -- proof 1: show by hand
  -- exact ⟨fun _ => s, fun _ => hs, iUnion_const _⟩
  -- proof 2: reduce to subspaces. not sure if that's nicer
  rw [isSigmaCompact_iff_sigmaCompactSpace]
  exact (isCompact_iff_compactSpace.mp hs).sigma_compact

/-- Countable unions of compact sets are σ-compact. -/
lemma isSigmaCompact_of_countable_compact (S : Set (Set X)) (hc : Set.Countable S)
    (hcomp : ∀ (s : Set X), s ∈ S → IsCompact s) : IsSigmaCompact (⋃₀ S) := by
  by_cases S = ∅
  · simp only [h, sUnion_empty, isSigmaCompact_empty]
  · -- Choose a surjection f : ℕ → S, this yields a map ℕ → Set X.
    obtain ⟨f, hf⟩ := (Set.countable_iff_exists_surjective (nmem_singleton_empty.mp h)).mp hc
    use fun n ↦ f n
    constructor
    · exact fun n ↦ hcomp (f n) (Subtype.mem (f n))
    · apply Subset.antisymm
      · -- Suppose x ∈ ⋃ n, f n. Then x ∈ f i for some i.
        intro _ hx
        rw [mem_iUnion] at hx
        rcases hx with ⟨i, hi⟩
        -- But f i is a set in S, so x ∈ ⋃ S as well.
        exact ⟨f i, Subtype.mem (f i), hi⟩
      · -- Suppose x ∈ ⋃ s, then x ∈ s for some s ∈ S.
        intro x hx
        rw [mem_sUnion] at hx
        rcases hx with ⟨s, h, hxs⟩
        -- Choose n with f n = s (using surjectitivity of ).
        have : ∀ s : ↑S, ∃ n : ℕ, f n = s := hf
        -- x has type X, but hs says x ∈ S -> how can I cast x to S?
        -- let sdf := this s -- type mismatch! s has type X, should have type s...
        -- let _ := this h
        have : ∃ n, f n = s := by sorry --exact?
        -- simp [hf] is also nice, but doesn't solve this
        rcases this with ⟨n, hn⟩
        exact ⟨f n, mem_range_self n, (by rw [hn]; exact hxs)⟩

/-- Countable unions of σ-compact sets are σ-compact. -/
lemma isSigmaCompact_of_countable_sigma_compact (S : Set (Set X)) (hc : Countable S) (hcomp : ∀ (s : Set X), s ∈ S → IsSigmaCompact s) :
  IsSigmaCompact (⋃₀ S) := by sorry -- TODO: renumbering the sequences, how?

-- A closed subset of a σ-compact set is σ-compact.
lemma IsSigmaCompact.of_isClosed_subset {s t : Set X} (ht : IsSigmaCompact t)
    (hs : IsClosed s) (h : s ⊆ t) : IsSigmaCompact s := by
  rcases ht with ⟨K, hcompact, hcov⟩
  use (fun n ↦ s ∩ (K n))
  constructor
  · exact fun n ↦ (hcompact n).inter_left hs
  · rw [← inter_iUnion, hcov]
    exact inter_eq_left_iff_subset.mpr h
