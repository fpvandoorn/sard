import Mathlib.Data.Set.Functor
import Mathlib.Topology.Compactness.Compact
-- Coercion of sets and subsets.
-- Solutions taken from zulip: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Cast.20to.20a.20subset.2C.20given.20proof.20of.20inclusion

set_option autoImplicit false

namespace Set
variable {X : Type*} (s t : Set X)

-- first variant uses a proof of inclusion: is not as nice to work with
/-- If two subsets `s` and `t` satisfy `s ⊆ t` and `h` is a proof of this inclusion,
`toSubset' s t h` is the set `s` as a subset of `t`. -/
def toSubset' (h : s ≤ t) : Set t := Set.range (Set.inclusion h)

@[simp]
lemma mem_toSubset' (h : s ≤ t)
    (x : t) : x ∈ toSubset' s t h ↔ ↑x ∈ s := by
  rw [toSubset', Set.range_inclusion, Set.mem_setOf_eq]

/-- Given sets `s t : Set X`, `Set.toSubset s t` is `s ∩ t` realized as a term of `Set t`. -/
def toSubset : Set t := (Subtype.val · ∈ s)

@[simp]
lemma mem_toSubset (x : t) : x ∈ toSubset s t ↔ ↑x ∈ s := Iff.rfl

@[simp]
lemma coe_toSubset : (s.toSubset t : Set X) = s ∩ t := by
  ext
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨_, ⟨⟨_, h.2⟩, rfl⟩, by simpa using ⟨h.1, rfl⟩⟩⟩
  · obtain ⟨-, ⟨a, rfl⟩, ha⟩ := h
    simp only [mem_toSubset, pure_def, mem_iUnion, mem_singleton_iff, exists_prop] at ha
    obtain ⟨ha, rfl⟩ := ha
    exact ⟨ha, a.property⟩
end Set

open Set
-- unused, but seems like missing API
lemma toSubset_aux1 {X Y : Type*} (f : X → Y) {s w : Set X} (hsw : s ⊆ w) :
    f '' (s ∩ w) = (w.restrict f) '' (toSubset s w) := sorry

-- unused, but seems like missing API
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

-- commented to prevent cycles
-- lemma toSubset_sigmaCompact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
--     {s w : Set X} (hsw : s ⊆ w) (hs : IsSigmaCompact s) : IsSigmaCompact (toSubset s w) := by
--   -- Choose a covering by compact sets. Each is compact on w also, done.
--   rcases hs with ⟨K, hcomp, hcov⟩
--   have : ∀ n, K n ⊆ w := by
--     intro n
--     apply Subset.trans _ hsw
--     rw [← hcov]
--     exact subset_iUnion K n
--   exact ⟨fun n ↦ toSubset (K n) w, fun n ↦ toSubset_compact (this n) (Y := Y) (hcomp n), by rw [← toSubset_iUnion, hcov]⟩
