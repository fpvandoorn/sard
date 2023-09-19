import Mathlib.Data.Set.Functor
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