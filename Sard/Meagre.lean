/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.GDelta

set_option autoImplicit false

section MeasureZero
/-! ## Meagre sets and measure zero
In general, neither of meagre and measure zero implies the other.
- for all $α ∈ (0,1)$, there is a generalised Cantor set $C ⊆ [0,1]$ of measure `α`.
Cantor sets are nowhere dense. (Taking a countable union of fat Cantor sets whose measure approaches 1,
we obtain a meagre set of measure 1.)
- ℚ ⊆ ℝ has measure zero, but is dense (in particular, not meagre).

However, a **closed** measure zero set is nowhere dense.
-/
open Function TopologicalSpace Set MeasureTheory Measure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsOpenPosMeasure μ]

lemma open_measure_zero_implies_empty {s : Set X} (hs : IsOpen s) (hs' : μ s = 0) : s = ∅ :=
  (IsOpen.measure_eq_zero_iff μ hs).mp hs'

/-- A measure zero subset has empty interior. -/
lemma empty_interior_of_null {s : Set X} (hs : μ s = 0) : interior s = ∅ :=
  open_measure_zero_implies_empty isOpen_interior (measure_mono_null interior_subset hs)

/-- A *closed* measure zero subset is nowhere dense.
(Closedness is required: there are generalised Cantor sets of positive Lebesgue measure.) -/
lemma nowhere_dense_of_closed_null {s : Set X} (h₁s : IsClosed s) (h₂s : μ s = 0) :
    IsNowhereDense s := h₁s.isNowhereDense_iff.mpr (empty_interior_of_null h₂s)

/-- A compact measure zero set is nowhere dense. -/
-- FIXME: is this lemma useful to have?
lemma nowhere_dense_of_compact_null [T2Space X] {s : Set X} (h₁s : IsCompact s) (h₂s : μ s = 0) :
    IsNowhereDense s := nowhere_dense_of_closed_null h₁s.isClosed h₂s

/-- A σ-compact measure zero subset is meagre. -/
lemma meagre_of_sigma_compact_null [T2Space X] {s : Set X} (h₁s : IsSigmaCompact s) (h₂s : μ s = 0) :
    IsMeagre s := by
  rcases h₁s with ⟨K, hcompact, hcover⟩
  have h : ∀ (n : ℕ), IsNowhereDense (K n) := by
    intro n
    have : μ (K n) = 0 := measure_mono_null (hcover ▸ subset_iUnion K n) h₂s
    exact nowhere_dense_of_compact_null (hcompact n) this
  rw [meagre_iff_countable_union_nowhereDense]
  exact ⟨range K, fun t ⟨n, hn⟩ ↦ (by rw [← hn]; exact h n), countable_range K, hcover.symm.subset⟩

end MeasureZero
