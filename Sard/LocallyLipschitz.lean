import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
## Locally Lipschitz functions
Define locally Lipschitz functions and show their elementary properties.
Show that C¹ functions are locally Lipschitz.
-/
-- FIXME: move to a separate section of Lipschitz

open Topology
set_option autoImplicit false

variable {X Y Z: Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

-- f : X → Y is locally Lipschitz iff every point `p ∈ X` has a neighourhood on which `f` is Lipschitz.
def LocallyLipschitz (f : X → Y) : Prop :=
  ∀ x : X, ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t

/-- A Lipschitz function is locally Lipschitz. -/
lemma Lipschitz_is_locally_Lipschitz {f : X → Y} (hf : ∃ K, LipschitzWith K f) :
    LocallyLipschitz f := by sorry

/-- The identity function is locally Lipschitz. -/
lemma LocallyLipschitz_id : LocallyLipschitz (@id X) := by
  sorry-- refine Lipschitz_is_locally_Lipschitz ?_
  -- exact LipschitzWith.id

/-- The composition of locally Lipschitz functions is locally Lipschitz. --/
lemma LocallyLipschitz_comp {f : X → Y} {g : Y → Z}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) : LocallyLipschitz (g ∘ f) := by sorry

/-- The sum of locally Lipschitz functions is locally Lipschitz. -/
lemma LocallyLipschitz_sum {f g : X → Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) : LocallyLipschitz (f + g) := by
  intro x
  rcases hf x with ⟨K₁, t₁, h₁t, hfL⟩
  rcases hg x with ⟨K₂, t₂, h₂t, hgL⟩
  use K₁ + K₂
  use t₁ ∩ t₂
  have as: LipschitzOnWith K₁ f (t₁∩t₂) := by exact LipschitzOnWith.mono (by exact hfL) (by exact Set.inter_subset_left t₁ t₂)
  have bs: LipschitzOnWith K₂ g (t₁∩t₂) := sorry --by exact LipschitzOnWith.mono (by exact hfL) (by exact Set.inter_subset_left t₁ t₂)
  constructor
  · exact Filter.inter_mem h₁t h₂t
  · sorry -- exact?


/-- The minimum of locally Lipschitz functions is locally Lipschitz. -/
lemma LocallyLipschitz_min {f g : X → ℝ} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => min (f x) (g x)) := by
  intro x
  rcases hf x with ⟨Kf, t₁, h₁t, hfL⟩
  rcases hg x with ⟨Kg, t₂, h₂t, hgL⟩
  use max Kf Kg
  use t₁ ∩ t₂

/-- The maximum of locally Lipschitz functions is locally Lipschitz. -/
lemma LocallyLipschitz_max {f g : X → ℝ} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => max (f x) (g x)) := by sorry

/-- Multiplying a locally Lipschitz function by a constant remains locally Lipschitz. -/
lemma LocallyLipschitz_scalarProduct {f : X → Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (hf : LocallyLipschitz f) {a : ℝ} :
    LocallyLipschitz (fun x ↦ a • f x) := by sorry

variable {E F: Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- C¹ functions are locally Lipschitz. -/
lemma LocallyLipschitz_sdfdsf {f : E → E} (hf : ContDiff ℝ 1 f) : LocallyLipschitz f := by sorry


-- example: f : ℝ → ℝ, x ↦ x^2 is locally Lipschitz (but not Lipschitz)