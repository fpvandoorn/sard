import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
## Locally Lipschitz functions
Define locally Lipschitz functions and show their elementary properties.
Show that C¹ functions are locally Lipschitz.
-/
-- FIXME: move to a separate section of Lipschitz

open NNReal Set Topology
set_option autoImplicit false

namespace LocallyLipschitz
variable {X Y Z: Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

/-- `f : X → Y` is **locally Lipschitz** iff every point `p ∈ X` has a neighourhood
on which `f` is Lipschitz. -/
def LocallyLipschitz (f : X → Y) : Prop := ∀ x : X, ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t

/-- A Lipschitz function is locally Lipschitz. -/
protected lemma of_Lipschitz {f : X → Y} (hf : ∃ K, LipschitzWith K f) : LocallyLipschitz f := by
  intro x
  obtain ⟨K, hK⟩ := hf
  use K, univ
  rw [lipschitzOn_univ]
  exact ⟨Filter.univ_mem, hK⟩

/-- The identity function is locally Lipschitz. -/
protected lemma id : LocallyLipschitz (@id X) := by
  apply LocallyLipschitz.of_Lipschitz
  use 1
  exact LipschitzWith.id

/-- Constant functions are locally Lipschitz. -/
protected lemma const (b : Y) : LocallyLipschitz (fun _ : X ↦ b) := by
  apply LocallyLipschitz.of_Lipschitz
  use 0
  exact LipschitzWith.const b

-- TODO: move to proper place, Set.Basic?
/-- If two subsets `s` and `t` satisfy `s ⊆ t` and `h` is a proof of this,
`toSubset s t h` is the set `s` as a subset of `t`. -/
def toSubset {X : Type*} (s t : Set X) (h : s ≤ t) : Set t := sorry
lemma mem_toSubset {X : Type*} (s t : Set X) (h : s ≤ t)
    (x : t) : x ∈ toSubset s t h ↔ ↑x ∈ s := sorry

protected lemma restrict_aux1 (s t : Set X) {x : s} (ht : t ∈ 𝓝 ↑x) :
    (toSubset (t∩s) s (inter_subset_right t s)) ∈ 𝓝 x := by sorry

-- FIXME: how different is this from restrict_aux1 - can I merge these?
protected lemma restrict_aux1b (t U: Set X) {x : U} (hU : IsOpen U) (ht : t ∈ 𝓝[U] ↑x) :
    (toSubset (t∩U) U (inter_subset_right t U)) ∈ 𝓝 x := by
  -- FIXME: is openness of U required? can I weaken this to just the nbhd filter?
  -- t ∩ U is a nbhd of x: as x and U are
  have : t ∩ U ∈ 𝓝 ↑x := by
    -- ht means t ∈ 𝓝[U] ↑x, i.e. t ⊇ U ∩ a for some nbhd a of x
    -- then `a` contains an open subset a', so t ⊇ U ∩ a' shows t is a nbhd
    have h₁: t ∈ 𝓝 ↑x := by sorry
    have : U ∈ 𝓝 ↑x := by sorry -- U is open and contains x
    exact Filter.inter_mem h₁ this
  sorry -- should be just unfolding toSubset

protected lemma restrict_aux2 {f : X → Y} {K : ℝ≥0} (s t : Set X) (hf : LipschitzOnWith K f t) :
    LipschitzOnWith K (restrict s f) (toSubset (t∩s) s (inter_subset_right t s)) := by
  let h := inter_subset_right t s
  intro x hx y hy
  have h₁: ↑x ∈ t := mem_of_mem_inter_left (Iff.mp (mem_toSubset (t ∩ s) s h x) hx)
  have h₂: ↑y ∈ t := mem_of_mem_inter_left (Iff.mp (mem_toSubset (t ∩ s) s h y) hy)
  calc edist (restrict s f x) (restrict s f y)
    _ = edist (f x) (f y) := rfl
    _ ≤ K * edist x y := by apply hf h₁ h₂

/-- Restrictions of locally Lipschitz functions are locally Lipschitz. -/
protected lemma restrict {f : X → Y} (hf : LocallyLipschitz f) (s : Set X) :
    LocallyLipschitz (s.restrict f) := by
  intro x
  rcases hf x with ⟨K, t, ht, hfL⟩
  -- Consider t' := t ∩ s as a neighbourhood of x *in s*.
  let t' := toSubset (t∩s) s (inter_subset_right t s)
  use K, t'
  exact ⟨LocallyLipschitz.restrict_aux1 s t ht, LocallyLipschitz.restrict_aux2 s t hfL⟩

/-- C¹ functions are locally Lipschitz. -/
-- TODO: move to ContDiff.lean!
protected lemma of_C1 {E F: Type*} {f : E → F} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hf : ContDiff ℝ 1 f) : LocallyLipschitz f := by
  intro x
  rcases (ContDiffAt.exists_lipschitzOnWith (ContDiff.contDiffAt hf)) with ⟨K, t, ht, hf⟩
  use K, t

/-- A C¹ function on an open set is locally Lipschitz. -/
-- TODO: move to ContDiffOn.lean!
lemma of_C1_on_open {E F: Type*} {f : E → F} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU: IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
  LocallyLipschitz (U.restrict f) := by
  intro x
  have : ContDiffWithinAt ℝ 1 f U x := ContDiffOn.contDiffWithinAt hf (Subtype.mem x)
  let h := ContDiffWithinAt.exists_lipschitzOnWith this
  have : Convex ℝ U := sorry -- pretend U is convex, say by restriction
  rcases (h this) with ⟨K, t, ht, hf⟩
  -- t is a neighbourhood of x "within U", i.e. contains the intersection of U with some nbhd a of x
  -- intersect with U to obtain a neighbourhood contained in U
  let t' := toSubset (t ∩ U) U (inter_subset_right t U)
  use K, t'
  exact ⟨LocallyLipschitz.restrict_aux1b t U hU ht, LocallyLipschitz.restrict_aux2 U t hf⟩

-- tweaked version of the result in mathlib, weaker hypotheses -- not just restricting the domain,
-- but also weakening the assumption on the codomain
theorem comp_lipschitzOnWith' {Kf Kg : ℝ≥0} {f : Y → Z} {g : X → Y} {s : Set X}
    (hf : LipschitzOnWith Kf f (g '' s)) (hg : LipschitzOnWith Kg g s) : LipschitzOnWith (Kf * Kg) (f ∘ g) s := by
  intro x hx y hy
  calc edist ((f ∘ g) x) ((f ∘ g) y)
    _ ≤ Kf * edist (g x) (g y) := hf (mem_image_of_mem g hx) (mem_image_of_mem g hy)
    _ ≤ Kf * (Kg * edist x y) := by exact mul_le_mul_left' (hg hx hy) Kf
    _ = ↑(Kf * Kg) * edist x y := by rw [← mul_assoc, ENNReal.coe_mul]

/-- The composition of locally Lipschitz functions is locally Lipschitz. --/
protected lemma comp  {f : Y → Z} {g : X → Y} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (f ∘ g) := by
  intro x
  rcases hg x with ⟨Kg, t₁, ht₁, hgL⟩
  -- g is Lipschitz on t, f is Lipschitz on u ∋ g(x)
  rcases hf (g x) with ⟨Kf, u, hu, hfL⟩
  sorry -- proof incubated on mathlib branch...

/-- If `f` and `g` are locally Lipschitz, so is the induced map `f × g` to the product type. -/
protected lemma prod {f : X → Y} (hf : LocallyLipschitz f) {g : X → Z} (hg : LocallyLipschitz g) :
    LocallyLipschitz fun x => (f x, g x) := by
  intro x
  rcases hf x with ⟨Kf, t₁, h₁t, hfL⟩
  rcases hg x with ⟨Kg, t₂, h₂t, hgL⟩
  use max Kf Kg, t₁ ∩ t₂
  constructor
  · exact Filter.inter_mem h₁t h₂t
  · intro y hy z hz
    have h₁ : edist (f y) (f z) ≤ Kf * edist y z := by
      exact LipschitzOnWith.mono hfL (inter_subset_left t₁ t₂) hy hz
    have h₂ : edist (g y) (g z) ≤ Kg * edist y z := by
      exact LipschitzOnWith.mono hgL (inter_subset_right t₁ t₂) hy hz
    rw [ENNReal.coe_mono.map_max, Prod.edist_eq, ENNReal.max_mul]
    exact max_le_max h₁ h₂

protected theorem prod_mk_left (a : X) : LocallyLipschitz (Prod.mk a : Y → X × Y) := by
  apply LocallyLipschitz.of_Lipschitz
  use 1
  apply LipschitzWith.prod_mk_left

protected theorem prod_mk_right (b : Y) : LocallyLipschitz (fun a : X => (a, b)) := by
  apply LocallyLipschitz.of_Lipschitz
  use 1
  apply LipschitzWith.prod_mk_right

/-- The sum of locally Lipschitz functions is locally Lipschitz. -/
protected lemma sum {f g : X → Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) : LocallyLipschitz (f + g) := by
  intro x
  rcases hf x with ⟨Kf, t₁, h₁t, hfL⟩
  rcases hg x with ⟨Kg, t₂, h₂t, hgL⟩
  use Kf + Kg
  use t₁ ∩ t₂
  have hf' : LipschitzOnWith Kf f (t₁ ∩ t₂) := LipschitzOnWith.mono hfL (Set.inter_subset_left t₁ t₂)
  have hg' : LipschitzOnWith Kg g (t₁ ∩ t₂) := LipschitzOnWith.mono hgL (Set.inter_subset_right t₁ t₂)
  constructor
  · exact Filter.inter_mem h₁t h₂t
  · intro y hy z hz
    simp only [Pi.add_apply, ENNReal.coe_add]
    sorry


/-- The minimum of locally Lipschitz functions is locally Lipschitz. -/
protected lemma min {f g : X → ℝ} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => min (f x) (g x)) := by
  intro x
  rcases hf x with ⟨Kf, t₁, h₁t, hfL⟩
  rcases hg x with ⟨Kg, t₂, h₂t, hgL⟩
  use max Kf Kg
  use t₁ ∩ t₂
  sorry

/-- The maximum of locally Lipschitz functions is locally Lipschitz. -/
protected lemma max {f g : X → ℝ} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => max (f x) (g x)) := by sorry

/-- Multiplying a locally Lipschitz function by a constant remains locally Lipschitz. -/
protected lemma scalarProduct {f : X → Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (hf : LocallyLipschitz f) {a : ℝ} :
    LocallyLipschitz (fun x ↦ a • f x) := by sorry
