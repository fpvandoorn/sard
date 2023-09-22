import Sard.ToSubset
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic

/-!
## Locally Lipschitz functions
Define locally Lipschitz functions and show their elementary properties.
Show that C¹ functions are locally Lipschitz.
-/
-- STATUS. This file has mostly been PRed to mathlib; refactors there are not merged here.

open Function NNReal Set Topology
set_option autoImplicit false

variable {X Y Z: Type*}

section EMetric
variable [EMetricSpace X] [EMetricSpace Y] [EMetricSpace Z]

/-- `f : X → Y` is **locally Lipschitz** iff every point `p ∈ X` has a neighourhood
on which `f` is Lipschitz. -/
def LocallyLipschitz (f : X → Y) : Prop := ∀ x : X, ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t

namespace LocallyLipschitz

/-- A Lipschitz function is locally Lipschitz. -/
protected lemma of_Lipschitz {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) : LocallyLipschitz f := by
  intro x
  use K, univ
  rw [lipschitzOn_univ]
  exact ⟨Filter.univ_mem, hf⟩

/-- The identity function is locally Lipschitz. -/
protected lemma id : LocallyLipschitz (@id X) := LocallyLipschitz.of_Lipschitz (LipschitzWith.id)

/-- Constant functions are locally Lipschitz. -/
protected lemma const (b : Y) : LocallyLipschitz (fun _ : X ↦ b) :=
  LocallyLipschitz.of_Lipschitz (LipschitzWith.const b)

/-- A locally Lipschitz function is continuous. (The converse is false: for example,
$x ↦ \sqrt{x}$ is continuous, but not locally Lipschitz at 0.) -/
protected theorem continuous {f : X → Y} (hf : LocallyLipschitz f) : Continuous f := by
  apply Iff.mpr continuous_iff_continuousAt
  intro x
  rcases (hf x) with ⟨K, t, ht, hK⟩
  exact ContinuousOn.continuousAt (LipschitzOnWith.continuousOn hK) ht

-- tweaked version of the result in mathlib, weaker hypotheses -- not just restricting the domain,
-- but also weakening the assumption on the codomain
theorem comp_lipschitzOnWith' {Kf Kg : ℝ≥0} {f : Y → Z} {g : X → Y} {s : Set X}
    (hf : LipschitzOnWith Kf f (g '' s)) (hg : LipschitzOnWith Kg g s) :
    LipschitzOnWith (Kf * Kg) (f ∘ g) s := by
  intro x hx y hy
  calc edist ((f ∘ g) x) ((f ∘ g) y)
    _ ≤ Kf * edist (g x) (g y) := hf (mem_image_of_mem g hx) (mem_image_of_mem g hy)
    _ ≤ Kf * (Kg * edist x y) := by exact mul_le_mul_left' (hg hx hy) Kf
    _ = ↑(Kf * Kg) * edist x y := by rw [← mul_assoc, ENNReal.coe_mul]

/-- The composition of locally Lipschitz functions is locally Lipschitz. --/
protected lemma comp  {f : Y → Z} {g : X → Y}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) : LocallyLipschitz (f ∘ g) := by
  intro x
  -- g is Lipschitz on t ∋ x, f is Lipschitz on u ∋ g(x)
  rcases hg x with ⟨Kg, t, ht, hgL⟩
  rcases hf (g x) with ⟨Kf, u, hu, hfL⟩
  -- idea: shrink u to g(t), then apply `comp_lipschitzOnWith'`
  -- more precisely: restrict g to t' := t ∩ g⁻¹(u); the preimage of u under g':=g∣t.
  let g' := t.restrict g
  let t' : Set X := ↑(g' ⁻¹' u)
  -- The following is mathematically obvious; sorries are merely wrestling with coercions.
  have h₁ : t' = t ∩ g ⁻¹' u := by
    apply Iff.mpr (Subset.antisymm_iff)
    constructor
    · intro x hx
      constructor
      · exact coe_subset hx
      · -- as x ∈ t', we can apply g' (and land in u by definition), so g'(x)=g(x) ∈ u
        sorry
    · intro x hx
      rcases hx with ⟨ht, hgu⟩
      -- as x ∈ t, we can write g(x)=g'(x); the rhs lies in u, so x ∈ g⁻¹(u) also
      sorry
  have h₂ : t' ∈ 𝓝 x := by -- FIXME: the following is a tour de force; there must be a nicer proof
    -- by ht, t contains an open subset U
    rcases (Iff.mp (mem_nhds_iff) ht) with ⟨U, hUt, hUopen, hxU⟩
    -- similarly, u contains an open subset V
    rcases (Iff.mp (mem_nhds_iff) hu) with ⟨V, hVt, hVopen, hgxV⟩
    -- by continuity, g⁻¹(u) contains the open subset g⁻¹(V)
    have : ContinuousOn g U := LipschitzOnWith.continuousOn (LipschitzOnWith.mono hgL hUt)
    have h : IsOpen (U ∩ (g ⁻¹' V)) := ContinuousOn.preimage_open_of_open this hUopen hVopen
    have : U ∩ (g ⁻¹' V) ⊆ t' := by rw [h₁]; apply inter_subset_inter hUt (preimage_mono hVt)
    -- now, U ∩ g⁻¹(V) is an open subset contained in t'
    rw [mem_nhds_iff]
    use U ∩ (g ⁻¹' V)
    exact ⟨this, ⟨h, ⟨hxU, hgxV⟩⟩⟩
  have : g '' t' ⊆ u := by calc g '' t'
    _ = g '' (t ∩ g ⁻¹' u) := by rw [h₁]
    _ ⊆ g '' t ∩ g '' (g ⁻¹' u) := by apply image_inter_subset
    _ ⊆ g '' t ∩ u := by gcongr; apply image_preimage_subset
    _ ⊆ u := by apply inter_subset_right
  use Kf * Kg, t'
  exact ⟨h₂, comp_lipschitzOnWith'
    (LipschitzOnWith.mono hfL this) (LipschitzOnWith.mono hgL coe_subset)⟩

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

protected theorem prod_mk_left (a : X) : LocallyLipschitz (Prod.mk a : Y → X × Y) :=
  LocallyLipschitz.of_Lipschitz (LipschitzWith.prod_mk_left a)

protected theorem prod_mk_right (b : Y) : LocallyLipschitz (fun a : X => (a, b)) :=
  LocallyLipschitz.of_Lipschitz (LipschitzWith.prod_mk_right b)

protected theorem iterate {f : X → X} (hf : LocallyLipschitz f) : ∀ n, LocallyLipschitz f^[n]
  | 0 => by simpa only [pow_zero] using LocallyLipschitz.id
  | n + 1 => by rw [iterate_add, iterate_one]; exact (LocallyLipschitz.iterate hf n).comp hf

protected theorem mul {f g : Function.End X} (hf : LocallyLipschitz f)
    (hg : LocallyLipschitz g) : LocallyLipschitz (f * g : Function.End X) := hf.comp hg

protected theorem pow {f : Function.End X} (h : LocallyLipschitz f) :
    ∀ n : ℕ, LocallyLipschitz (f ^ n : Function.End X)
  | 0 => by simpa only [pow_zero] using LocallyLipschitz.id
  | n + 1 => by
    rw [pow_succ]
    exact h.mul (LocallyLipschitz.pow h n)
end LocallyLipschitz
end EMetric

--------- everything above here has been PRed

section Metric
variable [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
namespace LocallyLipschitz
/-- `toSubset` is compatible with the neighbourhood filter. -/
protected lemma ToSubset.compatible_with_nhds (s t : Set X) {x : s} (ht : t ∈ 𝓝 ↑x) : toSubset t s ∈ 𝓝 x := by sorry

/-- `toSubset` is compatible with the "neighbourhood within" filter. -/
protected lemma ToSubset.compatible_with_nhds_within (t U: Set X) {x : U} (hU : IsOpen U) (ht : t ∈ 𝓝[U] ↑x) :
    toSubset t U ∈ 𝓝 x := by
  have : t ∩ U ∈ 𝓝 ↑x := by
    -- 𝓝[U] ↑x is the "neighbourhood within" filter, consisting of all sets t ⊇ U ∩ b
    -- for some neighbourhood b of x. Choose an open subset a ⊆ b,
    -- then a ∩ U is an open subset contained in t.
    rcases ht with ⟨b, hb, U', hU', htaU⟩
    rw [mem_nhds_iff] at hb
    rcases hb with ⟨a, ha, haopen, hxa⟩
    rw [mem_nhds_iff]
    use a ∩ U
    constructor
    · calc a ∩ U
        _ ⊆ b ∩ U := inter_subset_inter_left U ha
        _ = b ∩ (U' ∩ U) := by congr; rw [(Iff.mpr inter_eq_right_iff_subset hU')]
        _ ⊆ (b ∩ U') ∩ U := by rw [inter_assoc]
        _ = t ∩ U := by rw [htaU]
    · exact ⟨IsOpen.inter haopen hU, ⟨hxa, Subtype.mem x⟩⟩
  apply ToSubset.compatible_with_nhds
  exact Filter.mem_of_superset this (inter_subset_left t U)

/- Restrictions of Lipschitz functions is compatible with taking subtypes. -/
protected lemma LipschitzOnWith.restrict_subtype {f : X → Y} {K : ℝ≥0} (s t : Set X)
    (hf : LipschitzOnWith K f t) : LipschitzOnWith K (restrict s f) (toSubset t s) :=
  fun _ hx _ hy ↦ hf hx hy

/-- Restrictions of locally Lipschitz functions are locally Lipschitz. -/
protected lemma restrict {f : X → Y} (hf : LocallyLipschitz f) (s : Set X) :
    LocallyLipschitz (s.restrict f) := by
  intro x
  rcases hf x with ⟨K, t, ht, hfL⟩
  -- Consider t' := t ∩ s as a neighbourhood of x *in s*.
  use K, toSubset t s
  exact ⟨ToSubset.compatible_with_nhds s t ht, LipschitzOnWith.restrict_subtype s t hfL⟩

/-- C¹ functions are locally Lipschitz. -/
-- upstreamed, as ContDiff.locallyLipschitz
protected lemma of_C1 {E F: Type*} {f : E → F} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hf : ContDiff ℝ 1 f) : LocallyLipschitz f := by
  intro x
  rcases (ContDiffAt.exists_lipschitzOnWith (ContDiff.contDiffAt hf)) with ⟨K, t, ht, hf⟩
  use K, t

/-- If `f` is C¹ on an open convex set `U`, the restriction of `f` to `U` is locally Lipschitz. -/
-- TODO: upstream to ContDiffOn.lean! once the restriction stuff is figured out. can drop the variables there :-)
lemma of_C1_on_open {E F: Type*} {f : E → F} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (h₁U : IsOpen U) (h₂U : Convex ℝ U)
    (hf : ContDiffOn ℝ 1 f U) : LocallyLipschitz (U.restrict f) := by
  intro x
  have : ContDiffWithinAt ℝ 1 f U x := ContDiffOn.contDiffWithinAt hf (Subtype.mem x)
  let h := ContDiffWithinAt.exists_lipschitzOnWith this
  rcases (h h₂U) with ⟨K, t, ht, hf⟩
  -- `t` is a neighbourhood of x "within U", i.e. contains the intersection of U with some nbhd a of x.
  -- Intersect with `U` to obtain a neighbourhood contained in `U`.
  use K, toSubset t U
  exact ⟨ToSubset.compatible_with_nhds_within t U h₁U ht, LipschitzOnWith.restrict_subtype U t hf⟩
end LocallyLipschitz
end Metric

section EMetric
namespace LocallyLipschitz
---------------------------------
-- all of this section has been PRed, except for the sum and smul lemmas
---------------------------------
variable [MetricSpace X] [MetricSpace Y] [MetricSpace Z] {f g : X → ℝ}
/-- The minimum of locally Lipschitz functions is locally Lipschitz. -/
protected lemma min (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => min (f x) (g x)) := by
  let m : ℝ × ℝ → ℝ := fun p ↦ min p.1 p.2
  have h : LocallyLipschitz m := LocallyLipschitz.of_Lipschitz lipschitzWith_min
  exact LocallyLipschitz.comp h (LocallyLipschitz.prod hf hg)

/-- The maximum of locally Lipschitz functions is locally Lipschitz. -/
protected lemma max (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => max (f x) (g x)) := by
  let m : ℝ × ℝ → ℝ := fun p ↦ max p.1 p.2
  have h : LocallyLipschitz m := LocallyLipschitz.of_Lipschitz lipschitzWith_max
  exact LocallyLipschitz.comp h (LocallyLipschitz.prod hf hg)

theorem max_const (hf : LocallyLipschitz f) (a : ℝ) : LocallyLipschitz fun x => max (f x) a :=
  LocallyLipschitz.max hf (LocallyLipschitz.const a)

theorem const_max (hf : LocallyLipschitz f) (a : ℝ) : LocallyLipschitz fun x => max a (f x) :=
  LocallyLipschitz.max (LocallyLipschitz.const a) hf

theorem min_const (hf : LocallyLipschitz f) (a : ℝ) : LocallyLipschitz fun x => min (f x) a :=
  LocallyLipschitz.min hf (LocallyLipschitz.const a)

theorem const_min (hf : LocallyLipschitz f) (a : ℝ) : LocallyLipschitz fun x => min a (f x) :=
  LocallyLipschitz.min (LocallyLipschitz.const a) hf

/-- The sum of locally Lipschitz functions is locally Lipschitz. -/
protected lemma sum {f g : X → Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) : LocallyLipschitz (f + g) := by
  intro x
  rcases hf x with ⟨Kf, t₁, h₁t, hfL⟩
  rcases hg x with ⟨Kg, t₂, h₂t, hgL⟩
  use Kf + Kg, t₁ ∩ t₂
  have hf' : LipschitzOnWith Kf f (t₁ ∩ t₂) := LipschitzOnWith.mono hfL (Set.inter_subset_left t₁ t₂)
  have hg' : LipschitzOnWith Kg g (t₁ ∩ t₂) := LipschitzOnWith.mono hgL (Set.inter_subset_right t₁ t₂)
  constructor
  · exact Filter.inter_mem h₁t h₂t
  · intro y hy z hz
    -- FIXME. This can surely be golfed!
    simp only [Pi.add_apply, ENNReal.coe_add]
    calc edist (f y + g y) (f z + g z)
      _ ≤ edist (f y + g y) (g y + f z) + edist (g y + f z) (f z + g z) := by apply edist_triangle
      -- Y is normed, hence the distance is translation-invariant
      _ ≤ edist (f y) (f z) + edist (g y) (g z) := by sorry
      _ ≤ Kf * edist y z + Kg * edist y z := add_le_add (hf' hy hz) (hg' hy hz)
      _ = (Kf + Kg) * edist y z := by ring

/-- Multiplying a locally Lipschitz function by a constant remains locally Lipschitz. -/
protected lemma smul {f : X → Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (hf : LocallyLipschitz f) {a : ℝ} : LocallyLipschitz (fun x ↦ a • f x) := by
  intro x
  rcases hf x with ⟨Kf, t, ht, hfL⟩
  let a' : ℝ≥0 := sorry -- want ↑‖a‖
  use a' * Kf, t
  constructor
  · exact ht
  · have : ∀ x ∈ t, ∀ y ∈ t, dist (a • f x) (a • f y) ≤ (a' * Kf) * dist x y := by
      intro x hx y hy
      calc dist (a • f x) (a • f y) -- norm requires dist by definition
        _ = ‖(a • (f x)) - (a • (f y))‖ := by apply dist_eq_norm
        _ = ‖a • ((f x) - (f y))‖ := by rw [smul_sub]
        _ = ‖a‖ * ‖(f x) - (f y)‖ := by rw [norm_smul]
        _ = ‖a‖ * dist (f x) (f y) := by rw [← dist_eq_norm]
        _ = ‖a‖ * dist (f x) (f y) := by rw [← @dist_smul₀]
        _ ≤ ‖a‖ * Kf * dist x y := by sorry -- use hfL; that yields edist -> need to cast
        _ ≤ a' * Kf * dist x y := by sorry -- use definition of a'
        _ = (a' * Kf) * dist x y := by rfl
    let asdf := LipschitzOnWith.of_dist_le' (K := (a' * Kf)) this
    sorry -- *almost* there, except for some issue with casting
end LocallyLipschitz
end EMetric
