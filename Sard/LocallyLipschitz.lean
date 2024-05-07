import Sard.ToSubset
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
Additional lemmas about locally Lipschitz functions.
-/

open Function NNReal Set Topology

variable {X Y Z: Type*}

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
        _ = b ∩ (U' ∩ U) := by congr; apply (Set.inter_eq_right.mpr hU').symm
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
  exact ⟨K, toSubset t s, ToSubset.compatible_with_nhds s t ht, LipschitzOnWith.restrict_subtype s t hfL⟩

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
  exact ⟨K, toSubset t U, ToSubset.compatible_with_nhds_within t U h₁U ht, LipschitzOnWith.restrict_subtype U t hf⟩
end LocallyLipschitz
end Metric

section Normed
variable [MetricSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f g : X → Y}

/-- The sum of Lipschitz functions is Lipschitz. -/
protected lemma LipschitzOnWith.sum {Kf : ℝ≥0} {Kg : ℝ≥0} {s : Set X}
    (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s) :
    LipschitzOnWith (Kf + Kg) (f + g) s := by
  intro y hy z hz
  -- Since Y is normed, the distance is translation-invariant.
  have translation: ∀ w w' w'' : Y, edist (w + w'') (w' + w'') = edist w w' := by
    intro w w' w''
    simp only [edist_add_right]
  simp only [Pi.add_apply, ENNReal.coe_add]
  calc edist (f y + g y) (f z + g z)
    _ ≤ edist (f y + g y) (g y + f z) + edist (g y + f z) (f z + g z) := by apply edist_triangle
    _ = edist (f y + g y) (f z + g y) + edist (g y + f z) (g z + f z) := by
        simp only [add_comm, edist_add_right, edist_add_left]
    _ ≤ edist (f y) (f z) + edist (g y) (g z) := by rw [translation, translation]
    _ ≤ Kf * edist y z + Kg * edist y z := add_le_add (hf hy hz) (hg hy hz)
    _ = (Kf + Kg) * edist y z := by ring

/-- The sum of Lipschitz functions on `s` is Lipschitz on `s`. -/
protected lemma LipschitzWith.sum {Kf : ℝ≥0} {Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : LipschitzWith (Kf + Kg) (f + g) :=
  lipschitzOn_univ.mp ((lipschitzOn_univ.mpr hf).sum (lipschitzOn_univ.mpr hg))

/-- The sum of locally Lipschitz functions is locally Lipschitz. -/
protected lemma LocallyLipschitz.sum (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (f + g) := by
  intro x
  rcases hf x with ⟨Kf, t₁, h₁t, hfL⟩
  rcases hg x with ⟨Kg, t₂, h₂t, hgL⟩
  use Kf + Kg, t₁ ∩ t₂
  have hf' : LipschitzOnWith Kf f (t₁ ∩ t₂) := hfL.mono (Set.inter_subset_left t₁ t₂)
  have hg' : LipschitzOnWith Kg g (t₁ ∩ t₂) := hgL.mono (Set.inter_subset_right t₁ t₂)
  exact ⟨Filter.inter_mem h₁t h₂t, hf'.sum hg'⟩

-- this one should definitely be in mathlib!
lemma helper (a b : ℝ) : ENNReal.ofReal (a * b) = ENNReal.ofReal a * ENNReal.ofReal b := by sorry

open ENNReal
-- this version is obvious
lemma last' (a : ℝ≥0) (K : ℝ≥0) (c : ℝ≥0) : ((a * K) : NNReal) * c = a * ((K * c) : NNReal) := by
  exact mul_assoc a K c

lemma last'' (a : ℝ) (K : ℝ≥0) (c : ℝ≥0) : -- also works
    ((Real.toNNReal ‖a‖ * K) : NNReal) * c = Real.toNNReal ‖a‖ * ((K * c) : NNReal) := by
  exact mul_assoc _ K c

lemma last (a : ℝ) (K : ℝ≥0) (c : ENNReal) : (Real.toNNReal ‖a‖) * (K * c)
    = ↑(Real.toNNReal ‖a‖ * K) * c := by
  -- the only open question is whether c can be infinite, what happens then
  have : c ≠ ∞ := by sorry -- FIXME: uses cases tactic... syntax fails, somehow.
  lift c to ℝ≥0 using this
  --exact last'' a K c -- fails: coercion of the first factor makes a difference
  sorry

protected lemma LipschitzOnWith.smul {K : ℝ≥0} {s : Set X} (hf : LipschitzOnWith K f s)
    (a : ℝ) : LipschitzOnWith (ENNReal.toNNReal (ENNReal.ofReal ‖a‖) * K) (fun x ↦ a • f x) s := by
  intro x hx y hy
  have : dist (a • f x) (a • f y) = ‖a‖ * dist (f x) (f y) := by
      calc dist (a • f x) (a • f y)
        _ = ‖(a • (f x)) - (a • (f y))‖ := by apply dist_eq_norm
        _ = ‖a • ((f x) - (f y))‖ := by rw [smul_sub]
        _ = ‖a‖ * ‖(f x) - (f y)‖ := by rw [norm_smul]
        _ = ‖a‖ * dist (f x) (f y) := by rw [← dist_eq_norm]
        _ = ‖a‖ * dist (f x) (f y) := by rw [← dist_smul₀]
  calc edist (a • f x) (a • f y)
      _ = ENNReal.ofReal (dist (a • f x) (a • f y)) := by rw [edist_dist]
      _ = ENNReal.ofReal (‖a‖ * dist (f x) (f y)) := by rw [this]
      _ = ENNReal.ofReal (‖a‖) * ENNReal.ofReal (dist (f x) (f y)) := by rw [← helper]
      _ = ENNReal.ofReal ‖a‖ * edist (f x) (f y) := by rw [edist_dist]
      _ ≤ Real.toNNReal ‖a‖ * (K * edist x y) := by exact mul_le_mul_left' (hf hx hy) _
      _ = ↑(Real.toNNReal ‖a‖ * K) * edist x y := by exact last a K (edist x y)

protected lemma LipschitzWith.smul {K : ℝ≥0} (hf : LipschitzWith K f) {a : ℝ} :
    LipschitzWith (ENNReal.toNNReal (ENNReal.ofReal ‖a‖)  * K) (fun x ↦ a • f x) :=
  lipschitzOn_univ.mp ((lipschitzOn_univ.mpr hf).smul a)

/-- Multiplying a locally Lipschitz function by a constant remains locally Lipschitz. -/
protected lemma LocallyLipschitz.mysmul (hf : LocallyLipschitz f) {a : ℝ} : LocallyLipschitz (fun x ↦ a • f x) := by
  intro x
  rcases hf x with ⟨Kf, t, ht, hfL⟩
  exact ⟨ENNReal.toNNReal (ENNReal.ofReal ‖a‖) * Kf, t, ht, hfL.smul a⟩
end Normed
