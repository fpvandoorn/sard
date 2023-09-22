import Sard.LocallyLipschitz
import Mathlib.MeasureTheory.Measure.Hausdorff

-- Locally Lipschitz maps preserve measure zero sets.
open ENNReal NNReal LocallyLipschitz MeasureTheory Set Topology
set_option autoImplicit false
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

-- this belongs lower in mathlib, find_home! says Mathlib.MeasureTheory.Measure.MeasureSpaceDef
/-- If `(s_n)` is a countable cover of `t` consisting of null sets, `t` is a null set. -/
lemma null_set_from_countable_cover {t : Set X} (μ : Measure X)
    (s : ℕ → Set X) (hnull : ∀ n, μ (s n) = 0) (hcov : t ⊆ ⋃ (n : ℕ), s n) : μ t = 0 := by
  have h : μ t ≤ 0 := by
    have : ∀ n, μ (s n ∩ t) = 0 := fun n => measure_inter_null_of_null_left t (hnull n)
    calc μ t
      _ = μ ((⋃ (n : ℕ), s n) ∩ t) := by simp only [inter_eq_right_iff_subset.mpr hcov]
      _ = μ (⋃ (n : ℕ), (s n ∩ t)) := by rw [iUnion_inter]
      _ ≤ ∑' (n : ℕ), μ (s n ∩ t) := by apply OuterMeasure.iUnion_nat
      _ = ∑' (n : ℕ), 0 := by simp_rw [this]
      _ = 0 := by rw [tsum_zero]
  simp only [nonpos_iff_eq_zero, zero_le] at h ⊢
  exact h

section ImageMeasureZeroSet
/-- If `f : X → Y` is a Lipschitz map between metric spaces, then `f` maps null sets
to null sets, w.r.t. the `d`-dimensional Hausdorff measure on `X` resp. `Y`. -/
lemma lipschitz_image_null_set_is_null_set {d : ℝ} (hd : d ≥ 0) {s : Set X} {f : X → Y} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) (hs : μH[d] s = 0) : μH[d] (f '' s) = 0 := by
  have aux : μH[d] (f '' s) ≤ (K : ENNReal) ^ d * μH[d] s := hf.hausdorffMeasure_image_le hd
  rw [hs] at aux
  simp only [mul_zero, nonpos_iff_eq_zero, hs] at aux ⊢
  exact aux

/-- Consider two metric spaces `X` and `Y` with the `d`-dimensional Hausdorff measure.
If `X` is `σ`-compact, a locally Lipschitz map `f : X → Y` maps null sets in `X` to null sets in `Y`. -/
lemma locally_lipschitz_image_of_null_set_is_null_set [SigmaCompactSpace X] {d : ℕ}
    {f : X → Y} (hf : LocallyLipschitz f) {s : Set X} (hs : μH[d] s = 0) : μH[d] (f '' s) = 0 := by
  -- Choose a countable cover of X by compact sets K_n.
  let K : ℕ → Set X := compactCovering X
  have hcov : ⋃ (n : ℕ), K n = univ := iUnion_compactCovering X
  have hcompact : ∀ n : ℕ, IsCompact (K n) := isCompact_compactCovering X
  -- By countable subadditivity, it suffices to show the claim for each K_n.
  suffices ass : ∀ n : ℕ, μH[d] (f '' (s ∩ K n)) = 0 by
    apply null_set_from_countable_cover _ _ ass
    rw [← image_iUnion]
    have : s = ⋃ (n : ℕ), s ∩ K n := by calc s
        _ = s ∩ univ := (inter_univ s).symm
        _ = s ∩ ⋃ (n : ℕ), K n := by rw [hcov]
        _ = ⋃ (n : ℕ), s ∩ K n := by apply inter_iUnion s
    exact Eq.subset (congrArg (image f) this)

  intro n
  -- Consider the cover (t_x) of K_n induced by hf: for each x, choose a neighbourhood t_x of x
  -- and a constant K_x such that f is K_x-Lipschitz on t_x.
  choose Kx t ht hfL using fun x ↦ (hf x)
  -- For each t_x, choose an open set U_x ∋ x contained in t_x.
  choose U hut hUopen hxU using fun x ↦ mem_nhds_iff.mp (ht x)
  -- By construction, (U_x) is an open covering of K_n.
  have hcovering : K n ⊆ ⋃ (x : X), U x := fun y _ ↦ mem_iUnion_of_mem y (hxU y)
  -- Since K_n is compact, (U_x) has a finite subcover V_1, ..., V_l.
  let ⟨v, hv⟩ := IsCompact.elim_finite_subcover (hcompact n) U hUopen hcovering
  -- f is Lipschitz on each U_j, hence the previous lemma applies.
  have hnull: ∀ i : v, μH[d] (f '' (s ∩ U i)) = 0 := by
    intro i
    have h₂ : μH[d] (s ∩ U i) = 0 := measure_mono_null (inter_subset_left s (U ↑i)) hs
    have h₁ := ((hfL i).mono (hut i)).mono (inter_subset_right s (U i))
    refine lipschitz_image_null_set_is_null_set (Nat.cast_nonneg d) h₁ h₂

  -- Finite subadditivity implies the claim.
  have coe : ⋃ (i : v), U i = ⋃ (i : X) (_ : i ∈ v), U i := iUnion_coe_set _ _
  rw [← coe] at hv
  have : f '' (s ∩ (K n)) ⊆ ⋃ (i : v), f '' (s ∩ (U i)) := by
    calc f '' (s ∩ (K n))
      _ ⊆ f '' (s ∩ (⋃ (i : v), U i)) := by
        apply image_subset
        apply inter_subset_inter_right s hv
      _ = f '' ((⋃ (i : v), s ∩ (U i))) := by rw [inter_iUnion]
      _ = ⋃ (i : v), f '' ( s ∩ (U i)) := image_iUnion
  have hless : μH[d] (f '' (s ∩ (K n))) ≤ 0 := by
    calc μH[d] (f '' (s ∩ (K n)))
      _ ≤ μH[d] (⋃ (i : v), f '' (s ∩ (U i))) := measure_mono this
      _ ≤ ∑' (i : v), (μH[d] (f '' (s ∩ (U i))) : ℝ≥0∞) := by apply measure_iUnion_le
      _ = ∑' (_ : v), (0 : ℝ≥0∞) := tsum_congr hnull
      _ = 0 := by simp
  simp only [nonpos_iff_eq_zero, zero_le] at hless ⊢
  exact hless

-- version specialized to an open set. proof should be completely analogous
lemma locally_lipschitz_image_of_null_set_is_null_set_open [SigmaCompactSpace X] {d : ℕ}
    {f : X → Y} {U : Set X} (hf : LocallyLipschitz (U.restrict f))
    {s : Set X} (hsu : s ⊆ U) (hs : μH[d] s = 0) : μH[d] (f '' s) = 0 := by sorry
end ImageMeasureZeroSet
