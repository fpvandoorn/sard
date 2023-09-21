import Sard.LocallyLipschitz
import Mathlib.MeasureTheory.Measure.Hausdorff

-- Locally Lipschitz maps preserve measure zero sets.
open NNReal LocallyLipschitz MeasureTheory Set
set_option autoImplicit false

section ImageMeasureZeroSet
/-- If `f : X → Y` is a Lipschitz map between metric spaces, then `f` maps null sets
to null sets, w.r.t. the `d`-dimensional Hausdorff measure on `X` resp. `Y`. -/
lemma lipschitz_image_null_set_is_null_set
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {d : ℝ} (hd : d ≥ 0) {s : Set X} {f : X → Y} {K : ℝ≥0} (hf : LipschitzOnWith K f s)
    (hs : μH[d] s = 0) : μH[d] (f '' s) = 0 := by
  have aux : μH[d] (f '' s) ≤ (K : ENNReal) ^ d * μH[d] s :=
    LipschitzOnWith.hausdorffMeasure_image_le hf hd
  rw [hs] at aux
  simp only [mul_zero, nonpos_iff_eq_zero, hs] at aux ⊢
  exact aux

/-- Consider two metric spaces `X` and `Y` with the `d`-dimensional Hausdorff measure.
If `X` is `σ`-compact, a locally Lipschitz map $f : X → Y$ maps null sets in `X` to null sets in `Y`. -/
lemma locally_lipschitz_image_of_null_set_is_null_set {X Y : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SigmaCompactSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] {d : ℕ} {f : X → Y}
    (hf : LocallyLipschitz f) {s : Set X} (hs : μH[d] s = 0) : μH[d] (f '' s) = 0 := by
  -- Choose a countable cover of X by compact sets K_n.
  let K : ℕ → Set X := compactCovering X
  have hcov : ⋃ (n : ℕ), K n = univ := iUnion_compactCovering X
  have hcompact : ∀ n : ℕ, IsCompact (K n) := isCompact_compactCovering X

  -- By countable subadditivity, it suffices to show the claim for each K_n.
  suffices ass : ∀ n : ℕ, μH[d] (f '' (s ∩ K n)) = 0 by
    have : s = ⋃ (n : ℕ), s ∩ K n := by
      calc s
        _ = s ∩ univ := Eq.symm (inter_univ s)
        _ = s ∩ ⋃ (n : ℕ), K n := by rw [hcov]
        _ = ⋃ (n : ℕ), s ∩ K n := by apply inter_iUnion s
    have hless : μH[d] (f '' s) ≤ 0 := by
      calc μH[d] (f '' s)
        _ = μH[d] (f '' (⋃ (n : ℕ), s ∩ K n)) := by rw [← this]
        _ = μH[d] (⋃ (n : ℕ), f '' (s ∩ K n)) := by rw [image_iUnion]
        _ ≤ ∑' (n : ℕ), μH[d] (f '' (s ∩ K n)) := by apply OuterMeasure.iUnion_nat
        _ = ∑' (n : ℕ), 0 := by simp_rw [ass]
        _ = 0 := by rw [tsum_zero]
    simp only [nonpos_iff_eq_zero, zero_le] at hless ⊢
    exact hless

  intro n
  -- Consider the open cover (U_x) of K_n induced by hf: each U_x is an open subset containing x
  -- on which f is Lipschitz, say with constant K_x.
  let U : K n → Set X := by
    intro x
    -- tactic 'induction' failed, recursor 'Exists.casesOn' can only eliminate into Prop
    sorry -- rcases hf x with ⟨Kf, t, ht, hfL⟩
  -- These properties hold by construction.
  have hcovering : K n ⊆ ⋃ (x : (K n)), U x := sorry -- use kU above
  have hopen : ∀ x : (K n), IsOpen (U x) := sorry -- use kU above
  have hLipschitz : ∀ x : (K n), ∃ K, LipschitzOnWith K f (U x) := by sorry -- use hKU

  -- Since K_n is compact, (U_x) has a finite subcover U_1, ..., U_l.
  let subcover := IsCompact.elim_finite_subcover (hcompact n) U hopen hcovering
  rcases subcover with ⟨t, ht⟩
  -- On each U_j, f is Lipschitz by hypothesis, hence the previous lemma applies.
  have hnull: ∀ i : t, μH[d] (f '' (s ∩ U i)) = 0 := by
    intro i
    rcases hLipschitz i with ⟨K, hK⟩
    have h₂ : μH[d] (s ∩ U i) = 0 := measure_mono_null (inter_subset_left s (U ↑i)) hs
    have h₁ := LipschitzOnWith.mono hK (inter_subset_right s (U i))
    apply lipschitz_image_null_set_is_null_set (Nat.cast_nonneg d) h₁ h₂
  -- Finite subadditivity implies the claim.
  -- FIXME. This can surely be golfed more.
  have coe : ⋃ (i : t), U i = ⋃ (i : K n) (_ : i ∈ t), U i := by apply iUnion_coe_set
  rw [← coe] at ht
  have : f '' (s ∩ (K n)) ⊆ ⋃ (i : t), f '' (s ∩ (U i)) := by calc f '' (s ∩ (K n))
    _ ⊆ f '' (s ∩ (⋃ (i : t), U i)) := by
      apply Set.image_subset
      apply Set.inter_subset_inter_right s (ht)
    _ = f '' ((⋃ (i : t), s ∩ (U i))) := by rw [inter_iUnion]
    _ = ⋃ (i : t), f '' ( s ∩ (U i)) := image_iUnion
  have hless : μH[d] (f '' (s ∩ (K n))) ≤ 0 := by
    calc μH[d] (f '' (s ∩ (K n)))
      _ ≤ μH[d] (⋃ (i : t), f '' (s ∩ (U i))) := measure_mono this
      _ ≤ ∑' (i : t), (μH[d] (f '' (s ∩ (U i))) : ENNReal) := by apply measure_iUnion_le
      _ = ∑' (i : t), (0 : ENNReal) := tsum_congr hnull
      _ = 0 := by simp
  simp only [nonpos_iff_eq_zero, zero_le] at hless ⊢
  exact hless

-- version specialized to an open set
lemma locally_lipschitz_image_of_null_set_is_null_set_open {X Y : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SigmaCompactSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] {d : ℕ} {f : X → Y} {U : Set X}
    (hf : LocallyLipschitz (U.restrict f)) {s : Set X} (hsu : s ⊆ U) (hs : μH[d] s = 0) :
    μH[d] (f '' s) = 0 := by sorry
end ImageMeasureZeroSet
