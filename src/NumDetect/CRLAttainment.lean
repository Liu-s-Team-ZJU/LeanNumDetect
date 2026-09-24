import NumDetect.CRLFourierStability

/-! Perturbation lemmas for attainment of the number-detection CRL. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect
namespace NumDetect

noncomputable section

open Filter
open scoped Topology

private theorem normAt_const_mul {d : ℕ} (p : LpIndex)
    (c : ℝ) (hc : 0 ≤ c) (x : Point d) :
    normAt p (fun k => c * x k) = c * normAt p x := by
  cases p with
  | infinity =>
      simp only [normAt, linftyNorm]
      have he : (fun k => c * x k) = c • x := by
        funext k
        simp [Pi.smul_apply, smul_eq_mul]
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  | finite q hq =>
      simp only [normAt, lpNorm]
      have hsum :
          (∑ k : Fin d, |c * x k| ^ q) =
            c ^ q * ∑ k : Fin d, |x k| ^ q := by
        simp_rw [abs_mul, abs_of_nonneg hc, Real.mul_rpow hc (abs_nonneg _)]
        rw [Finset.mul_sum]
      rw [hsum, Real.mul_rpow (Real.rpow_nonneg hc _)
        (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (abs_nonneg _) _)]
      rw [one_div]
      rw [Real.rpow_rpow_inv hc (by linarith : q ≠ 0)]

private theorem normAt_pos_of_ne {d : ℕ} (p : LpIndex) {x : Point d}
    (hx : x ≠ 0) : 0 < normAt p x := by
  cases p with
  | infinity =>
      simpa only [normAt, linftyNorm] using norm_pos_iff.mpr hx
  | finite q hq =>
      obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
        by_contra hn
        push Not at hn
        exact hx (funext hn)
      have hterm : 0 < |x k| ^ q := Real.rpow_pos_of_pos (abs_pos.mpr hk) _
      have hsum : 0 < ∑ j : Fin d, |x j| ^ q :=
        (Finset.sum_pos_iff_of_nonneg
          (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)).mpr
          ⟨k, Finset.mem_univ _, hterm⟩
      simpa only [normAt, lpNorm] using Real.rpow_pos_of_pos hsum (1 / q)

/-- Dilation of a reduced atomic measure by a nonzero real factor. -/
private def dilatedMeasure {d n : ℕ} (μ : AtomicMeasure d n)
    (t : ℝ) (ht : t ≠ 0) : AtomicMeasure d n where
  amplitude := μ.amplitude
  node := fun j k => t * μ.node j k
  amplitude_ne_zero := μ.amplitude_ne_zero
  node_injective := by
    intro i j hij
    apply μ.node_injective
    funext k
    exact mul_left_cancel₀ ht (congrFun hij k)

private theorem minAmplitude_dilatedMeasure {d n : ℕ}
    (μ : AtomicMeasure d n) (hn : 0 < n) (t : ℝ) (ht : t ≠ 0) :
    minAmplitude (dilatedMeasure μ t ht) hn = minAmplitude μ hn := rfl

private theorem dilatedMeasure_cluster_eventually {d n : ℕ}
    (μ : AtomicMeasure d n) (Ω : ℝ)
    (hcluster : ∀ j, InOpenL1Ball (Real.pi * n / Ω) 0 (μ.node j)) :
    ∀ᶠ t in 𝓝 (1 : ℝ), ∀ j,
      InOpenL1Ball (Real.pi * n / Ω) 0
        (fun k => t * μ.node j k) := by
  apply Filter.eventually_all.mpr
  intro j
  have hcont : ContinuousAt (fun t : ℝ =>
      l1Norm (fun k => t * μ.node j k)) 1 := by
    unfold l1Norm
    fun_prop
  have hcenter : l1Norm (μ.node j) < Real.pi * n / Ω := by
    simpa [InOpenL1Ball] using hcluster j
  have hev := hcont.eventually_lt (continuousAt_const)
    (by simpa using hcenter)
  filter_upwards [hev] with t ht
  simpa [InOpenL1Ball] using ht

private theorem dilatedMeasure_separation_gt {d n : ℕ}
    (μ : AtomicMeasure d n) (p : LpIndex) (D t : ℝ)
    (ht : 1 < t)
    (hsep : ∀ i j, i ≠ j → D ≤ normAt p (μ.node i - μ.node j)) :
    ∀ i j, i ≠ j →
      D < normAt p
        ((dilatedMeasure μ t (ne_of_gt (lt_trans zero_lt_one ht))).node i -
          (dilatedMeasure μ t (ne_of_gt (lt_trans zero_lt_one ht))).node j) := by
  intro i j hij
  have hdiff : μ.node i - μ.node j ≠ 0 :=
    sub_ne_zero.mpr (fun h => hij (μ.node_injective h))
  have hpos : 0 < normAt p (μ.node i - μ.node j) :=
    normAt_pos_of_ne p hdiff
  have hscale :
      (dilatedMeasure μ t (ne_of_gt (lt_trans zero_lt_one ht))).node i -
        (dilatedMeasure μ t (ne_of_gt (lt_trans zero_lt_one ht))).node j =
          fun k => t * (μ.node i k - μ.node j k) := by
    funext k
    simp only [dilatedMeasure, Pi.sub_apply]
    ring
  rw [hscale, normAt_const_mul p t (le_of_lt (lt_trans zero_lt_one ht))]
  change D < t * normAt p (μ.node i - μ.node j)
  have := hsep i j hij
  nlinarith [mul_pos (sub_pos.mpr ht) hpos]

private theorem fourier_gap_of_band_and_admissible {d n k : ℕ}
    (μ : AtomicMeasure d n) (ν : AtomicMeasure d k)
    (Ω σ : ℝ) (Y : Point d → ℂ)
    (hmeasurement : IsBandMeasurement μ Ω σ Y)
    (hadmissible : IsAdmissible ν Ω σ Y) :
    ∀ ω, InFrequencyBand Ω ω →
      ‖fourier μ ω - fourier ν ω‖ < 2 * σ := by
  obtain ⟨W, hW, hY⟩ := hmeasurement
  intro ω hω
  have htriangle :
      ‖fourier μ ω - fourier ν ω‖ ≤
        ‖fourier μ ω - Y ω‖ + ‖Y ω - fourier ν ω‖ := by
    calc
      _ = ‖(fourier μ ω - Y ω) + (Y ω - fourier ν ω)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have hleft : ‖fourier μ ω - Y ω‖ = ‖W ω‖ := by
    rw [hY ω hω]
    simp
  have hright : ‖Y ω - fourier ν ω‖ = ‖fourier ν ω - Y ω‖ :=
    norm_sub_rev _ _
  rw [hleft, hright] at htriangle
  have := hW ω hω
  have := hadmissible ω hω
  linarith

private theorem norm_half_sub_lt {a b : ℂ} {σ : ℝ}
    (h : ‖a - b‖ < 2 * σ) : ‖(b - a) / 2‖ < σ := by
  have he : ‖(b - a) / 2‖ = ‖a - b‖ / 2 := by
    rw [norm_div, norm_sub_rev]
    norm_num
  rw [he]
  linarith

private theorem exists_larger_counterexample
    {d n k : ℕ} {Ω σ mMin D : ℝ} (hn : 2 ≤ n)
    (hΩ : 0 < Ω) (hσ : 0 < σ) (p : LpIndex)
    (μ : AtomicMeasure d n) (ν : AtomicMeasure d k)
    (hmin : minAmplitude μ (Nat.zero_lt_of_lt hn) = mMin)
    (hcluster : ∀ j, InOpenL1Ball (Real.pi * n / Ω) 0 (μ.node j))
    (hsep : ∀ i j, i ≠ j → D ≤ normAt p (μ.node i - μ.node j))
    (Y : Point d → ℂ) (hmeasurement : IsBandMeasurement μ Ω σ Y)
    (hadmissible : IsAdmissible ν Ω σ Y) :
    ∃ E : ℝ, D < E ∧ ∃ μ' : AtomicMeasure d n,
      minAmplitude μ' (Nat.zero_lt_of_lt hn) = mMin ∧
      μ'.amplitude = μ.amplitude ∧
      (∀ j, InOpenL1Ball (Real.pi * n / Ω) 0 (μ'.node j)) ∧
      (∀ i j, i ≠ j → E ≤ normAt p (μ'.node i - μ'.node j)) ∧
      ∃ Y' : Point d → ℂ,
        IsBandMeasurement μ' Ω σ Y' ∧ IsAdmissible ν Ω σ Y' := by
  have hgap := fourier_gap_of_band_and_admissible μ ν Ω σ Y hmeasurement hadmissible
  have hfourierEv := dilatedFourier_eventually_lt_two_sigma μ ν hΩ hσ hgap
  have hclusterEv := dilatedMeasure_cluster_eventually μ Ω hcluster
  obtain ⟨t, ht1, hfourier, hcluster'⟩ :=
    (hfourierEv.and hclusterEv).exists_gt
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht1)
  let μ' : AtomicMeasure d n := dilatedMeasure μ t ht0
  have hμfourier (ω : Point d) :
      fourier μ' ω = dilatedFourier μ t ω := rfl
  have hmin' : minAmplitude μ' (Nat.zero_lt_of_lt hn) = mMin := by
    rw [show μ' = dilatedMeasure μ t ht0 from rfl,
      minAmplitude_dilatedMeasure]
    exact hmin
  have hcluster'' : ∀ j, InOpenL1Ball (Real.pi * n / Ω) 0 (μ'.node j) := by
    intro j
    exact hcluster' j
  have hsepStrict : ∀ i j, i ≠ j →
      D < normAt p (μ'.node i - μ'.node j) :=
    dilatedMeasure_separation_gt μ p D t ht1 hsep
  let sepMin := minimumOverDistinctPairs hn
    (fun i j => normAt p (μ'.node i - μ'.node j))
  have hsepMin : D < sepMin := by
    dsimp [sepMin, minimumOverDistinctPairs]
    rw [Finset.lt_inf'_iff (distinctPairs_nonempty hn)]
    intro ij hij
    have hne : ij.1 ≠ ij.2 := by simpa [distinctPairs] using hij
    exact hsepStrict ij.1 ij.2 hne
  let E := (D + sepMin) / 2
  have hDE : D < E := by dsimp [E]; linarith
  have hEsep : ∀ i j, i ≠ j → E ≤ normAt p (μ'.node i - μ'.node j) := by
    intro i j hij
    have hminle : sepMin ≤ normAt p (μ'.node i - μ'.node j) := by
      dsimp [sepMin, minimumOverDistinctPairs]
      rw [Finset.inf'_le_iff (distinctPairs_nonempty hn)]
      exact ⟨(i, j), by simp [distinctPairs, hij], le_rfl⟩
    dsimp [E]
    linarith
  have hgap' (ω : Point d) (hω : InFrequencyBand Ω ω) :
      ‖fourier μ' ω - fourier ν ω‖ < 2 * σ := by
    rw [hμfourier]
    exact hfourier ω hω
  let Y' : Point d → ℂ :=
    fun ω => fourier μ' ω + (fourier ν ω - fourier μ' ω) / 2
  have hmeasurement' : IsBandMeasurement μ' Ω σ Y' := by
    refine ⟨fun ω => (fourier ν ω - fourier μ' ω) / 2, ?_, ?_⟩
    · intro ω hω
      exact norm_half_sub_lt (hgap' ω hω)
    · intro ω _
      rfl
  have hadmissible' : IsAdmissible ν Ω σ Y' := by
    intro ω hω
    have he : fourier ν ω - Y' ω =
        (fourier ν ω - fourier μ' ω) / 2 := by
      dsimp [Y']
      ring
    rw [he]
    exact norm_half_sub_lt (hgap' ω hω)
  exact ⟨E, hDE, μ', hmin', rfl, hcluster'', hEsep,
    Y', hmeasurement', hadmissible'⟩

/-- A failed separation threshold remains failed at a slightly larger value.
This is the openness of the counterexample side of the CRL definition. -/
theorem exists_larger_not_numberDetectionGuarantee
    {d n : ℕ} {Ω σ mMin D : ℝ} (hn : 2 ≤ n)
    (hΩ : 0 < Ω) (hσ : 0 < σ) (p : LpIndex)
    (hfail : ¬NumberDetectionGuarantee d n p Ω σ mMin D
      (Nat.zero_lt_of_lt hn)) :
    ∃ E : ℝ, D < E ∧
      ¬NumberDetectionGuarantee d n p Ω σ mMin E
        (Nat.zero_lt_of_lt hn) := by
  unfold NumberDetectionGuarantee at hfail
  push Not at hfail
  obtain ⟨μ, hmMin, hcluster, hsep, Y, hmeasurement, k, ν, hadmissible, hk⟩ := hfail
  obtain ⟨E, hDE, μ', hmMin', _hAmp, hcluster', hsep', Y', hmeasurement', hadmissible'⟩ :=
    exists_larger_counterexample hn hΩ hσ p μ ν hmMin hcluster hsep
      Y hmeasurement hadmissible
  refine ⟨E, hDE, ?_⟩
  intro hgood
  exact (not_le_of_gt hk)
    (hgood μ' hmMin' hcluster' hsep' Y' hmeasurement' k ν hadmissible')

/-- The same rightward extension for counterexamples with positive amplitudes. -/
theorem exists_larger_not_positiveNumberDetectionGuarantee
    {d n : ℕ} {Ω σ mMin D : ℝ} (hn : 2 ≤ n)
    (hΩ : 0 < Ω) (hσ : 0 < σ) (p : LpIndex)
    (hfail : ¬PositiveNumberDetectionGuarantee d n p Ω σ mMin D
      (Nat.zero_lt_of_lt hn)) :
    ∃ E : ℝ, D < E ∧
      ¬PositiveNumberDetectionGuarantee d n p Ω σ mMin E
        (Nat.zero_lt_of_lt hn) := by
  unfold PositiveNumberDetectionGuarantee at hfail
  push Not at hfail
  obtain ⟨μ, hpositive, hmMin, hcluster, hsep, Y, hmeasurement,
    k, ν, hadmissible, hk⟩ := hfail
  obtain ⟨E, hDE, μ', hmMin', hAmp, hcluster', hsep', Y', hmeasurement', hadmissible'⟩ :=
    exists_larger_counterexample hn hΩ hσ p μ ν hmMin hcluster hsep
      Y hmeasurement hadmissible.2
  have hpositive' : μ'.IsPositive := by
    simpa [AtomicMeasure.IsPositive, hAmp] using hpositive
  refine ⟨E, hDE, ?_⟩
  intro hgood
  exact (not_le_of_gt hk)
    (hgood μ' hpositive' hmMin' hcluster' hsep' Y' hmeasurement'
      k ν ⟨hadmissible.1, hadmissible'⟩)

end

end NumDetect
end LeanNumDetect
