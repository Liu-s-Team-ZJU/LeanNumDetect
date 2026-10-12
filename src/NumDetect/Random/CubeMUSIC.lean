import RandSamp.CubeRandomModel
import NumDetect.MUSIC.Stability
import NumDetect.Preliminaries.SingularValueFacts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open LeanNumDetect.FiniteMatrixSampling
open LeanNumDetect.RandSamp
open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

private theorem probability_prod {α β : Type*} [Fintype α] [Fintype β]
    (P : α → Prop) (Q : β → Prop) :
    probability (fun p : α × β => P p.1 ∧ Q p.2) =
      probability P * probability Q := by
  classical
  simp only [probability, Fintype.card_prod, Nat.cast_mul]
  calc
    _ = (((Finset.univ : Finset α).filter P).card : ℝ) *
        (((Finset.univ : Finset β).filter Q).card : ℝ) /
        ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) := by
      congr 1
      rw [← Nat.cast_mul, ← Finset.card_product]
      congr 1
      apply congrArg Finset.card
      ext p
      simp
    _ = _ := by rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, _root_.mul_inv_rev]; ring

theorem probability_product_lower_bound {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (P : α → Prop) (Q : β → Prop) (ε : ℝ)
    (hP : 1 - ε / 2 ≤ probability P)
    (hQ : 1 - ε / 2 ≤ probability Q) :
    1 - ε ≤ probability (fun p : α × β => P p.1 ∧ Q p.2) := by
  rw [probability_prod]
  have hP1 := probability_le_one P
  have hQ1 := probability_le_one Q
  have hmul : 0 ≤ (1 - probability P) * (1 - probability Q) :=
    mul_nonneg (sub_nonneg.mpr hP1) (sub_nonneg.mpr hQ1)
  nlinarith

end LeanNumDetect.FiniteMatrixSampling

namespace LeanNumDetect.NumDetect

noncomputable section

/-- The physical positive frequency represented by a row of a sampled cube. -/
def positiveCubeFrequency {d L M : ℕ}
    (W : FiniteSample (CubeFrequency d L) M) : W.val → Point d :=
  fun k r => ((k.val r : Fin (L + 1)).val : ℝ)

theorem normalizedCubeVandermonde_eq
    {d L n M : ℕ} (W : FiniteSample (CubeFrequency d L) M)
    (Y : Fin n → Point d) :
    cubeSampledVandermonde M Y W.val =
      (Real.sqrt (M : ℝ) : ℂ)⁻¹ •
        generalizedVandermonde (positiveCubeFrequency W) Y := by
  ext k j
  rfl


theorem unnormalizedCubeVandermonde_eq
    {d L n M : ℕ} (hM : 0 < M)
    (W : FiniteSample (CubeFrequency d L) M)
    (Y : Fin n → Point d) :
    generalizedVandermonde (positiveCubeFrequency W) Y =
      (Real.sqrt (M : ℝ) : ℂ) • cubeSampledVandermonde M Y W.val := by
  rw [normalizedCubeVandermonde_eq]
  have hsqrt : (Real.sqrt (M : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (Nat.cast_pos.mpr hM)).ne'
  ext k j
  simp only [Matrix.smul_apply, smul_eq_mul]
  field_simp

theorem unnormalizedCubeVandermonde_minimumSingularValue
    {d L n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (W : FiniteSample (CubeFrequency d L) M)
    (Y : Fin n → Point d) {b : ℝ} (_hb : 0 ≤ b)
    (hsv : Real.sqrt b ≤
      matrixSingularValue (cubeSampledVandermonde M Y W.val) (n - 1)) :
    Real.sqrt (M : ℝ) * Real.sqrt b ≤
      matrixSingularValue (generalizedVandermonde (positiveCubeFrequency W) Y) (n - 1) := by
  let A := generalizedVandermonde (positiveCubeFrequency W) Y
  let B := cubeSampledVandermonde M Y W.val
  have hA : A = (Real.sqrt (M : ℝ) : ℂ) • B :=
    unnormalizedCubeVandermonde_eq hM W Y
  have haction (z : EuclideanSpace ℂ (Fin n)) :
      A.toEuclideanLin z = (Real.sqrt (M : ℝ) : ℂ) • B.toEuclideanLin z := by
    rw [hA]
    change toLp 2 (((Real.sqrt (M : ℝ) : ℂ) • B) *ᵥ ofLp z) = _
    rw [Matrix.smul_mulVec, toLp_smul]
    rfl
  have hlower (z : EuclideanSpace ℂ (Fin n)) :
      (Real.sqrt (M : ℝ) * Real.sqrt b) * ‖z‖ ≤ ‖A.toEuclideanLin z‖ := by
    have hnorm := matrix_lastSingularValue_mul_norm_le B (by simpa using hn) z
    have hcore := (mul_le_mul_of_nonneg_right hsv (norm_nonneg z)).trans
      (by simpa only [Fintype.card_fin] using hnorm)
    rw [haction, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      (Real.sqrt (M : ℝ) * Real.sqrt b) * ‖z‖ =
          Real.sqrt (M : ℝ) * (Real.sqrt b * ‖z‖) := by ring
      _ ≤ Real.sqrt (M : ℝ) * ‖B.toEuclideanLin z‖ :=
        mul_le_mul_of_nonneg_left hcore (Real.sqrt_nonneg _)
  have hi : n - 1 < Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using
      Nat.sub_lt hn Nat.zero_lt_one
  have htop : Module.finrank ℂ (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin n))) =
      (n - 1) + 1 := by
    simp only [finrank_top, finrank_euclideanSpace, Fintype.card_fin]
    omega
  exact le_singularValue_of_subspace_lower A.toEuclideanLin hi ⊤ htop
    (fun z _ => hlower z)


/-- Restoring the unnormalized manuscript Vandermonde matrix multiplies a
    nonnegative lower bound by the square root of the sample size. -/
theorem unnormalizedCubeVandermonde_singular_lower
    {d L n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (W : FiniteSample (CubeFrequency d L) M) (Y : Fin n → Point d)
    {b : ℝ} (hb : 0 ≤ b)
    (hsv : b ≤ matrixSingularValue (cubeSampledVandermonde M Y W.val) (n - 1)) :
    Real.sqrt (M : ℝ) * b ≤
      matrixSingularValue (generalizedVandermonde (positiveCubeFrequency W) Y) (n - 1) := by
  have h := unnormalizedCubeVandermonde_minimumSingularValue hn hM W Y
    (sq_nonneg b) (by simpa only [Real.sqrt_sq hb] using hsv)
  simpa only [Real.sqrt_sq hb] using h


/-- Abstract deterministic MUSIC stability for two positive-cube samples, with
    the exact normalization of the sampled Fourier matrices. -/
theorem positiveCubeMUSIC_correlation_stability_of_singularValues
    {d L n M₁ M₂ : ℕ} (μ : AtomicMeasure d n)
    (W : FiniteSample (CubeFrequency d L) M₁)
    (Z : FiniteSample (CubeFrequency d L) M₂)
    (E : Matrix W.val Z.val ℂ)
    (hn : 0 < n) (hrows : n < M₁) (hcolumns : n ≤ M₂)
    {a ρ σ : ℝ} (ha : 0 < a) (hρ : ρ < 1)
    (hrow : Real.sqrt ((1 - ρ) * a) ≤
      matrixSingularValue (cubeSampledVandermonde M₁ μ.node W.val) (n - 1))
    (hcolumn : Real.sqrt ((1 - ρ) * a) ≤
      matrixSingularValue (cubeSampledVandermonde M₂ μ.node Z.val) (n - 1))
    (hnoise : matrixSpectralNorm E ≤ σ * Real.sqrt (M₁ * M₂))
    (hsmall : 2 * σ < minAmplitude μ hn * ((1 - ρ) * a)) :
    correlationUniformDistance
      (rankNoiseSpaceCorrelation (positiveCubeFrequency W)
        (generalizedVandermonde (positiveCubeFrequency W) μ.node *
          Matrix.diagonal μ.amplitude *
          Matrix.transpose (generalizedVandermonde (positiveCubeFrequency Z) μ.node) + E) n)
      (rankNoiseSpaceCorrelation (positiveCubeFrequency W)
        (generalizedVandermonde (positiveCubeFrequency W) μ.node *
          Matrix.diagonal μ.amplitude *
          Matrix.transpose (generalizedVandermonde (positiveCubeFrequency Z) μ.node)) n) ≤
      2 * σ / (minAmplitude μ hn * ((1 - ρ) * a)) := by
  have hM₁ : 0 < M₁ := by omega
  have hM₂ : 0 < M₂ := by omega
  have hb : 0 < (1 - ρ) * a := mul_pos (sub_pos.mpr hρ) ha
  have hB : 0 < Real.sqrt ((1 - ρ) * a) := Real.sqrt_pos.2 hb
  have hsqrt₁ : 0 < Real.sqrt (M₁ : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hM₁)
  have hsqrt₂ : 0 < Real.sqrt (M₂ : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hM₂)
  have hsource : 0 < minAmplitude μ hn := minAmplitude_pos μ hn
  let V₁ := generalizedVandermonde (positiveCubeFrequency W) μ.node
  let V₂ := generalizedVandermonde (positiveCubeFrequency Z) μ.node
  have hrow' : Real.sqrt (M₁ : ℝ) * Real.sqrt ((1 - ρ) * a) ≤
      matrixSingularValue V₁ (n - 1) :=
    unnormalizedCubeVandermonde_minimumSingularValue hn hM₁ W μ.node hb.le hrow
  have hcolumn' : Real.sqrt (M₂ : ℝ) * Real.sqrt ((1 - ρ) * a) ≤
      matrixSingularValue V₂ (n - 1) :=
    unnormalizedCubeVandermonde_minimumSingularValue hn hM₂ Z μ.node hb.le hcolumn
  have hfull₁ : HasFullColumnRank V₁ :=
    fullColumnRank_of_lastSingularValue_pos V₁ hn
      ((mul_pos hsqrt₁ hB).trans_le hrow')
  have hfull₂ : HasFullColumnRank V₂ :=
    fullColumnRank_of_lastSingularValue_pos V₂ hn
      ((mul_pos hsqrt₂ hB).trans_le hcolumn')
  let G := minAmplitude μ hn * (Real.sqrt (M₁ * M₂) * ((1 - ρ) * a))
  have hsqrtprod : Real.sqrt (M₁ * M₂ : ℝ) =
      Real.sqrt (M₁ : ℝ) * Real.sqrt (M₂ : ℝ) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg M₁)]
  have hGpos : 0 < G := by
    dsimp [G]
    exact mul_pos hsource (mul_pos (by positivity) hb)
  have hGle : G ≤ musicSignalGap (positiveCubeFrequency W)
      (positiveCubeFrequency Z) μ hn := by
    have hproduct :
        (Real.sqrt (M₁ : ℝ) * Real.sqrt ((1 - ρ) * a)) *
          (Real.sqrt (M₂ : ℝ) * Real.sqrt ((1 - ρ) * a)) ≤
        matrixSingularValue V₁ (n - 1) * matrixSingularValue V₂ (n - 1) := by
      exact mul_le_mul hrow' hcolumn'
        (mul_nonneg hsqrt₂.le (Real.sqrt_nonneg _))
        (matrixSingularValue_nonneg _ _)
    calc
      G = minAmplitude μ hn *
          ((Real.sqrt (M₁ : ℝ) * Real.sqrt ((1 - ρ) * a)) *
            (Real.sqrt (M₂ : ℝ) * Real.sqrt ((1 - ρ) * a))) := by
        dsimp [G]
        rw [hsqrtprod]
        calc
          minAmplitude μ hn *
              (Real.sqrt (M₁ : ℝ) * Real.sqrt (M₂ : ℝ) * ((1 - ρ) * a)) =
            minAmplitude μ hn *
              (Real.sqrt (M₁ : ℝ) * Real.sqrt (M₂ : ℝ) *
                Real.sqrt ((1 - ρ) * a) ^ 2) := by rw [Real.sq_sqrt hb.le]
          _ = _ := by ring
      _ ≤ minAmplitude μ hn *
          (matrixSingularValue V₁ (n - 1) * matrixSingularValue V₂ (n - 1)) :=
        mul_le_mul_of_nonneg_left hproduct hsource.le
      _ = musicSignalGap (positiveCubeFrequency W)
          (positiveCubeFrequency Z) μ hn := by
        unfold musicSignalGap V₁ V₂
        ring
  have hsmallGap : 2 * matrixSpectralNorm E <
      musicSignalGap (positiveCubeFrequency W) (positiveCubeFrequency Z) μ hn := by
    have hsqrtpos : 0 < Real.sqrt (M₁ * M₂ : ℝ) := by positivity
    have hscaled : 2 * σ * Real.sqrt (M₁ * M₂ : ℝ) < G := by
      dsimp [G]
      nlinarith [mul_lt_mul_of_pos_right hsmall hsqrtpos]
    have hnoiseScaled :
        2 * matrixSpectralNorm E ≤ 2 * σ * Real.sqrt (M₁ * M₂ : ℝ) := by
      nlinarith [hnoise]
    exact (hnoiseScaled.trans_lt hscaled).trans_le hGle
  have hcard₁ : n < Fintype.card W.val := by simpa [W.property] using hrows
  have hcard₂ : n ≤ Fintype.card Z.val := by simpa [Z.property] using hcolumns
  have hgeneral := ghmMUSIC_correlation_stability
    (positiveCubeFrequency W) (positiveCubeFrequency Z) μ μ.amplitude E
    hn hcard₁ hcard₂ (fun j => minAmplitude_le μ hn j)
    hfull₁ hfull₂ hsmallGap
  have hfrac :
      2 * matrixSpectralNorm E /
          musicSignalGap (positiveCubeFrequency W) (positiveCubeFrequency Z) μ hn ≤
      2 * σ / (minAmplitude μ hn * ((1 - ρ) * a)) := by
    have hnum : 0 ≤ 2 * matrixSpectralNorm E :=
      mul_nonneg (by norm_num) (norm_nonneg _)
    have hstep :
        2 * matrixSpectralNorm E /
            musicSignalGap (positiveCubeFrequency W) (positiveCubeFrequency Z) μ hn ≤
        2 * matrixSpectralNorm E / G :=
      div_le_div_of_nonneg_left hnum hGpos hGle
    have hnumle : 2 * matrixSpectralNorm E ≤
        2 * σ * Real.sqrt (M₁ * M₂ : ℝ) := by nlinarith [hnoise]
    have hstep' :
        2 * matrixSpectralNorm E / G ≤
          (2 * σ * Real.sqrt (M₁ * M₂ : ℝ)) / G :=
      div_le_div_of_nonneg_right hnumle hGpos.le
    calc
      _ ≤ 2 * matrixSpectralNorm E / G := hstep
      _ ≤ (2 * σ * Real.sqrt (M₁ * M₂ : ℝ)) / G := hstep'
      _ = 2 * σ / (minAmplitude μ hn * ((1 - ρ) * a)) := by
        dsimp [G]
        have hne : Real.sqrt (M₁ * M₂ : ℝ) ≠ 0 := by positivity
        field_simp
  exact hgeneral.trans hfrac

private theorem positiveCubeFrequency_sum_in_band
    {d L M₁ M₂ : ℕ} {Ω : ℝ}
    (W : FiniteSample (CubeFrequency d L) M₁)
    (Z : FiniteSample (CubeFrequency d L) M₂)
    (hΩ : (2 * L : ℝ) ≤ Ω)
    (i : W.val) (j : Z.val) :
    InFrequencyBand Ω (positiveCubeFrequency W i + positiveCubeFrequency Z j) := by
  intro k
  change |(((i.val k).val : ℝ) + ((j.val k).val : ℝ))| ≤ Ω
  have hi : (((i.val k).val : ℝ)) ≤ L := by
    exact_mod_cast Nat.le_of_lt_succ (i.val k).isLt
  have hj : (((j.val k).val : ℝ)) ≤ L := by
    exact_mod_cast Nat.le_of_lt_succ (j.val k).isLt
  rw [abs_of_nonneg (by positivity)]
  linarith

private theorem cubeGHM_sub_fourier_entry_lt
    {d n L M₁ M₂ : ℕ} {Ω σ : ℝ}
    (W : FiniteSample (CubeFrequency d L) M₁)
    (Z : FiniteSample (CubeFrequency d L) M₂)
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (hmeasurement : IsBandMeasurement μ Ω σ Y)
    (hΩ : (2 * L : ℝ) ≤ Ω)
    (i : W.val) (j : Z.val) :
    ‖(generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z) Y -
        generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z) (fourier μ)) i j‖ < σ := by
  rcases hmeasurement with ⟨noise, hnoise, hY⟩
  let ω := positiveCubeFrequency W i + positiveCubeFrequency Z j
  have hω : InFrequencyBand Ω ω :=
    positiveCubeFrequency_sum_in_band W Z hΩ i j
  have hvalue := hY ω hω
  have hsmall := hnoise ω hω
  simp only [generalizedHankel, Matrix.sub_apply]
  rw [hvalue, add_sub_cancel_left]
  exact hsmall

/-- A bounded band-query measurement gives a deterministic noise-norm bound
    for every pair of positive-cube subsets, including repeated frequency sums. -/
theorem positiveCubeGHM_noise_spectralNorm_lt
    {d n L M₁ M₂ : ℕ} {Ω σ : ℝ}
    (W : FiniteSample (CubeFrequency d L) M₁)
    (Z : FiniteSample (CubeFrequency d L) M₂)
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (hmeasurement : IsBandMeasurement μ Ω σ Y)
    (hΩ : (2 * L : ℝ) ≤ Ω)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) :
    matrixSpectralNorm
        (generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z) Y -
          generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z) (fourier μ)) <
      σ * Real.sqrt (M₁ * M₂) := by
  classical
  let E := generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z) Y -
    generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z) (fourier μ)
  have hcard₁ : Fintype.card W.val = M₁ := by simp [W.property]
  have hcard₂ : Fintype.card Z.val = M₂ := by simp [Z.property]
  letI : Nonempty W.val := Fintype.card_pos_iff.mp (by omega)
  letI : Nonempty Z.val := Fintype.card_pos_iff.mp (by omega)
  have hentry : ∀ i j, ‖E i j‖ < σ := by
    intro i j
    exact cubeGHM_sub_fourier_entry_lt W Z μ Y hmeasurement hΩ i j
  have hσ : 0 < σ := by
    let i : W.val := Classical.choice inferInstance
    let j : Z.val := Classical.choice inferInstance
    exact (norm_nonneg (E i j)).trans_lt (hentry i j)
  simpa only [hcard₁, hcard₂] using
    (matrixSpectralNorm_lt_card_sqrt E hσ hentry)

end
end LeanNumDetect.NumDetect
