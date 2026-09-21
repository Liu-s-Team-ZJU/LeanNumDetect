import NumDetect.UniformVandermonde
import NumDetect.MatrixFacts

/-!
Complete support lemmas for the two threshold results in `NumDetect.Uniform`.

The final two theorems below deliberately use distinct names.  This file can
therefore check their complete proofs without changing the manuscript-facing
declarations in `Uniform.lean`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Every frequency queried by a contiguous-grid GHM lies in its declared band. -/
theorem uniform_query_in_band
    {d s : ℕ} {Ω : ℝ} (hΩ : 0 ≤ Ω) (hs : 0 < s)
    (α β : UniformIndex d s) :
    InFrequencyBand Ω (fun k =>
      Ω / s * ((α k : ℝ) + (β k : ℝ) - s)) := by
  intro k
  have hα : (α k : ℕ) ≤ s := Nat.le_of_lt_succ (α k).isLt
  have hβ : (β k : ℕ) ≤ s := Nat.le_of_lt_succ (β k).isLt
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hαR : (α k : ℝ) ≤ s := by exact_mod_cast hα
  have hβR : (β k : ℝ) ≤ s := by exact_mod_cast hβ
  rw [abs_le]
  constructor
  · have hα0 : (0 : ℝ) ≤ α k := by positivity
    have hβ0 : (0 : ℝ) ≤ β k := by positivity
    have hsum : -(s : ℝ) ≤ (α k : ℝ) + (β k : ℝ) - s := by linarith
    have := mul_le_mul_of_nonneg_left hsum (div_nonneg hΩ hsR.le)
    calc
      -Ω = Ω / s * (-(s : ℝ)) := by field_simp
      _ ≤ _ := this
  · have hsum : (α k : ℝ) + (β k : ℝ) - s ≤ s := by linarith
    have := mul_le_mul_of_nonneg_left hsum (div_nonneg hΩ hsR.le)
    calc
      _ ≤ Ω / s * (s : ℝ) := this
      _ = Ω := by field_simp

/-- The contiguous measurement perturbation is pointwise strictly below `σ`. -/
theorem uniformMeasurementMatrix_sub_fourier_entry_lt
    {d n s : ℕ} {Ω σ : ℝ}
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (hΩ : 0 ≤ Ω) (hs : 0 < s)
    (hmeasurement : IsBandMeasurement μ Ω σ Y)
    (α β : UniformIndex d s) :
    ‖(uniformMeasurementMatrix s Ω Y -
        uniformMeasurementMatrix s Ω (fourier μ)) α β‖ < σ := by
  rcases hmeasurement with ⟨W, hW, hY⟩
  let ω : Point d := fun k =>
    Ω / s * ((α k : ℝ) + (β k : ℝ) - s)
  have hband : InFrequencyBand Ω ω :=
    uniform_query_in_band hΩ hs α β
  have hvalue := hY ω hband
  have hnoise := hW ω hband
  simp only [uniformMeasurementMatrix, Matrix.sub_apply]
  rw [hvalue, add_sub_cancel_left]
  exact hnoise

/-- The noiseless contiguous matrix has rank at most the source count. -/
theorem uniformNoiseless_rank_le
    {d n s : ℕ} (Ω : ℝ) (μ : AtomicMeasure d n) :
    (uniformNoiselessMatrix s Ω μ).rank ≤ n := by
  rw [uniformNoiselessMatrix]
  exact
    (Matrix.rank_mul_le_left
      (uniformVandermonde s Ω μ.node *
        Matrix.diagonal (uniformPhaseAmplitude Ω μ))
      (uniformVandermonde s Ω μ.node)ᵀ).trans
      ((Matrix.rank_le_card_width
        (uniformVandermonde s Ω μ.node *
          Matrix.diagonal (uniformPhaseAmplitude Ω μ))).trans (by simp))

/-- Consequently all noiseless singular values from index `n` onward vanish. -/
theorem uniformNoiseless_singularValue_eq_zero
    {d n s i : ℕ} (Ω : ℝ) (μ : AtomicMeasure d n) (hi : n ≤ i) :
    matrixSingularValue (uniformNoiselessMatrix s Ω μ) i = 0 :=
  matrixSingularValue_eq_zero_of_rank_le _ ((uniformNoiseless_rank_le Ω μ).trans hi)

/-- The uniform multi-index cube has `(s+1)^d` elements. -/
theorem card_uniformIndex (d s : ℕ) :
    Fintype.card (UniformIndex d s) = (s + 1) ^ d := by
  simp [UniformIndex]

/-- Positivity of the last column singular value implies full column rank. -/
theorem fullColumnRank_of_lastSingularValue_pos_uniform
    {m : Type*} [Fintype m] {n : ℕ}
    (A : Matrix m (Fin n) ℂ) (hn : 0 < n)
    (hA : 0 < matrixSingularValue A (n - 1)) :
    HasFullColumnRank A := by
  have hinjective : Function.Injective A.toEuclideanLin := by
    rw [A.toEuclideanLin.injective_iff_forall_lt_finrank_singularValues_pos]
    intro i hi
    have hi' : i < n := by
      simpa only [finrank_euclideanSpace, Fintype.card_fin] using hi
    exact hA.trans_le
      (A.toEuclideanLin.singularValues_antitone (by omega))
  intro x y hxy
  apply WithLp.toLp_injective
  apply hinjective
  change WithLp.toLp 2 (A *ᵥ x) = WithLp.toLp 2 (A *ᵥ y)
  exact congrArg (WithLp.toLp 2) hxy

/-- A strict squared Vandermonde lower bound gives the required noiseless gap. -/
theorem uniformNoiseless_singularValue_gt_of_lowerBound_sq
    {d n s : ℕ} {Ω σ mMin B : ℝ}
    (μ : AtomicMeasure d n) (hn : 0 < n)
    (hcard : n ≤ (s + 1) ^ d)
    (hmMin : minAmplitude μ hn = mMin)
    (hBpos : 0 < B)
    (hV : B ≤ matrixSingularValue (uniformVandermonde s Ω μ.node) (n - 1))
    (hgap : 2 * (((s + 1) ^ d : ℕ) : ℝ) * σ < mMin * B ^ 2) :
    2 * (((s + 1) ^ d : ℕ) : ℝ) * σ <
      matrixSingularValue (uniformNoiselessMatrix s Ω μ) (n - 1) := by
  let V := uniformVandermonde s Ω μ.node
  have hVpos : 0 < matrixSingularValue V (n - 1) := hBpos.trans_le hV
  have hfull : HasFullColumnRank V :=
    fullColumnRank_of_lastSingularValue_pos_uniform V hn hVpos
  have hmPos : 0 < mMin := by
    rw [← hmMin]
    exact minAmplitude_pos μ hn
  have hproduct :
      mMin * matrixSingularValue V (n - 1) *
          matrixSingularValue V (n - 1) ≤
        matrixSingularValue (uniformNoiselessMatrix s Ω μ) (n - 1) := by
    rw [uniformNoiselessMatrix]
    simpa only [V, Fintype.card_fin] using
      (matrixSingularValue_diagonal_transpose_lower_of_fullColumnRank
        V (uniformPhaseAmplitude Ω μ) V hn (by simpa using hcard) hfull hmPos.le
        (fun j => by
          rw [norm_uniformPhaseAmplitude, ← hmMin]
          exact minAmplitude_le μ hn j))
  calc
    2 * (((s + 1) ^ d : ℕ) : ℝ) * σ
        < mMin * B ^ 2 := hgap
    _ ≤ mMin * matrixSingularValue V (n - 1) *
          matrixSingularValue V (n - 1) := by
      have hsquare :
          B ^ 2 ≤ matrixSingularValue V (n - 1) ^ 2 :=
        (sq_le_sq₀ hBpos.le (matrixSingularValue_nonneg V (n - 1))).2 hV
      calc
        mMin * B ^ 2 ≤
            mMin * matrixSingularValue V (n - 1) ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare hmPos.le
        _ = _ := by ring
    _ ≤ _ := hproduct

/-- The separation threshold is exactly strong enough to make the squared
uniform Vandermonde lower bound dominate twice the noise threshold. -/
theorem uniformSeparation_implies_lowerBound_sq_gap
    {d n s : ℕ} {Ω σ mMin : ℝ}
    (node : Fin n → Point d) (hn : 2 ≤ n)
    (hΩ : 0 < Ω) (hσ : 0 < σ) (hmMin : 0 < mMin)
    (hseparation :
      uniformDetectionSeparationThreshold (d := d) (n := n) s Ω σ mMin <
        minimumL1Separation node hn) :
    2 * (((s + 1) ^ d : ℕ) : ℝ) * σ <
      mMin * uniformVandermondeLowerBound s Ω node hn ^ 2 := by
  let q : ℝ := (((2 * (s / (2 * n)) + 1) ^ d : ℕ) : ℝ)
  let sampleCount : ℝ := (((s + 1) ^ d : ℕ) : ℝ)
  let exponent : ℕ := 2 * (n - 1)
  let base : ℝ := (n * 2 ^ n : ℝ) / (mMin * q) * sampleCount * σ
  let theta : ℝ := normalizedMinimumSeparation Ω node hn
  have hnpos : 0 < n := by omega
  have hexponent : 0 < exponent := by omega
  have hexponentR : (0 : ℝ) < exponent := by exact_mod_cast hexponent
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hsample : 0 < sampleCount := by
    dsimp [sampleCount]
    positivity
  have hbase : 0 ≤ base := by
    dsimp [base]
    positivity
  have hscale : 0 < Ω / (2 * (n : ℝ) * Real.pi) := by positivity
  have hexponent_cast :
      (exponent : ℝ) = 2 * (n : ℝ) - 2 := by
    dsimp [exponent]
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ n)]
    ring_nf
  have hroot :
      base ^ (exponent : ℝ)⁻¹ < theta := by
    have hscaled :=
      mul_lt_mul_of_pos_left hseparation hscale
    rw [uniformDetectionSeparationThreshold] at hscaled
    change
      Ω / (2 * (n : ℝ) * Real.pi) *
          (2 * (n : ℝ) * Real.pi / Ω *
            ((n * 2 ^ n : ℝ) /
                (mMin * (((2 * (s / (2 * n)) + 1 : ℕ) : ℝ) ^ d)) *
              (((s + 1 : ℕ) : ℝ) ^ d) * σ) ^
              (1 / (2 * (n : ℝ) - 2))) <
        Ω / (2 * (n : ℝ) * Real.pi) *
          minimumL1Separation node hn at hscaled
    have hq_cast :
        (((2 * (s / (2 * n)) + 1 : ℕ) : ℝ) ^ d) = q := by
      simp only [q, Nat.cast_pow]
    have hsample_cast :
        (((s + 1 : ℕ) : ℝ) ^ d) = sampleCount := by
      simp only [sampleCount, Nat.cast_pow]
    rw [hq_cast, hsample_cast] at hscaled
    change
      Ω / (2 * (n : ℝ) * Real.pi) *
          (2 * (n : ℝ) * Real.pi / Ω *
            base ^ (1 / (2 * (n : ℝ) - 2))) <
        Ω / (2 * (n : ℝ) * Real.pi) *
          minimumL1Separation node hn at hscaled
    have hcancel :
        Ω / (2 * (n : ℝ) * Real.pi) *
            (2 * (n : ℝ) * Real.pi / Ω *
              base ^ (1 / (2 * (n : ℝ) - 2))) =
          base ^ (1 / (2 * (n : ℝ) - 2)) := by
      field_simp
    rw [hcancel] at hscaled
    change
      base ^ (1 / (2 * (n : ℝ) - 2)) < theta at hscaled
    rw [show 1 / (2 * (n : ℝ) - 2) = (exponent : ℝ)⁻¹ by
      rw [hexponent_cast]
      exact one_div _] at hscaled
    exact hscaled
  have htheta : 0 < theta :=
    (Real.rpow_nonneg hbase _).trans_lt hroot
  have hpower : base < theta ^ exponent := by
    have h := (Real.rpow_inv_lt_iff_of_pos hbase htheta.le hexponentR).1 hroot
    simpa only [Real.rpow_natCast] using h
  have hpow_split :
      theta ^ exponent = (theta ^ (n - 1)) ^ 2 := by
    dsimp [exponent]
    rw [show 2 * (n - 1) = (n - 1) + (n - 1) by omega, pow_add, pow_two]
  rw [hpow_split] at hpower
  have hnoiseGap :
      2 * sampleCount * σ <
        mMin * (1 / ((n : ℝ) * 2 ^ (n - 1)) * q) *
          (theta ^ (n - 1)) ^ 2 := by
    have hden : 0 < mMin * q := mul_pos hmMin hq
    have hnscale : 0 < (n : ℝ) * 2 ^ (n - 1) := by positivity
    have hbase_eq :
        base =
          (2 * ((n : ℝ) * 2 ^ (n - 1)) * sampleCount * σ) /
            (mMin * q) := by
      have hpowtwo : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
        calc
          (2 : ℝ) ^ n = 2 ^ ((n - 1) + 1) := by congr 1; omega
          _ = 2 * 2 ^ (n - 1) := by rw [pow_add]; ring
      dsimp [base]
      rw [hpowtwo]
      ring
    rw [hbase_eq] at hpower
    have hmul := (div_lt_iff₀ hden).1 hpower
    rw [show
      mMin * (1 / ((n : ℝ) * 2 ^ (n - 1)) * q) *
          (theta ^ (n - 1)) ^ 2 =
        ((theta ^ (n - 1)) ^ 2 * (mMin * q)) /
          ((n : ℝ) * 2 ^ (n - 1)) by
      field_simp]
    apply (lt_div_iff₀ hnscale).2
    convert hmul using 1
    all_goals ring
  have hsquare :
      uniformVandermondeLowerBound s Ω node hn ^ 2 =
        (1 / ((n : ℝ) * 2 ^ (n - 1)) * q) *
          (theta ^ (n - 1)) ^ 2 := by
    rw [uniformVandermondeLowerBound, mul_pow,
      Real.sq_sqrt (by positivity :
        0 ≤ 1 / ((n : ℝ) * 2 ^ (n - 1)) *
          (((2 * (s / (2 * n)) + 1 : ℕ) : ℝ) ^ d))]
    simp only [q, theta, normalizedMinimumSeparation, Nat.cast_pow]
  rw [hsquare]
  simpa only [mul_assoc] using hnoiseGap

/-- Complete auxiliary version of `uniformGHM_singularValueThreshold`. -/
theorem uniformGHM_singularValueThreshold_support
    {d n s : ℕ} {Ω σ mMin : ℝ}
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hΩ : 0 < Ω) (hσ : 0 < σ)
    (hmMin : minAmplitude μ (Nat.zero_lt_of_lt hn) = mMin)
    (hcluster : ∀ j, InOpenL1Ball (Real.pi * n / Ω) 0 (μ.node j))
    (hs : 4 * n ≤ s) (hseven : Even s)
    (hnoise : σ < mMin)
    (hmeasurement : IsBandMeasurement μ Ω σ Y) :
    (∀ j, n ≤ j → j < (s + 1) ^ d →
      matrixSingularValue (uniformMeasurementMatrix s Ω Y) j ≤
        ((s + 1 : ℕ) : ℝ) ^ d * σ) ∧
    (uniformDetectionSeparationThreshold (d := d) (n := n) s Ω σ mMin <
        minimumL1Separation μ.node hn →
      ((s + 1 : ℕ) : ℝ) ^ d * σ <
        matrixSingularValue (uniformMeasurementMatrix s Ω Y) (n - 1)) := by
  let G := uniformMeasurementMatrix s Ω Y
  let G₀ := uniformNoiselessMatrix s Ω μ
  let Δ := G - G₀
  let sampleCount : ℝ := (((s + 1) ^ d : ℕ) : ℝ)
  have hnpos : 0 < n := by omega
  have hspos : 0 < s := by omega
  have hcardpos : 0 < (s + 1) ^ d := by positivity
  have hsampleCountPos : 0 < sampleCount := by
    dsimp [sampleCount]
    positivity
  have hsamples : n ≤ (s + 1) ^ d := by
    exact (show n ≤ s + 1 by omega).trans (Nat.le_pow (by omega))
  letI : Nonempty (UniformIndex d s) :=
    Fintype.card_pos_iff.mp (by simpa [card_uniformIndex] using hcardpos)
  have hfactor :
      uniformMeasurementMatrix s Ω (fourier μ) = G₀ :=
    uniformMeasurementMatrix_fourier_eq_noiseless s Ω μ hspos
  have hGfourier :
      G - uniformMeasurementMatrix s Ω (fourier μ) = Δ := by
    rw [hfactor]
  have hΔentry : ∀ α β, ‖Δ α β‖ < σ := by
    intro α β
    rw [← hGfourier]
    exact uniformMeasurementMatrix_sub_fourier_entry_lt
      μ Y hΩ.le hspos hmeasurement α β
  have hΔnorm : matrixSpectralNorm Δ ≤ sampleCount * σ := by
    have h := matrixSpectralNorm_le_card_sqrt_mul_of_lt Δ hΔentry
    have hsqrt :
        Real.sqrt
            (((s + 1) ^ d : ℕ) * ((s + 1) ^ d : ℕ)) =
          sampleCount := by
      rw [Real.sqrt_mul_self]
      exact_mod_cast (Nat.zero_le ((s + 1) ^ d))
    have h' :
        matrixSpectralNorm Δ ≤
          Real.sqrt
              (((s + 1) ^ d : ℕ) * ((s + 1) ^ d : ℕ)) * σ := by
      simpa [UniformIndex] using h
    rw [hsqrt] at h'
    simpa only [mul_comm] using h'
  have hsum : G = G₀ + Δ := by
    dsimp [Δ]
    abel
  have htail :
      ∀ j, n ≤ j → j < (s + 1) ^ d →
        matrixSingularValue G j ≤ sampleCount * σ := by
    intro j hj hjcard
    have hperturb :=
      matrixSingularValue_add_le_add_spectralNorm G₀ Δ
        (i := j) (by simpa [card_uniformIndex] using hjcard)
    have hzero : matrixSingularValue G₀ j = 0 :=
      uniformNoiseless_singularValue_eq_zero Ω μ hj
    rw [← hsum, hzero, zero_add] at hperturb
    exact hperturb.trans hΔnorm
  refine ⟨?_, ?_⟩
  · intro j hj hjcard
    simpa only [G, sampleCount, Nat.cast_pow] using htail j hj hjcard
  · intro hseparation
    have hmPos : 0 < mMin := hσ.trans hnoise
    have hgap :=
      uniformSeparation_implies_lowerBound_sq_gap μ.node hn hΩ hσ hmPos
        hseparation
    have hminimum : 0 < minimumL1Separation μ.node hn := by
      apply (show 0 <
          uniformDetectionSeparationThreshold
            (d := d) (n := n) s Ω σ mMin by
        rw [uniformDetectionSeparationThreshold]
        positivity).trans hseparation
    have htheta :
        0 < normalizedMinimumSeparation Ω μ.node hn := by
      rw [normalizedMinimumSeparation]
      positivity
    let B := uniformVandermondeLowerBound s Ω μ.node hn
    have hBnonneg : 0 ≤ B := by
      dsimp [B, uniformVandermondeLowerBound]
      positivity
    have hBpos : 0 < B := by
      have hpositive : 0 < mMin * B ^ 2 := by
        exact (mul_pos (mul_pos (by norm_num) hsampleCountPos) hσ).trans hgap
      rcases lt_or_eq_of_le hBnonneg with hBpos | hBzero
      · exact hBpos
      · rw [← hBzero] at hpositive
        norm_num at hpositive
    have hV :
        B ≤ matrixSingularValue (uniformVandermonde s Ω μ.node) (n - 1) := by
      exact uniformVandermonde_minimumSingularValue
        μ hd hn hΩ hcluster hs hseven
    have hnoiseless :
        2 * sampleCount * σ < matrixSingularValue G₀ (n - 1) := by
      exact uniformNoiseless_singularValue_gt_of_lowerBound_sq
        μ hnpos hsamples hmMin hBpos hV (by
          simpa only [sampleCount, Nat.cast_pow] using hgap)
    have hweyl :=
      matrixSingularValue_sub_spectralNorm_le_add G₀ (G - G₀)
        (i := n - 1) (by
          rw [card_uniformIndex]
          omega)
    have hadd : G₀ + (G - G₀) = G := by abel
    rw [hadd] at hweyl
    have hperturb :
        matrixSingularValue G₀ (n - 1) - matrixSpectralNorm Δ ≤
          matrixSingularValue G (n - 1) := by
      have heq : G - G₀ = Δ := rfl
      simpa only [heq] using hweyl
    have hresult : sampleCount * σ < matrixSingularValue G (n - 1) := by
      linarith
    simpa only [G, sampleCount, Nat.cast_pow] using hresult

/-- Elementary source-count bound used in the specialization `s = 4n`. -/
theorem sourceCount_mul_two_pow_le_eight_pow
    {n : ℕ} (hn : 2 ≤ n) :
    n * 2 ^ n ≤ 8 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        (n + 1) * 2 ^ (n + 1)
            = 2 * (n + 1) * 2 ^ n := by
              rw [pow_succ]
              ring
        _ ≤ 8 * (n * 2 ^ n) := by
          simpa only [mul_assoc] using
            Nat.mul_le_mul_right (2 ^ n) (show 2 * (n + 1) ≤ 8 * n by omega)
        _ ≤ 8 * 8 ^ (n - 1) := Nat.mul_le_mul_left 8 ih
        _ = 8 ^ n := by
          calc
            8 * 8 ^ (n - 1) = 8 ^ (n - 1) * 8 := by ring
            _ = 8 ^ ((n - 1) + 1) := (pow_succ _ _).symm
            _ = 8 ^ n := by congr 1; omega
        _ = 8 ^ (n + 1 - 1) := by congr 1

/-- The spatial sample-count factor is bounded by the explicit paper constant. -/
theorem four_mul_add_one_mul_five_pow_le_nine_pow
    {n : ℕ} (hn : 2 ≤ n) :
    (4 * n + 1) * 5 ^ (n - 2) ≤ 9 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        (4 * (n + 1) + 1) * 5 ^ (n + 1 - 2)
            = (5 * (4 * n + 5)) * 5 ^ (n - 2) := by
              rw [show n + 1 - 2 = (n - 2) + 1 by omega, pow_succ]
              ring
        _ ≤ (9 * (4 * n + 1)) * 5 ^ (n - 2) := by
          exact Nat.mul_le_mul_right (5 ^ (n - 2))
            (show 5 * (4 * n + 5) ≤ 9 * (4 * n + 1) by omega)
        _ = 9 * ((4 * n + 1) * 5 ^ (n - 2)) := by ring
        _ ≤ 9 * 9 ^ (n - 1) := Nat.mul_le_mul_left 9 ih
        _ = 9 ^ n := by
          calc
            9 * 9 ^ (n - 1) = 9 ^ (n - 1) * 9 := by ring
            _ = 9 ^ ((n - 1) + 1) := (pow_succ _ _).symm
            _ = 9 ^ n := by congr 1; omega
        _ = 9 ^ (n + 1 - 1) := by congr 1

/-- The source-count component of the threshold root is at most `2√2`. -/
theorem sourceCount_rpow_le_two_sqrt_two
    {n : ℕ} (hn : 2 ≤ n) :
    ((n * 2 ^ n : ℕ) : ℝ) ^
        (1 / (2 * (n : ℝ) - 2)) ≤
      2 * Real.sqrt 2 := by
  let exponent : ℕ := 2 * (n - 1)
  have hexponent : 0 < exponent := by omega
  have hexponentR : (0 : ℝ) < exponent := by exact_mod_cast hexponent
  have hexponent_cast :
      (exponent : ℝ) = 2 * (n : ℝ) - 2 := by
    dsimp [exponent]
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ n)]
    ring_nf
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrhsPower :
      (2 * Real.sqrt 2) ^ (exponent : ℝ) =
        (8 : ℝ) ^ (n - 1) := by
    rw [Real.rpow_natCast]
    change (2 * Real.sqrt 2) ^ (2 * (n - 1)) = _
    rw [pow_mul, mul_pow, hsqrt]
    norm_num
  rw [show 1 / (2 * (n : ℝ) - 2) = (exponent : ℝ)⁻¹ by
    rw [hexponent_cast]
    exact one_div _]
  rw [Real.rpow_inv_le_iff_of_pos (by positivity)
    (by positivity) hexponentR]
  rw [hrhsPower]
  exact_mod_cast sourceCount_mul_two_pow_le_eight_pow hn

/-- The uniform-grid side-length root is at most `3/√5`. -/
theorem uniformSide_rpow_le_three_div_sqrt_five
    {n : ℕ} (hn : 2 ≤ n) :
    (((4 * n + 1 : ℕ) : ℝ) / 5) ^
        (1 / (2 * (n : ℝ) - 2)) ≤
      3 / Real.sqrt 5 := by
  let exponent : ℕ := 2 * (n - 1)
  have hexponent : 0 < exponent := by omega
  have hexponentR : (0 : ℝ) < exponent := by exact_mod_cast hexponent
  have hexponent_cast :
      (exponent : ℝ) = 2 * (n : ℝ) - 2 := by
    dsimp [exponent]
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ n)]
    ring_nf
  have hsqrtPos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hrhsPower :
      (3 / Real.sqrt 5) ^ (exponent : ℝ) =
        ((9 : ℝ) / 5) ^ (n - 1) := by
    rw [Real.rpow_natCast]
    change (3 / Real.sqrt 5) ^ (2 * (n - 1)) = _
    rw [pow_mul, div_pow, hsqrt]
    norm_num
  have hratio :
      (((4 * n + 1 : ℕ) : ℝ) / 5) ≤
        ((9 : ℝ) / 5) ^ (n - 1) := by
    have hreal :
        (((4 * n + 1) * 5 ^ (n - 2) : ℕ) : ℝ) ≤
          ((9 ^ (n - 1) : ℕ) : ℝ) := by
      exact_mod_cast four_mul_add_one_mul_five_pow_le_nine_pow hn
    have hfive :
        (5 : ℝ) ^ (n - 1) = 5 ^ (n - 2) * 5 := by
      calc
        (5 : ℝ) ^ (n - 1) = 5 ^ ((n - 2) + 1) := by congr 1; omega
        _ = 5 ^ (n - 2) * 5 := pow_succ _ _
    rw [div_pow]
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 5)
      (by positivity : (0 : ℝ) < 5 ^ (n - 1))).2
    rw [hfive]
    have hmul := mul_le_mul_of_nonneg_right hreal (by norm_num : (0 : ℝ) ≤ 5)
    calc
      ((4 * n + 1 : ℕ) : ℝ) * (5 ^ (n - 2) * 5)
          = (((4 * n + 1) * 5 ^ (n - 2) : ℕ) : ℝ) * 5 := by
            push_cast
            ring
      _ ≤ ((9 ^ (n - 1) : ℕ) : ℝ) * 5 := hmul
      _ = (9 : ℝ) ^ (n - 1) * 5 := by norm_num
  rw [show 1 / (2 * (n : ℝ) - 2) = (exponent : ℝ)⁻¹ by
    rw [hexponent_cast]
    exact one_div _]
  rw [Real.rpow_inv_le_iff_of_pos (by positivity)
    (div_nonneg (by norm_num) hsqrtPos.le) hexponentR]
  rw [hrhsPower]
  exact hratio

/-- At `s = 4n`, the uniform threshold is bounded by the explicit
number-detection constant. -/
theorem uniformDetectionThreshold_four_mul_le_numberDetectionThreshold
    {d n : ℕ} {Ω σ mMin : ℝ}
    (hn : 2 ≤ n) (hΩ : 0 < Ω) (hσ : 0 < σ) (hmMin : 0 < mMin) :
    uniformDetectionSeparationThreshold (d := d) (n := n)
        (4 * n) Ω σ mMin ≤
      numberDetectionSeparationThreshold d n Ω σ mMin := by
  let exponentInv : ℝ := 1 / (2 * (n : ℝ) - 2)
  let sourceFactor : ℝ := ((n * 2 ^ n : ℕ) : ℝ)
  let sideFactor : ℝ := (((4 * n + 1 : ℕ) : ℝ) / 5)
  let noiseRatio : ℝ := σ / mMin
  have hnpos : 0 < n := by omega
  have hside : 0 ≤ sideFactor := by dsimp [sideFactor]; positivity
  have hratio : 0 ≤ noiseRatio := by dsimp [noiseRatio]; positivity
  have hsource : 0 ≤ sourceFactor := by dsimp [sourceFactor]; positivity
  have hdiv : 4 * n / (2 * n) = 2 := by
    calc
      4 * n / (2 * n) = 2 * (2 * n) / (2 * n) := by
        congr 1
        ring
      _ = 2 := Nat.mul_div_left 2 (by positivity)
  have hsidePow :
      (((4 * n + 1 : ℕ) : ℝ) ^ d) =
        sideFactor ^ d * (5 : ℝ) ^ d := by
    dsimp [sideFactor]
    rw [div_pow]
    field_simp
  have hbase :
      ((n * 2 ^ n : ℝ) /
            (mMin *
              (((2 * ((4 * n) / (2 * n)) + 1 : ℕ) : ℝ) ^ d)) *
          (((4 * n + 1 : ℕ) : ℝ) ^ d) * σ) =
        sourceFactor * sideFactor ^ d * noiseRatio := by
    rw [hdiv]
    rw [hsidePow]
    dsimp [sourceFactor, sideFactor, noiseRatio]
    push_cast
    field_simp
  have hsideRpow :
      (sideFactor ^ d) ^ exponentInv =
        (sideFactor ^ exponentInv) ^ d := by
    calc
      (sideFactor ^ d) ^ exponentInv =
          (sideFactor ^ (d : ℝ)) ^ exponentInv := by
            rw [Real.rpow_natCast]
      _ = sideFactor ^ ((d : ℝ) * exponentInv) := by
        rw [Real.rpow_mul hside]
      _ = sideFactor ^ (exponentInv * (d : ℝ)) := by rw [mul_comm]
      _ = (sideFactor ^ exponentInv) ^ d :=
        Real.rpow_mul_natCast hside exponentInv d
  have hrootFactorization :
      (sourceFactor * sideFactor ^ d * noiseRatio) ^ exponentInv =
        sourceFactor ^ exponentInv *
          (sideFactor ^ exponentInv) ^ d *
          noiseRatio ^ exponentInv := by
    rw [Real.mul_rpow (mul_nonneg hsource (pow_nonneg hside d)) hratio,
      Real.mul_rpow hsource (pow_nonneg hside d), hsideRpow]
  have hsourceBound :
      sourceFactor ^ exponentInv ≤ 2 * Real.sqrt 2 := by
    exact sourceCount_rpow_le_two_sqrt_two hn
  have hsideBound :
      (sideFactor ^ exponentInv) ^ d ≤
        (3 / Real.sqrt 5) ^ d := by
    exact pow_le_pow_left₀ (by positivity)
      (uniformSide_rpow_le_three_div_sqrt_five hn) d
  rw [uniformDetectionSeparationThreshold,
    numberDetectionSeparationThreshold, hbase, hrootFactorization]
  have hrootBound :
      sourceFactor ^ exponentInv *
            (sideFactor ^ exponentInv) ^ d *
            noiseRatio ^ exponentInv ≤
        (2 * Real.sqrt 2) * (3 / Real.sqrt 5) ^ d *
            noiseRatio ^ exponentInv := by
    gcongr
  have hscale : 0 ≤ 2 * (n : ℝ) * Real.pi / Ω := by positivity
  calc
    2 * (n : ℝ) * Real.pi / Ω *
          (sourceFactor ^ exponentInv *
            (sideFactor ^ exponentInv) ^ d *
            noiseRatio ^ exponentInv)
        ≤ 2 * (n : ℝ) * Real.pi / Ω *
          ((2 * Real.sqrt 2) * (3 / Real.sqrt 5) ^ d *
            noiseRatio ^ exponentInv) :=
      mul_le_mul_of_nonneg_left hrootBound hscale
    _ = 4 * Real.sqrt 2 * (n : ℝ) * Real.pi / Ω *
          (3 / Real.sqrt 5) ^ d *
          noiseRatio ^ exponentInv := by ring

/-- An admissible candidate is pointwise within `σ` of the observed uniform GHM. -/
theorem admissible_uniformMeasurementMatrix_entry_lt
    {d k s : ℕ} {Ω σ : ℝ}
    (ν : AtomicMeasure d k) (Y : Point d → ℂ)
    (hΩ : 0 ≤ Ω) (hs : 0 < s)
    (hadmissible : IsAdmissible ν Ω σ Y)
    (α β : UniformIndex d s) :
    ‖(uniformMeasurementMatrix s Ω (fourier ν) -
        uniformMeasurementMatrix s Ω Y) α β‖ < σ := by
  let ω : Point d := fun j =>
    Ω / s * ((α j : ℝ) + (β j : ℝ) - s)
  have hband : InFrequencyBand Ω ω :=
    uniform_query_in_band hΩ hs α β
  simpa only [uniformMeasurementMatrix, Matrix.sub_apply] using
    hadmissible ω hband

/-- Complete auxiliary version of `noAdmissibleMeasureWithFewerSupports`.
The rank argument is uniform in `k`, so it includes the edge cases `k = 0`
and `k = 1` without invoking a separation theorem for the candidate. -/
theorem noAdmissibleMeasureWithFewerSupports_support
    {d n : ℕ} {Ω σ mMin : ℝ}
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hΩ : 0 < Ω) (hσ : 0 < σ)
    (hmMin : minAmplitude μ (Nat.zero_lt_of_lt hn) = mMin)
    (hcluster : ∀ j, InOpenL1Ball (Real.pi * n / Ω) 0 (μ.node j))
    (hnoise : σ < mMin)
    (hseparation :
      numberDetectionSeparationThreshold d n Ω σ mMin <
        minimumL1Separation μ.node hn)
    (hmeasurement : IsBandMeasurement μ Ω σ Y) :
    ¬ ∃ (k : ℕ) (ν : AtomicMeasure d k),
      k < n ∧ IsAdmissible ν Ω σ Y := by
  rintro ⟨k, ν, hk, hadmissible⟩
  let s := 4 * n
  let G := uniformMeasurementMatrix s Ω Y
  let H := uniformNoiselessMatrix s Ω ν
  let E := G - H
  let sampleCount : ℝ := (((s + 1) ^ d : ℕ) : ℝ)
  have hnpos : 0 < n := by omega
  have hspos : 0 < s := by dsimp [s]; omega
  have hseven : Even s := by
    dsimp [s]
    exact ⟨2 * n, by omega⟩
  have hslarge : 4 * n ≤ s := by rfl
  have hmPos : 0 < mMin := hσ.trans hnoise
  have hthresholdLe :=
    uniformDetectionThreshold_four_mul_le_numberDetectionThreshold
      (d := d) hn hΩ hσ hmPos
  have hthresholdSep :
      uniformDetectionSeparationThreshold (d := d) (n := n)
          s Ω σ mMin <
        minimumL1Separation μ.node hn := by
    dsimp [s]
    exact hthresholdLe.trans_lt hseparation
  have hsignal :
      sampleCount * σ < matrixSingularValue G (n - 1) := by
    have hmain :=
      uniformGHM_singularValueThreshold_support
        μ Y hd hn hΩ hσ hmMin hcluster hslarge hseven hnoise hmeasurement
    have := hmain.2 hthresholdSep
    simpa only [G, sampleCount, s, Nat.cast_pow] using this
  have hfactor :
      uniformMeasurementMatrix s Ω (fourier ν) = H :=
    uniformMeasurementMatrix_fourier_eq_noiseless s Ω ν hspos
  have hEentry : ∀ α β, ‖E α β‖ < σ := by
    intro α β
    have hcandidate :=
      admissible_uniformMeasurementMatrix_entry_lt
        ν Y hΩ.le hspos hadmissible α β
    rw [hfactor] at hcandidate
    dsimp [E, G]
    rw [show
      uniformMeasurementMatrix s Ω Y α β - H α β =
        -(H α β - uniformMeasurementMatrix s Ω Y α β) by ring,
      norm_neg]
    exact hcandidate
  have hcardpos : 0 < (s + 1) ^ d := by positivity
  letI : Nonempty (UniformIndex d s) :=
    Fintype.card_pos_iff.mp (by simpa [card_uniformIndex] using hcardpos)
  have hEnorm : matrixSpectralNorm E ≤ sampleCount * σ := by
    have h := matrixSpectralNorm_le_card_sqrt_mul_of_lt E hEentry
    have hsqrt :
        Real.sqrt
            (((s + 1) ^ d : ℕ) * ((s + 1) ^ d : ℕ)) =
          sampleCount := by
      rw [Real.sqrt_mul_self]
      exact_mod_cast (Nat.zero_le ((s + 1) ^ d))
    have h' :
        matrixSpectralNorm E ≤
          Real.sqrt
              (((s + 1) ^ d : ℕ) * ((s + 1) ^ d : ℕ)) * σ := by
      simpa [UniformIndex] using h
    rw [hsqrt] at h'
    simpa only [mul_comm] using h'
  have hzero : matrixSingularValue H (n - 1) = 0 := by
    exact uniformNoiseless_singularValue_eq_zero Ω ν (by omega)
  have hsum : G = H + E := by
    dsimp [E]
    abel
  have hsamples : n ≤ (s + 1) ^ d := by
    exact (show n ≤ s + 1 by dsimp [s]; omega).trans
      (Nat.le_pow (by omega))
  have hupper :
      matrixSingularValue G (n - 1) ≤ sampleCount * σ := by
    have hweyl :=
      matrixSingularValue_add_le_add_spectralNorm H E
        (i := n - 1) (by
          simpa [UniformIndex] using
            (show n - 1 < (s + 1) ^ d by omega))
    rw [← hsum, hzero, zero_add] at hweyl
    exact hweyl.trans hEnorm
  linarith

end

end NumDetect
end LeanNumDetect
