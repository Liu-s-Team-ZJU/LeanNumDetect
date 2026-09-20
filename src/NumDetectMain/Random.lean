import NumDetectMain.RandomProofSupport

/-! Deterministic singular-value bounds for realized random GHMs. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Matrix.Norms.L2Operator

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Embed a realized integer-vector frequency family into `ℝ^d`. -/
def integerVectorFrequencyPoint {d M : ℕ}
    (frequency : Fin M → Fin d → ℤ) :
    Fin M → Point d :=
  fun j k => frequency j k

/-- A realized random GHM built from two integer-vector frequency lists. -/
def realizedRandomGHM {d M₁ M₂ : ℕ}
    (rowFrequency : Fin M₁ → Fin d → ℤ)
    (columnFrequency : Fin M₂ → Fin d → ℤ)
    (Y : Point d → ℂ) : Matrix (Fin M₁) (Fin M₂) ℂ :=
  generalizedHankel (integerVectorFrequencyPoint rowFrequency)
    (integerVectorFrequencyPoint columnFrequency) Y

/-- Row-side Vandermonde matrix for a realized integer-vector frequency list. -/
def realizedRandomRowVandermonde {d M n : ℕ}
    (frequency : Fin M → Fin d → ℤ) (μ : AtomicMeasure d n) :
    Matrix (Fin M) (Fin n) ℂ :=
  generalizedVandermonde (integerVectorFrequencyPoint frequency) μ.node

/-- Transposed column-side Vandermonde factor for a realized integer-vector
frequency list. -/
def realizedRandomColumnVandermonde {d M n : ℕ}
    (frequency : Fin M → Fin d → ℤ) (μ : AtomicMeasure d n) :
    Matrix (Fin n) (Fin M) ℂ :=
  Matrix.transpose
    (generalizedVandermonde (integerVectorFrequencyPoint frequency) μ.node)

/-- A realized row-column integer-frequency sum lies in the declared band
when every coordinate of every such sum does. -/
theorem realizedRandom_frequency_sum_in_band
    {d M₁ M₂ : ℕ} {Ω : ℝ}
    (rowFrequency : Fin M₁ → Fin d → ℤ)
    (columnFrequency : Fin M₂ → Fin d → ℤ)
    (hband : ∀ i j k,
      |((rowFrequency i k + columnFrequency j k : ℤ) : ℝ)| ≤ Ω)
    (i : Fin M₁) (j : Fin M₂) :
    InFrequencyBand Ω
      (integerVectorFrequencyPoint rowFrequency i +
        integerVectorFrequencyPoint columnFrequency j) := by
  intro k
  simpa only [integerVectorFrequencyPoint, Pi.add_apply] using
    (show |(rowFrequency i k : ℝ) + (columnFrequency j k : ℝ)| ≤ Ω by
      exact_mod_cast hband i j k)

/-- Exact noiseless factorization of a realized integer-vector random GHM. -/
theorem realizedRandomGHM_fourier_factorization
    {d n M₁ M₂ : ℕ}
    (rowFrequency : Fin M₁ → Fin d → ℤ)
    (columnFrequency : Fin M₂ → Fin d → ℤ)
    (μ : AtomicMeasure d n) :
    realizedRandomGHM rowFrequency columnFrequency (fourier μ) =
      realizedRandomRowVandermonde rowFrequency μ *
        Matrix.diagonal μ.amplitude *
        realizedRandomColumnVandermonde columnFrequency μ := by
  exact generalizedHankel_fourier_eq_hankelVandermondeFactor
    (integerVectorFrequencyPoint rowFrequency)
    (integerVectorFrequencyPoint columnFrequency) μ

/-- Every entry of the realized random-GHM perturbation is strictly below the
declared pointwise noise level. -/
theorem realizedRandomGHM_sub_fourier_entry_lt
    {d n M₁ M₂ : ℕ} {Ω σ : ℝ}
    (rowFrequency : Fin M₁ → Fin d → ℤ)
    (columnFrequency : Fin M₂ → Fin d → ℤ)
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (hmeasurement : IsBandMeasurement μ Ω σ Y)
    (hband : ∀ i j k,
      |((rowFrequency i k + columnFrequency j k : ℤ) : ℝ)| ≤ Ω)
    (i : Fin M₁) (j : Fin M₂) :
    ‖(realizedRandomGHM rowFrequency columnFrequency Y -
        realizedRandomGHM rowFrequency columnFrequency (fourier μ)) i j‖ < σ := by
  rcases hmeasurement with ⟨W, hW, hY⟩
  let ω :=
    integerVectorFrequencyPoint rowFrequency i +
      integerVectorFrequencyPoint columnFrequency j
  have hω : InFrequencyBand Ω ω :=
    realizedRandom_frequency_sum_in_band rowFrequency columnFrequency hband i j
  have hvalue := hY ω hω
  have hnoise := hW ω hω
  simp only [realizedRandomGHM, generalizedHankel, Matrix.sub_apply]
  rw [hvalue, add_sub_cancel_left]
  exact hnoise

/-- Tail singular-value estimate in the first part of manuscript Theorem
`thm:resolutionrandghmnumber1`, for an arbitrary spatial dimension and fixed
realized draws. Injectivity expresses sampling without replacement, while
`hband` records that every queried frequency sum is legal. -/
theorem realizedRandomGHM_tail_singularValue_lt
    {d n M₁ M₂ : ℕ}
    (rowFrequency : Fin M₁ → Fin d → ℤ)
    (columnFrequency : Fin M₂ → Fin d → ℤ)
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (hM₁ : n < M₁) (hM₂ : n < M₂)
    (_hrowWithoutReplacement : Function.Injective rowFrequency)
    (_hcolumnWithoutReplacement : Function.Injective columnFrequency)
    {Ω σ : ℝ}
    (hmeasurement : IsBandMeasurement μ Ω σ Y)
    (hband : ∀ i j k,
      |((rowFrequency i k + columnFrequency j k : ℤ) : ℝ)| ≤ Ω) :
    ∀ j, n ≤ j → j < M₂ →
      matrixSingularValue (realizedRandomGHM rowFrequency columnFrequency Y) j <
        σ * Real.sqrt (M₁ * M₂) := by
  let G := realizedRandomGHM rowFrequency columnFrequency Y
  let G₀ :=
    realizedRandomGHM rowFrequency columnFrequency (fourier μ)
  let Δ := G - G₀
  have hM₁pos : 0 < M₁ := by omega
  have hM₂pos : 0 < M₂ := by omega
  letI : Nonempty (Fin M₁) := Fin.pos_iff_nonempty.mp hM₁pos
  letI : Nonempty (Fin M₂) := Fin.pos_iff_nonempty.mp hM₂pos
  have hΔentry : ∀ i j, ‖Δ i j‖ < σ := by
    intro i j
    exact realizedRandomGHM_sub_fourier_entry_lt
      rowFrequency columnFrequency μ Y hmeasurement hband i j
  have hσ : 0 < σ := by
    let i : Fin M₁ := ⟨0, hM₁pos⟩
    let j : Fin M₂ := ⟨0, hM₂pos⟩
    exact (norm_nonneg (Δ i j)).trans_lt (hΔentry i j)
  have hΔnorm :
      matrixSpectralNorm Δ < σ * Real.sqrt (M₁ * M₂) := by
    simpa only [Fintype.card_fin] using
      matrixSpectralNorm_lt_card_sqrt Δ hσ hΔentry
  have hfactor :
      G₀ =
        realizedRandomRowVandermonde rowFrequency μ *
          Matrix.diagonal μ.amplitude *
          realizedRandomColumnVandermonde columnFrequency μ :=
    realizedRandomGHM_fourier_factorization rowFrequency columnFrequency μ
  have hzero : ∀ j, n ≤ j → matrixSingularValue G₀ j = 0 := by
    intro j hj
    rw [hfactor]
    exact matrixSingularValue_three_mul_eq_zero_of_card_le
      (realizedRandomRowVandermonde rowFrequency μ)
      (Matrix.diagonal μ.amplitude)
      (realizedRandomColumnVandermonde columnFrequency μ) (by simpa using hj)
  intro j hj hjM₂
  have hperturb :=
    matrixSingularValue_le_add_spectralNorm_sub G G₀
      (i := j) (by simpa using hjM₂)
  rw [hzero j hj, zero_add] at hperturb
  exact hperturb.trans_lt hΔnorm

/-- Embed an integer frequency as a one-dimensional real frequency. -/
def integerFrequencyPoint {M : ℕ} (frequency : Fin M → ℤ) :
    Fin M → Point 1 :=
  fun j _ => frequency j

/-- Realized one-dimensional random GHM. -/
def randomMeasurementMatrix {M₁ M₂ : ℕ}
    (rowFrequency : Fin M₁ → ℤ) (columnFrequency : Fin M₂ → ℤ)
    (Y : Point 1 → ℂ) : Matrix (Fin M₁) (Fin M₂) ℂ :=
  generalizedHankel (integerFrequencyPoint rowFrequency)
    (integerFrequencyPoint columnFrequency) Y

/-- Row-side Vandermonde matrix at the realized frequencies. -/
def randomRowVandermonde {M n : ℕ}
    (frequency : Fin M → ℤ) (μ : AtomicMeasure 1 n) :
    Matrix (Fin M) (Fin n) ℂ :=
  generalizedVandermonde (integerFrequencyPoint frequency) μ.node

/-- Column-side factor at the realized frequencies. It is defined with the
ordinary transpose because the generalized Hankel factorization has no complex
conjugation on its right-hand Vandermonde factor. -/
def randomColumnVandermonde {M n : ℕ}
    (frequency : Fin M → ℤ) (μ : AtomicMeasure 1 n) :
    Matrix (Fin n) (Fin M) ℂ :=
  Matrix.transpose
    (generalizedVandermonde (integerFrequencyPoint frequency) μ.node)

/-- Every realized query frequency is in the declared one-dimensional band. -/
theorem random_query_in_band
    {M₁ M₂ : ℕ} {Ω : ℝ}
    (rowFrequency : Fin M₁ → ℤ) (columnFrequency : Fin M₂ → ℤ)
    (hband : ∀ i j, |((rowFrequency i + columnFrequency j : ℤ) : ℝ)| ≤ Ω)
    (i : Fin M₁) (j : Fin M₂) :
    InFrequencyBand Ω
      (integerFrequencyPoint rowFrequency i +
        integerFrequencyPoint columnFrequency j) := by
  intro k
  fin_cases k
  simpa only [integerFrequencyPoint, Pi.add_apply] using
    (show |(rowFrequency i : ℝ) + (columnFrequency j : ℝ)| ≤ Ω by
      exact_mod_cast hband i j)

/-- The realized noiseless GHM has the exact three-factor decomposition from
`eq:random-hankel-noisy-factorization`. -/
theorem randomMeasurementMatrix_fourier_factorization
    {n M₁ M₂ : ℕ}
    (rowFrequency : Fin M₁ → ℤ) (columnFrequency : Fin M₂ → ℤ)
    (μ : AtomicMeasure 1 n) :
    randomMeasurementMatrix rowFrequency columnFrequency (fourier μ) =
      randomRowVandermonde rowFrequency μ *
        Matrix.diagonal μ.amplitude *
        randomColumnVandermonde columnFrequency μ := by
  exact generalizedHankel_fourier_eq_hankelVandermondeFactor
    (integerFrequencyPoint rowFrequency)
    (integerFrequencyPoint columnFrequency) μ

/-- The realized perturbation has the pointwise strict noise bound. -/
theorem randomMeasurementMatrix_sub_fourier_entry_lt
    {n M₁ M₂ : ℕ} {Ω σ : ℝ}
    (rowFrequency : Fin M₁ → ℤ) (columnFrequency : Fin M₂ → ℤ)
    (μ : AtomicMeasure 1 n) (Y : Point 1 → ℂ)
    (hmeasurement : IsBandMeasurement μ Ω σ Y)
    (hband : ∀ i j, |((rowFrequency i + columnFrequency j : ℤ) : ℝ)| ≤ Ω)
    (i : Fin M₁) (j : Fin M₂) :
    ‖(randomMeasurementMatrix rowFrequency columnFrequency Y -
        randomMeasurementMatrix rowFrequency columnFrequency (fourier μ)) i j‖ < σ := by
  rcases hmeasurement with ⟨W, hW, hY⟩
  let ω :=
    integerFrequencyPoint rowFrequency i +
      integerFrequencyPoint columnFrequency j
  have hω : InFrequencyBand Ω ω :=
    random_query_in_band rowFrequency columnFrequency hband i j
  have hvalue := hY ω hω
  have hnoise := hW ω hω
  simp only [randomMeasurementMatrix, generalizedHankel, Matrix.sub_apply]
  rw [hvalue, add_sub_cancel_left]
  exact hnoise

/-- Deterministic fixed-realization implication used in the proof of manuscript
Theorem `thm:resolutionrandghmnumber1`.

The signal hypothesis records exactly the quantitative premise used by the
matrix perturbation step. It is not the manuscript's random sampling claim:
that claim uses an unjustified passage from parent-set spread to realized-set
spread and leaves its closeness, noise, and probability quantifiers implicit.
The conclusions here include the sharper perturbed signal lower bound and the
resulting strict threshold gap. Singular-value indices are zero-based. -/
theorem randomGHM_singularValueThreshold
    {n M₁ M₂ : ℕ}
    (rowFrequency : Fin M₁ → ℤ) (columnFrequency : Fin M₂ → ℤ)
    (μ : AtomicMeasure 1 n) (Y : Point 1 → ℂ)
    (hn : 2 ≤ n) (hM₁ : n < M₁) (hM₂ : n < M₂)
    (_hrowInjective : Function.Injective rowFrequency)
    (_hcolumnInjective : Function.Injective columnFrequency)
    {Ω σ : ℝ} (_hΩ : 0 < Ω) (hσ : 0 < σ)
    (hmeasurement : IsBandMeasurement μ Ω σ Y)
    (hband : ∀ i j, |((rowFrequency i + columnFrequency j : ℤ) : ℝ)| ≤ Ω)
    (hsignal :
      2 * σ * Real.sqrt (M₁ * M₂) <
        minAmplitude μ (Nat.zero_lt_of_lt hn) *
          matrixSingularValue (randomRowVandermonde rowFrequency μ) (n - 1) *
          matrixSingularValue (randomColumnVandermonde columnFrequency μ) (n - 1)) :
    (∀ j, n ≤ j → j < M₂ →
      matrixSingularValue
          (randomMeasurementMatrix rowFrequency columnFrequency Y) j <
        σ * Real.sqrt (M₁ * M₂)) ∧
    (minAmplitude μ (Nat.zero_lt_of_lt hn) *
          matrixSingularValue (randomRowVandermonde rowFrequency μ) (n - 1) *
          matrixSingularValue (randomColumnVandermonde columnFrequency μ) (n - 1) -
        σ * Real.sqrt (M₁ * M₂) <
      matrixSingularValue
        (randomMeasurementMatrix rowFrequency columnFrequency Y) (n - 1)) ∧
    σ * Real.sqrt (M₁ * M₂) <
      matrixSingularValue
        (randomMeasurementMatrix rowFrequency columnFrequency Y) (n - 1) := by
  let G :=
    randomMeasurementMatrix rowFrequency columnFrequency Y
  let G₀ :=
    randomMeasurementMatrix rowFrequency columnFrequency (fourier μ)
  let Δ := G - G₀
  have hM₁pos : 0 < M₁ := by omega
  have hM₂pos : 0 < M₂ := by omega
  letI : Nonempty (Fin M₁) := Fin.pos_iff_nonempty.mp hM₁pos
  letI : Nonempty (Fin M₂) := Fin.pos_iff_nonempty.mp hM₂pos
  have hΔentry : ∀ i j, ‖Δ i j‖ < σ := by
    intro i j
    exact randomMeasurementMatrix_sub_fourier_entry_lt
      rowFrequency columnFrequency μ Y hmeasurement hband i j
  have hΔnorm :
      matrixSpectralNorm Δ < σ * Real.sqrt (M₁ * M₂) := by
    simpa only [Fintype.card_fin] using
      matrixSpectralNorm_lt_card_sqrt Δ hσ hΔentry
  have hfactor :
      G₀ =
        randomRowVandermonde rowFrequency μ *
          Matrix.diagonal μ.amplitude *
          randomColumnVandermonde columnFrequency μ :=
    randomMeasurementMatrix_fourier_factorization rowFrequency columnFrequency μ
  have hzero : ∀ j, n ≤ j → matrixSingularValue G₀ j = 0 := by
    intro j hj
    rw [hfactor]
    exact matrixSingularValue_three_mul_eq_zero_of_card_le
      (randomRowVandermonde rowFrequency μ)
      (Matrix.diagonal μ.amplitude)
      (randomColumnVandermonde columnFrequency μ) (by simpa using hj)
  have hnoise :
      ∀ j, n ≤ j → j < M₂ →
        matrixSingularValue G j < σ * Real.sqrt (M₁ * M₂) := by
    intro j hj hjM₂
    have hperturb :=
      matrixSingularValue_le_add_spectralNorm_sub G G₀
        (i := j) (by simpa using hjM₂)
    rw [hzero j hj, zero_add] at hperturb
    exact hperturb.trans_lt hΔnorm
  have hminNonneg : 0 ≤ minAmplitude μ (Nat.zero_lt_of_lt hn) :=
    (minAmplitude_pos μ (Nat.zero_lt_of_lt hn)).le
  have hnoiseless :
      minAmplitude μ (Nat.zero_lt_of_lt hn) *
            matrixSingularValue (randomRowVandermonde rowFrequency μ) (n - 1) *
            matrixSingularValue (randomColumnVandermonde columnFrequency μ) (n - 1) ≤
        matrixSingularValue G₀ (n - 1) := by
    rw [hfactor]
    simpa only [Fintype.card_fin, mul_comm] using
      (matrixSingularValue_three_mul_lower
        (randomRowVandermonde rowFrequency μ) μ.amplitude
        (randomColumnVandermonde columnFrequency μ)
        (by simpa using Nat.zero_lt_of_lt hn) (by simpa using hM₂.le) hminNonneg
        (minAmplitude_le μ (Nat.zero_lt_of_lt hn)))
  have hreverseNorm :
      matrixSpectralNorm (G₀ - G) = matrixSpectralNorm Δ := by
    have heq : G₀ - G = -Δ := by
      simp only [Δ]
      abel
    rw [heq]
    simpa only [matrixSpectralNorm_eq_l2_opNorm] using (norm_neg Δ)
  have hsignalPerturb :=
    matrixSingularValue_sub_spectralNorm_le G₀ G
      (i := n - 1) (by simpa using (show n - 1 < M₂ by omega))
  rw [hreverseNorm] at hsignalPerturb
  have hlower :
      minAmplitude μ (Nat.zero_lt_of_lt hn) *
            matrixSingularValue (randomRowVandermonde rowFrequency μ) (n - 1) *
            matrixSingularValue (randomColumnVandermonde columnFrequency μ) (n - 1) -
          σ * Real.sqrt (M₁ * M₂) <
        matrixSingularValue G (n - 1) := by
    linarith
  refine ⟨hnoise, hlower, ?_⟩
  linarith

end

end NumDetect
end LeanNumDetect
