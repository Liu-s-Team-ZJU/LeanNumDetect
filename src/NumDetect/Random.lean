import NumDetect.RandomMatrixBounds
import RandSamp.NonuniformVandermonde

/-! Deterministic singular-value bounds for realized random GHMs. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
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

/-- The real-valued frequency family associated with one realized integer draw. -/
def realizedRealFrequency {M : ℕ} (frequency : Fin M → ℤ) : Fin M → ℝ :=
  fun j => frequency j

/-- A positive bound for the absolute values in a realized frequency family. -/
def realizedFrequencyRadius {M : ℕ} (frequency : Fin M → ℤ) : ℝ :=
  1 + ∑ j, |(frequency j : ℝ)|

theorem realizedFrequencyRadius_pos {M : ℕ} (frequency : Fin M → ℤ) :
    0 < realizedFrequencyRadius frequency := by
  unfold realizedFrequencyRadius
  positivity

theorem abs_realizedRealFrequency_le_radius {M : ℕ}
    (frequency : Fin M → ℤ) (i : Fin M) :
    |realizedRealFrequency frequency i| ≤ realizedFrequencyRadius frequency := by
  unfold realizedRealFrequency realizedFrequencyRadius
  have hi : |(frequency i : ℝ)| ≤ ∑ j, |(frequency j : ℝ)| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (frequency j : ℝ)) (Finset.mem_univ i)
  linarith

theorem realizedRealFrequency_injective {M : ℕ} {frequency : Fin M → ℤ}
    (hfrequency : Function.Injective frequency) :
    Function.Injective (realizedRealFrequency frequency) := by
  intro i j hij
  apply hfrequency
  change (frequency i : ℝ) = (frequency j : ℝ) at hij
  exact_mod_cast hij

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

theorem randomRowVandermonde_eq_fourierVandermonde {M n : ℕ}
    (frequency : Fin M → ℤ) (μ : AtomicMeasure 1 n) :
    randomRowVandermonde frequency μ =
      RandSamp.fourierVandermonde (realizedRealFrequency frequency)
        (fun j => μ.node j 0) := by
  ext i j
  simp [randomRowVandermonde, generalizedVandermonde, steeringVector,
    integerFrequencyPoint, realizedRealFrequency, RandSamp.fourierVandermonde,
    dot]

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

/-- Positivity of the last column singular value gives full column rank. -/
theorem randomFullColumnRank_of_lastSingularValue_pos
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

/-- Deterministic fixed-realization implication used in the proof of manuscript
Theorem `thm:resolutionrandghmnumber1`.  Its signal premise is stated using the
two untransposed Vandermonde factors from the manuscript. -/
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
          matrixSingularValue (randomRowVandermonde columnFrequency μ) (n - 1)) :
    (∀ j, n ≤ j → j < M₂ →
      matrixSingularValue
          (randomMeasurementMatrix rowFrequency columnFrequency Y) j <
        σ * Real.sqrt (M₁ * M₂)) ∧
    (minAmplitude μ (Nat.zero_lt_of_lt hn) *
          matrixSingularValue (randomRowVandermonde rowFrequency μ) (n - 1) *
          matrixSingularValue (randomRowVandermonde columnFrequency μ) (n - 1) -
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
  have hnoise :
      ∀ j, n ≤ j → j < M₂ →
        matrixSingularValue G j < σ * Real.sqrt (M₁ * M₂) := by
    let row : Fin M₁ → Fin 1 → ℤ := fun i _ => rowFrequency i
    let column : Fin M₂ → Fin 1 → ℤ := fun j _ => columnFrequency j
    have hrow : Function.Injective row := by
      intro i j hij
      apply _hrowInjective
      exact congrFun hij 0
    have hcolumn : Function.Injective column := by
      intro i j hij
      apply _hcolumnInjective
      exact congrFun hij 0
    have hband' : ∀ i j k,
        |((row i k + column j k : ℤ) : ℝ)| ≤ Ω := by
      intro i j k
      fin_cases k
      exact hband i j
    exact realizedRandomGHM_tail_singularValue_lt
      row column μ Y hM₁ hM₂ hrow hcolumn hmeasurement hband'
  have hminNonneg : 0 ≤ minAmplitude μ (Nat.zero_lt_of_lt hn) :=
    (minAmplitude_pos μ (Nat.zero_lt_of_lt hn)).le
  have hrowNonneg :
      0 ≤ matrixSingularValue (randomRowVandermonde rowFrequency μ) (n - 1) :=
    matrixSingularValue_nonneg _ _
  have hcolumnNonneg :
      0 ≤ matrixSingularValue (randomRowVandermonde columnFrequency μ) (n - 1) :=
    matrixSingularValue_nonneg _ _
  have hsignalProductPos :
      0 < minAmplitude μ (Nat.zero_lt_of_lt hn) *
          matrixSingularValue (randomRowVandermonde rowFrequency μ) (n - 1) *
          matrixSingularValue (randomRowVandermonde columnFrequency μ) (n - 1) := by
    have hthresholdPos : 0 < 2 * σ * Real.sqrt (M₁ * M₂) := by positivity
    exact hthresholdPos.trans hsignal
  have hcolumnPos :
      0 < matrixSingularValue (randomRowVandermonde columnFrequency μ) (n - 1) := by
    by_contra h
    have hle :
        matrixSingularValue (randomRowVandermonde columnFrequency μ) (n - 1) ≤ 0 :=
      le_of_not_gt h
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hminNonneg hrowNonneg) hle
    exact (not_lt_of_ge hnonpos) hsignalProductPos
  have hcolumnRank :
      HasFullColumnRank (randomRowVandermonde columnFrequency μ) :=
    randomFullColumnRank_of_lastSingularValue_pos _ (Nat.zero_lt_of_lt hn) hcolumnPos
  have hnoiseless :
      minAmplitude μ (Nat.zero_lt_of_lt hn) *
            matrixSingularValue (randomRowVandermonde rowFrequency μ) (n - 1) *
            matrixSingularValue (randomRowVandermonde columnFrequency μ) (n - 1) ≤
        matrixSingularValue G₀ (n - 1) := by
    rw [hfactor]
    simpa only [randomColumnVandermonde, randomRowVandermonde] using
      (matrixSingularValue_diagonal_transpose_lower_of_fullColumnRank
        (randomRowVandermonde rowFrequency μ) μ.amplitude
        (randomRowVandermonde columnFrequency μ)
        (Nat.zero_lt_of_lt hn) (by simpa using hM₂.le) hcolumnRank hminNonneg
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
            matrixSingularValue (randomRowVandermonde columnFrequency μ) (n - 1) -
          σ * Real.sqrt (M₁ * M₂) <
        matrixSingularValue G (n - 1) := by
    linarith
  refine ⟨hnoise, hlower, ?_⟩
  linarith

/-- One admissible manuscript constant `C₂(n)`.  Its role is conditional: the
realized sampling families are assumed to have at least this spread. -/
def randomGHMSpreadConstant (_n : ℕ) : ℝ := 1

/-- A source-separation constant with enough slack for the strict signal/noise
gap in manuscript Theorem `thm:resolutionrandghmnumber1`. -/
noncomputable def randomGHMSeparationConstant (n : ℕ) : ℝ :=
  let c := (1 / 2 : ℝ) * RandSamp.nonuniformVandermondeConstant n
  (n : ℝ) * (4 / c ^ 2) ^ (1 / (2 * (n : ℝ) - 2))

theorem randomGHMSpreadConstant_pos (n : ℕ) :
    0 < randomGHMSpreadConstant n := by
  simp [randomGHMSpreadConstant]

theorem randomGHMSeparationConstant_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < randomGHMSeparationConstant n := by
  unfold randomGHMSeparationConstant
  have hc := RandSamp.nonuniformVandermondeConstant_pos (by omega : 0 < n)
  positivity

/-- The manuscript separation scale implies a strict noiseless signal gap once
the two realized Vandermonde factors have the stated spread lower bounds. -/
theorem randomGHM_separation_implies_model_gap
    {n M₁ M₂ : ℕ} (hn : 2 ≤ n) {Ω σ mMin θ : ℝ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hΩ : 0 < Ω) (hσ : 0 < σ) (hmMin : 0 < mMin)
    (hseparation :
      randomGHMSeparationConstant n *
            (((M₁ * M₂ : ℕ) : ℝ) ^ (1 / (4 * (n : ℝ) - 4))) / Ω *
          (σ / mMin) ^ (1 / (2 * (n : ℝ) - 2)) ≤ θ) :
    2 * σ * Real.sqrt (M₁ * M₂) <
      mMin *
        ((1 / 2 : ℝ) * RandSamp.nonuniformVandermondeConstant n *
          (Ω / n * θ) ^ (n - 1)) *
        ((1 / 2 : ℝ) * RandSamp.nonuniformVandermondeConstant n *
          (Ω / n * θ) ^ (n - 1)) := by
  let p := 2 * (n - 1)
  let c := (1 / 2 : ℝ) * RandSamp.nonuniformVandermondeConstant n
  let N : ℝ := ((M₁ * M₂ : ℕ) : ℝ)
  have hnPos : 0 < n := by omega
  have hpPos : 0 < p := by dsimp [p]; omega
  have hpCast : (p : ℝ) = 2 * (n : ℝ) - 2 := by
    dsimp [p]
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (by norm_num) (RandSamp.nonuniformVandermondeConstant_pos hnPos)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Nat.mul_pos hM₁ hM₂
  have hratio : 0 ≤ σ / mMin := (div_pos hσ hmMin).le
  have hratioRoot :
      ((σ / mMin) ^ (1 / (2 * (n : ℝ) - 2))) ^ p = σ / mMin := by
    rw [show 1 / (2 * (n : ℝ) - 2) = (p : ℝ)⁻¹ by
      rw [hpCast]
      exact one_div _]
    exact Real.rpow_inv_natCast_pow hratio (Nat.ne_of_gt hpPos)
  have hconstantRoot :
      ((4 / c ^ 2) ^ (1 / (2 * (n : ℝ) - 2))) ^ p = 4 / c ^ 2 := by
    rw [show 1 / (2 * (n : ℝ) - 2) = (p : ℝ)⁻¹ by
      rw [hpCast]
      exact one_div _]
    exact Real.rpow_inv_natCast_pow (by positivity) (Nat.ne_of_gt hpPos)
  have hsampleRoot :
      (N ^ (1 / (4 * (n : ℝ) - 4))) ^ p = Real.sqrt N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, Real.sqrt_eq_rpow]
    congr 1
    rw [hpCast]
    have hnR : 1 < (n : ℝ) := by exact_mod_cast hn
    field_simp [ne_of_gt (sub_pos.mpr hnR)]
    ring
  have hthresholdNonneg :
      0 ≤ randomGHMSeparationConstant n *
            (N ^ (1 / (4 * (n : ℝ) - 4))) / Ω *
          (σ / mMin) ^ (1 / (2 * (n : ℝ) - 2)) := by
    exact le_of_lt (mul_pos
      (div_pos
        (mul_pos (randomGHMSeparationConstant_pos hn)
          (Real.rpow_pos_of_pos hN _)) hΩ)
      (Real.rpow_pos_of_pos (div_pos hσ hmMin) _))
  have hseparation' :
      randomGHMSeparationConstant n *
            (N ^ (1 / (4 * (n : ℝ) - 4))) / Ω *
          (σ / mMin) ^ (1 / (2 * (n : ℝ) - 2)) ≤ θ := by
    simpa only [N] using hseparation
  have hsepPow :
      (randomGHMSeparationConstant n *
            (N ^ (1 / (4 * (n : ℝ) - 4))) / Ω *
          (σ / mMin) ^ (1 / (2 * (n : ℝ) - 2))) ^ p ≤ θ ^ p :=
    pow_le_pow_left₀ hthresholdNonneg hseparation' p
  have hscaled :
      4 * σ * Real.sqrt N ≤
        mMin * c ^ 2 * (Ω / n) ^ p * θ ^ p := by
    have hthresholdPow :
        (randomGHMSeparationConstant n *
              (N ^ (1 / (4 * (n : ℝ) - 4))) / Ω *
            (σ / mMin) ^ (1 / (2 * (n : ℝ) - 2))) ^ p =
          ((n : ℝ) ^ p * (4 / c ^ 2) * Real.sqrt N / Ω ^ p *
            (σ / mMin)) := by
      rw [mul_pow, div_pow, mul_pow, hsampleRoot, hratioRoot]
      unfold randomGHMSeparationConstant
      dsimp only
      rw [mul_pow, hconstantRoot]
    calc
      4 * σ * Real.sqrt N =
          mMin * c ^ 2 * (Ω / n) ^ p *
            (randomGHMSeparationConstant n *
                (N ^ (1 / (4 * (n : ℝ) - 4))) / Ω *
              (σ / mMin) ^ (1 / (2 * (n : ℝ) - 2))) ^ p := by
            rw [hthresholdPow, div_pow]
            field_simp [ne_of_gt hc, ne_of_gt hΩ, ne_of_gt hmMin,
              Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnPos)]
      _ ≤ mMin * c ^ 2 * (Ω / n) ^ p * θ ^ p := by
        gcongr
  have hmodelIdentity :
      mMin * c ^ 2 * (Ω / n) ^ p * θ ^ p =
        mMin * (c * (Ω / n * θ) ^ (n - 1)) *
          (c * (Ω / n * θ) ^ (n - 1)) := by
    dsimp [p]
    rw [show 2 * (n - 1) = (n - 1) + (n - 1) by omega,
      pow_add, mul_pow]
    ring
  rw [hmodelIdentity] at hscaled
  have hsqrtPos : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hstrict :
      2 * σ * Real.sqrt N <
        mMin * (c * (Ω / n * θ) ^ (n - 1)) *
          (c * (Ω / n * θ) ^ (n - 1)) := by
    nlinarith [mul_pos hσ hsqrtPos]
  simpa only [c, N, Nat.cast_mul] using hstrict

/-- Distinct one-dimensional nodes remain distinct after evaluating their sole
coordinate. -/
theorem atomicMeasure_nodeCoordinate_injective {n : ℕ} (μ : AtomicMeasure 1 n) :
    Function.Injective (fun j => μ.node j 0) := by
  intro i j hij
  apply μ.node_injective
  funext k
  fin_cases k
  exact hij

/-- Signal singular-value estimate in manuscript Theorem
`thm:resolutionrandghmnumber1`.  The constants `C₂(n)` and `C₃(n)` precede
every realized sampling family, source, and noise level, so they depend only on
`n`.  For each realization the proof chooses a positive local scale `ε`; the
separate noise bound is `realizedRandomGHM_tail_singularValue_lt`. -/
theorem randomGHM_signalThreshold_of_separation (n : ℕ) (hn : 2 ≤ n) :
    ∃ C₂ C₃ : ℝ, 0 < C₂ ∧ 0 < C₃ ∧
      ∀ {M₁ M₂ : ℕ}
        (rowFrequency : Fin M₁ → ℤ) (columnFrequency : Fin M₂ → ℤ)
        (μ : AtomicMeasure 1 n) (Y : Point 1 → ℂ)
        (hM₁ : n < M₁) (hM₂ : n < M₂)
        (_hrowInjective : Function.Injective rowFrequency)
        (_hcolumnInjective : Function.Injective columnFrequency)
        {Ω σ τ center : ℝ} (_hΩ : 0 < Ω) (_hσ : 0 < σ)
        (_hτlower : (n : ℝ) - 1 ≤ τ)
        (_hmeasurement : IsBandMeasurement μ Ω σ Y)
        (_hband : ∀ i j,
          |((rowFrequency i + columnFrequency j : ℤ) : ℝ)| ≤ Ω),
        ∃ ε : ℝ, 0 < ε ∧ (
          minimumSeparation1D (fun j => μ.node j 0) hn < ε →
          τ < Real.pi / minimumSeparation1D (fun j => μ.node j 0) hn →
          IsLocalCluster1D (fun j => μ.node j 0) hn center τ →
          min
              (RandSamp.finiteFamilySamplingSpread
                (realizedRealFrequency rowFrequency) n hM₁.le hn)
              (RandSamp.finiteFamilySamplingSpread
                (realizedRealFrequency columnFrequency) n hM₂.le hn) ≥
            C₂ * Ω / n →
          C₃ * (((M₁ * M₂ : ℕ) : ℝ) ^ (1 / (4 * (n : ℝ) - 4))) / Ω *
                (σ / minAmplitude μ (Nat.zero_lt_of_lt hn)) ^
                  (1 / (2 * (n : ℝ) - 2)) ≤
            minimumSeparation1D (fun j => μ.node j 0) hn →
          σ * Real.sqrt (M₁ * M₂) <
            matrixSingularValue
              (randomMeasurementMatrix rowFrequency columnFrequency Y) (n - 1)) := by
  refine ⟨randomGHMSpreadConstant n, randomGHMSeparationConstant n,
    randomGHMSpreadConstant_pos n, randomGHMSeparationConstant_pos hn, ?_⟩
  intro M₁ M₂ rowFrequency columnFrequency μ Y hM₁ hM₂
    hrowInjective hcolumnInjective Ω σ τ center hΩ hσ hτlower
    hmeasurement hband
  have hnPos : 0 < n := by omega
  have hτ : 0 < τ := by
    have hnReal : 1 < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hrowRealInjective :
      Function.Injective (realizedRealFrequency rowFrequency) :=
    realizedRealFrequency_injective hrowInjective
  have hcolumnRealInjective :
      Function.Injective (realizedRealFrequency columnFrequency) :=
    realizedRealFrequency_injective hcolumnInjective
  rcases RandSamp.nonuniformVandermonde_minimumSingularValue
      (realizedRealFrequency rowFrequency) (fun j => μ.node j 0) center
      hM₁.le hn hrowRealInjective
      (realizedFrequencyRadius_pos rowFrequency)
      (abs_realizedRealFrequency_le_radius rowFrequency) hτ with
    ⟨εrow, hεrow, hrowBound⟩
  rcases RandSamp.nonuniformVandermonde_minimumSingularValue
      (realizedRealFrequency columnFrequency) (fun j => μ.node j 0) center
      hM₂.le hn hcolumnRealInjective
      (realizedFrequencyRadius_pos columnFrequency)
      (abs_realizedRealFrequency_le_radius columnFrequency) hτ with
    ⟨εcolumn, hεcolumn, hcolumnBound⟩
  refine ⟨min εrow εcolumn, lt_min hεrow hεcolumn, ?_⟩
  intro hθsmall _hτupper hcluster hspread hseparation
  let θ := minimumSeparation1D (fun j => μ.node j 0) hn
  have hnodeCoordinateInjective : Function.Injective (fun j => μ.node j 0) :=
    atomicMeasure_nodeCoordinate_injective μ
  have hθ : 0 < θ := by
    exact minimumSeparation1D_pos (fun j => μ.node j 0) hn
      hnodeCoordinateInjective
  have hθsmall' : θ < min εrow εcolumn := by simpa only [θ] using hθsmall
  have hθrow : θ < εrow := hθsmall'.trans_le (min_le_left _ _)
  have hθcolumn : θ < εcolumn := hθsmall'.trans_le (min_le_right _ _)
  have hcluster' : ∀ j, |μ.node j 0 - center| ≤ τ * θ / 2 := by
    simpa only [IsLocalCluster1D, θ] using hcluster
  have hnodeSep : ∀ i j, i ≠ j → θ ≤ |μ.node i 0 - μ.node j 0| := by
    intro i j hij
    exact minimumSeparation1D_le (fun j => μ.node j 0) hn hij
  have hrowVDM := hrowBound hθ hθrow hcluster' hnodeSep
  have hcolumnVDM := hcolumnBound hθ hθcolumn hcluster' hnodeSep
  rw [← randomRowVandermonde_eq_fourierVandermonde] at hrowVDM hcolumnVDM
  let γrow := RandSamp.finiteFamilySamplingSpread
    (realizedRealFrequency rowFrequency) n hM₁.le hn
  let γcolumn := RandSamp.finiteFamilySamplingSpread
    (realizedRealFrequency columnFrequency) n hM₂.le hn
  let c := (1 / 2 : ℝ) * RandSamp.nonuniformVandermondeConstant n
  let L := c * (Ω / n * θ) ^ (n - 1)
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (by norm_num)
      (RandSamp.nonuniformVandermondeConstant_pos hnPos)
  have hspread' : Ω / (n : ℝ) ≤ min γrow γcolumn := by
    simpa only [randomGHMSpreadConstant, one_mul, γrow, γcolumn] using hspread
  have hrowSpread : Ω / (n : ℝ) ≤ γrow :=
    hspread'.trans (min_le_left _ _)
  have hcolumnSpread : Ω / (n : ℝ) ≤ γcolumn :=
    hspread'.trans (min_le_right _ _)
  have hrowBase : Ω / (n : ℝ) * θ ≤ γrow * θ :=
    mul_le_mul_of_nonneg_right hrowSpread hθ.le
  have hcolumnBase : Ω / (n : ℝ) * θ ≤ γcolumn * θ :=
    mul_le_mul_of_nonneg_right hcolumnSpread hθ.le
  have hLrow :
      L ≤ matrixSingularValue (randomRowVandermonde rowFrequency μ) (n - 1) := by
    apply (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hrowBase (n - 1)) hc.le).trans
    simpa only [L, c, γrow] using hrowVDM
  have hLcolumn :
      L ≤ matrixSingularValue (randomRowVandermonde columnFrequency μ) (n - 1) := by
    apply (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hcolumnBase (n - 1)) hc.le).trans
    simpa only [L, c, γcolumn] using hcolumnVDM
  have hLnonneg : 0 ≤ L := by
    dsimp [L]
    positivity
  have hmMin : 0 < minAmplitude μ (Nat.zero_lt_of_lt hn) :=
    minAmplitude_pos μ (Nat.zero_lt_of_lt hn)
  have hmodelGap :
      2 * σ * Real.sqrt (M₁ * M₂) <
        minAmplitude μ (Nat.zero_lt_of_lt hn) * L * L := by
    simpa only [L, c] using
      (randomGHM_separation_implies_model_gap hn (by omega) (by omega)
        hΩ hσ hmMin (by simpa only [θ] using hseparation))
  have hsignalLower :
      minAmplitude μ (Nat.zero_lt_of_lt hn) * L * L ≤
        minAmplitude μ (Nat.zero_lt_of_lt hn) *
          matrixSingularValue (randomRowVandermonde rowFrequency μ) (n - 1) *
          matrixSingularValue (randomRowVandermonde columnFrequency μ) (n - 1) := by
    calc
      minAmplitude μ (Nat.zero_lt_of_lt hn) * L * L =
          minAmplitude μ (Nat.zero_lt_of_lt hn) * (L * L) := by ring
      _ ≤ minAmplitude μ (Nat.zero_lt_of_lt hn) *
            (matrixSingularValue (randomRowVandermonde rowFrequency μ) (n - 1) *
              matrixSingularValue (randomRowVandermonde columnFrequency μ) (n - 1)) := by
        apply mul_le_mul_of_nonneg_left _ hmMin.le
        exact mul_le_mul hLrow hLcolumn hLnonneg
          (matrixSingularValue_nonneg _ _)
      _ = minAmplitude μ (Nat.zero_lt_of_lt hn) *
            matrixSingularValue (randomRowVandermonde rowFrequency μ) (n - 1) *
            matrixSingularValue (randomRowVandermonde columnFrequency μ) (n - 1) := by
        ring
  rcases randomGHM_singularValueThreshold rowFrequency columnFrequency μ Y
      hn hM₁ hM₂ hrowInjective hcolumnInjective hΩ hσ hmeasurement hband
      (hmodelGap.trans_le hsignalLower) with ⟨_htail, _hlower, hsignal⟩
  exact hsignal

end

end NumDetect
end LeanNumDetect
