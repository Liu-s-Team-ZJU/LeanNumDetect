import NumDetectMain.SegmentedDefinitions
import NumDetectMain.ProofSupport
import General.MatrixAnalysis.SingularValueBounds

/-!
Complete support for the segmented singular-value threshold theorem.

The final theorem is conditional on an explicit lower bound `B` for the last
column singular value of the segmented Vandermonde matrix.  It therefore does
not depend on the unfinished manuscript-facing Vandermonde theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators Matrix.Norms.L2Operator

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Every frequency queried by the segmented GHM lies in its declared band. -/
theorem segmentedThreshold_query_in_band
    {d m r D : ℕ} (α β : SegmentedIndex d m r) :
    InFrequencyBand (segmentedCutoff m r D) (fun k =>
      segmentedFrequency d m r D α k +
        segmentedFrequency d m r D β k - segmentedCutoff m r D) := by
  intro k
  simp only [segmentedFrequency, segmentedCutoff]
  have hαr : (α k).1.val ≤ r := Nat.le_of_lt_succ (α k).1.isLt
  have hβr : (β k).1.val ≤ r := Nat.le_of_lt_succ (β k).1.isLt
  have hαm : (α k).2.val ≤ m := Nat.le_of_lt_succ (α k).2.isLt
  have hβm : (β k).2.val ≤ m := Nat.le_of_lt_succ (β k).2.isLt
  have hα : D * (α k).1.val + (α k).2.val ≤ r * D + m := by
    nlinarith [Nat.mul_le_mul_left D hαr]
  have hβ : D * (β k).1.val + (β k).2.val ≤ r * D + m := by
    nlinarith [Nat.mul_le_mul_left D hβr]
  push_cast
  rw [abs_le]
  have hαR : (D : ℝ) * (α k).1.val + (α k).2.val ≤
      (r : ℝ) * D + m := by exact_mod_cast hα
  have hβR : (D : ℝ) * (β k).1.val + (β k).2.val ≤
      (r : ℝ) * D + m := by exact_mod_cast hβ
  constructor <;>
    nlinarith [show (0 : ℝ) ≤ D * (α k).1.val + (α k).2.val by positivity,
      show (0 : ℝ) ≤ D * (β k).1.val + (β k).2.val by positivity]

/-- The segmented measurement perturbation is pointwise strictly below `σ`. -/
theorem segmentedThreshold_entrywise_perturbation
    {d n m r D : ℕ} {σ : ℝ}
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (hmeasurement : IsBandMeasurement μ (segmentedCutoff m r D) σ Y)
    (α β : SegmentedIndex d m r) :
    ‖(segmentedMeasurementMatrix m r D Y -
        segmentedMeasurementMatrix m r D (fourier μ)) α β‖ < σ := by
  rcases hmeasurement with ⟨W, hW, hY⟩
  let ω : Point d := fun k =>
    segmentedFrequency d m r D α k +
      segmentedFrequency d m r D β k - segmentedCutoff m r D
  have hband : InFrequencyBand (segmentedCutoff m r D) ω :=
    segmentedThreshold_query_in_band α β
  have hvalue := hY ω hband
  have hnoise := hW ω hband
  simp only [segmentedMeasurementMatrix, Matrix.sub_apply]
  rw [hvalue, add_sub_cancel_left]
  exact hnoise

/-- The segmented row index has cardinality `L^d`. -/
theorem card_segmentedIndex (d m r : ℕ) :
    Fintype.card (SegmentedIndex d m r) = (segmentedLength m r) ^ d := by
  simp [SegmentedIndex, SegmentedCoordinateIndex, segmentedLength]

/-- The noiseless segmented matrix has rank at most the source count. -/
theorem segmentedThreshold_noiseless_rank_le
    {d n m r D : ℕ} (μ : AtomicMeasure d n) :
    (segmentedNoiselessMatrix m r D μ).rank ≤ n := by
  rw [segmentedNoiselessMatrix]
  exact
    (Matrix.rank_mul_le_left
      (segmentedVandermonde m r D μ.node *
        Matrix.diagonal (segmentedPhaseAmplitude m r D μ))
      (segmentedColumnVandermonde m r D μ.node)ᵀ).trans
      ((Matrix.rank_le_card_width
        (segmentedVandermonde m r D μ.node *
          Matrix.diagonal (segmentedPhaseAmplitude m r D μ))).trans (by simp))

/-- All noiseless singular values from the source count onward vanish. -/
theorem segmentedThreshold_noiseless_singularValue_eq_zero
    {d n m r D i : ℕ} (μ : AtomicMeasure d n) (hi : n ≤ i) :
    matrixSingularValue (segmentedNoiselessMatrix m r D μ) i = 0 :=
  matrixSingularValue_eq_zero_of_rank_le _
    ((segmentedThreshold_noiseless_rank_le μ).trans hi)

/-- The entrywise noise budget gives the square-matrix operator-norm budget
`L^d σ`. -/
theorem segmentedThreshold_perturbation_spectralNorm_le
    {d n m r D : ℕ} {σ : ℝ}
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (hmeasurement : IsBandMeasurement μ (segmentedCutoff m r D) σ Y) :
    matrixSpectralNorm
        (segmentedMeasurementMatrix m r D Y -
          segmentedMeasurementMatrix m r D (fourier μ)) ≤
      (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ := by
  let Δ :=
    segmentedMeasurementMatrix m r D Y -
      segmentedMeasurementMatrix m r D (fourier μ)
  have hentry : ∀ i j, ‖Δ i j‖ < σ := by
    intro i j
    exact segmentedThreshold_entrywise_perturbation μ Y hmeasurement i j
  have hbound :=
    matrixSpectralNorm_le_card_sqrt_mul_of_lt Δ hentry
  change matrixSpectralNorm Δ ≤
    Real.sqrt
      ((Fintype.card (SegmentedIndex d m r) : ℝ) *
        (Fintype.card (SegmentedIndex d m r) : ℝ)) * σ at hbound
  rw [card_segmentedIndex] at hbound
  change matrixSpectralNorm Δ ≤
    (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ
  calc
    matrixSpectralNorm Δ
        ≤ Real.sqrt
            ((((segmentedLength m r) ^ d : ℕ) : ℝ) *
              (((segmentedLength m r) ^ d : ℕ) : ℝ)) * σ :=
      hbound
    _ = (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ := by
      rw [Real.sqrt_mul_self (by positivity)]

/-- Positivity of the last column singular value implies full column rank. -/
theorem segmentedThreshold_fullColumnRank_of_lastSingularValue_pos
    {q : Type*} [Fintype q] {n : ℕ}
    (A : Matrix q (Fin n) ℂ) (hn : 0 < n)
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

/-- A positive lower bound for the Vandermonde singular value gives the
corresponding three-factor lower bound for the noiseless segmented GHM. -/
theorem segmentedThreshold_noiseless_signal_lower
    {d n m r D : ℕ} {mMin B : ℝ}
    (μ : AtomicMeasure d n) (hn : 0 < n)
    (hmMin : minAmplitude μ hn = mMin)
    (hBpos : 0 < B)
    (hB : B ≤
      matrixSingularValue (segmentedVandermonde m r D μ.node) (n - 1)) :
    mMin * B ^ 2 ≤
      matrixSingularValue (segmentedNoiselessMatrix m r D μ) (n - 1) := by
  let V := segmentedVandermonde m r D μ.node
  have hVpos : 0 < matrixSingularValue V (n - 1) := hBpos.trans_le hB
  have hfull : HasFullColumnRank V :=
    segmentedThreshold_fullColumnRank_of_lastSingularValue_pos V hn hVpos
  have hinjective : Function.Injective V.toEuclideanLin :=
    toEuclideanLin_injective_of_fullColumnRank V hfull
  have hcard : n ≤ Fintype.card (SegmentedIndex d m r) := by
    have hdim := LinearMap.finrank_le_finrank_of_injective hinjective
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using hdim
  have hmPos : 0 < mMin := by
    rw [← hmMin]
    exact minAmplitude_pos μ hn
  have hproduct :
      mMin * matrixSingularValue V (n - 1) *
          matrixSingularValue V (n - 1) ≤
        matrixSingularValue (segmentedNoiselessMatrix m r D μ) (n - 1) := by
    rw [segmentedNoiselessMatrix]
    change
      mMin * matrixSingularValue V (n - 1) *
          matrixSingularValue V (n - 1) ≤
        matrixSingularValue
          (V * Matrix.diagonal (segmentedPhaseAmplitude m r D μ) * Vᵀ) (n - 1)
    simpa only [Fintype.card_fin] using
      (matrixSingularValue_diagonal_transpose_lower_of_fullColumnRank
        V (segmentedPhaseAmplitude m r D μ) V hn hcard hfull hmPos.le
        (fun j => by
          rw [norm_segmentedPhaseAmplitude, ← hmMin]
          exact minAmplitude_le μ hn j))
  have hsquare :
      B ^ 2 ≤ matrixSingularValue V (n - 1) ^ 2 :=
    (sq_le_sq₀ hBpos.le (matrixSingularValue_nonneg V (n - 1))).2 hB
  calc
    mMin * B ^ 2 ≤ mMin * matrixSingularValue V (n - 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare hmPos.le
    _ = mMin * matrixSingularValue V (n - 1) *
          matrixSingularValue V (n - 1) := by ring
    _ ≤ _ := hproduct

/-- Weyl transfers a noiseless gap larger than twice the noise budget to the
measured singular value. -/
theorem segmentedThreshold_signal_weyl
    {d n m r D : ℕ} {σ : ℝ}
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (_hn : 0 < n)
    (hmeasurement : IsBandMeasurement μ (segmentedCutoff m r D) σ Y)
    (hgap :
      2 * (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ <
        matrixSingularValue (segmentedNoiselessMatrix m r D μ) (n - 1)) :
    (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ <
      matrixSingularValue (segmentedMeasurementMatrix m r D Y) (n - 1) := by
  let G := segmentedMeasurementMatrix m r D Y
  let G₀ := segmentedMeasurementMatrix m r D (fourier μ)
  let Δ := G - G₀
  have hfactor : G₀ = segmentedNoiselessMatrix m r D μ :=
    segmentedMeasurementMatrix_fourier_eq_noiseless m r D μ
  have hnorm :
      matrixSpectralNorm Δ ≤
        (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ :=
    segmentedThreshold_perturbation_spectralNorm_le μ Y hmeasurement
  have hindex : n - 1 < Fintype.card (SegmentedIndex d m r) := by
    by_contra h
    have hz :
        matrixSingularValue (segmentedNoiselessMatrix m r D μ) (n - 1) = 0 := by
      apply matrixSingularValue_eq_zero_of_rank_le
      exact (Matrix.rank_le_card_width
        (segmentedNoiselessMatrix m r D μ)).trans (Nat.le_of_not_gt h)
    rw [hz] at hgap
    have hσnonneg : 0 ≤ σ := by
      rcases hmeasurement with ⟨W, hW, _⟩
      have hband :
          InFrequencyBand (segmentedCutoff m r D) (0 : Point d) := by
        intro k
        simp only [Pi.zero_apply, abs_zero]
        positivity
      exact (norm_nonneg (W (0 : Point d))).trans
        (hW (0 : Point d) hband).le
    have hbudget :
        0 ≤ 2 * (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ := by
      positivity
    linarith
  have hweyl :=
    matrixSingularValue_sub_spectralNorm_le_add
      (segmentedNoiselessMatrix m r D μ) Δ
      (i := n - 1) (by simpa [card_segmentedIndex] using hindex)
  have hsum : segmentedNoiselessMatrix m r D μ + Δ = G := by
    rw [← hfactor]
    simp only [Δ, G, G₀]
    abel
  rw [hsum] at hweyl
  linarith

/-- Matrix-theoretic threshold conclusion from a parameterized Vandermonde
lower bound and its squared signal gap. -/
theorem segmentedGHM_singularValueThreshold_of_lowerBound
    {d n m r D : ℕ} {σ mMin B : ℝ}
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (hn : 2 ≤ n) (_hσ : 0 < σ)
    (hmMin : minAmplitude μ (Nat.zero_lt_of_lt hn) = mMin)
    (hmeasurement :
      IsBandMeasurement μ (segmentedCutoff m r D) σ Y)
    (hBpos : 0 < B)
    (hB : B ≤
      matrixSingularValue (segmentedVandermonde m r D μ.node) (n - 1))
    (hgap :
      2 * (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ < mMin * B ^ 2) :
    (∀ j, n ≤ j → j < (segmentedLength m r) ^ d →
      matrixSingularValue (segmentedMeasurementMatrix m r D Y) j ≤
        ((segmentedLength m r : ℕ) : ℝ) ^ d * σ) ∧
    (((segmentedLength m r : ℕ) : ℝ) ^ d * σ <
      matrixSingularValue (segmentedMeasurementMatrix m r D Y) (n - 1)) := by
  let G := segmentedMeasurementMatrix m r D Y
  let G₀ := segmentedMeasurementMatrix m r D (fourier μ)
  let Δ := G - G₀
  have hfactor : G₀ = segmentedNoiselessMatrix m r D μ :=
    segmentedMeasurementMatrix_fourier_eq_noiseless m r D μ
  have hnorm :
      matrixSpectralNorm Δ ≤
        (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ :=
    segmentedThreshold_perturbation_spectralNorm_le μ Y hmeasurement
  have hnoise :
      ∀ j, n ≤ j → j < (segmentedLength m r) ^ d →
        matrixSingularValue G j ≤
          ((segmentedLength m r : ℕ) : ℝ) ^ d * σ := by
    intro j hj hjcard
    have hzero : matrixSingularValue G₀ j = 0 := by
      rw [hfactor]
      exact segmentedThreshold_noiseless_singularValue_eq_zero μ hj
    have hsum : G₀ + Δ = G := by
      simp only [Δ]
      abel
    have hweyl :=
      matrixSingularValue_add_le_add_spectralNorm G₀ Δ
        (i := j) (by
          rw [card_segmentedIndex]
          exact hjcard)
    rw [hsum, hzero, zero_add] at hweyl
    calc
      matrixSingularValue G j ≤
          (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ :=
        hweyl.trans hnorm
      _ = ((segmentedLength m r : ℕ) : ℝ) ^ d * σ := by
        rw [Nat.cast_pow]
  have hnoiseless :
      2 * (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ <
        matrixSingularValue (segmentedNoiselessMatrix m r D μ) (n - 1) :=
    hgap.trans_le
      (segmentedThreshold_noiseless_signal_lower μ
        (Nat.zero_lt_of_lt hn) hmMin hBpos hB)
  refine ⟨hnoise, ?_⟩
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    segmentedThreshold_signal_weyl μ Y (Nat.zero_lt_of_lt hn)
      hmeasurement hnoiseless

/-- The elementary growth estimate used to dominate the segmented grid size. -/
theorem two_mul_add_one_le_five_pow_sub_one
    {nStar : ℕ} (hnStar : 2 ≤ nStar) :
    2 * nStar + 1 ≤ 5 ^ (nStar - 1) := by
  have aux : ∀ k : ℕ, 2 * (k + 2) + 1 ≤ 5 ^ (k + 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        calc
          2 * (k + 1 + 2) + 1 ≤ 5 * (2 * (k + 2) + 1) := by omega
          _ ≤ 5 * 5 ^ (k + 1) := Nat.mul_le_mul_left 5 ih
          _ = 5 ^ (k + 1) * 5 := by ring
          _ = 5 ^ ((k + 1) + 1) := (pow_succ 5 (k + 1)).symm
          _ = 5 ^ (k + 1 + 1) := by rfl
  obtain ⟨k, hk⟩ : ∃ k, nStar = k + 2 := ⟨nStar - 2, by omega⟩
  subst nStar
  simpa only [show k + 2 - 1 = k + 1 by omega] using aux k

/-- The factor `5^(nStar-1)` in the separation threshold dominates the
one-dimensional segmented grid size. -/
theorem segmentedLength_le_constant_factor
    {nStar m r : ℕ} (hnStar : 2 ≤ nStar) (hr : 2 * nStar ≤ r) :
    (segmentedLength m r : ℝ) ≤
      (5 : ℝ) ^ (nStar - 1) * ((r : ℝ) / nStar) *
        (((m / 2 + 1 : ℕ) : ℝ)) := by
  have hnStarPos : 0 < nStar := by omega
  have hrPos : 0 < r := by omega
  have hfiveNat : 2 * nStar + 1 ≤ 5 ^ (nStar - 1) :=
    two_mul_add_one_le_five_pow_sub_one hnStar
  have hcoarseNat :
      2 * nStar * (r + 1) ≤ 5 ^ (nStar - 1) * r := by
    calc
      2 * nStar * (r + 1)
          = 2 * nStar * r + 2 * nStar := by ring
      _ ≤ 2 * nStar * r + r := by omega
      _ = (2 * nStar + 1) * r := by ring
      _ ≤ 5 ^ (nStar - 1) * r := Nat.mul_le_mul_right r hfiveNat
  have hfineNat : m + 1 ≤ 2 * (m / 2 + 1) := by omega
  have hcoarse :
      (2 : ℝ) * nStar * (r + 1) ≤
        (5 : ℝ) ^ (nStar - 1) * r := by
    exact_mod_cast hcoarseNat
  have hfine :
      (m + 1 : ℕ) ≤ 2 * (m / 2 + 1) := hfineNat
  have hfineR :
      (m + 1 : ℝ) ≤ 2 * ((m / 2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast hfine
  rw [segmentedLength]
  rw [show
    (5 : ℝ) ^ (nStar - 1) * ((r : ℝ) / nStar) *
        (((m / 2 + 1 : ℕ) : ℝ)) =
      ((5 : ℝ) ^ (nStar - 1) * r *
        (((m / 2 + 1 : ℕ) : ℝ))) / nStar by field_simp]
  apply (le_div_iff₀ (by exact_mod_cast hnStarPos : (0 : ℝ) < nStar)).2
  have h₁ := mul_le_mul_of_nonneg_left hfineR
    (show (0 : ℝ) ≤ nStar * (r + 1) by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hcoarse
    (show (0 : ℝ) ≤ ((m / 2 + 1 : ℕ) : ℝ) by positivity)
  push_cast
  calc
    ((r : ℝ) + 1) * ((m : ℝ) + 1) * (nStar : ℝ) =
        (nStar : ℝ) * ((r : ℝ) + 1) * ((m : ℝ) + 1) := by ring
    _ ≤ (nStar : ℝ) * ((r : ℝ) + 1) *
        (2 * ((m / 2 + 1 : ℕ) : ℝ)) := h₁
    _ = 2 * (nStar : ℝ) * ((r : ℝ) + 1) *
        ((m / 2 + 1 : ℕ) : ℝ) := by ring
    _ ≤ (5 : ℝ) ^ (nStar - 1) * (r : ℝ) *
        ((m / 2 + 1 : ℕ) : ℝ) := h₂
    _ = (5 : ℝ) ^ (nStar - 1) * (r : ℝ) *
        (((m / 2 : ℕ) : ℝ) + 1) := by norm_num

/-- Raising the threshold's positive root to its defining integer power
cancels the real exponent. -/
theorem thresholdRoot_pow
    {n nStar : ℕ} {σ mMin : ℝ}
    (hn : 0 < n) (hnStar : 2 ≤ nStar) (hσ : 0 < σ) (hmMin : 0 < mMin) :
    ((2 * n * σ / mMin) ^ (1 / (2 * (nStar : ℝ) - 2))) ^
        (2 * (nStar - 1)) =
      2 * n * σ / mMin := by
  have hbase : 0 < 2 * (n : ℝ) * σ / mMin := by positivity
  have hexp :
      (1 / (2 * (nStar : ℝ) - 2)) *
          ((2 * (nStar - 1) : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ nStar)]
    have hne : (nStar : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < nStar := by exact_mod_cast hnStar
      exact sub_ne_zero.mpr (ne_of_gt this)
    norm_num
    field_simp
  rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le, hexp, Real.rpow_one]

/-- Squaring the explicit segmented Vandermonde lower bound removes all
square roots and records the normalization in a form suitable for algebra. -/
theorem segmentedVandermondeLowerBound_sq
    {d n nStar m r D : ℕ} {β Δ : ℝ}
    (hn : 0 < n) (hnStar : 0 < nStar)
    (hq : 0 < 2 - Real.exp (1 / (2 * β))) :
    (segmentedVandermondeLowerBound d n nStar m r D β Δ) ^ 2 =
      1 / n *
        (2 - Real.exp (1 / (2 * β))) ^ (nStar : ℕ) *
        (((r : ℝ) / nStar) ^ d *
          (((m / 2 + 1 : ℕ) : ℝ) ^ d)) /
        2 ^ (nStar - 1) *
        ((((r * D : ℕ) : ℝ) / (Real.pi * nStar) * Δ) ^
          (2 * (nStar - 1))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnStarR : (0 : ℝ) < nStar := by exact_mod_cast hnStar
  have hA :
      0 ≤ ((r : ℝ) / nStar) ^ d *
        (((m / 2 + 1 : ℕ) : ℝ) ^ d) := by positivity
  have hrootn : (1 / Real.sqrt n) ^ 2 = 1 / (n : ℝ) := by
    simp only [one_div]
    rw [inv_pow, Real.sq_sqrt hnR.le]
  have hqpow :
      ((2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2)) ^ 2 =
        (2 - Real.exp (1 / (2 * β))) ^ (nStar : ℕ) := by
    calc
      ((2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2)) ^ 2 =
          ((2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2)) ^
            (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = (2 - Real.exp (1 / (2 * β))) ^
          (((nStar : ℝ) / 2) * 2) :=
        (Real.rpow_mul hq.le _ _).symm
      _ = (2 - Real.exp (1 / (2 * β))) ^ (nStar : ℝ) := by
        congr 1
        ring
      _ = (2 - Real.exp (1 / (2 * β))) ^ (nStar : ℕ) :=
        Real.rpow_natCast _ _
  have hsqrtA : (Real.sqrt
      (((r : ℝ) / nStar) ^ d *
        (((m / 2 + 1 : ℕ) : ℝ) ^ d))) ^ 2 =
      ((r : ℝ) / nStar) ^ d *
        (((m / 2 + 1 : ℕ) : ℝ) ^ d) :=
    Real.sq_sqrt hA
  have hsqrtTwo :
      ((Real.sqrt 2) ^ (nStar - 1)) ^ 2 =
        (2 : ℝ) ^ (nStar - 1) := by
    calc
      ((Real.sqrt 2) ^ (nStar - 1)) ^ 2 =
          (Real.sqrt 2) ^ ((nStar - 1) * 2) := by rw [pow_mul]
      _ = (Real.sqrt 2) ^ (2 * (nStar - 1)) := by
        congr 1
        omega
      _ = ((Real.sqrt 2) ^ 2) ^ (nStar - 1) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (nStar - 1) := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hzpow :
      ((((r * D : ℕ) : ℝ) / (Real.pi * nStar) * Δ) ^
        (nStar - 1)) ^ 2 =
      (((r * D : ℕ) : ℝ) / (Real.pi * nStar) * Δ) ^
        (2 * (nStar - 1)) := by
    rw [← pow_mul]
    congr 1
    omega
  unfold segmentedVandermondeLowerBound
  rw [show
    (1 / Real.sqrt n *
          (2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2) *
          Real.sqrt
            (((r : ℝ) / nStar) ^ d *
              (((m / 2 + 1 : ℕ) : ℝ) ^ d)) /
          (Real.sqrt 2) ^ (nStar - 1) *
          ((((r * D : ℕ) : ℝ) / (Real.pi * nStar) * Δ) ^
            (nStar - 1))) ^ 2 =
      (1 / Real.sqrt n) ^ 2 *
          ((2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2)) ^ 2 *
          (Real.sqrt
            (((r : ℝ) / nStar) ^ d *
              (((m / 2 + 1 : ℕ) : ℝ) ^ d))) ^ 2 /
          ((Real.sqrt 2) ^ (nStar - 1)) ^ 2 *
          (((((r * D : ℕ) : ℝ) / (Real.pi * nStar) * Δ) ^
            (nStar - 1)) ^ 2) by ring]
  rw [hrootn, hqpow, hsqrtA, hsqrtTwo, hzpow]

/-- The exponential base in the segmented Vandermonde estimate is positive
under the manuscript's hypothesis on `β`. -/
theorem segmentedThreshold_exponentialBase_pos
    {β : ℝ} (hβ : 1 / (2 * Real.log 2) < β) :
    0 < 2 - Real.exp (1 / (2 * β)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβpos : 0 < β :=
    (by positivity : 0 < 1 / (2 * Real.log 2)).trans hβ
  have hexponent : 1 / (2 * β) < Real.log 2 := by
    have h := (div_lt_iff₀ (by positivity : 0 < 2 * Real.log 2)).1 hβ
    apply (div_lt_iff₀ (by positivity : 0 < 2 * β)).2
    nlinarith
  have hexp : Real.exp (1 / (2 * β)) < 2 := by
    calc
      Real.exp (1 / (2 * β)) < Real.exp (Real.log 2) :=
        Real.exp_lt_exp.mpr hexponent
      _ = 2 := Real.exp_log (by norm_num)
  linarith

/-- The same exponential base is at most one. -/
theorem segmentedThreshold_exponentialBase_le_one
    {β : ℝ} (hβ : 1 / (2 * Real.log 2) < β) :
    2 - Real.exp (1 / (2 * β)) ≤ 1 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβpos : 0 < β :=
    (by positivity : 0 < 1 / (2 * Real.log 2)).trans hβ
  have hexponent : 0 < 1 / (2 * β) := by positivity
  have hexp : 1 < Real.exp (1 / (2 * β)) := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hexponent
  linarith

/-- After multiplication by `rD/(π nStar)`, the displayed separation
threshold dominates the simpler factor used in the power calculation. -/
theorem segmentedThreshold_normalizedSeparation_gt
    {d n nStar m r D : ℕ} {β σ mMin Δ : ℝ}
    (hn : 0 < n) (hnStar : 2 ≤ nStar)
    (hm : 1 ≤ m) (hD : m < D) (hr : 2 * nStar ≤ r)
    (hβ : 1 / (2 * Real.log 2) < β)
    (hσ : 0 < σ) (hmMin : 0 < mMin)
    (hseparation :
      segmentedDetectionSeparationThreshold
          d n nStar m r D β σ mMin < Δ) :
    Real.sqrt 2 * (Real.sqrt 5) ^ d /
          (2 - Real.exp (1 / (2 * β))) *
        (2 * n * σ / mMin) ^ (1 / (2 * (nStar : ℝ) - 2)) <
      (((r * D : ℕ) : ℝ) / (Real.pi * nStar)) * Δ := by
  have hnStarPos : 0 < nStar := by omega
  have hrPos : 0 < r := by omega
  have hDPos : 0 < D := Nat.zero_lt_of_lt (hm.trans_lt hD)
  have hcutoffPos : 0 < segmentedCutoff m r D := by
    unfold segmentedCutoff
    positivity
  have hq :
      0 < 2 - Real.exp (1 / (2 * β)) :=
    segmentedThreshold_exponentialBase_pos hβ
  have hroot :
      0 < (2 * n * σ / mMin) ^ (1 / (2 * (nStar : ℝ) - 2)) := by
    apply Real.rpow_pos_of_pos
    positivity
  have hscale :
      0 < ((r * D : ℕ) : ℝ) / (Real.pi * nStar) := by
    positivity
  have hmCast : (m : ℝ) < D := by exact_mod_cast hD
  have hrCast : (2 : ℝ) * nStar ≤ r := by exact_mod_cast hr
  have hcore :
      ((segmentedCutoff m r D : ℕ) : ℝ) * nStar <
        ((r * D : ℕ) : ℝ) * ((nStar : ℝ) + 1 / 2) := by
    unfold segmentedCutoff
    push_cast
    nlinarith [mul_lt_mul_of_pos_right hmCast
      (show (0 : ℝ) < 2 * nStar by positivity),
      mul_le_mul_of_nonneg_right hrCast (show (0 : ℝ) ≤ D by positivity)]
  have hratio :
      1 <
        (((r * D : ℕ) : ℝ) / (Real.pi * nStar)) *
          (Real.pi * ((nStar : ℝ) + 1 / 2) /
            segmentedCutoff m r D) := by
    rw [show
      (((r * D : ℕ) : ℝ) / (Real.pi * nStar)) *
          (Real.pi * ((nStar : ℝ) + 1 / 2) /
            segmentedCutoff m r D) =
        (((r * D : ℕ) : ℝ) * ((nStar : ℝ) + 1 / 2)) /
          ((nStar : ℝ) * segmentedCutoff m r D) by field_simp]
    exact (one_lt_div
      (by positivity : 0 < (nStar : ℝ) * segmentedCutoff m r D)).2
      (calc
        (nStar : ℝ) * segmentedCutoff m r D =
            (segmentedCutoff m r D : ℝ) * nStar := by ring
        _ < ((r * D : ℕ) : ℝ) * ((nStar : ℝ) + 1 / 2) := hcore)
  let C :=
    Real.sqrt 2 * (Real.sqrt 5) ^ d /
      (2 - Real.exp (1 / (2 * β)))
  let x :=
    (2 * n * σ / mMin) ^ (1 / (2 * (nStar : ℝ) - 2))
  let a := ((r * D : ℕ) : ℝ) / (Real.pi * nStar)
  let b :=
    Real.pi * ((nStar : ℝ) + 1 / 2) / segmentedCutoff m r D
  have hCx : 0 < C * x := by
    dsimp [C, x]
    positivity
  have hcoefficient : C * x < a *
      segmentedDetectionSeparationThreshold
        d n nStar m r D β σ mMin := by
    calc
      C * x = C * x * 1 := by ring
      _ < C * x * (a * b) := mul_lt_mul_of_pos_left hratio hCx
      _ = a * segmentedDetectionSeparationThreshold
          d n nStar m r D β σ mMin := by
        dsimp [C, x, a, b, segmentedDetectionSeparationThreshold]
        field_simp
  exact hcoefficient.trans
    (mul_lt_mul_of_pos_left hseparation hscale)

/-- The manuscript's explicit separation threshold makes the square of the
segmented Vandermonde lower bound exceed twice the full noise budget. -/
theorem segmentedThreshold_explicitLowerBound_gap
    {d n nStar m r D : ℕ} {β σ mMin Δ : ℝ}
    (hn : 2 ≤ n) (hnStar : 2 ≤ nStar)
    (hm : 1 ≤ m) (hD : m < D) (hr : 2 * nStar ≤ r)
    (hβ : 1 / (2 * Real.log 2) < β)
    (hσ : 0 < σ) (hmMin : 0 < mMin)
    (hseparation :
      segmentedDetectionSeparationThreshold
          d n nStar m r D β σ mMin < Δ) :
    2 * (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ <
      mMin *
        (segmentedVandermondeLowerBound
          d n nStar m r D β Δ) ^ 2 := by
  let q := 2 - Real.exp (1 / (2 * β))
  let x := (2 * n * σ / mMin) ^ (1 / (2 * (nStar : ℝ) - 2))
  let z := (((r * D : ℕ) : ℝ) / (Real.pi * nStar)) * Δ
  let A :=
    ((r : ℝ) / nStar) ^ d *
      (((m / 2 + 1 : ℕ) : ℝ) ^ d)
  let C := Real.sqrt 2 * (Real.sqrt 5) ^ d / q
  let N := 2 * (nStar - 1)
  have hnPos : 0 < n := by omega
  have hnStarPos : 0 < nStar := by omega
  have hq : 0 < q := by
    exact segmentedThreshold_exponentialBase_pos hβ
  have hqOne : q ≤ 1 := by
    exact segmentedThreshold_exponentialBase_le_one hβ
  have hx : 0 < x := by
    dsimp [x]
    apply Real.rpow_pos_of_pos
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hnormalized : C * x < z := by
    exact segmentedThreshold_normalizedSeparation_gt
      hnPos hnStar hm hD hr hβ hσ hmMin hseparation
  have hz : 0 < z := (mul_pos hC hx).trans hnormalized
  have hN : N ≠ 0 := by
    dsimp [N]
    omega
  have hpow : (C * x) ^ N < z ^ N :=
    pow_lt_pow_left₀ hnormalized (mul_pos hC hx).le hN
  have hsqrtTwo :
      (Real.sqrt 2) ^ N = (2 : ℝ) ^ (nStar - 1) := by
    dsimp [N]
    calc
      (Real.sqrt 2) ^ (2 * (nStar - 1)) =
          ((Real.sqrt 2) ^ 2) ^ (nStar - 1) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (nStar - 1) := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtFive :
      ((Real.sqrt 5) ^ d) ^ N =
        (5 : ℝ) ^ (d * (nStar - 1)) := by
    dsimp [N]
    calc
      ((Real.sqrt 5) ^ d) ^ (2 * (nStar - 1)) =
          (Real.sqrt 5) ^ (d * (2 * (nStar - 1))) :=
        (pow_mul (Real.sqrt 5) d (2 * (nStar - 1))).symm
      _ = (Real.sqrt 5) ^ (2 * (d * (nStar - 1))) := by
        congr 1
        ring
      _ = ((Real.sqrt 5) ^ 2) ^ (d * (nStar - 1)) :=
        pow_mul (Real.sqrt 5) 2 (d * (nStar - 1))
      _ = (5 : ℝ) ^ (d * (nStar - 1)) := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  have hCpow :
      C ^ N =
        (2 : ℝ) ^ (nStar - 1) *
          (5 : ℝ) ^ (d * (nStar - 1)) / q ^ N := by
    dsimp [C]
    rw [div_pow, mul_pow, hsqrtTwo, hsqrtFive]
  have hxpow : x ^ N = 2 * n * σ / mMin := by
    dsimp [x, N]
    exact thresholdRoot_pow hnPos hnStar hσ hmMin
  have hCxpow :
      (C * x) ^ N =
        ((2 : ℝ) ^ (nStar - 1) *
          (5 : ℝ) ^ (d * (nStar - 1)) / q ^ N) *
        (2 * n * σ / mMin) := by
    rw [mul_pow, hCpow, hxpow]
  have hlength :
      (segmentedLength m r : ℝ) ≤
        (5 : ℝ) ^ (nStar - 1) * ((r : ℝ) / nStar) *
          (((m / 2 + 1 : ℕ) : ℝ)) :=
    segmentedLength_le_constant_factor hnStar hr
  have hspatial :
      (((segmentedLength m r) ^ d : ℕ) : ℝ) ≤
        (5 : ℝ) ^ (d * (nStar - 1)) * A := by
    have hp := pow_le_pow_left₀
      (show (0 : ℝ) ≤ segmentedLength m r by positivity) hlength d
    rw [Nat.cast_pow]
    calc
      (segmentedLength m r : ℝ) ^ d
          ≤ ((5 : ℝ) ^ (nStar - 1) * ((r : ℝ) / nStar) *
              (((m / 2 + 1 : ℕ) : ℝ))) ^ d := hp
      _ = (5 : ℝ) ^ (d * (nStar - 1)) * A := by
        dsimp [A]
        rw [mul_pow, mul_pow, ← pow_mul]
        ring
  have hqPowers : q ^ N ≤ q ^ (nStar : ℕ) := by
    apply pow_le_pow_of_le_one hq.le hqOne
    dsimp [N]
    omega
  have hqRatio : 1 ≤ q ^ (nStar : ℕ) / q ^ N :=
    (one_le_div (pow_pos hq N)).2 hqPowers
  have hΔ : 0 < Δ := by
    have hrDPos : 0 < r * D :=
      Nat.mul_pos (by omega) (Nat.zero_lt_of_lt (hm.trans_lt hD))
    have hscale :
        0 < ((r * D : ℕ) : ℝ) / (Real.pi * nStar) := by
      exact div_pos (by exact_mod_cast hrDPos)
        (mul_pos Real.pi_pos (by exact_mod_cast hnStarPos))
    dsimp [z] at hz
    rcases (mul_pos_iff.mp hz) with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge hscale.le) h.1)
  have hBsq :
      (segmentedVandermondeLowerBound
        d n nStar m r D β Δ) ^ 2 =
        1 / n * q ^ (nStar : ℕ) * A /
          2 ^ (nStar - 1) * z ^ N := by
    dsimp [q, A, z, N]
    exact segmentedVandermondeLowerBound_sq
      hnPos hnStarPos
      (segmentedThreshold_exponentialBase_pos hβ)
  have hApos : 0 < A := by
    dsimp [A]
    have hrPos : 0 < r := by omega
    positivity
  have hpref :
      0 <
        mMin * (1 / (n : ℝ) * q ^ (nStar : ℕ) * A /
          2 ^ (nStar - 1)) := by
    positivity
  have hstrict :
      mMin * (1 / (n : ℝ) * q ^ (nStar : ℕ) * A /
            2 ^ (nStar - 1)) * (C * x) ^ N <
        mMin *
          (segmentedVandermondeLowerBound
            d n nStar m r D β Δ) ^ 2 := by
    rw [hBsq]
    calc
      mMin * (1 / (n : ℝ) * q ^ (nStar : ℕ) * A /
            2 ^ (nStar - 1)) * (C * x) ^ N
          < mMin * (1 / (n : ℝ) * q ^ (nStar : ℕ) * A /
            2 ^ (nStar - 1)) * z ^ N :=
        mul_lt_mul_of_pos_left hpow hpref
      _ = mMin * (1 / (n : ℝ) * q ^ (nStar : ℕ) * A /
            2 ^ (nStar - 1) * z ^ N) := by ring
  have hnormalize :
      mMin * (1 / (n : ℝ) * q ^ (nStar : ℕ) * A /
            2 ^ (nStar - 1)) * (C * x) ^ N =
        2 * σ *
          ((5 : ℝ) ^ (d * (nStar - 1)) * A) *
          (q ^ (nStar : ℕ) / q ^ N) := by
    rw [hCxpow]
    field_simp
  calc
    2 * (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ
        ≤ 2 * σ * ((5 : ℝ) ^ (d * (nStar - 1)) * A) := by
      nlinarith [hspatial]
    _ ≤ 2 * σ * ((5 : ℝ) ^ (d * (nStar - 1)) * A) *
          (q ^ (nStar : ℕ) / q ^ N) := by
      exact le_mul_of_one_le_right
        (by positivity : 0 ≤ 2 * σ *
          ((5 : ℝ) ^ (d * (nStar - 1)) * A)) hqRatio
    _ = mMin * (1 / (n : ℝ) * q ^ (nStar : ℕ) * A /
            2 ^ (nStar - 1)) * (C * x) ^ N := hnormalize.symm
    _ < _ := hstrict

/-- Noise singular values at and beyond the source count are bounded by the
entrywise noise budget. -/
theorem segmentedThreshold_noise_singularValue_le
    {d n m r D : ℕ} {σ : ℝ}
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (hmeasurement :
      IsBandMeasurement μ (segmentedCutoff m r D) σ Y)
    {j : ℕ} (hj : n ≤ j) (hjcard : j < (segmentedLength m r) ^ d) :
    matrixSingularValue (segmentedMeasurementMatrix m r D Y) j ≤
      ((segmentedLength m r : ℕ) : ℝ) ^ d * σ := by
  let G := segmentedMeasurementMatrix m r D Y
  let G₀ := segmentedMeasurementMatrix m r D (fourier μ)
  let E := G - G₀
  have hfactor : G₀ = segmentedNoiselessMatrix m r D μ :=
    segmentedMeasurementMatrix_fourier_eq_noiseless m r D μ
  have hzero : matrixSingularValue G₀ j = 0 := by
    rw [hfactor]
    exact segmentedThreshold_noiseless_singularValue_eq_zero μ hj
  have hnorm :
      matrixSpectralNorm E ≤
        (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ :=
    segmentedThreshold_perturbation_spectralNorm_le μ Y hmeasurement
  have hsum : G₀ + E = G := by
    simp only [E]
    abel
  have hweyl :=
    matrixSingularValue_add_le_add_spectralNorm G₀ E
      (i := j) (by
        rw [card_segmentedIndex]
        exact hjcard)
  rw [hsum, hzero, zero_add] at hweyl
  calc
    matrixSingularValue G j ≤
        (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ :=
      hweyl.trans hnorm
    _ = ((segmentedLength m r : ℕ) : ℝ) ^ d * σ := by
      rw [Nat.cast_pow]

/-- The explicit segmented Vandermonde lower bound is positive whenever the
separation threshold is satisfied. -/
theorem segmentedThreshold_explicitLowerBound_pos
    {d n nStar m r D : ℕ} {β σ mMin Δ : ℝ}
    (hn : 2 ≤ n) (hnStar : 2 ≤ nStar)
    (hm : 1 ≤ m) (hD : m < D) (hr : 2 * nStar ≤ r)
    (hβ : 1 / (2 * Real.log 2) < β)
    (hσ : 0 < σ) (hmMin : 0 < mMin)
    (hseparation :
      segmentedDetectionSeparationThreshold
          d n nStar m r D β σ mMin < Δ) :
    0 <
      segmentedVandermondeLowerBound d n nStar m r D β Δ := by
  have hthreshold :
      0 < segmentedDetectionSeparationThreshold
        d n nStar m r D β σ mMin := by
    unfold segmentedDetectionSeparationThreshold
    have hq := segmentedThreshold_exponentialBase_pos hβ
    have hcutoff : 0 < segmentedCutoff m r D := by
      unfold segmentedCutoff
      have hrPos : 0 < r := by omega
      have hDPos : 0 < D := Nat.zero_lt_of_lt (hm.trans_lt hD)
      positivity
    have hroot :
        0 < (2 * n * σ / mMin) ^
          (1 / (2 * (nStar : ℝ) - 2)) := by
      apply Real.rpow_pos_of_pos
      positivity
    positivity
  have hΔ : 0 < Δ := hthreshold.trans hseparation
  unfold segmentedVandermondeLowerBound
  have hq := segmentedThreshold_exponentialBase_pos hβ
  have hnPos : 0 < n := by omega
  have hnStarPos : 0 < nStar := by omega
  have hrPos : 0 < r := by omega
  have hDPos : 0 < D := Nat.zero_lt_of_lt (hm.trans_lt hD)
  positivity

/-- Complete proof of the segmented threshold conclusion from a supplied
Vandermonde lower bound.  The hypotheses `hExplicit` and `hB` are the only
interface to the separate Vandermonde theorem. -/
theorem segmentedGHM_singularValueThreshold_of_segmentedLowerBound
    {d n A nStar m r D : ℕ} {τ η β σ mMin B : ℝ}
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (_hd : 1 ≤ d) (hn : 2 ≤ n)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hm : 1 ≤ m) (hD : m < D)
    (_hτ : τ ≤ Real.pi / (2 * D * d))
    (hβ : 1 / (2 * Real.log 2) < β)
    (_hη : 4 * Real.pi * β * d / (localizationOrder m nStar + 1) ≤ η)
    (hr : 2 * nStar ≤ r)
    (hσ : 0 < σ)
    (hmMin : minAmplitude μ (Nat.zero_lt_of_lt hn) = mMin)
    (_hnoise : σ < mMin)
    (hmeasurement :
      IsBandMeasurement μ (segmentedCutoff m r D) σ Y)
    (hExplicit :
      segmentedVandermondeLowerBound d n nStar m r D β
          (periodicMinimumL1Separation μ.node hn) ≤ B)
    (hB :
      B ≤ matrixSingularValue
        (segmentedVandermonde m r D μ.node) (n - 1)) :
    (∀ j, n ≤ j → j < (segmentedLength m r) ^ d →
      matrixSingularValue (segmentedMeasurementMatrix m r D Y) j ≤
        ((segmentedLength m r : ℕ) : ℝ) ^ d * σ) ∧
    (periodicMinimumL1Separation μ.node hn ≤
        Real.pi * nStar / ((r * D : ℕ) : ℝ) →
      segmentedDetectionSeparationThreshold d n nStar m r D β σ mMin <
          periodicMinimumL1Separation μ.node hn →
      ((segmentedLength m r : ℕ) : ℝ) ^ d * σ <
        matrixSingularValue (segmentedMeasurementMatrix m r D Y) (n - 1)) := by
  have hnStar : 2 ≤ nStar := hclumps.1
  have hmMinPos : 0 < mMin := by
    rw [← hmMin]
    exact minAmplitude_pos μ (Nat.zero_lt_of_lt hn)
  refine ⟨?_, ?_⟩
  · intro j hj hjcard
    exact segmentedThreshold_noise_singularValue_le
      μ Y hmeasurement hj hjcard
  · intro _hlocal hseparation
    have hExplicitPos :
        0 < segmentedVandermondeLowerBound d n nStar m r D β
          (periodicMinimumL1Separation μ.node hn) :=
      segmentedThreshold_explicitLowerBound_pos
        hn hnStar hm hD hr hβ hσ hmMinPos hseparation
    have hBpos : 0 < B := hExplicitPos.trans_le hExplicit
    have hExplicitGap :
        2 * (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ <
          mMin *
            (segmentedVandermondeLowerBound d n nStar m r D β
              (periodicMinimumL1Separation μ.node hn)) ^ 2 :=
      segmentedThreshold_explicitLowerBound_gap
        hn hnStar hm hD hr hβ hσ hmMinPos hseparation
    have hsquare :
        (segmentedVandermondeLowerBound d n nStar m r D β
            (periodicMinimumL1Separation μ.node hn)) ^ 2 ≤ B ^ 2 :=
      (sq_le_sq₀ hExplicitPos.le hBpos.le).2 hExplicit
    have hgap :
        2 * (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ <
          mMin * B ^ 2 :=
      hExplicitGap.trans_le
        (mul_le_mul_of_nonneg_left hsquare hmMinPos.le)
    exact
      (segmentedGHM_singularValueThreshold_of_lowerBound
        μ Y hn hσ hmMin hmeasurement hBpos hB hgap).2

end

end NumDetect
end LeanNumDetect
