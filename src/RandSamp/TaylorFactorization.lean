import RandSamp.SquareVandermonde
import General.MatrixAnalysis.SingularValueBounds
import Mathlib.Analysis.Complex.Exponential

/-!
Taylor factors for nonuniform Fourier matrices.  This file keeps the analytic
remainder separate from the Lagrange lower bounds, making the hypotheses used
by the final theorem explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators Matrix.Norms.L2Operator

namespace LeanNumDetect
namespace RandSamp

noncomputable section

def squareVandermondeLower (n : ℕ) (η : ℝ) : ℝ :=
  1 / (Real.sqrt n * ((n : ℝ) * (2 / η) ^ (n - 1)))

/-- An explicit constant depending only on the source number.  The proof uses
a deliberately coarse coefficient-energy estimate; sharp constants are not
needed for the scaling theorem. -/
def nonuniformVandermondeConstant (n : ℕ) : ℝ :=
  1 / ((n : ℝ) ^ 3 * 4 ^ (n - 1) * (n - 1).factorial)

theorem nonuniformVandermondeConstant_pos {n : ℕ} (hn : 0 < n) :
    0 < nonuniformVandermondeConstant n := by
  unfold nonuniformVandermondeConstant
  positivity

def normalizedComplexNodes {n : ℕ} (x : Fin n → ℝ) (scale : ℝ) : Fin n → ℂ :=
  fun j => ((x j / scale : ℝ) : ℂ)

def frequencyTaylorFactor {n : ℕ} (frequency : Fin n → ℝ) (W : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (powerVandermonde (normalizedComplexNodes frequency W))ᵀ *
    Matrix.diagonal (fun k => Complex.I ^ k.val / (k.val.factorial : ℂ))

def sourceTaylorFactor {n : ℕ} (offset : Fin n → ℝ) (W ρ : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun k => ((W * ρ : ℝ) : ℂ) ^ k.val) *
    powerVandermonde (normalizedComplexNodes offset ρ)

def taylorPrincipal {n : ℕ} (frequency offset : Fin n → ℝ) (W ρ : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  frequencyTaylorFactor frequency W * sourceTaylorFactor offset W ρ

def centeredFourierVandermonde {m n : ℕ}
    (frequency : Fin m → ℝ) (offset : Fin n → ℝ) :
    Matrix (Fin m) (Fin n) ℂ :=
  fun i j => Complex.exp (Complex.I * ((frequency i * offset j : ℝ) : ℂ))

theorem frequencyTaylorFactor_apply {n : ℕ} (frequency : Fin n → ℝ)
    (W : ℝ) (i k : Fin n) :
    frequencyTaylorFactor frequency W i k =
      (Complex.I * ((frequency i / W : ℝ) : ℂ)) ^ k.val /
        (k.val.factorial : ℂ) := by
  classical
  simp only [frequencyTaylorFactor, Matrix.mul_apply, Matrix.transpose_apply,
    powerVandermonde, normalizedComplexNodes, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl]
    push_cast
    rw [mul_pow]
    ring
  · intro b _ hbk
    rw [if_neg hbk]
    simp
  · simp

theorem sourceTaylorFactor_apply {n : ℕ} (offset : Fin n → ℝ)
    (W : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (k j : Fin n) :
    sourceTaylorFactor offset W ρ k j =
      (((W * offset j : ℝ) : ℂ) ^ k.val) := by
  classical
  simp only [sourceTaylorFactor, Matrix.mul_apply, Matrix.diagonal_apply,
    powerVandermonde, normalizedComplexNodes]
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl]
    push_cast
    rw [← mul_pow]
    congr 1
    have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
    field_simp [hρC]
  · intro b _ hbk
    rw [if_neg hbk.symm]
    simp
  · simp

theorem taylorPrincipal_apply {n : ℕ} (frequency offset : Fin n → ℝ)
    {W ρ : ℝ} (hW : W ≠ 0) (hρ : ρ ≠ 0) (i j : Fin n) :
    taylorPrincipal frequency offset W ρ i j =
      ∑ k : Fin n,
        (Complex.I * (((frequency i * offset j : ℝ) : ℂ))) ^ k.val /
          (k.val.factorial : ℂ) := by
  classical
  simp only [taylorPrincipal, Matrix.mul_apply,
    frequencyTaylorFactor_apply frequency W,
    sourceTaylorFactor_apply offset W hρ]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  rw [div_mul_eq_mul_div, ← mul_pow]
  congr 1
  have hWC : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  field_simp [hWC]

theorem factorial_mono_fin {n : ℕ} (k : Fin n) :
    k.val.factorial ≤ (n - 1).factorial := by
  exact Nat.factorial_le (Nat.le_sub_one_of_lt k.isLt)

theorem frequencyTaylorFactor_lower {n : ℕ} (frequency : Fin n → ℝ)
    (hn : 0 < n) {W γ : ℝ} (hW : 0 < W)
    (hfreq : ∀ i, |frequency i| ≤ W)
    (hγ : 0 < γ) (hsep : ∀ i j, i ≠ j → γ ≤ |frequency i - frequency j|)
    (v : EuclideanSpace ℂ (Fin n)) :
    (squareVandermondeLower n (γ / W) / (n - 1).factorial) * ‖v‖ ≤
      ‖(frequencyTaylorFactor frequency W).toEuclideanLin v‖ := by
  let z := normalizedComplexNodes frequency W
  have hzNorm : ∀ j, ‖z j‖ ≤ 1 := by
    intro j
    simp only [z, normalizedComplexNodes, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos hW]
    exact (div_le_one hW).2 (hfreq j)
  have hgap : 0 < γ / W := div_pos hγ hW
  have hzsep : ∀ i j, i ≠ j → γ / W ≤ ‖z i - z j‖ := by
    intro i j hij
    simp only [z, normalizedComplexNodes, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hW]
    exact div_le_div_of_nonneg_right (hsep i j hij) hW.le
  have hsv := powerVandermonde_transpose_minimumSingularValue z hn hzNorm hgap hzsep
  have hdiag (k : Fin n) :
      1 / ((n - 1).factorial : ℝ) ≤
        ‖Complex.I ^ k.val / (k.val.factorial : ℂ)‖ := by
    simp only [norm_div, norm_pow, Complex.norm_I, one_pow, norm_natCast, one_div]
    exact inv_le_inv₀ (by positivity) (by positivity) |>.2 (by
      exact_mod_cast factorial_mono_fin k)
  have hd := diagonalToEuclideanLin_lower
    (fun k : Fin n => Complex.I ^ k.val / (k.val.factorial : ℂ))
    (by positivity : 0 ≤ 1 / ((n - 1).factorial : ℝ)) hdiag v
  have hp := lastMatrixSingularValue_mul_norm_le
    (powerVandermonde z)ᵀ (by simpa using hn)
    ((Matrix.diagonal (fun k : Fin n =>
      Complex.I ^ k.val / (k.val.factorial : ℂ))).toEuclideanLin v)
  change _ ≤ ‖((powerVandermonde z)ᵀ * Matrix.diagonal _).toEuclideanLin v‖
  calc
    (squareVandermondeLower n (γ / W) / (n - 1).factorial) * ‖v‖
        = squareVandermondeLower n (γ / W) *
            (1 / (n - 1).factorial * ‖v‖) := by ring
    _ ≤ matrixSingularValue (powerVandermonde z)ᵀ (n - 1) *
          (1 / (n - 1).factorial * ‖v‖) := by
      exact mul_le_mul_of_nonneg_right hsv (by positivity)
    _ ≤ matrixSingularValue (powerVandermonde z)ᵀ (n - 1) *
          ‖(Matrix.diagonal (fun k : Fin n =>
            Complex.I ^ k.val / (k.val.factorial : ℂ))).toEuclideanLin v‖ := by
      gcongr
      exact (powerVandermonde z).transpose.toEuclideanLin.singularValues_nonneg (n - 1)
    _ ≤ ‖(powerVandermonde z)ᵀ.toEuclideanLin
          ((Matrix.diagonal (fun k : Fin n =>
            Complex.I ^ k.val / (k.val.factorial : ℂ))).toEuclideanLin v)‖ := by
      simpa only [Fintype.card_fin] using hp
    _ = _ := by
      rw [Matrix.toLpLin_mul_same]
      rfl

theorem sourceTaylorFactor_lower {n : ℕ} (offset : Fin n → ℝ)
    (hn : 0 < n) {W ρ Δ : ℝ} (hWρ : 0 < W * ρ) (hWρone : W * ρ ≤ 1)
    (hρ : 0 < ρ) (hoffset : ∀ j, |offset j| ≤ ρ)
    (hΔ : 0 < Δ) (hsep : ∀ i j, i ≠ j → Δ ≤ |offset i - offset j|)
    (v : EuclideanSpace ℂ (Fin n)) :
    (squareVandermondeLower n (Δ / ρ) * (W * ρ) ^ (n - 1)) * ‖v‖ ≤
      ‖(sourceTaylorFactor offset W ρ).toEuclideanLin v‖ := by
  let z := normalizedComplexNodes offset ρ
  have hzNorm : ∀ j, ‖z j‖ ≤ 1 := by
    intro j
    simp only [z, normalizedComplexNodes, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos hρ]
    exact (div_le_one hρ).2 (hoffset j)
  have hgap : 0 < Δ / ρ := div_pos hΔ hρ
  have hzsep : ∀ i j, i ≠ j → Δ / ρ ≤ ‖z i - z j‖ := by
    intro i j hij
    simp only [z, normalizedComplexNodes, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hρ]
    exact div_le_div_of_nonneg_right (hsep i j hij) hρ.le
  have hsv := powerVandermonde_minimumSingularValue z hn hzNorm hgap hzsep
  have hp := lastMatrixSingularValue_mul_norm_le
    (powerVandermonde z) (by simpa using hn) v
  have hdiag (k : Fin n) :
      (W * ρ) ^ (n - 1) ≤ ‖(((W * ρ : ℝ) : ℂ) ^ k.val)‖ := by
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hWρ]
    exact pow_le_pow_of_le_one hWρ.le hWρone (Nat.le_sub_one_of_lt k.isLt)
  have hd := diagonalToEuclideanLin_lower
    (fun k : Fin n => (((W * ρ : ℝ) : ℂ) ^ k.val))
    (pow_nonneg hWρ.le _) hdiag ((powerVandermonde z).toEuclideanLin v)
  change _ ≤ ‖(Matrix.diagonal _ * powerVandermonde z).toEuclideanLin v‖
  calc
    (squareVandermondeLower n (Δ / ρ) * (W * ρ) ^ (n - 1)) * ‖v‖
        = (W * ρ) ^ (n - 1) *
            (squareVandermondeLower n (Δ / ρ) * ‖v‖) := by ring
    _ ≤ (W * ρ) ^ (n - 1) *
          (matrixSingularValue (powerVandermonde z) (n - 1) * ‖v‖) := by
      gcongr
      exact hsv
    _ ≤ (W * ρ) ^ (n - 1) * ‖(powerVandermonde z).toEuclideanLin v‖ := by
      gcongr
      simpa only [Fintype.card_fin] using hp
    _ ≤ ‖(Matrix.diagonal (fun k : Fin n =>
          (((W * ρ : ℝ) : ℂ) ^ k.val))).toEuclideanLin
          ((powerVandermonde z).toEuclideanLin v)‖ := hd
    _ = _ := by
      rw [Matrix.toLpLin_mul_same]
      rfl

theorem taylorPrincipal_lower {n : ℕ} (frequency offset : Fin n → ℝ)
    (hn : 0 < n) {W ρ γ Δ : ℝ} (hW : 0 < W)
    (hfreq : ∀ i, |frequency i| ≤ W)
    (hγ : 0 < γ) (hfreqSep : ∀ i j, i ≠ j → γ ≤ |frequency i - frequency j|)
    (hρ : 0 < ρ) (hoffset : ∀ j, |offset j| ≤ ρ)
    (hΔ : 0 < Δ) (hoffsetSep : ∀ i j, i ≠ j → Δ ≤ |offset i - offset j|)
    (hscale : W * ρ ≤ 1) (v : EuclideanSpace ℂ (Fin n)) :
    ((squareVandermondeLower n (γ / W) / (n - 1).factorial) *
        (squareVandermondeLower n (Δ / ρ) * (W * ρ) ^ (n - 1))) * ‖v‖ ≤
      ‖(taylorPrincipal frequency offset W ρ).toEuclideanLin v‖ := by
  have hWρ : 0 < W * ρ := mul_pos hW hρ
  have hs := sourceTaylorFactor_lower offset hn hWρ hscale hρ hoffset
    hΔ hoffsetSep v
  have hf := frequencyTaylorFactor_lower frequency hn hW hfreq hγ hfreqSep
    ((sourceTaylorFactor offset W ρ).toEuclideanLin v)
  change _ ≤ ‖(frequencyTaylorFactor frequency W *
    sourceTaylorFactor offset W ρ).toEuclideanLin v‖
  calc
    ((squareVandermondeLower n (γ / W) / (n - 1).factorial) *
        (squareVandermondeLower n (Δ / ρ) * (W * ρ) ^ (n - 1))) * ‖v‖
        = (squareVandermondeLower n (γ / W) / (n - 1).factorial) *
            ((squareVandermondeLower n (Δ / ρ) * (W * ρ) ^ (n - 1)) * ‖v‖) := by ring
    _ ≤ (squareVandermondeLower n (γ / W) / (n - 1).factorial) *
          ‖(sourceTaylorFactor offset W ρ).toEuclideanLin v‖ := by
      gcongr
      unfold squareVandermondeLower
      positivity
    _ ≤ ‖(frequencyTaylorFactor frequency W).toEuclideanLin
          ((sourceTaylorFactor offset W ρ).toEuclideanLin v)‖ := hf
    _ = _ := by
      rw [Matrix.toLpLin_mul_same]
      rfl

def exponentialRemainderCoefficient (n : ℕ) : ℝ :=
  (n.succ : ℝ) * (((n.factorial * n : ℕ) : ℝ)⁻¹)

def taylorRemainder {n : ℕ} (frequency offset : Fin n → ℝ) (W ρ : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  centeredFourierVandermonde frequency offset - taylorPrincipal frequency offset W ρ

theorem taylorRemainder_entry_bound {n : ℕ} (frequency offset : Fin n → ℝ)
    (hn : 0 < n) {W ρ : ℝ} (hW : 0 < W) (hρ : 0 < ρ)
    (hscale : W * ρ ≤ 1) (hfreq : ∀ i, |frequency i| ≤ W)
    (hoffset : ∀ j, |offset j| ≤ ρ) (i j : Fin n) :
    ‖taylorRemainder frequency offset W ρ i j‖ ≤
      (W * ρ) ^ n * exponentialRemainderCoefficient n := by
  have hW0 : W ≠ 0 := ne_of_gt hW
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  let t : ℂ := Complex.I * (((frequency i * offset j : ℝ) : ℂ))
  have htNorm : ‖t‖ = |frequency i| * |offset j| := by
    simp [t]
  have ht : ‖t‖ ≤ 1 := by
    rw [htNorm]
    calc
      |frequency i| * |offset j| ≤ W * ρ :=
        mul_le_mul (hfreq i) (hoffset j) (abs_nonneg _) hW.le
      _ ≤ 1 := hscale
  have hexp := Complex.exp_bound ht hn
  rw [show taylorRemainder frequency offset W ρ i j =
      Complex.exp t - ∑ k ∈ Finset.range n, t ^ k / k.factorial by
    rw [taylorRemainder, Matrix.sub_apply, centeredFourierVandermonde,
      taylorPrincipal_apply frequency offset hW0 hρ0]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun k => t ^ k / (k.factorial : ℂ)) n]
  calc
    ‖Complex.exp t - ∑ k ∈ Finset.range n, t ^ k / k.factorial‖
        ≤ ‖t‖ ^ n * exponentialRemainderCoefficient n := by
      simpa [exponentialRemainderCoefficient, Nat.cast_mul] using hexp
    _ ≤ (W * ρ) ^ n * exponentialRemainderCoefficient n := by
      gcongr
      · unfold exponentialRemainderCoefficient
        positivity
      · rw [htNorm]
        exact mul_le_mul (hfreq i) (hoffset j) (abs_nonneg _) hW.le

theorem squareMatrix_action_norm_le_of_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {r : ℝ} (hr : 0 ≤ r) (hentry : ∀ i j, ‖A i j‖ ≤ r)
    (v : EuclideanSpace ℂ (Fin n)) :
    ‖A.toEuclideanLin v‖ ≤ (n : ℝ) * r * ‖v‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hr)
    (norm_nonneg _))]
  rw [mul_pow, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change (∑ i, ‖A i ⬝ᵥ ofLp v‖ ^ 2) ≤
    (n : ℝ) ^ 2 * r ^ 2 * ∑ j, ‖ofLp v j‖ ^ 2
  calc
    ∑ i, ‖A i ⬝ᵥ ofLp v‖ ^ 2
        ≤ ∑ i, SegmentedVDM.energy (A i) * SegmentedVDM.energy (ofLp v) := by
      apply Finset.sum_le_sum
      intro i _
      exact SegmentedVDM.dotProduct_norm_sq_le (A i) (ofLp v)
    _ ≤ ∑ _i : Fin n, ((n : ℝ) * r ^ 2) * SegmentedVDM.energy (ofLp v) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (SegmentedVDM.energy_nonneg _)
      unfold SegmentedVDM.energy
      calc
        ∑ j : Fin n, ‖A i j‖ ^ 2 ≤ ∑ _j : Fin n, r ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          exact pow_le_pow_left₀ (norm_nonneg _) (hentry i j) 2
        _ = (n : ℝ) * r ^ 2 := by simp
    _ = (n : ℝ) ^ 2 * r ^ 2 * ∑ j, ‖ofLp v j‖ ^ 2 := by
      simp [SegmentedVDM.energy]
      ring

theorem taylorRemainder_action_bound {n : ℕ} (frequency offset : Fin n → ℝ)
    (hn : 0 < n) {W ρ : ℝ} (hW : 0 < W) (hρ : 0 < ρ)
    (hscale : W * ρ ≤ 1) (hfreq : ∀ i, |frequency i| ≤ W)
    (hoffset : ∀ j, |offset j| ≤ ρ) (v : EuclideanSpace ℂ (Fin n)) :
    ‖(taylorRemainder frequency offset W ρ).toEuclideanLin v‖ ≤
      (n : ℝ) * ((W * ρ) ^ n * exponentialRemainderCoefficient n) * ‖v‖ := by
  apply squareMatrix_action_norm_le_of_entry
  · unfold exponentialRemainderCoefficient
    positivity
  · exact taylorRemainder_entry_bound frequency offset hn hW hρ hscale hfreq hoffset

/-- Raw nonuniform Fourier--Vandermonde lower bound for a selected set of `n`
sampling rows.  The leading term is the Taylor-factorization bound and the
second term is the fully verified exponential remainder. -/
theorem centeredFourierVandermonde_minimumSingularValue_raw {n : ℕ}
    (frequency offset : Fin n → ℝ) (hn : 0 < n)
    {W ρ γ Δ : ℝ} (hW : 0 < W) (hfreq : ∀ i, |frequency i| ≤ W)
    (hγ : 0 < γ) (hfreqSep : ∀ i j, i ≠ j → γ ≤ |frequency i - frequency j|)
    (hρ : 0 < ρ) (hoffset : ∀ j, |offset j| ≤ ρ)
    (hΔ : 0 < Δ) (hoffsetSep : ∀ i j, i ≠ j → Δ ≤ |offset i - offset j|)
    (hscale : W * ρ ≤ 1) :
    (squareVandermondeLower n (γ / W) / (n - 1).factorial) *
        (squareVandermondeLower n (Δ / ρ) * (W * ρ) ^ (n - 1)) -
        (n : ℝ) * ((W * ρ) ^ n * exponentialRemainderCoefficient n) ≤
      matrixSingularValue (centeredFourierVandermonde frequency offset) (n - 1) := by
  let c := (squareVandermondeLower n (γ / W) / (n - 1).factorial) *
    (squareVandermondeLower n (Δ / ρ) * (W * ρ) ^ (n - 1))
  let e := (n : ℝ) * ((W * ρ) ^ n * exponentialRemainderCoefficient n)
  apply le_singularValues_of_subspace
    (centeredFourierVandermonde frequency offset).toEuclideanLin
    (i := n - 1) (by simpa using Nat.sub_lt hn Nat.zero_lt_one) ⊤
  · simp [Nat.sub_add_cancel hn]
  · intro v _
    have hp := taylorPrincipal_lower frequency offset hn hW hfreq hγ hfreqSep
      hρ hoffset hΔ hoffsetSep hscale v
    have hr := taylorRemainder_action_bound frequency offset hn hW hρ hscale hfreq hoffset v
    have hdecomp : centeredFourierVandermonde frequency offset =
        taylorPrincipal frequency offset W ρ + taylorRemainder frequency offset W ρ := by
      simp [taylorRemainder]
    have htriangle :
        ‖(taylorPrincipal frequency offset W ρ).toEuclideanLin v‖ ≤
          ‖(centeredFourierVandermonde frequency offset).toEuclideanLin v‖ +
            ‖(taylorRemainder frequency offset W ρ).toEuclideanLin v‖ := by
      calc
        _ = ‖(centeredFourierVandermonde frequency offset).toEuclideanLin v -
            (taylorRemainder frequency offset W ρ).toEuclideanLin v‖ := by
          rw [hdecomp]
          simp
        _ ≤ _ := norm_sub_le _ _
    change (c - e) * ‖v‖ ≤ _
    change c * ‖v‖ ≤ _ at hp
    change ‖(taylorRemainder frequency offset W ρ).toEuclideanLin v‖ ≤ e * ‖v‖ at hr
    nlinarith [norm_nonneg ((taylorRemainder frequency offset W ρ).toEuclideanLin v)]

theorem taylorLeadingTerm_eq {n : ℕ} (hn : 0 < n)
    {W ρ γ Δ : ℝ} (hW : 0 < W) (hρ : 0 < ρ) (hγ : 0 < γ) (hΔ : 0 < Δ) :
    (squareVandermondeLower n (γ / W) / (n - 1).factorial) *
        (squareVandermondeLower n (Δ / ρ) * (W * ρ) ^ (n - 1)) =
      nonuniformVandermondeConstant n * (γ * Δ) ^ (n - 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hne : (Real.sqrt n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnR)
  unfold squareVandermondeLower nonuniformVandermondeConstant
  field_simp [ne_of_gt hW, ne_of_gt hρ, ne_of_gt hγ, ne_of_gt hΔ, hne]
  rw [hsqrt]
  field_simp [pow_ne_zero _ (ne_of_gt hγ), pow_ne_zero _ (ne_of_gt hΔ)]
  ring_nf
  rw [inv_pow, inv_pow]
  field_simp [pow_ne_zero _ hγ.ne', pow_ne_zero _ hΔ.ne']
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm 2 (n - 1)]

/-- The manuscript's simplified scaling bound for a selected `n`-row
nonuniform array, under the explicit remainder-control condition. -/
theorem centeredFourierVandermonde_minimumSingularValue {n : ℕ}
    (frequency offset : Fin n → ℝ) (hn : 0 < n)
    {W ρ γ Δ : ℝ} (hW : 0 < W) (hfreq : ∀ i, |frequency i| ≤ W)
    (hγ : 0 < γ) (hfreqSep : ∀ i j, i ≠ j → γ ≤ |frequency i - frequency j|)
    (hρ : 0 < ρ) (hoffset : ∀ j, |offset j| ≤ ρ)
    (hΔ : 0 < Δ) (hoffsetSep : ∀ i j, i ≠ j → Δ ≤ |offset i - offset j|)
    (hscale : W * ρ ≤ 1)
    (hremainder :
      (n : ℝ) * ((W * ρ) ^ n * exponentialRemainderCoefficient n) ≤
        (1 / 2 : ℝ) * nonuniformVandermondeConstant n * (γ * Δ) ^ (n - 1)) :
    (1 / 2 : ℝ) * nonuniformVandermondeConstant n * (γ * Δ) ^ (n - 1) ≤
      matrixSingularValue (centeredFourierVandermonde frequency offset) (n - 1) := by
  have hraw := centeredFourierVandermonde_minimumSingularValue_raw
    frequency offset hn hW hfreq hγ hfreqSep hρ hoffset hΔ hoffsetSep hscale
  rw [taylorLeadingTerm_eq hn hW hρ hγ hΔ] at hraw
  linarith

end

end RandSamp
end LeanNumDetect
