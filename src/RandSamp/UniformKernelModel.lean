import RandSamp.CubeRandomModel
import General.Fourier.PhaseEstimates

/-! Sampled and full Fourier kernels on a frequency cube. Their exact
normalization, periodicity, Lipschitz estimates, and Gram entries are shared
by the uniform separated-node theorem and its one-dimensional corollary. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- A Fourier phase at a frequency in `{0,...,M}^d`. -/
def cubePhase {d M : ℕ} (k : CubeFrequency d M) (t : Fin d → ℝ) : ℂ :=
  Complex.exp (Complex.I * ((∑ r, ((k r : ℕ) : ℝ) * t r : ℝ) : ℂ))

@[simp] theorem norm_cubePhase {d M : ℕ} (k : CubeFrequency d M) (t : Fin d → ℝ) :
    ‖cubePhase k t‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal _

@[simp] theorem cubePhase_zero {d M : ℕ} (k : CubeFrequency d M) :
    cubePhase k 0 = 1 := by simp [cubePhase]

/-- Coordinatewise products give the same cube Fourier phase. -/
theorem cubePhase_eq_prod {d M : ℕ} (k : CubeFrequency d M) (t : Fin d → ℝ) :
    cubePhase k t = ∏ r, Complex.exp (Complex.I * (((k r : ℕ) : ℝ) * t r : ℝ)) := by
  rw [cubePhase, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]

/-- Each coordinate frequency is at most `M`, giving an `ℓ¹` Lipschitz bound. -/
theorem norm_cubePhase_sub_le {d M : ℕ} (k : CubeFrequency d M) (t u : Fin d → ℝ) :
    ‖cubePhase k t - cubePhase k u‖ ≤ (M : ℝ) * ∑ r, |t r - u r| := by
  have h := norm_exp_I_mul_sub_le (∑ r, ((k r : ℕ) : ℝ) * t r)
    (∑ r, ((k r : ℕ) : ℝ) * u r)
  apply h.trans
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ r, (((k r : ℕ) : ℝ) * t r - ((k r : ℕ) : ℝ) * u r)|
        ≤ ∑ r, |((k r : ℕ) : ℝ) * t r - ((k r : ℕ) : ℝ) * u r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, (M : ℝ) * |t r - u r| := by
      apply Finset.sum_le_sum
      intro r _
      rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact_mod_cast (show (k r).val ≤ M by omega)
    _ = (M : ℝ) * ∑ r, |t r - u r| := (Finset.mul_sum ..).symm

/-- Wrapping every coordinate modulo `2π` preserves the phase exactly. -/
theorem cubePhase_wrap {d M : ℕ} (k : CubeFrequency d M) (t : Fin d → ℝ) :
    cubePhase k (fun r => toIcoMod Real.two_pi_pos 0 (t r)) = cubePhase k t := by
  rw [cubePhase_eq_prod, cubePhase_eq_prod]
  apply Finset.prod_congr rfl
  intro r _
  exact exp_I_int_mul_toIcoMod (k r).val (t r)

/-- The sampled kernel has the same `1/m` normalization as the sampled Gram. -/
def sampledCubeKernel {d M : ℕ} (m : ℕ) (Ω : Finset (CubeFrequency d M))
    (t : Fin d → ℝ) : ℂ :=
  (m : ℂ)⁻¹ * ∑ k ∈ Ω, cubePhase k t

/-- The full kernel is the average over all `(M+1)^d` frequencies. -/
def fullCubeKernel {d : ℕ} (M : ℕ) (t : Fin d → ℝ) : ℂ :=
  (((M + 1) ^ d : ℕ) : ℂ)⁻¹ * ∑ k : CubeFrequency d M, cubePhase k t

/-- The random kernel deviation, on the actual fixed-size sample space. -/
def cubeKernelError {d M m : ℕ} (Ω : FiniteSample (CubeFrequency d M) m)
    (t : Fin d → ℝ) : ℂ :=
  sampledCubeKernel m Ω.val t - fullCubeKernel M t

/-- Averaging the phase Lipschitz estimates preserves their constant. -/
theorem norm_sampledCubeKernel_sub_le {d M m : ℕ} (hm : 1 ≤ m)
    (Ω : FiniteSample (CubeFrequency d M) m) (t u : Fin d → ℝ) :
    ‖sampledCubeKernel m Ω.val t - sampledCubeKernel m Ω.val u‖ ≤
      (M : ℝ) * ∑ r, |t r - u r| := by
  rw [sampledCubeKernel, sampledCubeKernel, ← mul_sub, ← Finset.sum_sub_distrib]
  rw [norm_mul, norm_inv, ← Complex.ofReal_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    (m : ℝ)⁻¹ * ‖∑ k ∈ Ω.val, (cubePhase k t - cubePhase k u)‖
        ≤ (m : ℝ)⁻¹ * ∑ k ∈ Ω.val, ‖cubePhase k t - cubePhase k u‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ (m : ℝ)⁻¹ * ∑ _k ∈ Ω.val, ((M : ℝ) * ∑ r, |t r - u r|) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact Finset.sum_le_sum (fun k _ => norm_cubePhase_sub_le k t u)
    _ = (M : ℝ) * ∑ r, |t r - u r| := by
      simp only [Finset.sum_const, Ω.prop, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (show m ≠ 0 by omega)), one_mul]

/-- The full-population kernel has the same Lipschitz constant. -/
theorem norm_fullCubeKernel_sub_le {d M : ℕ} (t u : Fin d → ℝ) :
    ‖fullCubeKernel M t - fullCubeKernel M u‖ ≤ (M : ℝ) * ∑ r, |t r - u r| := by
  let Ω : FiniteSample (CubeFrequency d M) ((M + 1) ^ d) := ⟨Finset.univ, by simp⟩
  have h := norm_sampledCubeKernel_sub_le
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero d (Nat.succ_ne_zero M))) Ω t u
  simpa only [sampledCubeKernel, fullCubeKernel, Ω] using h

/-- The sampled-minus-full error has Lipschitz constant `2M` in `ℓ¹`. -/
theorem norm_cubeKernelError_sub_le {d M m : ℕ} (hm : 1 ≤ m)
    (Ω : FiniteSample (CubeFrequency d M) m) (t u : Fin d → ℝ) :
    ‖cubeKernelError Ω t - cubeKernelError Ω u‖ ≤
      2 * (M : ℝ) * ∑ r, |t r - u r| := by
  unfold cubeKernelError
  rw [sub_sub_sub_comm]
  exact (norm_sub_le _ _).trans ((add_le_add
    (norm_sampledCubeKernel_sub_le hm Ω t u) (norm_fullCubeKernel_sub_le t u)).trans_eq (by ring))

/-- The kernel error is a function on the angular torus. -/
theorem cubeKernelError_wrap {d M m : ℕ} (Ω : FiniteSample (CubeFrequency d M) m)
    (t : Fin d → ℝ) :
    cubeKernelError Ω (fun r => toIcoMod Real.two_pi_pos 0 (t r)) = cubeKernelError Ω t := by
  simp only [cubeKernelError, sampledCubeKernel, fullCubeKernel, cubePhase_wrap]

/-- The phase at a difference is the inner product of the corresponding rows. -/
theorem cubeFourierRowGram_eq_cubePhase {d M s : ℕ} (Y : Fin s → Fin d → ℝ)
    (k : CubeFrequency d M) (i j : Fin s) :
    cubeFourierRowGram Y k i j = cubePhase k (fun r => Y j r - Y i r) := by
  unfold cubeFourierRowGram
  rw [show star (cubeFourierRow Y k i) = (cubeFourierRow Y k i)⁻¹ from
    (Complex.inv_eq_conj (norm_cubeFourierRow Y k i)).symm]
  rw [mul_comm, ← div_eq_mul_inv, cubeFourierRow, cubeFourierRow, ← Complex.exp_sub]
  unfold cubePhase
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib, Complex.ofReal_sub]

/-- Every sampled Gram entry is a sampled kernel value at the node difference. -/
theorem cubeSampledVandermonde_gram_entry {d M s : ℕ} (m : ℕ)
    (Y : Fin s → Fin d → ℝ) (Ω : Finset (CubeFrequency d M)) (i j : Fin s) :
    ((cubeSampledVandermonde m Y Ω)ᴴ * cubeSampledVandermonde m Y Ω) i j =
      sampledCubeKernel m Ω (fun r => Y j r - Y i r) := by
  change (∑ k : Ω, star (cubeSampledVandermonde m Y Ω k i) *
      cubeSampledVandermonde m Y Ω k j) = _
  simp only [cubeSampledVandermonde, star_mul]
  have hc : star ((Real.sqrt (m : ℝ) : ℂ)⁻¹) = ((Real.sqrt (m : ℝ) : ℂ)⁻¹) := by simp
  have hrow (k : CubeFrequency d M) :
      star (cubeFourierRow Y k i) * cubeFourierRow Y k j =
        cubePhase k (fun r => Y j r - Y i r) := cubeFourierRowGram_eq_cubePhase Y k i j
  rw [hc]
  simp_rw [show ∀ a b c : ℂ, b * a * (a * c) = a ^ 2 * (b * c) by intros; ring,
    hrow,
    ← Complex.ofReal_inv, ← Complex.ofReal_pow, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg m), Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [← Finset.mul_sum]
  change (m : ℂ)⁻¹ * (∑ k : Ω, cubePhase k.val (fun r => Y j r - Y i r)) =
    (m : ℂ)⁻¹ * ∑ k ∈ Ω, cubePhase k (fun r => Y j r - Y i r)
  congr 1
  exact Finset.sum_coe_sort Ω (fun k => cubePhase k (fun r => Y j r - Y i r))

/-- Every full Gram entry is the corresponding full kernel value. -/
theorem cubeFullGram_entry {d M s : ℕ} (Y : Fin s → Fin d → ℝ) (i j : Fin s) :
    cubeFullGram M Y i j = fullCubeKernel M (fun r => Y j r - Y i r) := by
  simp only [cubeFullGram, finiteMean, cubeFourierPopulation, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul, cubeFourierRowGram_eq_cubePhase,
    card_cubeFrequency, fullCubeKernel]

@[simp] theorem sampledCubeKernel_zero {d M m : ℕ} (hm : 1 ≤ m)
    (Ω : FiniteSample (CubeFrequency d M) m) : sampledCubeKernel m Ω.val 0 = 1 := by
  simp [sampledCubeKernel, Ω.prop, ne_of_gt (show 0 < m by omega)]

@[simp] theorem fullCubeKernel_zero {d : ℕ} (M : ℕ) :
    fullCubeKernel (d := d) M 0 = 1 := by
  simp only [fullCubeKernel, cubePhase_zero, Finset.sum_const, Finset.card_univ,
    card_cubeFrequency, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast pow_ne_zero d (Nat.succ_ne_zero M))

/-- Sampled and full Gram matrices have the same unit diagonal. -/
theorem cubeSampledVandermonde_gram_diag {d M s m : ℕ} (hm : 1 ≤ m)
    (Y : Fin s → Fin d → ℝ) (Ω : FiniteSample (CubeFrequency d M) m) (i : Fin s) :
    ((cubeSampledVandermonde m Y Ω.val)ᴴ * cubeSampledVandermonde m Y Ω.val) i i = 1 := by
  rw [cubeSampledVandermonde_gram_entry]
  simpa only [sub_self, ← Pi.zero_def] using sampledCubeKernel_zero hm Ω

@[simp] theorem cubeFullGram_diag {d M s : ℕ} (Y : Fin s → Fin d → ℝ) (i : Fin s) :
    cubeFullGram M Y i i = 1 := by
  rw [cubeFullGram_entry]
  simpa only [sub_self, ← Pi.zero_def] using fullCubeKernel_zero (d := d) M

/-- The full normalized Vandermonde matrix realizes the full Gram energy. -/
theorem cubeFullVandermonde_energy {d M s : ℕ} (Y : Fin s → Fin d → ℝ)
    (z : EuclideanSpace ℂ (Fin s)) :
    ‖(cubeSampledVandermonde ((M + 1) ^ d) Y
      (Finset.univ : Finset (CubeFrequency d M))).toEuclideanLin z‖ ^ 2 =
      FiniteMatrixSampling.quadratic (cubeFullGram M Y) z := by
  rw [cubeSampledVandermonde_energy, cubeFullGram, quadratic_cubeFourier_mean]
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]

/-- The full normalized Vandermonde matrix has exactly the full average Gram. -/
theorem cubeFullVandermonde_gram {d M s : ℕ} (Y : Fin s → Fin d → ℝ) :
    (cubeSampledVandermonde ((M + 1) ^ d) Y
      (Finset.univ : Finset (CubeFrequency d M)))ᴴ *
      cubeSampledVandermonde ((M + 1) ^ d) Y Finset.univ = cubeFullGram M Y := by
  ext i j
  rw [cubeSampledVandermonde_gram_entry, cubeFullGram_entry]
  rfl

/-- The Gram perturbation is exactly the kernel error at each node difference. -/
theorem cubeGram_difference_entry {d M s m : ℕ}
    (Y : Fin s → Fin d → ℝ) (Ω : FiniteSample (CubeFrequency d M) m) (i j : Fin s) :
    ((cubeSampledVandermonde m Y Ω.val)ᴴ * cubeSampledVandermonde m Y Ω.val) i j -
      cubeFullGram M Y i j = cubeKernelError Ω (fun r => Y j r - Y i r) := by
  rw [cubeSampledVandermonde_gram_entry, cubeFullGram_entry]
  rfl

end

end LeanNumDetect.RandSamp
