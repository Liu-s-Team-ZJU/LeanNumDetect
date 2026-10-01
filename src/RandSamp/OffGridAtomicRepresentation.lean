import RandSamp.OffGridSignal
import General.Fourier.FourierAtomicGrid

/-!
# Exact finite-dictionary representations of full Fourier signals

The continuous Fourier dictionary embeds into a deterministic finite dictionary
with coefficient mass at most twice the original mass. A positive full-Gram
lower bound then controls this mass by the norm of the full signal, uniformly
over its nodes and coefficients. Every normalization is exact.
-/

set_option autoImplicit false

open WithLp
open scoped BigOperators

namespace LeanNumDetect.RandSamp

noncomputable section

/-- The normalized finite Fourier dictionary in the full frequency space. -/
def normalizedFourierGridAtom (M : ℕ) (j : Fin (fourierAtomicGridSize M)) :
    EuclideanSpace ℂ (Fin (M + 1)) :=
  toLp 2 (fun k => (Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
    fourierAtomicGrid M j k)

/-- Each normalized dictionary atom has unit Euclidean norm, including at
zero bandwidth. -/
@[simp] theorem norm_normalizedFourierGridAtom (M : ℕ)
    (j : Fin (fourierAtomicGridSize M)) :
    ‖normalizedFourierGridAtom M j‖ = 1 := by
  have hsq : ‖normalizedFourierGridAtom M j‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ k : Fin (M + 1),
      ‖(Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ * fourierAtomicGrid M j k‖ ^ 2) = 1
    rw [sum_norm_sq_scaled_fourierAtomicGrid]
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg (M + 1))]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (mul_inv_cancel₀ (by positivity : ((M + 1 : ℕ) : ℝ) ≠ 0))
  nlinarith [norm_nonneg (normalizedFourierGridAtom M j)]

/-- All coordinates of every normalized grid atom have the same modulus. -/
@[simp] theorem norm_normalizedFourierGridAtom_apply (M : ℕ)
    (j : Fin (fourierAtomicGridSize M)) (k : Fin (M + 1)) :
    ‖normalizedFourierGridAtom M j k‖ =
      (Real.sqrt ((M + 1 : ℕ) : ℝ))⁻¹ := by
  change ‖(Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ * fourierAtomicGrid M j k‖ = _
  simp only [norm_scaled_fourierAtomicGrid, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- The exact grid expansion preserves the full Fourier signal and costs at
most twice the original coefficient mass. No condition on the nodes is needed. -/
theorem exists_fullFourierSignal_atomic_expansion {s : ℕ} (M : ℕ)
    (Y : Fin s → ℝ) (z : EuclideanSpace ℂ (Fin s)) :
    ∃ b : Fin (fourierAtomicGridSize M) → ℂ,
      fullFourierSignal M Y z = ∑ j, b j • normalizedFourierGridAtom M j ∧
      (∑ j, ‖b j‖) ≤ 2 * ∑ i, ‖ofLp z i‖ := by
  classical
  obtain ⟨b, hb, hm⟩ := exists_fourierPolynomial_grid_expansion M Y (ofLp z)
  refine ⟨b, ?_, hm⟩
  apply (WithLp.ext_iff 2).2
  funext k
  simp only [fullFourierSignal, normalizedFourierGridAtom, ofLp_toLp,
    ofLp_sum, ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ = (Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        ∑ i, ofLp z i * fourierAtom M (Y i) k := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [fourierRow, fourierAtom]
      ring
    _ = (Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        ∑ j, b j * fourierAtomicGrid M j k := by rw [hb]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Cauchy--Schwarz controls the mass of any Euclidean coefficient vector,
with no nonemptiness assumption on its index set. -/
theorem sum_norm_fourierCoefficients_le {s : ℕ}
    (z : EuclideanSpace ℂ (Fin s)) :
    (∑ i, ‖ofLp z i‖) ≤ Real.sqrt (s : ℝ) * ‖z‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i : Fin s => ‖ofLp z i‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  have he : (∑ i, ‖ofLp z i‖ ^ 2) = ‖z‖ ^ 2 :=
    (EuclideanSpace.norm_sq_eq z).symm
  rw [he, Real.sqrt_sq (norm_nonneg z), mul_comm] at h
  exact h

/-- A positive full-Gram lower bound controls the original coefficient mass
by the norm of its full Fourier signal. -/
theorem sum_norm_fourierCoefficients_le_of_fullGram_lower {M s : ℕ}
    (Y : Fin s → ℝ) (z : EuclideanSpace ℂ (Fin s)) {a : ℝ} (ha : 0 < a)
    (hgram : a * ‖z‖ ^ 2 ≤ FiniteMatrixSampling.quadratic (fullGram M Y) z) :
    (∑ i, ‖ofLp z i‖) ≤
      Real.sqrt ((s : ℝ) / a) * ‖fullFourierSignal M Y z‖ := by
  have hsqrt : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have henergy : a * ‖z‖ ^ 2 ≤ ‖fullFourierSignal M Y z‖ ^ 2 := by
    rwa [norm_fullFourierSignal_sq]
  have hn : Real.sqrt a * ‖z‖ ≤ ‖fullFourierSignal M Y z‖ := by
    have h := Real.sqrt_le_sqrt henergy
    rwa [Real.sqrt_mul ha.le, Real.sqrt_sq (norm_nonneg z),
      Real.sqrt_sq (norm_nonneg (fullFourierSignal M Y z))] at h
  have hz : ‖z‖ ≤ ‖fullFourierSignal M Y z‖ / Real.sqrt a :=
    (le_div_iff₀ hsqrt).2 (by simpa only [mul_comm] using hn)
  calc
    _ ≤ Real.sqrt (s : ℝ) * ‖z‖ := sum_norm_fourierCoefficients_le z
    _ ≤ Real.sqrt (s : ℝ) * (‖fullFourierSignal M Y z‖ / Real.sqrt a) :=
      mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_div (Nat.cast_nonneg s)]; ring

/-- Every full Fourier signal with a positive full-Gram lower bound has an
exact expansion in unit atoms of mass at most `2 √(s/a)` times its norm. -/
theorem exists_fullFourierSignal_atomic_expansion_of_fullGram_lower {M s : ℕ}
    (Y : Fin s → ℝ) (z : EuclideanSpace ℂ (Fin s)) {a : ℝ} (ha : 0 < a)
    (hgram : a * ‖z‖ ^ 2 ≤ FiniteMatrixSampling.quadratic (fullGram M Y) z) :
    ∃ b : Fin (fourierAtomicGridSize M) → ℂ,
      fullFourierSignal M Y z = ∑ j, b j • normalizedFourierGridAtom M j ∧
      (∑ j, ‖b j‖) ≤
        2 * Real.sqrt ((s : ℝ) / a) * ‖fullFourierSignal M Y z‖ := by
  obtain ⟨b, hb, hm⟩ := exists_fullFourierSignal_atomic_expansion M Y z
  refine ⟨b, hb, hm.trans ?_⟩
  calc
    _ ≤ 2 * (Real.sqrt ((s : ℝ) / a) * ‖fullFourierSignal M Y z‖) :=
      mul_le_mul_of_nonneg_left
        (sum_norm_fourierCoefficients_le_of_fullGram_lower Y z ha hgram) (by norm_num)
    _ = _ := by ring

end

end LeanNumDetect.RandSamp
