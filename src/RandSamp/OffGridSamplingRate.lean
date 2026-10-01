import General.Probability.BoundedAtomicSamplingRate
import General.Fourier.FourierAtomicGrid

/-!
# Fourier logarithmic sampling-rate comparison

The exact finite Fourier dictionary has quadratic size in the bandwidth.
Replacing its cardinality by `M+1` in the logarithmic rate and replacing
the atomic sparsity `4s/a` by `s/a` costs only a universal constant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- The exact logarithmic factor in the manuscript's uniform off-grid rate. -/
def offGridSamplingLogFactor (M s : ℕ) (a ρ η : ℝ) : ℝ :=
  (1 + Real.log ((M + 1 : ℕ) : ℝ)) * (1 + Real.log ((s : ℝ) / (a * ρ))) ^ 2 +
    Real.log (2 / η)

/-- An explicit universal constant for replacing the atomic logarithmic
factor by the manuscript's bandwidth and sparsity logarithms. -/
def offGridAtomicLogComparisonConstant : ℝ := 64 * (Real.pi + 1)

theorem offGridAtomicLogComparisonConstant_one_le :
    1 ≤ offGridAtomicLogComparisonConstant := by
  unfold offGridAtomicLogComparisonConstant
  linarith [Real.pi_pos]

/-- The logarithm of the exact Fourier dictionary is controlled by the
logarithm of the full frequency-space dimension. -/
theorem offGrid_dictionary_log_le (M : ℕ) :
    1 + Real.log (fourierAtomicGridSize M : ℝ) ≤
      (4 * Real.pi + 4) * (1 + Real.log ((M + 1 : ℕ) : ℝ)) := by
  have hQ0 : (0 : ℝ) < fourierAtomicGridSize M := by
    exact_mod_cast fourierAtomicGridSize_pos M
  have hN0 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hK0 : 0 < 4 * Real.pi + 2 := by positivity
  have hbound : (fourierAtomicGridSize M : ℝ) ≤
      (4 * Real.pi + 2) * ((M + 1 : ℕ) : ℝ) ^ 2 := by
    calc
      _ ≤ (4 * Real.pi * M + 2) * (M + 1) := fourierAtomicGridSize_le M
      _ ≤ ((4 * Real.pi + 2) * (M + 1)) * (M + 1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [Real.pi_pos]
      _ = _ := by push_cast; ring
  have hlog := Real.log_le_log hQ0 hbound
  rw [Real.log_mul hK0.ne' (pow_pos hN0 2).ne', Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hlogK := Real.log_le_sub_one_of_pos hK0
  have hlogN : 0 ≤ Real.log ((M + 1 : ℕ) : ℝ) := Real.log_nonneg hN1
  have hleft : 1 + Real.log (fourierAtomicGridSize M : ℝ) ≤
      4 * Real.pi + 2 + 2 * Real.log ((M + 1 : ℕ) : ℝ) := by linarith
  apply hleft.trans
  have hprod : 0 ≤ (4 * Real.pi + 2) * Real.log ((M + 1 : ℕ) : ℝ) :=
    mul_nonneg (by positivity) hlogN
  nlinarith only [hprod]

/-- The factor four in atomic sparsity changes its shifted logarithm by
at most a factor four when the manuscript sparsity ratio is at least two. -/
theorem offGrid_atomic_sparsity_log_le {s a ρ : ℝ} (_ha : 0 < a) (_hρ : 0 < ρ)
    (hx : 2 ≤ s / (a * ρ)) :
    0 ≤ 1 + Real.log ((4 * s / a) / ρ) ∧
      1 + Real.log ((4 * s / a) / ρ) ≤ 4 * (1 + Real.log (s / (a * ρ))) := by
  have hx0 : 0 < s / (a * ρ) := by linarith
  have hlogx : 0 ≤ Real.log (s / (a * ρ)) := Real.log_nonneg (by linarith)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog4le := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  rw [show (4 * s / a) / ρ = 4 * (s / (a * ρ)) by ring,
    Real.log_mul (by norm_num) hx0.ne']
  constructor <;> linarith

/-- Explicit logarithmic-factor comparison at the actual dictionary
cardinality. The assumptions are those of the manuscript's theorem. -/
theorem offGrid_atomic_logFactor_le_explicit {M s : ℕ} (_hM : 2 ≤ M) (hs : 2 ≤ s)
    {a ρ η : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hη0 : 0 < η) (hη1 : η < 1) :
    boundedAtomicSamplingLogFactor (4 * (s : ℝ) / a)
      (fourierAtomicGridSize M : ℝ) ρ η ≤
      offGridAtomicLogComparisonConstant * offGridSamplingLogFactor M s a ρ η := by
  have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have haρ : a * ρ ≤ 1 := by
    calc
      a * ρ ≤ 1 * ρ := mul_le_mul_of_nonneg_right ha1 hρ0.le
      _ = ρ := one_mul _
      _ ≤ 1 := hρ1.le
  have hx : 2 ≤ (s : ℝ) / (a * ρ) :=
    (le_div_iff₀ (mul_pos ha0 hρ0)).mpr (by linarith)
  have hlogx : 0 ≤ Real.log ((s : ℝ) / (a * ρ)) := Real.log_nonneg (by linarith)
  have hN1 : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
  have hlogN : 0 ≤ Real.log ((M + 1 : ℕ) : ℝ) := Real.log_nonneg hN1
  have hQlog := offGrid_dictionary_log_le M
  have hSlog := offGrid_atomic_sparsity_log_le ha0 hρ0 hx
  have hSq := pow_le_pow_left₀ hSlog.1 hSlog.2 2
  have hA : boundedAtomicEntropyFactor (4 * (s : ℝ) / a)
      (fourierAtomicGridSize M : ℝ) ρ ≤ offGridAtomicLogComparisonConstant *
        ((1 + Real.log ((M + 1 : ℕ) : ℝ)) *
          (1 + Real.log ((s : ℝ) / (a * ρ))) ^ 2) := by
    unfold boundedAtomicEntropyFactor
    calc
      _ ≤ ((4 * Real.pi + 4) * (1 + Real.log ((M + 1 : ℕ) : ℝ))) *
          (4 * (1 + Real.log ((s : ℝ) / (a * ρ)))) ^ 2 :=
        mul_le_mul hQlog hSq (sq_nonneg _) (by positivity)
      _ = _ := by unfold offGridAtomicLogComparisonConstant; ring
  have hL : 0 ≤ Real.log (2 / η) :=
    Real.log_nonneg ((one_le_div hη0).mpr (by linarith))
  have hLmul : Real.log (2 / η) ≤
      offGridAtomicLogComparisonConstant * Real.log (2 / η) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      offGridAtomicLogComparisonConstant_one_le hL
  unfold boundedAtomicSamplingLogFactor offGridSamplingLogFactor
  nlinarith

/-- Universal-constant form of the exact Fourier atomic logarithmic
comparison, ready to absorb into the theorem's single sample-size constant. -/
theorem offGrid_atomic_logFactor_le :
    ∃ L : ℝ, 0 < L ∧ ∀ (M s : ℕ) (a ρ η : ℝ),
      2 ≤ M → 2 ≤ s → 0 < a → a ≤ 1 → 0 < ρ → ρ < 1 → 0 < η → η < 1 →
      boundedAtomicSamplingLogFactor (4 * (s : ℝ) / a)
        (fourierAtomicGridSize M : ℝ) ρ η ≤ L * offGridSamplingLogFactor M s a ρ η := by
  refine ⟨offGridAtomicLogComparisonConstant,
    lt_of_lt_of_le zero_lt_one offGridAtomicLogComparisonConstant_one_le, ?_⟩
  intro M s a ρ η hM hs ha0 ha1 hρ0 hρ1 hη0 hη1
  exact offGrid_atomic_logFactor_le_explicit hM hs ha0 ha1 hρ0 hρ1 hη0 hη1

end

end LeanNumDetect.RandSamp
