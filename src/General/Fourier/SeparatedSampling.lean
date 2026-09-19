import General.Fourier.SeparatedFourierEnergy
import General.Fourier.CosineSquaredEnergy

/-! A fully proved lower large-sieve bound at twice the Rayleigh separation.
The proof uses disjoint compact cosine-squared windows, shifted Parseval, and
a one-sided scalar limit. It includes equality in the separation condition. -/

set_option autoImplicit false
open scoped BigOperators
namespace LeanNumDetect

/-- Consecutive powers of nodes on the unit circle, with frequencies in turns. -/
noncomputable def unitCircleVandermonde (N K : ℕ) (ξ : Fin K → ℝ) :
    Matrix (Fin N) (Fin K) ℂ :=
  fun h j => Complex.exp (2 * Real.pi * Complex.I * (ξ j : ℂ)) ^ h.val

/-- Consecutive angular samples have lower frame constant one half whenever
the periodic node separation is at least `4π/N`. -/
theorem separated_sampling_half {n N : ℕ} (hN : 2 ≤ N)
    (x : Fin n → ℝ) (c : Fin n → ℂ)
    (hsep : ∀ i j, i ≠ j → ∀ p : ℤ, 4*Real.pi/(N : ℝ) ≤ |x i-x j-2*Real.pi*p|) :
    ((N : ℝ)/2) * (∑ j, ‖c j‖^2) ≤
      ∑ k : Fin N, ‖exponentialSum x c k‖^2 := by
  apply separated_sampling_half_of_cosineMass hN x c hsep
  intro eta heta hwidth
  apply cosineWeight_one_hasSum heta hwidth
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  positivity

end LeanNumDetect
