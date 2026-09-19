import General.Fourier.SeparatedSampling
import SegmentedVDM.Separation
import SegmentedVDM.Localization
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The one-dimensional localization input, obtained from the original
Aubel–Bölcskei large-sieve inequality. Normalization, minimum-separation
attainment, sample/column cardinality, and singleton cases are proved here. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix LeanNumDetect
open scoped BigOperators
namespace SegmentedVDM

noncomputable def normalizedFrequency (x : ℝ) : ℝ := Int.fract (x/(2*Real.pi))

theorem normalizedFrequency_mem (x : ℝ) :
    0 ≤ normalizedFrequency x ∧ normalizedFrequency x < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem normalizedFrequency_exp (x : ℝ) :
    Complex.exp (2*Real.pi*Complex.I*(normalizedFrequency x : ℂ)) =
      Complex.exp (Complex.I*(x : ℂ)) := by
  have he : 2*Real.pi*Complex.I*(normalizedFrequency x : ℂ) =
      Complex.I*(x : ℂ) + ((-⌊x/(2*Real.pi)⌋ : ℤ) : ℂ)*(2*Real.pi*Complex.I) := by
    unfold normalizedFrequency Int.fract
    push_cast
    field_simp
    <;> ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem normalizedFrequency_separation {N : ℕ} (x y : ℝ)
    (hsep : ∀ p : ℤ, 4*Real.pi/(N : ℝ) ≤ |x-y-2*Real.pi*p|) (p : ℤ) :
    2/(N : ℝ) ≤ |normalizedFrequency x-normalizedFrequency y-p| := by
  have he : normalizedFrequency x-normalizedFrequency y-p =
      (x-y-2*Real.pi*(⌊x/(2*Real.pi)⌋-⌊y/(2*Real.pi)⌋+p : ℤ))/(2*Real.pi) := by
    unfold normalizedFrequency Int.fract
    push_cast
    field_simp
    <;> ring
  rw [he, abs_div, abs_of_pos (by positivity : 0 < 2*Real.pi)]
  apply (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).2
  convert! hsep (⌊x/(2*Real.pi)⌋-⌊y/(2*Real.pi)⌋+p) using 1 <;> ring

theorem unitCircleVandermonde_normalized {n : ℕ} (K : ℕ) (x : Fin n → ℝ) :
    LeanNumDetect.unitCircleVandermonde (K+1) n (fun j => normalizedFrequency (x j)) =
      uniformEvaluation K x := by
  ext h j
  simp only [LeanNumDetect.unitCircleVandermonde, normalizedFrequency_exp, uniformEvaluation]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem uniform_frame_half_fin {n : ℕ} (K : ℕ) (x : Fin n → ℝ)
    (hsep : ∀ i j, i ≠ j → ∀ p : ℤ, 4*Real.pi/(K+1) ≤ |x i-x j-2*Real.pi*p|)
    (v : Fin n → ℂ) : ((K+1)/2 : ℝ)*energy v ≤ energy (uniformEvaluation K x *ᵥ v) := by
  classical
  by_cases hn : 2 ≤ n
  · let ξ := fun j => normalizedFrequency (x j)
    have hξ : ∀ j, 0 ≤ ξ j ∧ ξ j < 1 := fun j => normalizedFrequency_mem _
    have hsep' (i j : Fin n) (hij : i ≠ j) (p : ℤ) :
        2/((K+1 : ℕ) : ℝ) ≤ |ξ i-ξ j-p| :=
      normalizedFrequency_separation (x i) (x j) (by simpa using hsep i j hij) p
    have hcard : n < K+1 := separated_card_lt_samples hn (by omega) ξ hξ
      (fun i j hij => by simpa using hsep' i j hij 0)
    have hh := LeanNumDetect.separated_sampling_half (show 2 ≤ K+1 by omega) x v
      (by simpa using hsep)
    simpa [energy, uniformEvaluation, Matrix.mulVec, dotProduct,
      LeanNumDetect.exponentialSum, mul_comm] using hh
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · simp [energy, Matrix.mulVec, dotProduct]
    · have he : energy (uniformEvaluation K x *ᵥ v) = (K+1 : ℝ)*energy v := by
        simp [energy, uniformEvaluation, Matrix.mulVec, dotProduct, norm_mul, Complex.norm_exp]
      rw [he]
      nlinarith [energy_nonneg v]

theorem uniform_frame_half {ι : Type} [Fintype ι] (K : ℕ) (x : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → ∀ p : ℤ, 4*Real.pi/(K+1) ≤ |x i-x j-2*Real.pi*p|)
    (v : ι → ℂ) : ((K+1)/2 : ℝ)*energy v ≤ energy (uniformEvaluation K x *ᵥ v) := by
  classical
  let e := (Fintype.equivFin ι).symm
  have hh := uniform_frame_half_fin K (fun j => x (e j))
    (fun i j hij => hsep _ _ (fun h => hij (e.injective h))) (fun j => v (e j))
  have he : energy (fun j => v (e j)) = energy v := Equiv.sum_comp e (fun j => ‖v j‖^2)
  rw [he] at hh
  convert! hh using 1
  congr 1
  funext h
  unfold uniformEvaluation Matrix.mulVec dotProduct
  exact (Equiv.sum_comp e (fun j => Complex.exp (Complex.I*((h.val*x j : ℝ) : ℂ))*v j)).symm

end SegmentedVDM
