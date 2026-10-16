import MultiTuran.Turan.Complex
import MultiTuran.Turan.PruningInduction

/-! # Imaginary spectra, modulation and geometric-mean invariance

The real-line exponential sum and its entire complex extension are identified
literally. Centering the frequencies changes only a unit-modulus phase on the
real line, so logarithmic regularity and geometric means are preserved.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BigOperators

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- The complex purely imaginary spectrum corresponding to real angular
frequencies. -/
def imaginaryExponents {n : ℕ} (frequency : Fin n → ℝ) : Fin n → ℂ :=
  fun j => Complex.I*(frequency j : ℂ)

@[simp] theorem norm_imaginaryExponents {n : ℕ} (frequency : Fin n → ℝ) (j : Fin n) :
    ‖imaginaryExponents frequency j‖ = |frequency j| := by
  simp only [imaginaryExponents,norm_mul,Complex.norm_I,Complex.norm_real,
    Real.norm_eq_abs,one_mul]

@[simp] theorem re_imaginaryExponents {n : ℕ} (frequency : Fin n → ℝ) (j : Fin n) :
    (imaginaryExponents frequency j).re = 0 := by
  simp [imaginaryExponents,Complex.mul_re]

/-- Exact identification of the scalar sum with the real trace of its entire
complex exponential sum. -/
theorem complexExponentialSum_imaginary {n : ℕ} (frequency : Fin n → ℝ)
    (c : Fin n → ℂ) (t : ℝ) :
    complexExponentialSum (imaginaryExponents frequency) c (t : ℂ) =
      ExponentialSumEstimates.exponentialSum frequency c t := by
  unfold complexExponentialSum imaginaryExponents ExponentialSumEstimates.exponentialSum
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  push_cast
  ring

/-- A nonzero real-line function gives a nonzero entire extension, regardless
of repeated frequencies or a redundant coefficient presentation. -/
theorem complexExponentialSum_imaginary_ne_zero {n : ℕ} (frequency : Fin n → ℝ)
    (c : Fin n → ℂ) (hne : ExponentialSumEstimates.exponentialSum frequency c ≠ 0) :
    complexExponentialSum (imaginaryExponents frequency) c ≠ 0 := by
  intro hz
  apply hne
  funext t
  rw [← complexExponentialSum_imaginary,congrFun hz (t : ℂ)]
  rfl

/-- Pointwise equality of norms preserves both branches of the actual
zero-aware geometric mean. -/
theorem measureGeometricMean_congr_norm {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℂ} (h : ∀ x, ‖f x‖ = ‖g x‖) :
    measureGeometricMean μ f = measureGeometricMean μ g := by
  have hz : f = 0 ↔ g = 0 := by
    constructor
    · intro hf
      funext x
      apply norm_eq_zero.mp
      rw [← h x,hf]
      simp
    · intro hg
      funext x
      apply norm_eq_zero.mp
      rw [h x,hg]
      simp
  by_cases hf : f = 0
  · simp [hf,hz.mp hf]
  have hg : g ≠ 0 := fun hg => hf (hz.mpr hg)
  rw [measureGeometricMean,measureGeometricMean,if_neg hf,if_neg hg]
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => congrArg Real.log (h x))

theorem geometricMean_congr_norm (E : Set ℝ) {f g : ℝ → ℂ}
    (h : ∀ x, ‖f x‖ = ‖g x‖) : geometricMean E f = geometricMean E g :=
  measureGeometricMean_congr_norm _ h

/-- Logarithmic integrability and a.e. nonvanishing are both invariant under
pointwise equality of norms. -/
theorem logRegular_congr_norm {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℂ} (h : ∀ x, ‖f x‖ = ‖g x‖) :
    LogRegular μ f ↔ LogRegular μ g := by
  have hlog : (fun x => Real.log ‖f x‖) = (fun x => Real.log ‖g x‖) :=
    funext (fun x => congrArg Real.log (h x))
  have hzero (x : X) : f x = 0 ↔ g x = 0 := by
    constructor
    · intro hx
      apply norm_eq_zero.mp
      rw [← h x,hx,norm_zero]
    · intro hx
      apply norm_eq_zero.mp
      rw [h x,hx,norm_zero]
  constructor
  · intro hf
    refine ⟨hlog ▸ hf.1,?_⟩
    exact hf.2.mono (fun x hx hg => hx ((hzero x).mpr hg))
  · intro hg
    refine ⟨hlog.symm ▸ hg.1,?_⟩
    exact hg.2.mono (fun x hx hf => hx ((hzero x).mp hf))

/-- Imaginary demodulation preserves the literal geometric mean. -/
theorem geometricMean_frequency_sub {n : ℕ} (E : Set ℝ)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) (a : ℝ) :
    geometricMean E (ExponentialSumEstimates.exponentialSum (fun j => frequency j-a) c) =
      geometricMean E (ExponentialSumEstimates.exponentialSum frequency c) :=
  geometricMean_congr_norm E (norm_exponentialSum_frequency_sub frequency c a)

theorem logRegular_frequency_sub {n : ℕ} (μ : Measure ℝ)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) (a : ℝ) :
    LogRegular μ (ExponentialSumEstimates.exponentialSum (fun j => frequency j-a) c) ↔
      LogRegular μ (ExponentialSumEstimates.exponentialSum frequency c) :=
  logRegular_congr_norm μ (norm_exponentialSum_frequency_sub frequency c a)

/-- Centering at any indexed frequency puts every complex imaginary exponent
inside the disk given by a diameter bound. -/
theorem centered_imaginaryExponents_norm_le {n : ℕ} (frequency : Fin n → ℝ)
    (a : Fin n) {ρ : ℝ} (hdiam : ∀ i j, |frequency j-frequency i| ≤ ρ) :
    ∀ j, ‖imaginaryExponents (fun j => frequency j-frequency a) j‖ ≤ ρ := by
  intro j
  rw [norm_imaginaryExponents]
  exact hdiam a j

/-- Centering at an actual minimum also gives nonnegative real shifted
frequencies; no artificial enclosing spectral interval is introduced. -/
theorem exists_minimum_frequency_center {n : ℕ} (hn : 0 < n) (frequency : Fin n → ℝ)
    {ρ : ℝ} (hdiam : ∀ i j, |frequency j-frequency i| ≤ ρ) :
    ∃ a : Fin n, ∀ j, 0 ≤ frequency j-frequency a ∧
      ‖imaginaryExponents (fun j => frequency j-frequency a) j‖ ≤ ρ := by
  obtain ⟨a,b,hext⟩ := exists_frequency_extremal_pair hn frequency
  refine ⟨a,?_⟩
  intro j
  exact ⟨sub_nonneg.mpr (hext j).1,centered_imaginaryExponents_norm_le frequency a hdiam j⟩

/-- The order-dependent exponential loss is absorbed with the exact
number-of-terms exponent when the centered spectrum is bounded by `n`. -/
theorem exp_bounded_spectrum_absorption {n : ℕ} (hn : 2 ≤ n) {σ A : ℝ}
    (hσ : σ ≤ (n : ℝ)) (hA : 0 ≤ A) :
    Real.exp (A*((n : ℝ)+σ)) ≤ (Real.exp (4*A))^(n-1) := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  nlinarith

/-- A generous fixed constant sufficient for the bounded-spectrum branch. -/
theorem bounded_spectrum_exp_loss_le {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : σ ≤ (n : ℝ)) :
    Real.exp (10000*((n : ℝ)+σ)) ≤ (Real.exp 1000000)^(n-1) := by
  calc
    _ ≤ (Real.exp (4*10000))^(n-1) := exp_bounded_spectrum_absorption hn hσ (by norm_num)
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by norm_num)) _

end
end LeanNumDetect.MultiTuran
