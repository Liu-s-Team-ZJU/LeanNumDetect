import General.Fourier.ExponentialWindowOrthogonality

/-! A compact Fourier window gives a lower frame bound for periodically separated
nodes. The signed tail is retained throughout; no large-sieve theorem is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace LeanNumDetect

/-- Decoupling into singleton translates only needs the scalar mass of the weight. -/
theorem separated_cosineWeight_hasSum {n : ℕ} {eta T W : ℝ}
    (heta : 0 < eta) (hT : 0 < T) (x : Fin n → ℝ) (c : Fin n → ℂ)
    (hsep : ∀ i j, i ≠ j → ∀ p : ℤ, eta < |x i-x j-2*Real.pi*p|)
    (shift : ℝ) (hw : HasSum (fun k : ℤ => cosineWeight 1 eta T ((k : ℝ)-shift)) W) :
    HasSum (fun k : ℤ => cosineWeight 1 eta T ((k : ℝ)-shift) *
      ‖exponentialSum x c ((k : ℝ)-shift)‖^2) (W * ∑ j, ‖c j‖^2) := by
  have hc (j : Fin n) (t : ℝ) :
      ‖c j * Complex.exp (Complex.I * ((t*x j : ℝ) : ℂ))‖^2 = ‖c j‖^2 := by
    simp [Complex.norm_exp, Complex.mul_re]
  have hd (j : Fin n) : HasSum (fun k : ℤ => cosineWeight 1 eta T ((k : ℝ)-shift) *
      ‖c j * Complex.exp (Complex.I * ((((k : ℝ)-shift)*x j : ℝ) : ℂ))‖^2)
      (W * ‖c j‖^2) := by
    simpa only [hc] using hw.mul_right (‖c j‖^2)
  have he := weighted_sum_energy_hasSum
    (fun k : ℤ => cosineWeight 1 eta T ((k : ℝ)-shift))
    (fun j k => c j * Complex.exp (Complex.I * ((((k : ℝ)-shift)*x j : ℝ) : ℂ)))
    (fun j => W * ‖c j‖^2) hd
  simp only [← Finset.mul_sum] at he
  apply he
  intro i j hij
  have h := (cosineWeight_realCross_torus_hasSum (by omega : 1 ≤ 1)
    heta hT (hsep j i hij.symm) (c i) (c j) shift).div_const 2
  convert! h using 1
  · funext k
    rw [exponential_node_inner]
    ring
  · norm_num

/-- Restrict a signed Fourier weight to precisely the integer sampling block. -/
theorem cosineWeight_le_sample_energy {n N : ℕ} (hN : 0 < N)
    {eta W : ℝ} (heta : 0 < eta) (x : Fin n → ℝ) (c : Fin n → ℂ)
    (hw : HasSum (fun k : ℤ => cosineWeight 1 eta ((N : ℝ)/2)
      ((k : ℝ)-((N : ℝ)-1)/2) *
      ‖exponentialSum x c ((k : ℝ)-((N : ℝ)-1)/2)‖^2) W) :
    W ≤ ∑ k : Fin N, ‖exponentialSum x c ((k : ℝ)-((N : ℝ)-1)/2)‖^2 := by
  classical
  let S : Finset ℤ := Finset.univ.image (fun k : Fin N => (k.val : ℤ))
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hin (k : ℤ) (hk : k ∈ S) : |(k : ℝ)-((N : ℝ)-1)/2| ≤ (N : ℝ)/2 := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    have hj : (j.val : ℝ)+1 ≤ N := by exact_mod_cast j.isLt
    have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
    push_cast
    rw [abs_le]
    constructor <;> linarith
  have hout (k : ℤ) (hk : k ∉ S) : (N : ℝ)/2 < |(k : ℝ)-((N : ℝ)-1)/2| := by
    have hk' : k < 0 ∨ (N : ℤ) ≤ k := by
      by_contra hh
      push Not at hh
      apply hk
      have ht : k.toNat < N := by omega
      exact Finset.mem_image.mpr ⟨⟨k.toNat, ht⟩, Finset.mem_univ _, by simp [hh.1]⟩
    rcases hk' with hk' | hk'
    · have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      rw [abs_of_neg (by linarith)]
      linarith
    · have hkr : (N : ℝ) ≤ k := by exact_mod_cast hk'
      rw [abs_of_pos (by linarith)]
      linarith
  have hh := weighted_series_le_block S
    (fun k : ℤ => cosineWeight 1 eta ((N : ℝ)/2) ((k : ℝ)-((N : ℝ)-1)/2))
    (fun k : ℤ => ‖exponentialSum x c ((k : ℝ)-((N : ℝ)-1)/2)‖^2) W
    (fun _ => sq_nonneg _)
    (fun k hk => (cosineWeight_inside 1 heta (by positivity) (hin k hk)).2)
    (fun k hk => cosineWeight_outside 1 (by positivity) (hout k hk)) hw
  have hs : ∑ k ∈ S, ‖exponentialSum x c ((k : ℝ)-((N : ℝ)-1)/2)‖^2 =
      ∑ k : Fin N, ‖exponentialSum x c ((k : ℝ)-((N : ℝ)-1)/2)‖^2 := by
    rw [Finset.sum_image]
    · simp only [Int.cast_natCast]
    · intro i _ j _ hij
      apply Fin.ext
      exact_mod_cast (show (i.val : ℤ) = j.val from hij)
  rwa [hs] at hh

/-- Modulating coefficients removes a shift of the sampling grid without changing energy. -/
theorem exponentialSum_modulated_shift {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ)
    (shift t : ℝ) :
    exponentialSum x (fun j => c j * Complex.exp
      (Complex.I * ((shift*x j : ℝ) : ℂ))) (t-shift) = exponentialSum x c t := by
  unfold exponentialSum
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- A scalar Fourier mass yields the same lower bound on an unshifted finite block. -/
theorem separated_sampling_lower_of_cosineWeight {n N : ℕ} (hN : 0 < N)
    {eta W : ℝ} (heta : 0 < eta) (x : Fin n → ℝ) (c : Fin n → ℂ)
    (hsep : ∀ i j, i ≠ j → ∀ p : ℤ, eta < |x i-x j-2*Real.pi*p|)
    (hw : HasSum (fun k : ℤ => cosineWeight 1 eta ((N : ℝ)/2)
      ((k : ℝ)-((N : ℝ)-1)/2)) W) :
    W * (∑ j, ‖c j‖^2) ≤ ∑ k : Fin N, ‖exponentialSum x c k‖^2 := by
  let shift := ((N : ℝ)-1)/2
  let d := fun j => c j * Complex.exp (Complex.I * ((shift*x j : ℝ) : ℂ))
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh := separated_cosineWeight_hasSum heta (by positivity : 0 < (N : ℝ)/2)
    x d hsep shift hw
  have hs := cosineWeight_le_sample_energy hN heta x d hh
  have he : (∑ j, ‖d j‖^2) = ∑ j, ‖c j‖^2 := by
    simp [d, Complex.norm_exp, Complex.mul_re]
  have hd (t : ℝ) : exponentialSum x d (t-shift) = exponentialSum x c t :=
    exponentialSum_modulated_shift x c shift t
  change W * (∑ j, ‖d j‖^2) ≤
    ∑ k : Fin N, ‖exponentialSum x d ((k : ℝ)-shift)‖^2 at hs
  simpa only [he, hd] using hs

open Filter Topology

/-- The endpoint separation follows from strictly narrower windows by a scalar limit.
The supplied mass identity is an analytic interface, discharged for the cosine-squared
window in the public separated-sampling theorem. -/
theorem separated_sampling_half_of_cosineMass {n N : ℕ} (hN : 2 ≤ N)
    (x : Fin n → ℝ) (c : Fin n → ℂ)
    (hsep : ∀ i j, i ≠ j → ∀ p : ℤ, 4*Real.pi/(N : ℝ) ≤ |x i-x j-2*Real.pi*p|)
    (hmass : ∀ eta : ℝ, 0 < eta → eta < 2*Real.pi →
      HasSum (fun k : ℤ => cosineWeight 1 eta ((N : ℝ)/2)
        ((k : ℝ)-((N : ℝ)-1)/2))
        (3*Real.pi/eta - 4*Real.pi^3/(((N : ℝ)/2)^2*eta^3))) :
    ((N : ℝ)/2) * (∑ j, ‖c j‖^2) ≤ ∑ k : Fin N, ‖exponentialSum x c k‖^2 := by
  let eta₀ := 4*Real.pi/(N : ℝ)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have heta : 0 < eta₀ := by dsimp [eta₀]; positivity
  have hetaUpper : eta₀ ≤ 2*Real.pi := by
    dsimp [eta₀]
    apply (div_le_iff₀ hNr).2
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [Real.pi_pos]
  have hcont : ContinuousAt (fun eta : ℝ =>
      (3*Real.pi/eta - 4*Real.pi^3/(((N : ℝ)/2)^2*eta^3)) *
        (∑ j, ‖c j‖^2)) eta₀ := by
    have hne := heta.ne'
    fun_prop (disch := positivity)
  have he : 3*Real.pi/eta₀ - 4*Real.pi^3/(((N : ℝ)/2)^2*eta₀^3) = (N : ℝ)/2 := by
    dsimp [eta₀]
    field_simp
    ring
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio eta₀))
  rw [he] at hlim
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT heta] with eta he'
  exact separated_sampling_lower_of_cosineWeight (by omega) he'.1 x c
    (fun i j hij p => he'.2.trans_le (hsep i j hij p))
    (hmass eta he'.1 (he'.2.trans_le hetaUpper))

end LeanNumDetect
