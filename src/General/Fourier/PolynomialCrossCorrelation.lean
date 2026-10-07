import General.Fourier.PhaseEstimates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import General.Finite.FiniteRealGeometry
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Finite summation-by-parts bounds for polynomially weighted Fourier sums.
The normalized monomial cross moments are bounded independently of the
polynomial degree. These estimates are the discrete orthogonality ingredient
for separated, modulated polynomial column spaces.
-/

set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open WithLp

namespace LeanNumDetect.PolynomialCrossCorrelation
noncomputable section

/-- Exact finite Abel identity, with both endpoint terms displayed. -/
theorem geometric_weighted_sum_identity (q : ℂ) (a : ℕ → ℂ) (N : ℕ) :
    (q - 1) * (∑ k ∈ Finset.range (N + 1), q ^ k * a k) =
      q ^ (N + 1) * a N - a 0 -
        ∑ k ∈ Finset.range N, q ^ (k + 1) * (a (k + 1) - a k) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ]
    simp only [pow_succ]
    ring

/-- Abel's inequality for a complex sequence and a unit-modulus phase. -/
theorem geometric_weighted_sum_norm_bound (q : ℂ) (hq : ‖q‖ = 1)
    (a : ℕ → ℂ) (N : ℕ) :
    ‖q - 1‖ * ‖∑ k ∈ Finset.range (N + 1), q ^ k * a k‖ ≤
      ‖a 0‖ + ‖a N‖ + ∑ k ∈ Finset.range N, ‖a (k + 1) - a k‖ := by
  rw [← norm_mul, geometric_weighted_sum_identity]
  calc
    ‖q ^ (N + 1) * a N - a 0 -
        ∑ k ∈ Finset.range N, q ^ (k + 1) * (a (k + 1) - a k)‖ ≤
        ‖q ^ (N + 1) * a N‖ + ‖a 0‖ +
          ∑ k ∈ Finset.range N, ‖q ^ (k + 1) * (a (k + 1) - a k)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_sum_le _ _))
    _ = ‖a 0‖ + ‖a N‖ + ∑ k ∈ Finset.range N, ‖a (k + 1) - a k‖ := by
      simp only [norm_mul, norm_pow, hq, one_pow, one_mul]
      ring

/-- For a nonnegative increasing real weight, its total variation telescopes
exactly, so the weighted sum bound is twice the final weight. -/
theorem geometric_monotone_real_weight_bound (q : ℂ) (hq : ‖q‖ = 1)
    (a : ℕ → ℝ) (ha0 : 0 ≤ a 0) (ha : Monotone a) (N : ℕ) :
    ‖q - 1‖ * ‖∑ k ∈ Finset.range (N + 1), q ^ k * (a k : ℂ)‖ ≤ 2 * a N := by
  have h := geometric_weighted_sum_norm_bound q hq (fun k => (a k : ℂ)) N
  have hnonneg (k : ℕ) : 0 ≤ a k := ha0.trans (ha (Nat.zero_le _))
  have hdiff (k : ℕ) : 0 ≤ a (k + 1) - a k := sub_nonneg.mpr (ha (Nat.le_succ _))
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnonneg _),
    ← Complex.ofReal_sub, abs_of_nonneg (hdiff _)] at h
  rw [Finset.sum_range_sub] at h
  linarith

/-- A normalized polynomial monomial has unit final weight. -/
theorem geometric_normalized_monomial_bound (q : ℂ) (hq : ‖q‖ = 1)
    (N : ℕ) (hN : 0 < N) (r : ℕ) :
    ‖q - 1‖ *
      ‖∑ k : Fin (N + 1), q ^ k.val * (((k.val : ℝ) / N) ^ r : ℝ)‖ ≤ 2 := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmono : Monotone (fun k : ℕ => ((k : ℝ) / N) ^ r) := by
    intro k l hkl
    exact pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_right (by exact_mod_cast hkl) hNR.le) r
  have h := geometric_monotone_real_weight_bound q hq
    (fun k => ((k : ℝ) / N) ^ r) (by positivity) hmono N
  change ‖q - 1‖ * ‖∑ k : Fin (N + 1),
    (fun k : ℕ => q ^ k * ((((k : ℝ) / N) ^ r : ℝ) : ℂ)) k.val‖ ≤ 2
  rw [Fin.sum_univ_eq_sum_range
    (fun k => q ^ k * ((((k : ℝ) / N) ^ r : ℝ) : ℂ)) (N + 1)]
  simpa only [div_self hNR.ne', one_pow, mul_one] using h

/-- Convert the moment estimate to a quotient whenever the two phases differ. -/
theorem geometric_normalized_monomial_norm_le (q : ℂ) (hq : ‖q‖ = 1)
    (hq1 : q ≠ 1) (N : ℕ) (hN : 0 < N) (r : ℕ) :
    ‖∑ k : Fin (N + 1), q ^ k.val * (((k.val : ℝ) / N) ^ r : ℝ)‖ ≤ 2 / ‖q - 1‖ := by
  have hp : 0 < ‖q - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hq1)
  exact (le_div_iff₀ hp).2 (by
    simpa only [mul_comm] using geometric_normalized_monomial_bound q hq N hN r)

/-- The chord on the unit circle controls the angular distance on a principal
interval. -/
theorem norm_exp_sub_one_lower {θ : ℝ} (hθ : |θ| ≤ Real.pi) :
    (2 / Real.pi) * |θ| ≤ ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ := by
  have hhalf : |θ / 2| ≤ Real.pi := by rw [abs_div]; norm_num; linarith [abs_nonneg θ]
  have hhalf' : |θ| / 2 ≤ Real.pi / 2 := by linarith
  have h := Real.mul_le_sin (by positivity : 0 ≤ |θ| / 2) hhalf'
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.abs_sin_eq_sin_abs_of_abs_le_pi hhalf, abs_div]
  norm_num
  nlinarith

/-- Any uniform lower bound on all winding distances is a chord lower bound,
without fixing angular representatives. -/
theorem periodic_chord_lower (θ η : ℝ)
    (hsep : ∀ p : ℤ, η ≤ |θ - 2 * Real.pi * p|) :
    (2 / Real.pi) * η ≤ ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ := by
  obtain ⟨p, hp⟩ := exists_periodic_gap_le_pi θ
  have h := norm_exp_sub_one_lower hp
  have he : Complex.exp (Complex.I * ((θ - 2 * Real.pi * p : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (θ : ℂ)) := by
    have harg : Complex.I * ((θ - 2 * Real.pi * p : ℝ) : ℂ) =
        Complex.I * (θ : ℂ) - (p : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      ring
    rw [harg, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]
  rw [he] at h
  exact (mul_le_mul_of_nonneg_left (hsep p) (by positivity)).trans h

/-- A separated Fourier phase weighted by any normalized monomial has a
degree-independent bound `π/η` on the full integer sum. -/
theorem fourier_normalized_monomial_norm_le (θ η : ℝ) (hη : 0 < η)
    (hsep : ∀ p : ℤ, η ≤ |θ - 2 * Real.pi * p|)
    (N : ℕ) (hN : 0 < N) (r : ℕ) :
    ‖∑ k : Fin (N + 1), Complex.exp (Complex.I * (((k.val : ℝ) * θ : ℝ) : ℂ)) *
      (((k.val : ℝ) / N) ^ r : ℝ)‖ ≤ Real.pi / η := by
  let q := Complex.exp (Complex.I * (θ : ℂ))
  have hq : ‖q‖ = 1 := Complex.norm_exp_I_mul_ofReal θ
  have hchord : 2 / Real.pi * η ≤ ‖q - 1‖ := periodic_chord_lower θ η hsep
  have hnorm0 : 0 < ‖q - 1‖ := (by positivity : 0 < 2 / Real.pi * η).trans_le hchord
  have hq1 : q ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hnorm0
    exact hnorm0.false
  have hsum := geometric_normalized_monomial_norm_le q hq hq1 N hN r
  have he (k : Fin (N + 1)) : q ^ k.val =
      Complex.exp (Complex.I * (((k.val : ℝ) * θ : ℝ) : ℂ)) := by
    dsimp [q]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [he] at hsum
  apply hsum.trans
  have hquot := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
    (by positivity : 0 < 2 / Real.pi * η) hchord
  have hcancel : 2 / (2 / Real.pi * η) = Real.pi / η := by field_simp
  rwa [hcancel] at hquot

/-- Evaluate a polynomial in the normalized integer variable `k/N`. -/
def polynomialValue {s N : ℕ} (c : Fin s → ℂ) (k : Fin (N + 1)) : ℂ :=
  ∑ r, c r * ((((k.val : ℝ) / N) ^ r.val : ℝ) : ℂ)

theorem star_phase_mul_phase (x y : ℝ) (k : ℕ) :
    star (Complex.exp (Complex.I * (((k : ℝ) * x : ℝ) : ℂ))) *
      Complex.exp (Complex.I * (((k : ℝ) * y : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (((k : ℝ) * (y - x) : ℝ) : ℂ)) := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- Expand a cross inner product into scalar Fourier moments. -/
theorem cross_polynomial_identity {s t N : ℕ} (c : Fin s → ℂ) (d : Fin t → ℂ)
    (x y : ℝ) :
    (∑ k : Fin (N + 1),
      star (Complex.exp (Complex.I * (((k.val : ℝ) * x : ℝ) : ℂ)) * polynomialValue c k) *
        (Complex.exp (Complex.I * (((k.val : ℝ) * y : ℝ) : ℂ)) * polynomialValue d k)) =
      ∑ r : Fin s, ∑ v : Fin t, (star (c r) * d v) *
        (∑ k : Fin (N + 1),
          Complex.exp (Complex.I * (((k.val : ℝ) * (y - x) : ℝ) : ℂ)) *
            ((((k.val : ℝ) / N) ^ (r.val + v.val) : ℝ) : ℂ)) := by
  have hk (k : Fin (N + 1)) :
      star (Complex.exp (Complex.I * (((k.val : ℝ) * x : ℝ) : ℂ)) * polynomialValue c k) *
        (Complex.exp (Complex.I * (((k.val : ℝ) * y : ℝ) : ℂ)) * polynomialValue d k) =
      ∑ r : Fin s, ∑ v : Fin t, (star (c r) * d v) *
        (Complex.exp (Complex.I * (((k.val : ℝ) * (y - x) : ℝ) : ℂ)) *
          ((((k.val : ℝ) / N) ^ (r.val + v.val) : ℝ) : ℂ)) := by
    simp only [polynomialValue, star_mul, star_sum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro v _
    simp only [Complex.star_def, Complex.conj_ofReal, pow_add]
    have h := star_phase_mul_phase x y k.val
    change star (Complex.exp (Complex.I * (((k.val : ℝ) * x : ℝ) : ℂ))) *
      Complex.exp (Complex.I * (((k.val : ℝ) * y : ℝ) : ℂ)) = _ at h
    rw [Complex.star_def] at h
    calc
      _ = (star (c r) * d v) *
          (star (Complex.exp (Complex.I * (((k.val : ℝ) * x : ℝ) : ℂ))) *
            Complex.exp (Complex.I * (((k.val : ℝ) * y : ℝ) : ℂ))) *
          (((((k.val : ℝ) / N) ^ r.val : ℝ) : ℂ) *
            ((((k.val : ℝ) / N) ^ v.val : ℝ) : ℂ)) := by
          simp only [Complex.star_def]
          ring
      _ = _ := by rw [Complex.star_def, h, Complex.ofReal_mul]; push_cast; ring
  simp_rw [hk]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]

/-- A coefficient-level cross bound for two modulated polynomial sequences.
No uniform dimension bound is needed here; source-count norm-equivalence
constants can be applied separately by the caller. -/
theorem cross_polynomial_norm_le {s t N : ℕ} (hN : 0 < N)
    (c : Fin s → ℂ) (d : Fin t → ℂ) (x y η : ℝ) (hη : 0 < η)
    (hsep : ∀ p : ℤ, η ≤ |y - x - 2 * Real.pi * p|) :
    ‖∑ k : Fin (N + 1),
      star (Complex.exp (Complex.I * (((k.val : ℝ) * x : ℝ) : ℂ)) * polynomialValue c k) *
        (Complex.exp (Complex.I * (((k.val : ℝ) * y : ℝ) : ℂ)) * polynomialValue d k)‖ ≤
      (Real.pi / η) * (∑ r, ‖c r‖) * (∑ v, ‖d v‖) := by
  rw [cross_polynomial_identity]
  calc
    _ ≤ ∑ r : Fin s, ∑ v : Fin t, ‖(star (c r) * d v) *
        (∑ k : Fin (N + 1),
          Complex.exp (Complex.I * (((k.val : ℝ) * (y - x) : ℝ) : ℂ)) *
            ((((k.val : ℝ) / N) ^ (r.val + v.val) : ℝ) : ℂ))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => norm_sum_le _ _)
    _ ≤ ∑ r : Fin s, ∑ v : Fin t, ‖c r‖ * ‖d v‖ * (Real.pi / η) := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro v _
      simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left
        (fourier_normalized_monomial_norm_le (y - x) η hη hsep N hN (r.val + v.val))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      simp_rw [mul_assoc]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- The unnormalized modulated polynomial vector on the integer rows. -/
def modulatedPolynomial {s : ℕ} (N : ℕ) (x : ℝ) (c : Fin s → ℂ) :
    EuclideanSpace ℂ (Fin (N + 1)) :=
  toLp 2 (fun k => Complex.exp (Complex.I * (((k.val : ℝ) * x : ℝ) : ℂ)) *
    polynomialValue c k)

theorem inner_modulatedPolynomial_norm_le {s t N : ℕ} (hN : 0 < N)
    (c : Fin s → ℂ) (d : Fin t → ℂ) (x y η : ℝ) (hη : 0 < η)
    (hsep : ∀ p : ℤ, η ≤ |y - x - 2 * Real.pi * p|) :
    ‖⟪modulatedPolynomial N x c, modulatedPolynomial N y d⟫_ℂ‖ ≤
      (Real.pi / η) * (∑ r, ‖c r‖) * (∑ v, ‖d v‖) := by
  simpa only [PiLp.inner_apply, modulatedPolynomial, ofLp_toLp,
    RCLike.inner_apply', RCLike.star_def] using
      cross_polynomial_norm_le hN c d x y η hη hsep

/-- A general cross-inner-product perturbation bound. Both approximation
errors are measured relative to the original vectors, so no rank or
condition-number hypothesis is hidden in the conclusion. -/
theorem inner_approximation_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u v u0 v0 : E) {ε κ : ℝ}
    (hε : 0 ≤ ε) (hu : ‖u - u0‖ ≤ ε * ‖u‖) (hv : ‖v - v0‖ ≤ ε * ‖v‖)
    (hcross : ‖⟪u0, v0⟫_ℂ‖ ≤ κ * ‖u‖ * ‖v‖) :
    ‖⟪u, v⟫_ℂ‖ ≤ (κ + 2 * ε + ε ^ 2) * ‖u‖ * ‖v‖ := by
  have hu0 : ‖u0‖ ≤ (1 + ε) * ‖u‖ := by
    have h := norm_sub_le u (u - u0)
    rw [sub_sub_cancel] at h
    linarith
  have he : ⟪u, v⟫_ℂ = ⟪u0, v0⟫_ℂ + ⟪u - u0, v⟫_ℂ + ⟪u0, v - v0⟫_ℂ := by
    rw [inner_sub_left, inner_sub_right]
    ring
  rw [he]
  have hfirst := (norm_inner_le_norm (𝕜 := ℂ) (u - u0) v).trans
    (mul_le_mul_of_nonneg_right hu (norm_nonneg _))
  have hsecond := (norm_inner_le_norm (𝕜 := ℂ) u0 (v - v0)).trans
    (mul_le_mul hu0 hv (norm_nonneg _) (by positivity))
  have htotal := ((norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add hcross hfirst) hsecond)
  calc
    _ ≤ κ * ‖u‖ * ‖v‖ + ε * ‖u‖ * ‖v‖ +
        (1 + ε) * ‖u‖ * (ε * ‖v‖) := htotal
    _ = (κ + 2 * ε + ε ^ 2) * ‖u‖ * ‖v‖ := by ring

end
end LeanNumDetect.PolynomialCrossCorrelation
