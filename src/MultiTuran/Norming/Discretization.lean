import General.Fourier.UniformGridEvaluationBounds

/-!
# Segmented Riemann sums and the norming threshold

The analytic conversion used by the manuscript's `prop:discretization` is
separated from the exponential-sum derivative estimates. Every integral here
is an actual interval integral. The intervals may be translated arbitrarily.

The relative-error coefficient and the sufficient-condition coefficient are
kept distinct: an error coefficient `K` requires the threshold `2 * K` to
obtain the norming constant `1 / 2`.
-/

set_option autoImplicit false
open scoped BigOperators
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran.Discretization
noncomputable section

/-- Integral over one thickened block of consecutive integer samples. -/
def blockIntegral (f : ℝ → ℝ) (a : ℝ) (L : ℕ) : ℝ :=
  ∫ t in a..a + L, f t

/-- Left endpoint samples in one block of `L` unit cells. -/
def blockSamples (f : ℝ → ℝ) (a : ℝ) (L : ℕ) : ℝ :=
  ∑ k ∈ Finset.range L, f (a + k)

/-- A pointwise error on each unit cell bounds the error of its left sum. -/
theorem blockIntegral_le_blockSamples_add_error
    {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) (L : ℕ) (ε : ℝ)
    (hcell : ∀ k < L, ∀ t ∈ Icc (a + k) (a + k + 1),
      f t ≤ f (a + k) + ε) :
    blockIntegral f a L ≤ blockSamples f a L + L * ε := by
  let x : ℕ → ℝ := fun k => a + k
  have hstep (k : ℕ) : x (k + 1) - x k = 1 := by
    dsimp [x]
    push_cast
    ring
  have hmono (k : ℕ) : x k ≤ x (k + 1) := by linarith [hstep k]
  have hlocal (k : ℕ) (hk : k < L) :
      (∫ t in x k..x (k + 1), f t) ≤ f (a + k) + ε := by
    have h := intervalIntegral.integral_mono_on (μ := volume) (hmono k)
      (hf.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      (g := fun _ => f (a + k) + ε) (fun t ht => by
        apply hcell k hk t
        simpa [x, Nat.cast_add, Nat.cast_one, add_assoc] using ht)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, hstep, one_mul] using h
  have hpartition := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (a := x) (n := L) (fun k _ => hf.intervalIntegrable (x k) (x (k + 1)))
  have hpartition' :
      blockIntegral f a L = ∑ k ∈ Finset.range L, ∫ t in x k..x (k + 1), f t := by
    simpa [blockIntegral, x] using hpartition.symm
  rw [hpartition']
  calc
    _ ≤ ∑ k ∈ Finset.range L, (f (a + k) + ε) :=
      Finset.sum_le_sum (fun k hk => hlocal k (Finset.mem_range.mp hk))
    _ = blockSamples f a L + L * ε := by
      simp [blockSamples, Finset.sum_add_distrib]

/-- A Lipschitz estimate on every cell supplies its pointwise Riemann error. -/
theorem blockIntegral_le_blockSamples_add_lipschitz_error
    {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) (L : ℕ)
    {D : ℝ} (hD : 0 ≤ D)
    (hLip : ∀ k < L, ∀ t ∈ Icc (a + k) (a + k + 1),
      f t ≤ f (a + k) + D * |t - (a + k)|) :
    blockIntegral f a L ≤ blockSamples f a L + L * D := by
  apply blockIntegral_le_blockSamples_add_error hf a L D
  intro k hk t ht
  have hdist : |t - (a + k)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have h := mul_le_mul_of_nonneg_left hdist hD
  exact (hLip k hk t ht).trans (by simpa using add_le_add_left h (f (a + k)))

/-- Sum of actual interval integrals over a finite family of measured blocks. -/
def segmentedIntegral {B : Type*} [Fintype B]
    (f : ℝ → ℝ) (a : B → ℝ) (L : B → ℕ) : ℝ :=
  ∑ b, blockIntegral f (a b) (L b)

/-- Sum of the left endpoint samples over all blocks. -/
def segmentedSamples {B : Type*} [Fintype B]
    (f : ℝ → ℝ) (a : B → ℝ) (L : B → ℕ) : ℝ :=
  ∑ b, blockSamples f (a b) (L b)

/-- The errors of separate blocks add without an aperture factor. -/
theorem segmentedIntegral_le_segmentedSamples_add_error
    {B : Type*} [Fintype B] {f : ℝ → ℝ} (hf : Continuous f)
    (a : B → ℝ) (L : B → ℕ) (ε : B → ℝ)
    (hcell : ∀ b, ∀ k < L b, ∀ t ∈ Icc (a b + k) (a b + k + 1),
      f t ≤ f (a b + k) + ε b) :
    segmentedIntegral f a L ≤ segmentedSamples f a L + ∑ b, L b * ε b := by
  calc
    _ ≤ ∑ b, (blockSamples f (a b) (L b) + L b * ε b) :=
      Finset.sum_le_sum (fun b _ =>
        blockIntegral_le_blockSamples_add_error hf (a b) (L b) (ε b) (hcell b))
    _ = _ := by simp [segmentedSamples, Finset.sum_add_distrib]

/-- A total Riemann error of at most half the integral gives norming `1 / 2`. -/
theorem half_integral_le_samples_of_error {I S E : ℝ}
    (herror : I ≤ S + E) (hsmall : 2 * E ≤ I) : (1 / 2 : ℝ) * I ≤ S := by
  linarith

/-- Version for a relative error, also valid when the energy vanishes. -/
theorem half_integral_le_samples_of_relative_error {I S κ : ℝ}
    (hI : 0 ≤ I) (herror : |I - S| ≤ κ * I) (hκ : κ ≤ 1 / 2) :
    (1 / 2 : ℝ) * I ≤ S := by
  have h := (le_abs_self (I - S)).trans herror
  have hmul := mul_le_mul_of_nonneg_right hκ hI
  linarith

/-- The sufficient threshold is twice the coefficient in the error estimate. -/
theorem relative_error_le_half_of_threshold (d : ℕ) {K R L : ℝ}
    (_hK : 0 ≤ K) (_hR : 0 ≤ R) (hL : 0 < L)
    (hthreshold : (2 * K) * R ≤ L ^ (d + 1)) :
    K * R / L ^ (d + 1) ≤ 1 / 2 := by
  rw [div_le_iff₀ (pow_pos hL (d + 1))]
  nlinarith

/-- The arithmetic step in the manuscript's sufficient discretization condition.
Here `R` can be the sampled cardinality times `n ^ (4 * d + 5)`. -/
theorem half_integral_le_samples_of_threshold (d : ℕ) {I S K R L : ℝ}
    (hI : 0 ≤ I) (hK : 0 ≤ K) (hR : 0 ≤ R) (hL : 0 < L)
    (herror : |I - S| ≤ (K * R / L ^ (d + 1)) * I)
    (hthreshold : (2 * K) * R ≤ L ^ (d + 1)) :
    (1 / 2 : ℝ) * I ≤ S :=
  half_integral_le_samples_of_relative_error hI herror
    (relative_error_le_half_of_threshold d hK hR hL hthreshold)

end
end LeanNumDetect.MultiTuran.Discretization
