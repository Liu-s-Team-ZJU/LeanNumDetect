import NumDetect.MUSICPeakCurvatureIdentity
import NumDetect.MUSICPeakFourierDerivativeNorm
import NumDetect.MUSICPeakFourierLineVector

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WithLp
open scoped InnerProductSpace RealInnerProductSpace
namespace LeanNumDetect
namespace NumDetect
noncomputable section

private def fourierPhase {d : ℕ} {ι : Type*}
    (frequency : ι → Point d) (u : Point d) (i : ι) : ℂ :=
  Complex.I * (dot (frequency i) u : ℂ)

private def fourierPowerVector {d : ℕ} {ι : Type*} [Fintype ι]
    (frequency : ι → Point d) (u : Point d) (k : ℕ) (y : Point d) :
    EuclideanSpace ℂ ι :=
  toLp 2 (fun i => fourierPhase frequency u i ^ k * normalizedSteering frequency y i)

private def fourierMixedVector {d : ℕ} {ι : Type*} [Fintype ι]
    (frequency : ι → Point d) (u v : Point d) (k : ℕ) (y : Point d) :
    EuclideanSpace ℂ ι :=
  toLp 2 (fun i =>
    (fourierPhase frequency u i ^ k * fourierPhase frequency v i) *
      normalizedSteering frequency y i)

theorem fourierPowerVector_norm_le
    {d k : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (frequency : ι → Point d) (u y : Point d) (Ω : ℝ)
    (hΩ : 0 ≤ Ω) (hphase : ∀ i, |dot (frequency i) u| ≤ Ω) :
    ‖fourierPowerVector frequency u k y‖ ≤ Ω ^ k := by
  exact norm_fourier_directional_derivative_vector_le
    frequency y u Ω hΩ hphase

theorem fourierMixedVector_norm_le
    {d k : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (frequency : ι → Point d) (u v y : Point d) (Ω : ℝ)
    (hΩ : 0 ≤ Ω)
    (hu : ∀ i, |dot (frequency i) u| ≤ Ω)
    (hv : ∀ i, |dot (frequency i) v| ≤ Ω) :
    ‖fourierMixedVector frequency u v k y‖ ≤ Ω ^ (k + 1) := by
  have ha (i : ι) :
      ‖fourierPhase frequency u i ^ k * fourierPhase frequency v i‖ ≤
        Ω ^ (k + 1) := by
    have hu' : ‖fourierPhase frequency u i‖ ≤ Ω := by
      simpa [fourierPhase] using hu i
    have hv' : ‖fourierPhase frequency v i‖ ≤ Ω := by
      simpa [fourierPhase] using hv i
    calc
      ‖fourierPhase frequency u i ^ k * fourierPhase frequency v i‖ =
          ‖fourierPhase frequency u i‖ ^ k *
            ‖fourierPhase frequency v i‖ := by rw [norm_mul, norm_pow]
      _ ≤ Ω ^ k * Ω := by
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hu' k)
          hv' (norm_nonneg _) (pow_nonneg hΩ _)
      _ = Ω ^ (k + 1) := by rw [pow_succ]
  have h := norm_toLp_pointwise_mul_le
    (fun i => fourierPhase frequency u i ^ k * fourierPhase frequency v i)
    (normalizedSteering frequency y) (Ω ^ (k + 1))
    (pow_nonneg hΩ _) ha
  simpa only [fourierMixedVector, norm_normalizedSteering, mul_one] using h

theorem fourierMixedVector_norm_le_twoRadii
    {d k : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (frequency : ι → Point d) (u v y : Point d) (Ωu Ωv : ℝ)
    (hΩu : 0 ≤ Ωu) (hΩv : 0 ≤ Ωv)
    (hu : ∀ i, |dot (frequency i) u| ≤ Ωu)
    (hv : ∀ i, |dot (frequency i) v| ≤ Ωv) :
    ‖fourierMixedVector frequency u v k y‖ ≤ Ωu ^ k * Ωv := by
  have ha (i : ι) :
      ‖fourierPhase frequency u i ^ k * fourierPhase frequency v i‖ ≤
        Ωu ^ k * Ωv := by
    have hu' : ‖fourierPhase frequency u i‖ ≤ Ωu := by
      simpa [fourierPhase] using hu i
    have hv' : ‖fourierPhase frequency v i‖ ≤ Ωv := by
      simpa [fourierPhase] using hv i
    calc
      ‖fourierPhase frequency u i ^ k * fourierPhase frequency v i‖ =
          ‖fourierPhase frequency u i‖ ^ k *
            ‖fourierPhase frequency v i‖ := by rw [norm_mul, norm_pow]
      _ ≤ Ωu ^ k * Ωv :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hu' k)
          hv' (norm_nonneg _) (pow_nonneg hΩu _)
  have h := norm_toLp_pointwise_mul_le
    (fun i => fourierPhase frequency u i ^ k * fourierPhase frequency v i)
    (normalizedSteering frequency y) (Ωu ^ k * Ωv)
    (mul_nonneg (pow_nonneg hΩu _) hΩv) ha
  simpa only [fourierMixedVector, norm_normalizedSteering, mul_one] using h

theorem fourierPowerVector_hasDerivAt_line
    {d k : ℕ} {ι : Type*} [Fintype ι]
    (frequency : ι → Point d) (y u v : Point d) (t : ℝ) :
    HasDerivAt (fun s => fourierPowerVector frequency u k (y + s • v))
      (fourierMixedVector frequency u v k (y + t • v)) t := by
  convert (normalizedSteeringVector_mul_hasDerivAt_line frequency y v
      (fun i => fourierPhase frequency u i ^ k) t) using 1 <;>
    rfl

theorem fourierMixedVector_same_eq_power_succ
    {d k : ℕ} {ι : Type*} [Fintype ι]
    (frequency : ι → Point d) (y u : Point d) :
    fourierMixedVector frequency u u k y =
      fourierPowerVector frequency u (k + 1) y := by
  ext i
  simp only [fourierMixedVector, fourierPowerVector, pow_succ]

theorem fourierPowerVector_hasDerivAt_same
    {d k : ℕ} {ι : Type*} [Fintype ι]
    (frequency : ι → Point d) (y u : Point d) (t : ℝ) :
    HasDerivAt (fun s => fourierPowerVector frequency u k (y + s • u))
      (fourierPowerVector frequency u (k + 1) (y + t • u)) t := by
  simpa only [fourierMixedVector_same_eq_power_succ] using
    (fourierPowerVector_hasDerivAt_line (k := k) frequency y u u t)

theorem fourierPowerVector_zero
    {d : ℕ} {ι : Type*} [Fintype ι]
    (frequency : ι → Point d) (y u : Point d) :
    fourierPowerVector frequency u 0 y =
      toLp 2 (normalizedSteering frequency y) := by
  ext i
  simp [fourierPowerVector]

section
variable {ι : Type*} [Fintype ι]
local instance realInnerProductSpace_fourierCurvature :
    InnerProductSpace ℝ (EuclideanSpace ℂ ι) :=
  InnerProductSpace.rclikeToReal ℂ _

/-- Exact line curvature of the squared normalized MUSIC residual. -/
theorem fourierProjected_sq_line_curvature_formula
    {d : ℕ} (frequency : ι → Point d)
    (S : Submodule ℂ (EuclideanSpace ℂ ι))
    (y u : Point d) :
    iteratedDeriv 2 (fun t : ℝ =>
      ‖S.starProjection (toLp 2
        (normalizedSteering frequency (y + t • u)))‖ ^ 2) 0 =
      2 * ⟪S.starProjection (fourierPowerVector frequency u 0 y),
        S.starProjection (fourierPowerVector frequency u 2 y)⟫_ℝ +
      2 * ⟪S.starProjection (fourierPowerVector frequency u 1 y),
        S.starProjection (fourierPowerVector frequency u 1 y)⟫_ℝ := by
  let T := S.starProjection.restrictScalars ℝ
  have h0 : ∀ t, HasDerivAt
      (fun s : ℝ => fourierPowerVector frequency u 0 (y + s • u))
      (fourierPowerVector frequency u 1 (y + t • u)) t := by
    intro t
    simpa using
      (fourierPowerVector_hasDerivAt_same (k := 0) frequency y u t)
  have h1 : ∀ t, HasDerivAt
      (fun s : ℝ => fourierPowerVector frequency u 1 (y + s • u))
      (fourierPowerVector frequency u 2 (y + t • u)) t := by
    intro t
    simpa using
      (fourierPowerVector_hasDerivAt_same (k := 1) frequency y u t)
  have h := iteratedDeriv_projected_normSq_two T
    (fun t => fourierPowerVector frequency u 0 (y + t • u))
    (fun t => fourierPowerVector frequency u 1 (y + t • u))
    (fun t => fourierPowerVector frequency u 2 (y + t • u)) h0 h1 0
  simpa [T, fourierPowerVector_zero] using h

/-- Mixed third derivatives control radial variation of squared MUSIC curvature. -/
theorem fourierProjected_sq_line_curvature_radial_deriv_abs_le
    {d : ℕ} [Nonempty ι]
    (frequency : ι → Point d)
    (S : Submodule ℂ (EuclideanSpace ℂ ι))
    (y u v : Point d) (Ωu Ωv : ℝ)
    (hΩu : 0 ≤ Ωu) (hΩv : 0 ≤ Ωv)
    (hu : ∀ i, |dot (frequency i) u| ≤ Ωu)
    (hv : ∀ i, |dot (frequency i) v| ≤ Ωv) :
    ∀ s : ℝ,
      DifferentiableAt ℝ (fun τ : ℝ => iteratedDeriv 2 (fun t : ℝ =>
        ‖S.starProjection (toLp 2
          (normalizedSteering frequency ((y + τ • v) + t • u)))‖ ^ 2) 0) s ∧
      |deriv (fun τ : ℝ => iteratedDeriv 2 (fun t : ℝ =>
        ‖S.starProjection (toLp 2
          (normalizedSteering frequency ((y + τ • v) + t • u)))‖ ^ 2) 0) s| ≤
        8 * Ωu ^ 2 * Ωv := by
  let T := S.starProjection.restrictScalars ℝ
  let a (s : ℝ) := fourierPowerVector frequency u 0 (y + s • v)
  let au (s : ℝ) := fourierPowerVector frequency u 1 (y + s • v)
  let auu (s : ℝ) := fourierPowerVector frequency u 2 (y + s • v)
  let av (s : ℝ) := fourierMixedVector frequency u v 0 (y + s • v)
  let auv (s : ℝ) := fourierMixedVector frequency u v 1 (y + s • v)
  let auuv (s : ℝ) := fourierMixedVector frequency u v 2 (y + s • v)
  let H (s : ℝ) := iteratedDeriv 2 (fun t : ℝ =>
    ‖S.starProjection (toLp 2
      (normalizedSteering frequency ((y + s • v) + t • u)))‖ ^ 2) 0
  have hH : H = fun s =>
      2 * ⟪T (a s), T (auu s)⟫_ℝ +
        2 * ⟪T (au s), T (au s)⟫_ℝ := by
    funext s
    simpa [H, T, a, au, auu] using
      (fourierProjected_sq_line_curvature_formula frequency S (y + s • v) u)
  have hT : ∀ z, ‖T z‖ ≤ ‖z‖ := by
    intro z
    simpa [T] using S.norm_starProjection_apply_le z
  have hderivA : ∀ s, HasDerivAt a (av s) s := by
    intro s
    exact fourierPowerVector_hasDerivAt_line (k := 0) frequency y u v s
  have hderivU : ∀ s, HasDerivAt au (auv s) s := by
    intro s
    exact fourierPowerVector_hasDerivAt_line (k := 1) frequency y u v s
  have hderivUU : ∀ s, HasDerivAt auu (auuv s) s := by
    intro s
    exact fourierPowerVector_hasDerivAt_line (k := 2) frequency y u v s
  have ha : ∀ s, ‖a s‖ ≤ 1 := by
    intro s
    simpa [a] using
      (fourierPowerVector_norm_le (k := 0) frequency u (y + s • v) Ωu hΩu hu)
  have hau : ∀ s, ‖au s‖ ≤ Ωu := by
    intro s
    simpa [au] using
      (fourierPowerVector_norm_le (k := 1) frequency u (y + s • v) Ωu hΩu hu)
  have hauu : ∀ s, ‖auu s‖ ≤ Ωu ^ 2 := by
    intro s
    exact fourierPowerVector_norm_le (k := 2) frequency u (y + s • v) Ωu hΩu hu
  have hav : ∀ s, ‖av s‖ ≤ Ωv := by
    intro s
    simpa [av] using (fourierMixedVector_norm_le_twoRadii (k := 0)
      frequency u v (y + s • v) Ωu Ωv hΩu hΩv hu hv)
  have hauv : ∀ s, ‖auv s‖ ≤ Ωu * Ωv := by
    intro s
    simpa [auv] using (fourierMixedVector_norm_le_twoRadii (k := 1)
      frequency u v (y + s • v) Ωu Ωv hΩu hΩv hu hv)
  have hauuv : ∀ s, ‖auuv s‖ ≤ Ωu ^ 2 * Ωv := by
    intro s
    exact fourierMixedVector_norm_le_twoRadii (k := 2)
      frequency u v (y + s • v) Ωu Ωv hΩu hΩv hu hv
  have hbound :=
    projected_curvature_radial_deriv_abs_le T a hT au auu av auv auuv H
      Ωu Ωv hΩu hΩv hH hderivA hderivUU hderivU
      ha hau hauu hav hauv hauuv
  intro s
  constructor
  · rw [show (fun τ : ℝ => iteratedDeriv 2 (fun t : ℝ =>
          ‖S.starProjection (toLp 2
            (normalizedSteering frequency ((y + τ • v) + t • u)))‖ ^ 2) 0) = H from rfl,
        hH]
    exact (projected_mixed_third_hasDerivAt T a au auu av auv auuv
      (hderivA s) (hderivUU s) (hderivU s)).differentiableAt
  · exact hbound s

end

end
end NumDetect
end LeanNumDetect
