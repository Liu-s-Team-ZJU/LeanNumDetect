import NumDetect.Basic

/-! Uniform stability of finite Fourier sums under dilation of their nodes. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped Topology

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- The Fourier sum obtained by multiplying each node of `μ` by `t`. -/
def dilatedFourier {d n : ℕ} (μ : AtomicMeasure d n) (t : ℝ)
    (ω : Point d) : ℂ :=
  ∑ j, μ.amplitude j *
    Complex.exp (Complex.I * (dot (fun k => t * μ.node j k) ω : ℂ))

theorem dilatedFourier_one {d n : ℕ} (μ : AtomicMeasure d n)
    (ω : Point d) : dilatedFourier μ 1 ω = fourier μ ω := by
  simp [dilatedFourier, fourier]

private theorem continuous_dilatedFourier_sub_fourier_norm
    {d n k : ℕ} (μ : AtomicMeasure d n) (ν : AtomicMeasure d k) :
    Continuous (fun z : ℝ × Point d =>
      ‖dilatedFourier μ z.1 z.2 - fourier ν z.2‖) := by
  unfold dilatedFourier fourier dot
  fun_prop

/-- A strict Fourier discrepancy bound on a compact frequency band persists
uniformly when the nodes of the first measure are dilated near one. -/
theorem dilatedFourier_eventually_lt_two_sigma
    {d n k : ℕ} {Ω σ : ℝ}
    (μ : AtomicMeasure d n) (ν : AtomicMeasure d k)
    (_hΩ : 0 < Ω) (_hσ : 0 < σ)
    (hbound : ∀ ω, InFrequencyBand Ω ω →
      ‖fourier μ ω - fourier ν ω‖ < 2 * σ) :
    ∀ᶠ t in 𝓝 (1 : ℝ), ∀ ω, InFrequencyBand Ω ω →
      ‖dilatedFourier μ t ω - fourier ν ω‖ < 2 * σ := by
  let K : Set (Point d) := {ω | InFrequencyBand Ω ω}
  have hK : IsCompact K := by
    have hK' : IsCompact {ω : Point d | ∀ j, ω j ∈ Set.Icc (-Ω) Ω} :=
      isCompact_pi_infinite (fun _ => isCompact_Icc)
    convert hK' using 1
    ext ω
    simp only [K, Set.mem_setOf_eq, InFrequencyBand, Set.mem_Icc]
    constructor
    · intro h j
      exact (abs_le.mp (h j))
    · intro h j
      exact abs_le.mpr (h j)
  have hc := continuous_dilatedFourier_sub_fourier_norm μ ν
  have hpoint : ∀ ω ∈ K, ∀ᶠ z : ℝ × Point d in 𝓝 ((1 : ℝ), ω),
      ‖dilatedFourier μ z.1 z.2 - fourier ν z.2‖ < 2 * σ := by
    intro ω hω
    have hval :
        ‖dilatedFourier μ 1 ω - fourier ν ω‖ < 2 * σ := by
      rw [dilatedFourier_one]
      exact hbound ω hω
    exact hc.continuousAt.eventually_lt continuousAt_const hval
  simpa only [K, Set.mem_setOf_eq] using
    hK.eventually_forall_of_forall_eventually hpoint

end

end NumDetect
end LeanNumDetect
