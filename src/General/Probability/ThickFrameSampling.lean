import General.MatrixAnalysis.CappedWeightSequence
import General.Probability.CappedWeightSpectralCoercivity

/-! Quantitative subspace thickness yields an unconditional lower sampling
estimate for finite isotropic frames. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.FiniteMatrixSampling

open CappedWeightIteration
open FrameMatrixBounds (framePopulation framePopulation_posSemidef
  quadratic_framePopulation trace_mul_weightedMean)
noncomputable section
attribute [local instance] Classical.propDecidable

def thickFrameDetFloor (n : ℕ) (θ : ℝ) : ℝ :=
  Real.exp (-(5*(n : ℝ)+6*(n : ℝ)*Real.log (((12/5 : ℝ)*n)/θ^2)))

theorem thickFrameDetFloor_pos (n : ℕ) (θ : ℝ) : 0 < thickFrameDetFloor n θ :=
  Real.exp_pos _

theorem exists_thick_frame_weights {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    (f : Fin N → EuclideanSpace ℂ (Fin n)) (hfull : mean (framePopulation f) = 1)
    {θ : ℝ} (hθ : 0 < θ)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      (n+1)*(n-Module.finrank ℂ U)*N ≤ 2*n^2*(Finset.univ.filter (fun k =>
        ∀ u : U, θ < ‖f k-(u : EuclideanSpace ℂ (Fin n))‖)).card) :
    ∃ w : Fin N → ℝ, (∀ k, 0 < w k ∧ w k ≤ 1) ∧
      (mean (weightedPopulation (framePopulation f) w)).PosDef ∧
      (∀ x : EuclideanSpace ℂ (Fin n), thickFrameDetFloor n θ*‖x‖^2 ≤
        quadratic (mean (weightedPopulation (framePopulation f) w)) x) ∧
      (∀ k (x : EuclideanSpace ℂ (Fin n)),
        quadratic (weightedPopulation (framePopulation f) w k) x ≤
          (5/2 : ℝ)*n*quadratic (mean (weightedPopulation (framePopulation f) w)) x) := by
  apply exists_capped_weights_of_determinant_floor hN hn f hfull (thickFrameDetFloor_pos n θ)
  intro k
  apply framePotential_realDet_lower_slack_of_card hn (by simpa using hN) f
    (cappedGramSequence f ((12/5 : ℝ)*n) k) (cappedGramSequence_posDef hN f (by positivity) hfull k)
    hθ (by simpa using hthick)
  simpa only [framePotential, realDet, Fintype.card_fin] using
    cappedGramSequence_entropy_bound hN f (by positivity : (0 : ℝ) < (12/5 : ℝ)*n) hfull k

/-- Uniform sampling is unchanged; the auxiliary weights enter only the proof. -/
theorem sampleMean_thick_frame_lower_bound_probability {N n m : ℕ}
    (hN : 0 < N) (hn : 0 < n) (hm : 1 ≤ m) (hmN : m ≤ N)
    (f : Fin N → EuclideanSpace ℂ (Fin n)) (hfull : mean (framePopulation f) = 1)
    {θ ρ ε : ℝ} (hθ : 0 < θ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      (n+1)*(n-Module.finrank ℂ U)*N ≤ 2*n^2*(Finset.univ.filter (fun k =>
        ∀ u : U, θ < ‖f k-(u : EuclideanSpace ℂ (Fin n))‖)).card)
    (hsample : 3*(n : ℝ)/ρ^2*Real.log ((n : ℝ)/ε) ≤ (m : ℝ)) :
    1-ε ≤ probability (fun Ω : Sample N m => ∀ x : EuclideanSpace ℂ (Fin n),
      ((1-ρ)/2)*thickFrameDetFloor n θ*‖x‖^2 ≤ quadratic (sampleMean (framePopulation f) Ω) x) := by
  obtain ⟨w, hw, hG, hlower, hbound⟩ := exists_thick_frame_weights hN hn f hfull hθ hthick
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp := sampleMean_weighted_half_lower_bound_probability hN hn hm hmN (framePopulation f) w
    hn' hρ0 hρ1 hε (framePopulation_posSemidef f) (fun k => (hw k).1.le)
    (fun k => (hw k).2) hG (by simpa only [hfull, quadratic_identity] using hlower) hbound hsample
  simpa only [hfull, quadratic_identity] using hp

end
end LeanNumDetect.FiniteMatrixSampling
