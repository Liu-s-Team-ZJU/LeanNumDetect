import RandSamp.FixedSupport
import RandSamp.SeparatedGramBounds

/-! The fixed well-separated node-set theorem, with the manuscript's explicit
sampling rate and singular-value endpoints. -/

set_option autoImplicit false

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- The lower endpoint in the fixed separated theorem is strictly positive. -/
theorem fixedSeparated_lower_bound_pos {M : ℕ} (hM : 0 < M) {Δ δ : ℝ}
    (hΔ : 2 * Real.pi / M < Δ) (hδ : δ < 1) :
    0 < Real.sqrt ((1 - δ) * ((M : ℝ) - 2 * Real.pi / Δ) / (M + 1)) := by
  apply Real.sqrt_pos.mpr
  rw [mul_div_assoc]
  exact mul_pos (sub_pos.mpr hδ) (separatedLower_pos hM hΔ)

/-- Manuscript `thm:fixed-separated-singular-values`. The tuple `Y` is fixed
before drawing the uniformly random subset. All constants and the logarithmic
sampling rate are exactly those in the manuscript. -/
theorem fixedSeparated_singularValues {M s m : ℕ}
    (hM : 3 ≤ M) (hs : 2 ≤ s) (_hsM : s < M)
    (hm : 1 ≤ m) (hmM : m ≤ M + 1)
    {Δ δ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hΔlow : 2 * Real.pi / M < Δ) (hΔhigh : Δ ≤ 2 * Real.pi / s)
    (Y : Fin s → ℝ) (hsep : AngularSeparated Δ Y)
    (hsample : 3 * (s : ℝ) * (M + 1) /
      (δ ^ 2 * ((M : ℝ) - 2 * Real.pi / Δ)) * Real.log (2 * s / η) ≤ m) :
    1 - η ≤ probability (fun Ω : Sample (M + 1) m =>
      Real.sqrt ((1 - δ) * ((M : ℝ) - 2 * Real.pi / Δ) / (M + 1)) ≤
        matrixSingularValue (sampledVandermonde m Y Ω.val) (s - 1) ∧
      matrixSingularValue (sampledVandermonde m Y Ω.val) (s - 1) ≤
        matrixSingularValue (sampledVandermonde m Y Ω.val) 0 ∧
      matrixSingularValue (sampledVandermonde m Y Ω.val) 0 ≤
        Real.sqrt ((1 + δ) * ((M : ℝ) + 2 * Real.pi / Δ) / (M + 1))) := by
  have hMpos : 0 < M := by omega
  have ha := separatedLower_pos hMpos hΔlow
  have hΔpos : 0 < Δ :=
    (by positivity : 0 < 2 * Real.pi / (M : ℝ)).trans hΔlow
  have hab := separatedLower_le_upper M hΔpos
  have hrate : 3 * (s : ℝ) / (separatedLower M Δ * δ ^ 2) *
      Real.log (2 * s / η) ≤ m := by
    convert hsample using 1
    unfold separatedLower
    congr 1
    field_simp
  have h := fixedSupport_singularValues (by omega : 1 ≤ M) (by omega : 0 < s)
    hm hmM Y ha hab hδ0 hδ1 hη0 hη1
    (separated_full_gram_bounds hMpos (by omega) hΔlow hΔhigh Y hsep) hrate
  simpa only [SingularValueEvent, separatedLower, separatedUpper, mul_div_assoc] using h

end

end LeanNumDetect.RandSamp
