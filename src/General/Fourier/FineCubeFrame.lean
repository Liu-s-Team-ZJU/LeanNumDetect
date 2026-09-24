import General.Finite.FiniteRealGeometry
import General.Fourier.SeparatedCubeFourier
import General.Fourier.TranslatedCubeFourier

/-!
Algebraic conversions from a centered integer-frequency cube to a one-sided
angular-frequency cube. The conversion is exact when the largest one-sided
frequency is even. In that case the real radius `(K + 1) / 2` has integer
points `{-K/2, ..., K/2}`, which translate to `{0, ..., K}`.

This file also provides the shared normalization `normalizedAngularPoint`
from angular representatives in `(-π, π]` to the unit-torus representatives
of `External`, together with the exact identity converting the external
translated-cube Fourier energy to `fineCubeFourierEnergy`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators

namespace LeanNumDetect
namespace FineCubeFrame

noncomputable section

abbrev FineCubeFrequency (d K : ℕ) := Fin d → Fin (K + 1)

noncomputable def fineCubeFourierEnergy
    {d : ℕ} {ι : Type*} [Fintype ι]
    (K : ℕ) (x : ι → NumDetect.Point d) (c : ι → ℂ) : ℝ :=
  ∑ α : FineCubeFrequency d K,
    ‖∑ j, c j * Complex.exp
      (Complex.I * (∑ k, ((α k : ℕ) : ℂ) * x j k))‖ ^ 2

private theorem floor_odd_half (q : ℕ) :
    ⌊(((2 * q + 1 : ℕ) : ℝ) / 2)⌋ = (q : ℤ) := by
  rw [Int.floor_eq_iff]
  constructor <;> push_cast <;> linarith

private def centeredIntegerEquivFin (q : ℕ) :
    External.CenteredInteger (((2 * q + 1 : ℕ) : ℝ) / 2) ≃ Fin (2 * q + 1) where
  toFun w :=
    ⟨(w.val + q).toNat, by
      have hw := Finset.mem_Icc.mp w.property
      have hw' : -(q : ℤ) ≤ w.val ∧ w.val ≤ q := by
        simpa only [floor_odd_half q] using hw
      have hnonneg : 0 ≤ w.val + q := by omega
      rw [Int.toNat_lt hnonneg]
      omega⟩
  invFun a :=
    ⟨(a.val : ℤ) - q, by
      rw [Finset.mem_Icc, floor_odd_half]
      constructor <;> omega⟩
  left_inv w := by
    apply Subtype.ext
    have hw := Finset.mem_Icc.mp w.property
    have hw' : -(q : ℤ) ≤ w.val ∧ w.val ≤ q := by
      simpa only [floor_odd_half q] using hw
    have hnonneg : 0 ≤ w.val + q := by omega
    change (((w.val + q).toNat : ℕ) : ℤ) - q = w.val
    rw [Int.toNat_of_nonneg hnonneg]
    omega
  right_inv a := by
    apply Fin.ext
    change ((a.val : ℤ) - q + q).toNat = a.val
    have he : (a.val : ℤ) - q + q = a.val := by omega
    simp [he]

private def centeredCubeEquivFineCube (d q : ℕ) :
    External.CenteredCubeFrequency d (((2 * q + 1 : ℕ) : ℝ) / 2) ≃
      FineCubeFrequency d (2 * q) :=
  Equiv.piCongrRight fun _ => centeredIntegerEquivFin q

private theorem centeredCubeEquivFineCube_apply
    {d q : ℕ}
    (ω : External.CenteredCubeFrequency d (((2 * q + 1 : ℕ) : ℝ) / 2))
    (k : Fin d) :
    (((centeredCubeEquivFineCube d q ω) k : ℕ) : ℤ) =
      (ω k : ℤ) + q := by
  change (((((ω k).val + q).toNat : ℕ) : ℤ)) = _
  have hw := Finset.mem_Icc.mp (ω k).property
  have hw' : -(q : ℤ) ≤ (ω k).val ∧ (ω k).val ≤ q := by
    simpa only [floor_odd_half q] using hw
  have hnonneg : 0 ≤ (ω k).val + q := by omega
  rw [Int.toNat_of_nonneg hnonneg]

/-- Convert angular representatives in `(-π, π]` to Li's representatives in
`[-1/2, 1/2)`.  The minus sign matches Li's Fourier phase convention. -/
def normalizedAngularPoint {d : ℕ} (x : NumDetect.Point d) :
    External.UnitTorusPoint d :=
  fun k => -x k / (2 * Real.pi)

theorem normalizedAngularPoint_mem_halfOpenCube
    {d : ℕ} {x : NumDetect.Point d}
    (hx : NumDetect.InAngularCube x) :
    External.InUnitHalfOpenCube (normalizedAngularPoint x) := by
  intro k
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    nlinarith [Real.pi_pos, (hx k).2]
  · apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    nlinarith [Real.pi_pos, (hx k).1]

theorem normalizedAngularPoint_coordinateDistance
    {u v : ℝ}
    (hu : -Real.pi < u ∧ u ≤ Real.pi)
    (hv : -Real.pi < v ∧ v ≤ Real.pi) :
    External.unitPeriodicCoordinateDistance
        (-u / (2 * Real.pi)) (-v / (2 * Real.pi)) =
      NumDetect.periodicCoordinateDistance u v /
        (2 * Real.pi) := by
  unfold External.unitPeriodicCoordinateDistance
    NumDetect.periodicCoordinateDistance
  have hp : 0 < 2 * Real.pi := by positivity
  have habs : |u - v| ≤ 2 * Real.pi := by
    rw [abs_le]
    constructor <;> linarith
  rw [show -u / (2 * Real.pi) - -v / (2 * Real.pi) =
      -(u - v) / (2 * Real.pi) by ring,
    abs_div, abs_neg, abs_of_pos hp]
  rw [show 1 - |u - v| / (2 * Real.pi) =
      (2 * Real.pi - |u - v|) / (2 * Real.pi) by field_simp]
  rw [min_div_div_right hp.le]

theorem normalizedAngularPoint_lInfDistance
    {d : ℕ} {u v : NumDetect.Point d}
    (hu : NumDetect.InAngularCube u)
    (hv : NumDetect.InAngularCube v) :
    External.unitPeriodicLInfDistance
        (normalizedAngularPoint u) (normalizedAngularPoint v) =
      NumDetect.periodicLInfDistance u v /
        (2 * Real.pi) := by
  unfold External.unitPeriodicLInfDistance
    NumDetect.periodicLInfDistance normalizedAngularPoint
  simp_rw [normalizedAngularPoint_coordinateDistance (hu _) (hv _)]
  rw [show (fun k => NumDetect.periodicCoordinateDistance
      (u k) (v k) / (2 * Real.pi)) =
      (2 * Real.pi)⁻¹ •
        (fun k => NumDetect.periodicCoordinateDistance
          (u k) (v k)) by
      funext k
      simp [div_eq_inv_mul]]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity))]
  field_simp

/-- Li's translated-cube energy becomes the one-sided angular cube energy
after normalization of the nodes. -/
theorem translatedCubeFourierEnergy_normalizedAngularPoint
    {d K : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → NumDetect.Point d) (c : ι → ℂ) :
    External.translatedCubeFourierEnergy (K + 1)
        (fun j => normalizedAngularPoint (x j)) c =
      fineCubeFourierEnergy K x c := by
  classical
  unfold External.translatedCubeFourierEnergy
    fineCubeFourierEnergy
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply congrArg Complex.exp
  have hsum :
      (∑ k,
          (((ω k : Fin (K + 1)) : ℕ) : ℂ) *
            normalizedAngularPoint (x j) k) =
        -(∑ k, (((ω k : Fin (K + 1)) : ℕ) : ℂ) * x j k) /
          (2 * (Real.pi : ℂ)) := by
    calc
      _ = ∑ k,
          -((((ω k : Fin (K + 1)) : ℕ) : ℂ) * x j k) /
            (2 * (Real.pi : ℂ)) := by
          apply Finset.sum_congr rfl
          intro k _
          unfold normalizedAngularPoint
          push_cast
          field_simp [Real.pi_ne_zero]
      _ = _ := by rw [← Finset.sum_div, Finset.sum_neg_distrib]
  rw [hsum]
  field_simp [Real.pi_ne_zero]

private theorem centered_card
    (d q : ℕ) :
    Fintype.card
        (External.CenteredCubeFrequency d (((2 * q + 1 : ℕ) : ℝ) / 2)) =
      (2 * q + 1) ^ d := by
  exact Fintype.card_congr (centeredCubeEquivFineCube d q) |>.trans (by simp)

private theorem modulated_coefficient_energy
    {d : ℕ} {ι : Type*} [Fintype ι]
    (q : ℕ) (x : ι → NumDetect.Point d) (c : ι → ℂ) :
    External.coefficientEnergy
        (fun j => c j * Complex.exp
          (Complex.I * (q * ∑ k, x j k : ℝ))) =
      External.coefficientEnergy c := by
  unfold External.coefficientEnergy
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.norm_exp, Complex.mul_re]

private theorem discreteEnergy_modulated_eq_fineCubeEnergy
    {d q : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → NumDetect.Point d) (c : ι → ℂ) :
    External.discreteCubeFourierEnergy
        (((2 * q + 1 : ℕ) : ℝ) / 2)
        (fun j k => -x j k / (2 * Real.pi))
        (fun j => c j * Complex.exp
          (Complex.I * (q * ∑ k, x j k : ℝ))) =
      fineCubeFourierEnergy (2 * q) x c := by
  classical
  unfold External.discreteCubeFourierEnergy fineCubeFourierEnergy
  apply Fintype.sum_equiv (centeredCubeEquivFineCube d q)
  intro ω
  congr 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  have hfrequency :
      ∑ k, ((((centeredCubeEquivFineCube d q ω) k : ℕ) : ℂ) * x j k) =
        q * ∑ k, x j k + ∑ k, (((ω k : ℤ) : ℂ) * x j k) := by
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hk :
        ((((centeredCubeEquivFineCube d q ω) k : ℕ) : ℂ)) =
          (q : ℂ) + ((ω k : ℤ) : ℂ) := by
      have hk' := centeredCubeEquivFineCube_apply ω k
      exact_mod_cast hk'.trans (add_comm _ _)
    rw [hk]
    ring
  have hsourcePhase :
      -2 * Real.pi * Complex.I *
          (∑ k, ((ω k : ℤ) : ℂ) *
            ((-x j k / (2 * Real.pi) : ℝ) : ℂ)) =
        Complex.I * ∑ k, ((ω k : ℤ) : ℂ) * x j k := by
    have hsum :
        (∑ k, ((ω k : ℤ) : ℂ) *
            ((-x j k / (2 * Real.pi) : ℝ) : ℂ)) =
          -(∑ k, ((ω k : ℤ) : ℂ) * x j k) /
            (2 * (Real.pi : ℂ)) := by
      calc
        _ = ∑ k, -(((ω k : ℤ) : ℂ) * x j k) /
              (2 * (Real.pi : ℂ)) := by
            apply Finset.sum_congr rfl
            intro k _
            push_cast
            field_simp [Real.pi_ne_zero]
        _ = _ := by rw [← Finset.sum_div, Finset.sum_neg_distrib]
    rw [hsum]
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hsourcePhase, hfrequency]
  push_cast
  ring

end

end FineCubeFrame
end LeanNumDetect
