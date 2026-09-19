import External.SeparatedCubeFourier

/-!
Conversions from Li's centered integer-cube frame bound to a one-sided
angular-frequency cube.  The conversion is exact when the largest one-sided
frequency is even.  In that case the real source radius `(K + 1) / 2` has
integer points `{-K/2, ..., K/2}`, which translate to `{0, ..., K}`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators

namespace LeanNumDetect
namespace FineCubeFrame

noncomputable section

abbrev AngularPoint (d : ℕ) := Fin d → ℝ

def InAngularCube {d : ℕ} (x : AngularPoint d) : Prop :=
  ∀ k, -Real.pi < x k ∧ x k ≤ Real.pi

def angularPeriodicCoordinateDistance (u v : ℝ) : ℝ :=
  min |u - v| (2 * Real.pi - |u - v|)

def angularPeriodicLInfDistance {d : ℕ}
    (u v : AngularPoint d) : ℝ :=
  ‖fun k => angularPeriodicCoordinateDistance (u k) (v k)‖

abbrev FineCubeFrequency (d K : ℕ) := Fin d → Fin (K + 1)

noncomputable def fineCubeFourierEnergy
    {d : ℕ} {ι : Type*} [Fintype ι]
    (K : ℕ) (x : ι → AngularPoint d) (c : ι → ℂ) : ℝ :=
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

private theorem normalized_mem_halfOpenCube
    {d : ℕ} {x : AngularPoint d} (hx : InAngularCube x) :
    External.InUnitHalfOpenCube (fun k => -x k / (2 * Real.pi)) := by
  intro k
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    nlinarith [Real.pi_pos, (hx k).2]
  · apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    nlinarith [Real.pi_pos, (hx k).1]

private theorem normalized_coordinateDistance
    {u v : ℝ}
    (hu : -Real.pi < u ∧ u ≤ Real.pi)
    (hv : -Real.pi < v ∧ v ≤ Real.pi) :
    External.unitPeriodicCoordinateDistance
        (-u / (2 * Real.pi)) (-v / (2 * Real.pi)) =
      angularPeriodicCoordinateDistance u v / (2 * Real.pi) := by
  unfold External.unitPeriodicCoordinateDistance
    angularPeriodicCoordinateDistance
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

private theorem normalized_lInfDistance
    {d : ℕ} {u v : AngularPoint d}
    (hu : InAngularCube u) (hv : InAngularCube v) :
    External.unitPeriodicLInfDistance
        (fun k => -u k / (2 * Real.pi))
        (fun k => -v k / (2 * Real.pi)) =
      angularPeriodicLInfDistance u v / (2 * Real.pi) := by
  unfold External.unitPeriodicLInfDistance angularPeriodicLInfDistance
  simp_rw [normalized_coordinateDistance (hu _) (hv _)]
  rw [show (fun k => angularPeriodicCoordinateDistance (u k) (v k) /
      (2 * Real.pi)) =
      (2 * Real.pi)⁻¹ •
        (fun k => angularPeriodicCoordinateDistance (u k) (v k)) by
      funext k
      simp [div_eq_inv_mul]]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity))]
  field_simp

private theorem centered_card
    (d q : ℕ) :
    Fintype.card
        (External.CenteredCubeFrequency d (((2 * q + 1 : ℕ) : ℝ) / 2)) =
      (2 * q + 1) ^ d := by
  exact Fintype.card_congr (centeredCubeEquivFineCube d q) |>.trans (by simp)

private theorem modulated_coefficient_energy
    {d : ℕ} {ι : Type*} [Fintype ι]
    (q : ℕ) (x : ι → AngularPoint d) (c : ι → ℂ) :
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
    (x : ι → AngularPoint d) (c : ι → ℂ) :
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

/-- Li's registered centered-cube theorem gives the exact one-sided fine-cube
lower frame bound when `K` is positive and even. -/
theorem lowerFrame_of_separatedCubeFourier
    {d K : ℕ} {ι : Type*} [Fintype ι]
    (hd : 2 ≤ d) (hKpos : 0 < K) (hKeven : Even K)
    (β : ℝ) (hβ : 1 / (2 * Real.log 2) ≤ β)
    (x : ι → AngularPoint d) (hx : ∀ j, InAngularCube (x j))
    (hsep : ∀ i j, i ≠ j →
      4 * Real.pi * β * d / (K + 1) <
        angularPeriodicLInfDistance (x i) (x j)) :
    ∀ c,
      (2 - Real.exp (1 / (2 * β))) *
          (((K + 1) ^ d : ℕ) : ℝ) *
          External.coefficientEnergy c ≤
        fineCubeFourierEnergy K x c := by
  obtain ⟨q, rfl⟩ := hKeven
  have hq : 0 < q := by omega
  let m : ℝ := ((2 * q + 1 : ℕ) : ℝ) / 2
  let z : ι → External.UnitTorusPoint d :=
    fun j k => -x j k / (2 * Real.pi)
  have hm : 1 ≤ m := by
    dsimp [m]
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by exact_mod_cast (show 2 ≤ 2 * q + 1 by omega))
  have hz : ∀ j, External.InUnitHalfOpenCube (z j) :=
    fun j => normalized_mem_halfOpenCube (hx j)
  have hsep' : ∀ i j, i ≠ j →
      β * d / m ≤ External.unitPeriodicLInfDistance (z i) (z j) := by
    intro i j hij
    rw [normalized_lInfDistance (hx i) (hx j)]
    have hs := (hsep i j hij).le
    dsimp [m, z]
    have hp : 0 < 2 * Real.pi := by positivity
    apply (le_div_iff₀ hp).2
    convert hs using 1 <;> push_cast <;> field_simp <;> ring
  have hsource :=
    (External.separatedCubeFourier_frame m β z hd hm hβ hz hsep').2.2.1
  intro c
  have h := hsource
    (fun j => c j * Complex.exp
      (Complex.I * (q * ∑ k, x j k : ℝ)))
  rw [modulated_coefficient_energy, centered_card,
    discreteEnergy_modulated_eq_fineCubeEnergy] at h
  simpa [m, two_mul] using h

end

end FineCubeFrame
end LeanNumDetect
