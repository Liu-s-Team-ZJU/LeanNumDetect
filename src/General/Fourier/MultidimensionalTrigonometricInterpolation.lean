import SegmentedVDM.Interpolation
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Finite presentations of trigonometric polynomials supported in an integer
cube, with exact cardinal interpolation and coefficient norm estimates obtained
by averaging integer translates. Frequencies in a presentation may repeat. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators InnerProductSpace
open Matrix WithLp

namespace LeanNumDetect.MultidimensionalTrigonometricInterpolation
noncomputable section

abbrev Frequency (d M : ℕ) := Fin d → Fin (M + 1)

def exponential {d : ℕ} (k : Fin d → ℕ) (x : Fin d → ℝ) : ℂ :=
  Complex.exp (Complex.I * ((∑ r, (k r : ℝ) * x r : ℝ) : ℂ))

@[simp] theorem norm_exponential {d : ℕ} (k : Fin d → ℕ) (x : Fin d → ℝ) :
    ‖exponential k x‖ = 1 := by
  simpa only [exponential, mul_comm] using
    Complex.norm_exp_ofReal_mul_I (∑ r, (k r : ℝ) * x r)

structure CubePacket (d M : ℕ) where
  Index : Type
  finite : Fintype Index
  frequency : Index → Fin d → ℕ
  frequency_le : ∀ i r, frequency i r ≤ M
  coeff : Index → ℂ

attribute [instance] CubePacket.finite

namespace CubePacket

variable {d M : ℕ}

noncomputable def value (P : CubePacket d M) (x : Fin d → ℝ) : ℂ :=
  ∑ i, P.coeff i * exponential (P.frequency i) x

noncomputable def mass (P : CubePacket d M) : ℝ := ∑ i, ‖P.coeff i‖

theorem mass_nonneg (P : CubePacket d M) : 0 ≤ P.mass :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

noncomputable def one (d M : ℕ) : CubePacket d M where
  Index := Unit
  finite := inferInstance
  frequency _ _ := 0
  frequency_le _ _ := Nat.zero_le _
  coeff _ := 1

@[simp] theorem value_one (x : Fin d → ℝ) : (one d M).value x = 1 := by
  simp [value, one, exponential]

@[simp] theorem mass_one : (one d M).mass = 1 := by simp [mass, one]

noncomputable def prod {n : ℕ} (P : Fin n → CubePacket d M) : CubePacket d (n * M) where
  Index := ∀ j, (P j).Index
  finite := inferInstance
  frequency i r := ∑ j, (P j).frequency (i j) r
  frequency_le i r := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => (P j).frequency_le (i j) r)
  coeff i := ∏ j, (P j).coeff (i j)

theorem mass_prod {n : ℕ} (P : Fin n → CubePacket d M) :
    (prod P).mass = ∏ j, (P j).mass := by
  simp only [mass, prod, norm_prod]
  exact (Fintype.prod_sum (fun j i => ‖(P j).coeff i‖)).symm

theorem value_prod {n : ℕ} (P : Fin n → CubePacket d M) (x : Fin d → ℝ) :
    (prod P).value x = ∏ j, (P j).value x := by
  simp only [value, prod]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : exponential (fun r => ∑ j, (P j).frequency (i j) r) x =
      ∏ j, exponential ((P j).frequency (i j)) x := by
    unfold exponential
    push_cast
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum, Complex.exp_sum]
  rw [he, ← Finset.prod_mul_distrib]

/-- One coordinate factor vanishes at one source and equals one at its center. -/
noncomputable def coordinateFactor (Q : ℕ) (r : Fin d) (q : ℕ) (hq : q ≤ Q)
    (center other : ℝ) : CubePacket d Q where
  Index := Bool
  finite := inferInstance
  frequency b t := if b = true ∧ t = r then q else 0
  frequency_le b t := by split_ifs <;> omega
  coeff b := if b then
    (Complex.exp (Complex.I * ((q : ℝ) * center : ℝ)) -
      Complex.exp (Complex.I * ((q : ℝ) * other : ℝ)))⁻¹ else
    -Complex.exp (Complex.I * ((q : ℝ) * other : ℝ)) /
      (Complex.exp (Complex.I * ((q : ℝ) * center : ℝ)) -
        Complex.exp (Complex.I * ((q : ℝ) * other : ℝ)))

theorem coordinateFactor_value (Q : ℕ) (r : Fin d) (q : ℕ) (hq : q ≤ Q)
    (center other : ℝ) (x : Fin d → ℝ) :
    (coordinateFactor Q r q hq center other).value x =
      (Complex.exp (Complex.I * ((q : ℝ) * x r : ℝ)) -
        Complex.exp (Complex.I * ((q : ℝ) * other : ℝ))) /
      (Complex.exp (Complex.I * ((q : ℝ) * center : ℝ)) -
        Complex.exp (Complex.I * ((q : ℝ) * other : ℝ))) := by
  simp [value, coordinateFactor, exponential, ite_mul, apply_ite,
    div_eq_mul_inv]
  ring

theorem coordinateFactor_mass (Q : ℕ) (r : Fin d) (q : ℕ) (hq : q ≤ Q)
    (center other : ℝ) :
    (coordinateFactor Q r q hq center other).mass =
      2 / ‖Complex.exp (Complex.I * ((q : ℝ) * center : ℝ)) -
        Complex.exp (Complex.I * ((q : ℝ) * other : ℝ))‖ := by
  have he : ‖Complex.exp (Complex.I * ((q : ℝ) * other : ℝ))‖ = 1 := by
    simpa only [mul_comm] using Complex.norm_exp_ofReal_mul_I ((q : ℝ) * other)
  simp only [mass, coordinateFactor, Fintype.sum_bool, Bool.false_eq_true,
    reduceIte, norm_inv, norm_div, norm_neg, he]
  ring

end CubePacket

/-- Integer translations of an averaging cube inject into the larger cube. -/
def shiftFrequency {d M L : ℕ} (ν : Fin d → ℕ) (hν : ∀ r, ν r + L ≤ M + 1)
    (a : Fin d → Fin L) : Frequency d M := fun r =>
  ⟨ν r + (a r).val, by have h := (a r).isLt; have hb := hν r; omega⟩

theorem shiftFrequency_injective {d M L : ℕ} (ν : Fin d → ℕ)
    (hν : ∀ r, ν r + L ≤ M + 1) : Function.Injective (shiftFrequency ν hν) := by
  intro a b hab
  funext r
  apply Fin.ext
  have h := congrArg (fun k => (k r).val) hab
  exact Nat.add_left_cancel h

/-- Uniform averaging over a translated integer cube. -/
noncomputable def averagingVector {d M L : ℕ} (ν : Fin d → ℕ)
    (hν : ∀ r, ν r + L ≤ M + 1) (center : Fin d → ℝ) :
    EuclideanSpace ℂ (Frequency d M) :=
  (((L ^ d : ℕ) : ℂ)⁻¹) • ∑ a : Fin d → Fin L,
    exponential (fun r => (a r).val) (fun r => -center r) •
      EuclideanSpace.basisFun (Frequency d M) ℂ (shiftFrequency ν hν a)

theorem averagingVector_norm_sq {d M L : ℕ} (hL : 0 < L)
    (ν : Fin d → ℕ) (hν : ∀ r, ν r + L ≤ M + 1) (center : Fin d → ℝ) :
    ‖averagingVector ν hν center‖ ^ 2 = ((L ^ d : ℕ) : ℝ)⁻¹ := by
  let ψ := fun a : Fin d → Fin L => exponential (fun r => (a r).val) (fun r => -center r)
  let b := EuclideanSpace.basisFun (Frequency d M) ℂ
  let w := ∑ a : Fin d → Fin L, ψ a • b (shiftFrequency ν hν a)
  have hv : Orthonormal ℂ (b ∘ shiftFrequency ν hν) :=
    b.orthonormal.comp _ (shiftFrequency_injective ν hν)
  have hi : ⟪w, w⟫_ℂ = ((L ^ d : ℕ) : ℂ) := by
    have h := hv.inner_sum ψ ψ Finset.univ
    have he (a : Fin d → Fin L) : star (ψ a) * ψ a = 1 := by
      rw [RCLike.star_def, Complex.conj_mul']
      simp [ψ]
    simpa only [Function.comp_apply, ← Complex.star_def, he, Finset.sum_const,
      Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, mul_one, w] using h
  have hn : ‖w‖ ^ 2 = ((L ^ d : ℕ) : ℝ) := by
    have h : Complex.re ⟪w, w⟫_ℂ = ((L ^ d : ℕ) : ℝ) := by
      rw [hi]
      norm_cast
    change RCLike.re ⟪w, w⟫_ℂ = _ at h
    rw [inner_self_eq_norm_sq] at h
    exact h
  have hC : 0 < ((L ^ d : ℕ) : ℝ) := by positivity
  change ‖(((L ^ d : ℕ) : ℂ)⁻¹) • w‖ ^ 2 = _
  rw [norm_smul, mul_pow, hn, norm_inv, Complex.norm_natCast,
    inv_pow]
  field_simp

/-- Averaging evaluations preserve a cardinal value at the averaging center. -/
theorem averagingVector_evaluation {d M L : ℕ} (ν : Fin d → ℕ)
    (hν : ∀ r, ν r + L ≤ M + 1) (center x : Fin d → ℝ) :
    (ofLp (averagingVector ν hν center)) ⬝ᵥ
      (fun k => exponential (fun r => (k r).val) x) =
    (((L ^ d : ℕ) : ℂ)⁻¹) * exponential ν x *
      ∑ a : Fin d → Fin L, exponential (fun r => (a r).val) (fun r => x r - center r) := by
  classical
  simp only [averagingVector, ofLp_smul, ofLp_sum, dotProduct, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.single, PiLp.ofLp_single]
  simp only [Pi.single_apply, mul_ite, ite_mul, mul_one, zero_mul,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_assoc]
  apply congrArg (fun z => (((L ^ d : ℕ) : ℂ)⁻¹) * z)
  unfold exponential
  rw [← Complex.exp_add, ← Complex.exp_add]
  apply congrArg Complex.exp
  dsimp [shiftFrequency]
  push_cast
  simp only [add_mul, mul_sub, mul_neg, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

namespace CubePacket

noncomputable def scale {d Q : ℕ} (P : CubePacket d Q) (c : ℂ) : CubePacket d Q :=
  { P with coeff := fun i => c * P.coeff i }

@[simp] theorem value_scale {d Q : ℕ} (P : CubePacket d Q) (c : ℂ) (x : Fin d → ℝ) :
    (P.scale c).value x = c * P.value x := by
  simp only [value, scale, mul_assoc, Finset.mul_sum]

@[simp] theorem mass_scale {d Q : ℕ} (P : CubePacket d Q) (c : ℂ) :
    (P.scale c).mass = ‖c‖ * P.mass := by
  simp only [mass, scale, norm_mul, Finset.mul_sum]

/-- Collecting frequencies after cube averaging, including repeated packet
frequencies, loses no control of the coefficient norm. -/
noncomputable def averagedVector {d M Q L : ℕ} (P : CubePacket d Q)
    (hband : Q + L ≤ M + 1) (center : Fin d → ℝ) :
    EuclideanSpace ℂ (Frequency d M) :=
  ∑ i, P.coeff i • averagingVector (P.frequency i)
    (fun r => (Nat.add_le_add_right (P.frequency_le i r) L).trans hband) center

theorem averagedVector_norm_le {d M Q L : ℕ} (hL : 0 < L) (P : CubePacket d Q)
    (hband : Q + L ≤ M + 1) (center : Fin d → ℝ) :
    ‖P.averagedVector hband center‖ ≤ P.mass * Real.sqrt (((L ^ d : ℕ) : ℝ)⁻¹) := by
  have hav (i : P.Index) : ‖averagingVector (P.frequency i)
      (fun r => (Nat.add_le_add_right (P.frequency_le i r) L).trans hband) center‖ =
      Real.sqrt (((L ^ d : ℕ) : ℝ)⁻¹) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [averagingVector_norm_sq hL, Real.sq_sqrt (by positivity)]
  unfold averagedVector
  calc
    _ ≤ ∑ i, ‖P.coeff i • averagingVector (P.frequency i)
        (fun r => (Nat.add_le_add_right (P.frequency_le i r) L).trans hband) center‖ := norm_sum_le _ _
    _ = ∑ i, ‖P.coeff i‖ * Real.sqrt (((L ^ d : ℕ) : ℝ)⁻¹) := by
      simp only [norm_smul, hav]
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem averagedVector_evaluation {d M Q L : ℕ} (P : CubePacket d Q)
    (hband : Q + L ≤ M + 1) (center x : Fin d → ℝ) :
    (ofLp (P.averagedVector hband center)) ⬝ᵥ
      (fun k => exponential (fun r => (k r).val) x) =
      P.value x * ((((L ^ d : ℕ) : ℂ)⁻¹) *
        ∑ a : Fin d → Fin L, exponential (fun r => (a r).val) (fun r => x r - center r)) := by
  simp only [averagedVector, ofLp_sum, ofLp_smul, dotProduct, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  have he (i : P.Index) :
      ∑ k : Frequency d M, P.coeff i *
        ofLp (averagingVector (P.frequency i)
          (fun r => (Nat.add_le_add_right (P.frequency_le i r) L).trans hband) center) k *
          exponential (fun r => (k r).val) x =
      P.coeff i * (exponential (P.frequency i) x *
        ((((L ^ d : ℕ) : ℂ)⁻¹) *
          ∑ a : Fin d → Fin L, exponential (fun r => (a r).val) (fun r => x r - center r))) := by
    rw [show (∑ k : Frequency d M, P.coeff i *
        ofLp (averagingVector (P.frequency i)
          (fun r => (Nat.add_le_add_right (P.frequency_le i r) L).trans hband) center) k *
          exponential (fun r => (k r).val) x) =
      P.coeff i * ((ofLp (averagingVector (P.frequency i)
        (fun r => (Nat.add_le_add_right (P.frequency_le i r) L).trans hband) center)) ⬝ᵥ
          (fun k => exponential (fun r => (k r).val) x)) by
      simp only [dotProduct, Finset.mul_sum, mul_assoc]]
    rw [MultidimensionalTrigonometricInterpolation.averagingVector_evaluation]
    ring
  simp_rw [he]
  simp only [← mul_assoc, ← Finset.sum_mul, value]

/-- A cardinal value at the averaging center survives exactly. -/
theorem averagedVector_evaluation_center {d M Q L : ℕ} (hL : 0 < L)
    (P : CubePacket d Q) (hband : Q + L ≤ M + 1) (center : Fin d → ℝ) :
    (ofLp (P.averagedVector hband center)) ⬝ᵥ
      (fun k => exponential (fun r => (k r).val) center) = P.value center := by
  rw [averagedVector_evaluation]
  simp only [sub_self, exponential, mul_zero, Finset.sum_const_zero, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Nat.pow_pos hL : 0 < L ^ d).ne'), mul_one]

/-- Scaling a cardinal factor by at most its denominator keeps coefficient
mass at most two. -/
theorem scaled_coordinateFactor_mass_le {d : ℕ} (Q : ℕ) (r : Fin d)
    (q : ℕ) (hq : q ≤ Q) (center other : ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hden : 0 < ‖Complex.exp (Complex.I * ((q : ℝ) * center : ℝ)) -
      Complex.exp (Complex.I * ((q : ℝ) * other : ℝ))‖)
    (hscale : a ≤ ‖Complex.exp (Complex.I * ((q : ℝ) * center : ℝ)) -
      Complex.exp (Complex.I * ((q : ℝ) * other : ℝ))‖) :
    ((coordinateFactor Q r q hq center other).scale (a : ℂ)).mass ≤ 2 := by
  rw [mass_scale, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha,
    coordinateFactor_mass, ← mul_div_assoc]
  apply (div_le_iff₀ hden).mpr
  nlinarith

/-- Product factors separate every pair by one coordinate. Different pairs
may use different coordinates and integer frequencies. -/
noncomputable def globalPacket {d n : ℕ} (Q : ℕ) (Y : Fin n → Fin d → ℝ)
    (i : Fin n) (r : Fin n → Fin d) (q : Fin n → ℕ) (hq : ∀ j, q j ≤ Q)
    (scale : Fin n → ℝ) : CubePacket d (n * Q) :=
  prod (fun j => if j = i then one d Q else
    (coordinateFactor Q (r j) (q j) (hq j) (Y i (r j)) (Y j (r j))).scale (scale j : ℂ))

theorem globalPacket_value_center {d n : ℕ} (Q : ℕ) (Y : Fin n → Fin d → ℝ)
    (i : Fin n) (r : Fin n → Fin d) (q : Fin n → ℕ) (hq : ∀ j, q j ≤ Q)
    (scale : Fin n → ℝ)
    (hden : ∀ j, j ≠ i → Complex.exp (Complex.I * ((q j : ℝ) * Y i (r j) : ℝ)) -
      Complex.exp (Complex.I * ((q j : ℝ) * Y j (r j) : ℝ)) ≠ 0) :
    (globalPacket Q Y i r q hq scale).value (Y i) =
      ∏ j, if j = i then (1 : ℂ) else (scale j : ℂ) := by
  rw [globalPacket, value_prod]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hji : j = i
  · simp only [hji, ite_true, value_one]
  · simp only [if_neg hji, value_scale, coordinateFactor_value,
      div_self (hden j hji), mul_one]

theorem globalPacket_value_other {d n : ℕ} (Q : ℕ) (Y : Fin n → Fin d → ℝ)
    (i l : Fin n) (hli : l ≠ i) (r : Fin n → Fin d) (q : Fin n → ℕ)
    (hq : ∀ j, q j ≤ Q) (scale : Fin n → ℝ) :
    (globalPacket Q Y i r q hq scale).value (Y l) = 0 := by
  rw [globalPacket, value_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ l)
  simp only [if_neg hli, value_scale, coordinateFactor_value, sub_self,
    zero_div, mul_zero]

theorem globalPacket_mass_le {d n : ℕ} (Q : ℕ) (Y : Fin n → Fin d → ℝ)
    (i : Fin n) (r : Fin n → Fin d) (q : Fin n → ℕ) (hq : ∀ j, q j ≤ Q)
    (scale : Fin n → ℝ) (hscale0 : ∀ j, 0 ≤ scale j)
    (hden : ∀ j, j ≠ i → 0 < ‖Complex.exp (Complex.I * ((q j : ℝ) * Y i (r j) : ℝ)) -
      Complex.exp (Complex.I * ((q j : ℝ) * Y j (r j) : ℝ))‖)
    (hscale : ∀ j, j ≠ i → scale j ≤
      ‖Complex.exp (Complex.I * ((q j : ℝ) * Y i (r j) : ℝ)) -
        Complex.exp (Complex.I * ((q j : ℝ) * Y j (r j) : ℝ))‖) :
    (globalPacket Q Y i r q hq scale).mass ≤ (2 : ℝ) ^ n := by
  rw [globalPacket, mass_prod]
  calc
    _ ≤ ∏ _j : Fin n, (2 : ℝ) := Finset.prod_le_prod
      (fun _ _ => mass_nonneg _) (fun j _ => by
        by_cases hji : j = i
        · simp only [hji, ite_true, mass_one]; norm_num
        · simp only [if_neg hji]
          exact scaled_coordinateFactor_mass_le Q (r j) (q j) (hq j)
            (Y i (r j)) (Y j (r j)) (hscale0 j) (hden j hji) (hscale j hji))
    _ = _ := by simp

end CubePacket

/-- Diagonal interpolation with a uniform coefficient bound gives a lower
frame bound. Positivity of the smallest diagonal entry is explicit. -/
theorem diagonal_interpolation_energy_lower {ρ : Type*} [Fintype ρ] {n : ℕ}
    (V : Matrix ρ (Fin n) ℂ) (C : Matrix (Fin n) ρ ℂ) (w : Fin n → ℝ)
    (hCV : C * V = Matrix.diagonal (fun i => (w i : ℂ)))
    {b B : ℝ} (hb : 0 ≤ b) (hw : ∀ i, b ≤ w i)
    (hC : ∀ i, SegmentedVDM.energy (C i) ≤ B ^ 2) (z : Fin n → ℂ) :
    b ^ 2 * SegmentedVDM.energy z ≤
      (n : ℝ) * B ^ 2 * SegmentedVDM.energy (V *ᵥ z) := by
  classical
  have haction : C *ᵥ (V *ᵥ z) = fun i => (w i : ℂ) * z i := by
    rw [Matrix.mulVec_mulVec, hCV]
    ext i
    exact Matrix.mulVec_diagonal _ _ i
  have hdiag : b ^ 2 * SegmentedVDM.energy z ≤
      SegmentedVDM.energy (C *ᵥ (V *ᵥ z)) := by
    rw [haction]
    unfold SegmentedVDM.energy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hb.trans (hw i))]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ hb (hb.trans (hw i))).mpr (hw i)) (sq_nonneg _)
  calc
    _ ≤ SegmentedVDM.energy (C *ᵥ (V *ᵥ z)) := hdiag
    _ ≤ ∑ i, SegmentedVDM.energy (C i) * SegmentedVDM.energy (V *ᵥ z) :=
      Finset.sum_le_sum fun i _ => SegmentedVDM.dotProduct_norm_sq_le _ _
    _ ≤ ∑ _i : Fin n, B ^ 2 * SegmentedVDM.energy (V *ᵥ z) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hC i)
        (SegmentedVDM.energy_nonneg _)
    _ = _ := by simp; ring

end
end LeanNumDetect.MultidimensionalTrigonometricInterpolation
