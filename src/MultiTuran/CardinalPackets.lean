import MultiTuran.Interpolation
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Finite cardinal polynomial packets without continuous Fourier-analysis
imports. Repeated frequencies are collected in a genuine Euclidean vector. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators InnerProductSpace
open Matrix WithLp

namespace LeanNumDetect.MultiTuran
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

/-- Change an upper support bound while retaining exactly the same coefficients. -/
def withBand {s : ℕ} (P : CubePacket d M) (h : M ≤ s) : CubePacket d s where
  Index := P.Index
  finite := P.finite
  frequency := P.frequency
  frequency_le i r := (P.frequency_le i r).trans h
  coeff := P.coeff

noncomputable def value (P : CubePacket d M) (x : Fin d → ℝ) : ℂ :=
  ∑ i, P.coeff i * exponential (P.frequency i) x

noncomputable def mass (P : CubePacket d M) : ℝ := ∑ i, ‖P.coeff i‖

theorem mass_nonneg (P : CubePacket d M) : 0 ≤ P.mass :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

@[simp] theorem value_withBand {s : ℕ} (P : CubePacket d M) (h : M ≤ s)
    (x : Fin d → ℝ) : (P.withBand h).value x = P.value x := rfl

@[simp] theorem mass_withBand {s : ℕ} (P : CubePacket d M) (h : M ≤ s) :
    (P.withBand h).mass = P.mass := rfl

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

namespace CubePacket
noncomputable def scale {d Q : ℕ} (P : CubePacket d Q) (c : ℂ) : CubePacket d Q :=
  { P with coeff := fun i => c * P.coeff i }

@[simp] theorem value_scale {d Q : ℕ} (P : CubePacket d Q) (c : ℂ) (x : Fin d → ℝ) :
    (P.scale c).value x = c * P.value x := by
  simp only [value, scale, mul_assoc, Finset.mul_sum]

@[simp] theorem mass_scale {d Q : ℕ} (P : CubePacket d Q) (c : ℂ) :
    (P.scale c).mass = ‖c‖ * P.mass := by
  simp only [mass, scale, norm_mul, Finset.mul_sum]


/-- Collect repeated frequencies into the coefficient vector on the cube. -/
def coefficientVector {d Q s : ℕ} (P : CubePacket d Q) (hband : Q ≤ s) :
    EuclideanSpace ℂ (Frequency d s) :=
  ∑ i, P.coeff i • EuclideanSpace.basisFun (Frequency d s) ℂ
    (fun r => ⟨P.frequency i r, (P.frequency_le i r).trans_lt (Nat.lt_succ_of_le hband)⟩)

theorem coefficientVector_norm_le {d Q s : ℕ} (P : CubePacket d Q) (hband : Q ≤ s) :
    ‖P.coefficientVector hband‖ ≤ P.mass := by
  unfold coefficientVector
  calc
    _ ≤ ∑ i, ‖P.coeff i • EuclideanSpace.basisFun (Frequency d s) ℂ
        (fun r => ⟨P.frequency i r, (P.frequency_le i r).trans_lt
          (Nat.lt_succ_of_le hband)⟩)‖ := norm_sum_le _ _
    _ = _ := by simp [norm_smul, mass]

theorem coefficientVector_evaluation {d Q s : ℕ} (P : CubePacket d Q) (hband : Q ≤ s)
    (x : Fin d → ℝ) :
    ofLp (P.coefficientVector hband) ⬝ᵥ
      (fun k => exponential (fun r => (k r).val) x) = P.value x := by
  classical
  simp only [coefficientVector, ofLp_sum, ofLp_smul, dotProduct, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.single, PiLp.ofLp_single]
  simp only [Pi.single_apply, mul_ite, ite_mul, mul_one, zero_mul,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, value]

/-- A scaled coordinate factor has coefficient mass at most two whenever
its scale is below the separating chord. -/
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

end CubePacket

/-- The square Euclidean energy of a coefficient family. -/
def packetEnergy {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖^2

private theorem packetEnergy_nonneg {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    0 ≤ packetEnergy v := Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem packet_dotProduct_norm_sq_le {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    ‖u ⬝ᵥ v‖^2 ≤ packetEnergy u * packetEnergy v := by
  have h := norm_sum_le Finset.univ (fun i => u i * v i)
  simp only [norm_mul] at h
  exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
    (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).2 h).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖u i‖) (fun i => ‖v i‖))

/-- Diagonal cardinal interpolation implies the sharp coefficient energy bound. -/
theorem packet_interpolation_energy_lower {ρ : Type*} [Fintype ρ] {n : ℕ}
    (V : Matrix ρ (Fin n) ℂ) (C : Matrix (Fin n) ρ ℂ) (b : ℝ)
    (hCV : C * V = Matrix.diagonal (fun _ => (b : ℂ)))
    {B : ℝ} (hC : ∀ i, packetEnergy (C i) ≤ B^2) (z : Fin n → ℂ) :
    b^2 * packetEnergy z ≤ (n : ℝ) * B^2 * packetEnergy (V *ᵥ z) := by
  classical
  have haction : C *ᵥ (V *ᵥ z) = fun i => (b : ℂ) * z i := by
    rw [Matrix.mulVec_mulVec, hCV]
    ext i
    exact Matrix.mulVec_diagonal _ _ i
  have hdiag : packetEnergy (C *ᵥ (V *ᵥ z)) = b^2 * packetEnergy z := by
    rw [haction]
    simp [packetEnergy, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  calc
    _ = packetEnergy (C *ᵥ (V *ᵥ z)) := hdiag.symm
    _ ≤ ∑ i, packetEnergy (C i) * packetEnergy (V *ᵥ z) :=
      Finset.sum_le_sum fun i _ => packet_dotProduct_norm_sq_le _ _
    _ ≤ ∑ _i : Fin n, B^2 * packetEnergy (V *ᵥ z) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hC i)
        (packetEnergy_nonneg _)
    _ = _ := by simp; ring

end
end LeanNumDetect.MultiTuran
