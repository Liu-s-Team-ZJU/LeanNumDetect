import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# A continuous companion representation of exponential sums

The characteristic polynomial, and hence the companion generator, remain
continuous when frequencies collide. This avoids estimates involving an
inverse Vandermonde matrix or a minimum frequency gap. All results here
are proved; no result from `External` is imported.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix.Norms.Operator Topology
open Matrix Polynomial Set

namespace LeanNumDetect.ExponentialCompanion
noncomputable section

def rootPolynomial {s : ℕ} (frequency : Fin s → ℂ) : ℂ[X] :=
  ∏ i, (Polynomial.X - Polynomial.C (frequency i))

theorem rootPolynomial_monic {s : ℕ} (frequency : Fin s → ℂ) :
    (rootPolynomial frequency).Monic :=
  Polynomial.monic_prod_X_sub_C _ _

@[simp] theorem rootPolynomial_natDegree {s : ℕ} (frequency : Fin s → ℂ) :
    (rootPolynomial frequency).natDegree = s := by
  rw [rootPolynomial, Polynomial.natDegree_prod_of_monic]
  · simp
  · intro i _
    exact Polynomial.monic_X_sub_C _

@[simp] theorem rootPolynomial_coeff_degree {s : ℕ} (frequency : Fin s → ℂ) :
    (rootPolynomial frequency).coeff s = 1 := by
  simpa only [rootPolynomial_natDegree] using (rootPolynomial_monic frequency).coeff_natDegree

@[simp] theorem rootPolynomial_eval_node {s : ℕ} (frequency : Fin s → ℂ) (i : Fin s) :
    (rootPolynomial frequency).eval (frequency i) = 0 := by
  simp only [rootPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

theorem continuous_rootPolynomial_coeff {s : ℕ} (k : ℕ) :
    Continuous (fun frequency : Fin s → ℂ => (rootPolynomial frequency).coeff k) := by
  have h (S : Finset (Fin s)) : ∀ k : ℕ,
      Continuous (fun frequency : Fin s → ℂ =>
        (∏ i ∈ S, (Polynomial.X - Polynomial.C (frequency i))).coeff k) := by
    induction S using Finset.induction_on with
    | empty => intro k; simpa only [Finset.prod_empty] using
        (continuous_const : Continuous (fun _ : Fin s → ℂ => (1 : ℂ[X]).coeff k))
    | @insert i S hi ih =>
      intro k
      cases k with
      | zero =>
        simpa only [Finset.prod_insert hi, sub_mul, Polynomial.coeff_sub,
          Polynomial.coeff_X_mul_zero, Polynomial.coeff_C_mul, Pi.sub_def, Pi.mul_def] using
          (continuous_const.sub ((continuous_apply i).mul (ih 0)))
      | succ k =>
        simpa only [Finset.prod_insert hi, sub_mul, Polynomial.coeff_sub,
          Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, Pi.sub_def, Pi.mul_def] using
          ((ih k).sub ((continuous_apply i).mul (ih (k + 1))))
  exact h Finset.univ k

/-- The top rows shift the jet, and the last row is the annihilating
polynomial recurrence. -/
def generator {s : ℕ} (frequency : Fin s → ℂ) : Matrix (Fin s) (Fin s) ℂ :=
  fun i j => if i.val + 1 < s then
    if j.val = i.val + 1 then 1 else 0
  else -(rootPolynomial frequency).coeff j.val

theorem continuous_generator (s : ℕ) :
    Continuous (generator : (Fin s → ℂ) → Matrix (Fin s) (Fin s) ℂ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  dsimp [generator]
  split_ifs <;> first | exact continuous_const | exact (continuous_rootPolynomial_coeff _).neg

def powerVector {s : ℕ} (z : ℂ) : Fin s → ℂ := fun j => z ^ j.val

theorem rootPolynomial_recurrence {s : ℕ} (frequency : Fin s → ℂ) (i : Fin s) :
    ∑ j : Fin s, (rootPolynomial frequency).coeff j.val * (frequency i) ^ j.val = -(frequency i) ^ s := by
  have h := Polynomial.eval_eq_sum_range'
    (p := rootPolynomial frequency) (n := s + 1)
    (by simp : (rootPolynomial frequency).natDegree < s + 1) (frequency i)
  rw [rootPolynomial_eval_node, Finset.sum_range_succ,
    rootPolynomial_coeff_degree, one_mul] at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem generator_powerVector {s : ℕ} (frequency : Fin s → ℂ) (j : Fin s) :
    (generator frequency).mulVec (powerVector (frequency j)) = (frequency j) • powerVector (frequency j) := by
  ext i
  by_cases hi : i.val + 1 < s
  · let next : Fin s := ⟨i.val + 1, hi⟩
    have heq : ∀ k : Fin s, k.val = i.val + 1 ↔ k = next := by
      intro k
      exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    simp only [Matrix.mulVec, dotProduct, generator, if_pos hi,
      powerVector, Pi.smul_apply, smul_eq_mul, heq]
    simp [next, pow_succ, mul_comm]
  · have hlast : i.val + 1 = s := by omega
    simp only [Matrix.mulVec, dotProduct, generator, if_neg hi, powerVector,
      neg_mul, Finset.sum_neg_distrib, rootPolynomial_recurrence,
      neg_neg, Pi.smul_apply, smul_eq_mul]
    simpa only [hlast, pow_succ, mul_comm] using
      (pow_succ (frequency j) i.val)

/-- The eigenvector identity is valid even for repeated nodes. -/
theorem generator_vandermonde {s : ℕ} (frequency : Fin s → ℂ) :
    generator frequency * (Matrix.vandermonde frequency)ᵀ =
      (Matrix.vandermonde frequency)ᵀ * Matrix.diagonal frequency := by
  ext i j
  rw [Matrix.mul_diagonal]
  have h := congrFun (generator_powerVector frequency j) i
  simpa only [Matrix.mul_diagonal, Matrix.mul_apply, Matrix.vandermonde, Matrix.of_apply,
    Matrix.transpose_apply, Matrix.mul_diagonal, Matrix.mulVec, dotProduct,
    powerVector, Pi.smul_apply, smul_eq_mul, mul_comm] using h

/-- A matrix exponential transports the entire eigenvector family without
ever dividing by a frequency gap. -/
theorem exp_generator_vandermonde {s : ℕ} (frequency : Fin s → ℂ) (t : ℂ) :
    NormedSpace.exp (t • generator frequency) * (Matrix.vandermonde frequency)ᵀ =
      (Matrix.vandermonde frequency)ᵀ * Matrix.diagonal (fun j => Complex.exp (t * frequency j)) := by
  have h : SemiconjBy (Matrix.vandermonde frequency)ᵀ
      (Matrix.diagonal (fun j => t * frequency j)) (t • generator frequency) := by
    change (Matrix.vandermonde frequency)ᵀ * Matrix.diagonal (fun j => t * frequency j) =
      (t • generator frequency) * (Matrix.vandermonde frequency)ᵀ
    rw [show Matrix.diagonal (fun j => t * frequency j) = t • Matrix.diagonal frequency by
      ext i j; simp [Matrix.diagonal, smul_eq_mul]]
    rw [Matrix.mul_smul, Matrix.smul_mul, generator_vandermonde]
  have hexp := h.exp_right
  rw [Matrix.exp_diagonal] at hexp
  simpa only [SemiconjBy, Complex.exp_eq_exp_ℂ, Pi.exp_def] using hexp.symm

theorem continuous_exp_generator (s : ℕ) :
    Continuous (fun p : (Fin s → ℂ) × ℂ => NormedSpace.exp (p.2 • generator p.1)) := by
  exact NormedSpace.exp_continuous.comp
    (continuous_snd.smul ((continuous_generator s).comp continuous_fst))

/-- The initial derivatives, before factorial normalization. -/
def initialJet {s : ℕ} (frequency coefficient : Fin s → ℂ) : Fin s → ℂ :=
  (Matrix.vandermonde frequency)ᵀ.mulVec coefficient

theorem exponentialSum_eq_evolution {s : ℕ} (hs : 0 < s)
    (frequency coefficient : Fin s → ℂ) (t : ℂ) :
    ∑ j, coefficient j * Complex.exp (t * frequency j) =
      (NormedSpace.exp (t • generator frequency)).mulVec
        (initialJet frequency coefficient) ⟨0, hs⟩ := by
  have h := congrArg (fun A : Matrix (Fin s) (Fin s) ℂ => A.mulVec coefficient)
    (exp_generator_vandermonde frequency t)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h
  have h0 := congrFun h ⟨0, hs⟩
  simpa [initialJet, Matrix.mulVec, dotProduct, Matrix.vandermonde,
    Matrix.diagonal, mul_comm] using h0.symm

/-- The limiting generator is a shift when all frequencies coincide at zero. -/
def jetShift (s : ℕ) : Matrix (Fin s) (Fin s) ℂ :=
  fun i j => if j.val = i.val + 1 then 1 else 0

theorem generator_zero (s : ℕ) : generator (0 : Fin s → ℂ) = jetShift s := by
  have hpoly : rootPolynomial (0 : Fin s → ℂ) = (Polynomial.X : ℂ[X]) ^ s := by
    simp [rootPolynomial]
  ext i j
  by_cases hi : i.val + 1 < s
  · simp [generator, jetShift, hi]
  · have hj : j.val ≠ i.val + 1 := by omega
    simp [generator, jetShift, hi, hj, hpoly, Polynomial.coeff_X_pow,
      Nat.ne_of_lt j.isLt]

theorem jetShift_pow (s r : ℕ) (i j : Fin s) :
    (jetShift s ^ r) i j = if j.val = i.val + r then 1 else 0 := by
  induction r generalizing i j with
  | zero => simp [Matrix.one_apply, Fin.ext_iff, eq_comm]
  | succ r ih =>
    rw [pow_succ', Matrix.mul_apply]
    by_cases hi : i.val + 1 < s
    · let next : Fin s := ⟨i.val + 1, hi⟩
      have hnext (k : Fin s) : k.val = i.val + 1 ↔ k = next := by
        exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      simp only [jetShift, hnext, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, ih]
      simp only [next, Nat.add_assoc, Nat.add_comm 1 r]
    · have hzero (k : Fin s) : ¬ k.val = i.val + 1 := by omega
      have hj : ¬ j.val = i.val + (r + 1) := by omega
      simp [jetShift, hzero, hj]

theorem exp_jetShift_firstRow {s : ℕ} (hs : 0 < s) (t : ℂ) (j : Fin s) :
    NormedSpace.exp (t • jetShift s) ⟨0, hs⟩ j = t ^ j.val / (j.val.factorial : ℂ) := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  dsimp only
  have hsum : Summable (fun n : ℕ =>
      (n.factorial : ℂ)⁻¹ • (t • jetShift s) ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) _
  rw [tsum_apply hsum, tsum_apply ((Pi.summable.mp hsum) ⟨0, hs⟩)]
  simp only [Matrix.smul_apply, smul_pow, smul_eq_mul,
    jetShift_pow, Nat.zero_add]
  rw [tsum_eq_single j.val]
  · simp [div_eq_mul_inv, mul_comm]
  · intro r hr
    simp [Ne.symm hr]

theorem zero_evolution_eq_jetPolynomial {s : ℕ} (hs : 0 < s)
    (coefficient : Fin s → ℂ) (t : ℂ) :
    (NormedSpace.exp (t • generator (0 : Fin s → ℂ))).mulVec coefficient ⟨0, hs⟩ =
      ∑ j, coefficient j * t ^ j.val / (j.val.factorial : ℂ) := by
  rw [generator_zero]
  simp only [Matrix.mulVec, dotProduct, exp_jetShift_firstRow hs]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Uniform convergence of every first-row basis function to its Taylor
monomial as all frequencies approach zero. The radius depends on the
number of frequencies and the requested tolerance, never on their gaps. -/
theorem exists_uniform_jet_radius {s : ℕ} (hs : 0 < s)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ frequency : Fin s → ℂ, ‖frequency‖ ≤ η →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ j : Fin s,
        ‖NormedSpace.exp ((t : ℂ) • generator frequency) ⟨0, hs⟩ j -
          (t : ℂ) ^ j.val / (j.val.factorial : ℂ)‖ ≤ ε := by
  let F : (Fin s → ℂ) → Icc (0 : ℝ) 1 → Fin s → ℂ :=
    fun frequency t => NormedSpace.exp ((t.val : ℂ) • generator frequency) ⟨0, hs⟩
  have hF : Continuous F.uncurry := by
    have hp : Continuous (fun p : (Fin s → ℂ) × Icc (0 : ℝ) 1 =>
        (p.1, ((p.2.val : ℝ) : ℂ))) := continuous_fst.prodMk
      (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd))
    exact (continuous_apply (⟨0, hs⟩ : Fin s)).comp
      ((continuous_exp_generator s).comp hp)
  have hU := Continuous.tendstoUniformly F hF (0 : Fin s → ℂ)
  have he := (Metric.tendstoUniformly_iff.mp hU) ε hε
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨η / 2, by positivity, ?_⟩
  intro frequency hfrequency t ht j
  have hmem : frequency ∈ Metric.ball (0 : Fin s → ℂ) η := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hfrequency.trans_lt (by linarith)
  have hdist := hball hmem (⟨t, ht⟩ : Icc (0 : ℝ) 1)
  have hentry := (norm_le_pi_norm
    (F frequency ⟨t, ht⟩ - F 0 ⟨t, ht⟩) j).trans_lt
      (by simpa only [dist_eq_norm, norm_sub_rev] using hdist)
  simpa only [F, Pi.sub_apply, generator_zero, exp_jetShift_firstRow hs]
    using hentry.le

end
end LeanNumDetect.ExponentialCompanion
