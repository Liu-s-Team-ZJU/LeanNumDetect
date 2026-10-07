import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! Tensor Taylor approximation for arbitrary multidimensional exponential
nodes. A nonzero kernel of the box-moment matrix exists solely by dimension
counting; no general-position or Cartesian-product hypothesis is used. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Matrix WithLp

namespace LeanNumDetect.MultidimensionalTaylorBounds
noncomputable section

/-- Moments indexed by a box of multiindices. -/
def boxMomentMatrix {d s : ℕ} (q : ℕ) (offset : Fin s → Fin d → ℝ) :
    Matrix (Fin d → Fin q) (Fin s) ℂ :=
  fun a j => ∏ r, (offset j r : ℂ) ^ (a r).val

theorem exists_unit_box_moment_kernel {d s q : ℕ} (hcard : q ^ d < s)
    (offset : Fin s → Fin d → ℝ) :
    ∃ u : EuclideanSpace ℂ (Fin s), ‖u‖ = 1 ∧
      ∀ a : Fin d → Fin q, ∑ j, (∏ r, (offset j r : ℂ) ^ (a r).val) * ofLp u j = 0 := by
  let T := (boxMomentMatrix q offset).toEuclideanLin
  have hker : T.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hcard)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let u := (‖v‖⁻¹ : ℂ) • v
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hv0
  have hTu : T u = 0 := by rw [map_smul, LinearMap.mem_ker.mp hv, smul_zero]
  refine ⟨u, hu, ?_⟩
  intro a
  have h := congrArg (fun w : EuclideanSpace ℂ (Fin d → Fin q) => ofLp w a) hTu
  change (∑ j, (∏ r, (offset j r : ℂ) ^ (a r).val) * ofLp u j) = 0 at h
  exact h

/-- Every tensor Taylor polynomial is annihilated by the box moments. -/
theorem box_taylor_action_zero {d s q : ℕ} (offset : Fin s → Fin d → ℝ)
    (frequency : Fin d → ℝ) (u : EuclideanSpace ℂ (Fin s))
    (hkernel : ∀ a : Fin d → Fin q,
      ∑ j, (∏ r, (offset j r : ℂ) ^ (a r).val) * ofLp u j = 0) :
    ∑ j, (∏ r, ∑ a : Fin q,
      (Complex.I * ((frequency r * offset j r : ℝ) : ℂ)) ^ a.val /
        (a.val.factorial : ℂ)) * ofLp u j = 0 := by
  classical
  simp_rw [Fintype.prod_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a _
  have he (j : Fin s) :
      (∏ r, (Complex.I * ((frequency r * offset j r : ℝ) : ℂ)) ^ (a r).val /
        ((a r).val.factorial : ℂ)) * ofLp u j =
      (∏ r, (Complex.I * (frequency r : ℂ)) ^ (a r).val /
        ((a r).val.factorial : ℂ)) *
        ((∏ r, (offset j r : ℂ) ^ (a r).val) * ofLp u j) := by
    have hfactor (r : Fin d) :
        (Complex.I * ((frequency r * offset j r : ℝ) : ℂ)) ^ (a r).val /
          ((a r).val.factorial : ℂ) =
        ((Complex.I * (frequency r : ℂ)) ^ (a r).val /
          ((a r).val.factorial : ℂ)) * (offset j r : ℂ) ^ (a r).val := by
      push_cast
      rw [show Complex.I * ((frequency r : ℂ) * (offset j r : ℂ)) =
        (Complex.I * (frequency r : ℂ)) * (offset j r : ℂ) by ring, mul_pow]
      ring
    simp_rw [hfactor, Finset.prod_mul_distrib]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, hkernel a, mul_zero]

/-- A convenient absolute remainder constant on the unit complex ball. -/
theorem exponential_remainder_le {q : ℕ} (hq : 0 < q) (t : ℂ)
    {B : ℝ} (_hB : 0 ≤ B) (ht : ‖t‖ ≤ 1) (htB : ‖t‖ ≤ B) :
    ‖Complex.exp t - ∑ a : Fin q, t ^ a.val / (a.val.factorial : ℂ)‖ ≤
      2 / (q.factorial : ℝ) * B ^ q := by
  have hcoef : (q.succ : ℝ) * (((q.factorial * q : ℕ) : ℝ)⁻¹) ≤
      2 / (q.factorial : ℝ) := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hf : (0 : ℝ) < q.factorial := by positivity
    have hqp : (0 : ℝ) < q := by exact_mod_cast hq
    simp only [Nat.cast_mul, Nat.cast_succ]
    field_simp
    nlinarith
  have hbound := Complex.exp_bound ht hq
  rw [← Fin.sum_univ_eq_sum_range] at hbound
  calc
    _ ≤ ‖t‖ ^ q * ((q.succ : ℝ) * (((q.factorial * q : ℕ) : ℝ)⁻¹)) := by
      simpa only [Nat.cast_mul] using hbound
    _ ≤ ‖t‖ ^ q * (2 / (q.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hcoef (pow_nonneg (norm_nonneg _) _)
    _ ≤ B ^ q * (2 / (q.factorial : ℝ)) := by gcongr
    _ = _ := by ring

/-- A product perturbation estimate, with a deliberately loose power that
avoids exceptional empty-product conventions. -/
theorem norm_prod_sub_prod_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a b : ι → ℂ) {E B : ℝ} (hE : 0 ≤ E) (hB : 1 ≤ B)
    (ha : ∀ i ∈ S, ‖a i‖ ≤ B) (hb : ∀ i ∈ S, ‖b i‖ ≤ B)
    (hab : ∀ i ∈ S, ‖a i - b i‖ ≤ E) :
    ‖∏ i ∈ S, a i - ∏ i ∈ S, b i‖ ≤ (S.card : ℝ) * E * B ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have haS : ∀ j ∈ S, ‖a j‖ ≤ B := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hbS : ∀ j ∈ S, ‖b j‖ ≤ B := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have habS : ∀ j ∈ S, ‖a j - b j‖ ≤ E := fun j hj => hab j (Finset.mem_insert_of_mem hj)
    have hpa : ‖∏ j ∈ S, a j‖ ≤ B ^ S.card := by
      rw [norm_prod]
      simpa only [Finset.prod_const] using Finset.prod_le_prod
        (fun _ _ => norm_nonneg _) haS
    have hbi := hb i (Finset.mem_insert_self i S)
    have habi := hab i (Finset.mem_insert_self i S)
    have hdiff := ih haS hbS habS
    have heq : a i * (∏ j ∈ S, a j) - b i * (∏ j ∈ S, b j) =
        (a i - b i) * (∏ j ∈ S, a j) +
          b i * ((∏ j ∈ S, a j) - ∏ j ∈ S, b j) := by ring
    rw [heq]
    calc
      _ ≤ ‖(a i - b i) * (∏ j ∈ S, a j)‖ +
          ‖b i * ((∏ j ∈ S, a j) - ∏ j ∈ S, b j)‖ := norm_add_le _ _
      _ ≤ E * B ^ S.card + B * ((S.card : ℝ) * E * B ^ S.card) := by
        simp only [norm_mul]
        exact add_le_add (mul_le_mul habi hpa (norm_nonneg _) hE)
          (mul_le_mul hbi hdiff (norm_nonneg _) (by positivity))
      _ ≤ _ := by
        rw [pow_succ]
        push_cast
        have hpow : 0 ≤ E * B ^ S.card := by positivity
        nlinarith

/-- A tensor exponential and its box Taylor polynomial differ by order `q`
in the largest coordinate phase. The exponential phases are purely imaginary. -/
theorem tensor_exponential_remainder_le {d q : ℕ} (hq : 0 < q)
    (t : Fin d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (ht : ∀ r, |t r| ≤ 1) (htB : ∀ r, |t r| ≤ B) :
    ‖Complex.exp (Complex.I * ((∑ r, t r : ℝ) : ℂ)) -
      ∏ r, ∑ a : Fin q, (Complex.I * (t r : ℂ)) ^ a.val /
        (a.val.factorial : ℂ)‖ ≤
      (d : ℝ) * (2 / (q.factorial : ℝ) * B ^ q) * (3 : ℝ) ^ d := by
  let a := fun r : Fin d => Complex.exp (Complex.I * (t r : ℂ))
  let b := fun r : Fin d => ∑ k : Fin q, (Complex.I * (t r : ℂ)) ^ k.val /
    (k.val.factorial : ℂ)
  have ha (r : Fin d) : ‖a r‖ = 1 := by simp [a]
  have hrem (r : Fin d) : ‖a r - b r‖ ≤ 2 / (q.factorial : ℝ) * B ^ q := by
    exact exponential_remainder_le hq _ hB (by simpa using ht r) (by simpa using htB r)
  have hrem1 (r : Fin d) : ‖a r - b r‖ ≤ 2 := by
    have h := exponential_remainder_le hq (Complex.I * (t r : ℂ)) (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa using ht r) (by simpa using ht r)
    have hf : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
    have hbq : 2 / (q.factorial : ℝ) ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    exact h.trans (by simpa only [one_pow, mul_one] using hbq)
  have hb (r : Fin d) : ‖b r‖ ≤ 3 := by
    have h := norm_le_norm_add_norm_sub (a r) (b r)
    rw [ha r] at h
    have hd := hrem1 r
    linarith
  have heq : Complex.exp (Complex.I * ((∑ r, t r : ℝ) : ℂ)) = ∏ r, a r := by
    rw [show Complex.I * ((∑ r, t r : ℝ) : ℂ) =
      ∑ r, Complex.I * (t r : ℂ) by push_cast; rw [Finset.mul_sum], Complex.exp_sum]
  rw [heq]
  simpa only [Finset.card_univ, Fintype.card_fin] using norm_prod_sub_prod_le
    Finset.univ a b (by positivity : 0 ≤ 2 / (q.factorial : ℝ) * B ^ q)
    (by norm_num : (1 : ℝ) ≤ 3) (fun r _ => by rw [ha r]; norm_num)
    (fun r _ => hb r) (fun r _ => hrem r)

/-- A clump with more points than box moments has a unit coefficient vector
whose Fourier action is uniformly of order `(M * B)^q`. -/
theorem exists_unit_tensor_fourier_row_upper {d s q : ℕ}
    (hq : 0 < q) (hcard : q ^ d < s) (offset : Fin s → Fin d → ℝ)
    {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hoffset : ∀ j r, |offset j r| ≤ B)
    (hshort : ∀ j r, M * |offset j r| ≤ 1) :
    ∃ u : EuclideanSpace ℂ (Fin s), ‖u‖ = 1 ∧
      ∀ frequency : Fin d → ℝ, (∀ r, |frequency r| ≤ M) →
        ‖∑ j, Complex.exp (Complex.I * ((∑ r, frequency r * offset j r : ℝ) : ℂ)) *
          ofLp u j‖ ≤
          (Real.sqrt (s : ℝ) * (d : ℝ) * (3 : ℝ) ^ d * 2 /
            (q.factorial : ℝ)) * (M * B) ^ q := by
  obtain ⟨u, hu, hkernel⟩ := exists_unit_box_moment_kernel hcard offset
  refine ⟨u, hu, ?_⟩
  intro frequency hfrequency
  let low := fun j : Fin s => ∏ r, ∑ a : Fin q,
    (Complex.I * ((frequency r * offset j r : ℝ) : ℂ)) ^ a.val /
      (a.val.factorial : ℂ)
  let rem := fun j : Fin s =>
    Complex.exp (Complex.I * ((∑ r, frequency r * offset j r : ℝ) : ℂ)) - low j
  let E := (d : ℝ) * (2 / (q.factorial : ℝ) * (M * B) ^ q) * (3 : ℝ) ^ d
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hrem (j : Fin s) : ‖rem j‖ ≤ E := by
    apply tensor_exponential_remainder_le hq (fun r => frequency r * offset j r)
      (mul_nonneg hM hB)
    · intro r
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hfrequency r) (abs_nonneg _)).trans (hshort j r)
    · intro r
      rw [abs_mul]
      exact mul_le_mul (hfrequency r) (hoffset j r) (abs_nonneg _) hM
  have hlow : ∑ j, low j * ofLp u j = 0 :=
    box_taylor_action_zero offset frequency u hkernel
  have haction :
      ∑ j, Complex.exp (Complex.I * ((∑ r, frequency r * offset j r : ℝ) : ℂ)) * ofLp u j =
        ∑ j, rem j * ofLp u j := by
    dsimp [rem]
    simp only [sub_mul, Finset.sum_sub_distrib, hlow, sub_zero]
  have hL1 : ∑ j, ‖ofLp u j‖ ≤ Real.sqrt (s : ℝ) := by
    apply (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Real.sqrt_nonneg _)).1
    rw [Real.sq_sqrt (Nat.cast_nonneg s)]
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin s => (1 : ℝ))
      (fun j => ‖ofLp u j‖)
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, ← EuclideanSpace.norm_sq_eq, hu] using h
  rw [haction]
  calc
    _ ≤ ∑ j, ‖rem j * ofLp u j‖ := norm_sum_le _ _
    _ = ∑ j, ‖rem j‖ * ‖ofLp u j‖ := by simp only [norm_mul]
    _ ≤ ∑ j, E * ‖ofLp u j‖ := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (hrem j) (norm_nonneg _)
    _ = E * ∑ j, ‖ofLp u j‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ E * Real.sqrt (s : ℝ) := mul_le_mul_of_nonneg_left hL1 hE
    _ = _ := by dsimp [E]; ring

/-- A one-dimensional source configuration embedded in a selected coordinate. -/
def collinearNodes {d s : ℕ} (r₀ : Fin d) (t : Fin s → ℝ) : Fin s → Fin d → ℝ :=
  fun j r => if r = r₀ then t j else 0

@[simp] theorem collinear_phase_sum {d s : ℕ} (r₀ : Fin d) (t : Fin s → ℝ)
    (frequency : Fin d → ℝ) (j : Fin s) :
    (∑ r, frequency r * collinearNodes r₀ t j r) = frequency r₀ * t j := by
  classical
  simp [collinearNodes, mul_ite]

/-- Collinear clumps realize the exponent `s - 1` in every dimension, for
all bounded frequency rows, including any possible subsampling. -/
theorem exists_unit_collinear_fourier_row_upper {d s : ℕ} (hs : 2 ≤ s)
    (r₀ : Fin d) (t : Fin s → ℝ) {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (ht : ∀ j, |t j| ≤ B) (hshort : ∀ j, M * |t j| ≤ 1) :
    ∃ u : EuclideanSpace ℂ (Fin s), ‖u‖ = 1 ∧
      ∀ frequency : Fin d → ℝ, (∀ r, |frequency r| ≤ M) →
        ‖∑ j, Complex.exp (Complex.I *
          ((∑ r, frequency r * collinearNodes r₀ t j r : ℝ) : ℂ)) * ofLp u j‖ ≤
          (6 * Real.sqrt (s : ℝ) / ((s - 1).factorial : ℝ)) * (M * B) ^ (s - 1) := by
  have hcard : (s - 1) ^ (1 : ℕ) < s := by simp; omega
  obtain ⟨u, hu, hrow⟩ := exists_unit_tensor_fourier_row_upper (by omega : 0 < s - 1)
    hcard (fun j (_ : Fin 1) => t j) hM hB (fun j _ => ht j) (fun j _ => hshort j)
  refine ⟨u, hu, ?_⟩
  intro frequency hfrequency
  have h := hrow (fun _ => frequency r₀) (fun _ => hfrequency r₀)
  simp only [collinear_phase_sum, Fin.sum_univ_one, Nat.cast_one,
    mul_one, pow_one] at h ⊢
  convert h using 1; ring

end
end LeanNumDetect.MultidimensionalTaylorBounds
