import SegmentedVDM.Interpolation
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Lagrange

/-!
Quantitative lower bounds for square power Vandermonde matrices.  The proof
constructs the inverse rows from the Lagrange basis and bounds their coefficient
energy through the Mahler measure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix Polynomial Finset
open scoped BigOperators

namespace LeanNumDetect
namespace RandSamp

noncomputable section

/-- The square power Vandermonde matrix, with nodes indexing rows. -/
def powerVandermonde {n : ℕ} (z : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun k j => z j ^ k.val

/-- Coefficient row of the Lagrange polynomial attached to `j`. -/
def lagrangeCoefficientRow {n : ℕ} (z : Fin n → ℂ) (j : Fin n) : Fin n → ℂ :=
  fun k => (Lagrange.basis Finset.univ z j).coeff k.val

theorem lagrangeCoefficientRow_interpolates {n : ℕ} (z : Fin n → ℂ)
    (hz : Function.Injective z) (j k : Fin n) :
    lagrangeCoefficientRow z j ⬝ᵥ (powerVandermonde z)ᵀ k = if j = k then 1 else 0 := by
  classical
  rw [show lagrangeCoefficientRow z j ⬝ᵥ (powerVandermonde z)ᵀ k =
      (Lagrange.basis Finset.univ z j).eval (z k) by
    have hn : 0 < n := Fin.pos_iff_nonempty.mpr ⟨j⟩
    have hdegree : (Lagrange.basis Finset.univ z j).natDegree < n := by
      rw [Lagrange.natDegree_basis hz.injOn (Finset.mem_univ j)]
      simpa using Nat.sub_lt hn Nat.zero_lt_one
    rw [Polynomial.eval_eq_sum_range' hdegree]
    simp only [lagrangeCoefficientRow, dotProduct, transpose_apply, powerVandermonde]
    exact Fin.sum_univ_eq_sum_range
      (fun i => (Lagrange.basis Finset.univ z j).coeff i * z k ^ i) n ]
  by_cases hjk : j = k
  · subst k
    simpa using Lagrange.eval_basis_self hz.injOn (Finset.mem_univ j)
  · simpa [hjk] using Lagrange.eval_basis_of_ne hjk (Finset.mem_univ k)

theorem mahlerMeasure_basisDivisor_le {x y : ℂ} {γ : ℝ}
    (hγ : 0 < γ) (hy : ‖y‖ ≤ 1) (hsep : γ ≤ ‖x - y‖) :
    (Lagrange.basisDivisor x y).mahlerMeasure ≤ 1 / γ := by
  have hxy : x - y ≠ 0 := by
    intro h
    have : ‖x - y‖ = 0 := by rw [h, norm_zero]
    linarith
  rw [Lagrange.basisDivisor, Polynomial.mahlerMeasure_mul,
    Polynomial.mahlerMeasure_const, Polynomial.mahlerMeasure_X_sub_C,
    max_eq_left hy, norm_inv]
  simpa only [mul_one, one_div] using
    (inv_le_inv₀ (lt_of_lt_of_le hγ hsep) hγ).2 hsep

theorem lagrangeBasis_mahlerMeasure_le {n : ℕ} (z : Fin n → ℂ)
    (hzNorm : ∀ j, ‖z j‖ ≤ 1) {γ : ℝ} (hγ : 0 < γ)
    (hsep : ∀ i j, i ≠ j → γ ≤ ‖z i - z j‖) (j : Fin n) :
    (Lagrange.basis Finset.univ z j).mahlerMeasure ≤ (1 / γ) ^ (n - 1) := by
  classical
  rw [Lagrange.basis]
  have hmeasure :
      (∏ k ∈ Finset.univ.erase j, Lagrange.basisDivisor (z j) (z k)).mahlerMeasure =
        ∏ k ∈ Finset.univ.erase j,
          (Lagrange.basisDivisor (z j) (z k)).mahlerMeasure := by
    induction Finset.univ.erase j using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [ha, Polynomial.mahlerMeasure_mul, ih]
  rw [hmeasure]
  calc
    _ ≤ ∏ _k ∈ Finset.univ.erase j, (1 / γ) := by
      apply Finset.prod_le_prod
      · intro k hk
        exact (Lagrange.basisDivisor (z j) (z k)).mahlerMeasure_nonneg
      · intro k hk
        exact mahlerMeasure_basisDivisor_le hγ (hzNorm k)
          (hsep j k (Finset.ne_of_mem_erase hk).symm)
    _ = (1 / γ) ^ (n - 1) := by
      rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j),
        Finset.card_univ, Fintype.card_fin]

theorem lagrangeCoefficientRow_energy_le {n : ℕ} (z : Fin n → ℂ)
    (hz : Function.Injective z) (hzNorm : ∀ j, ‖z j‖ ≤ 1)
    {γ : ℝ} (hγ : 0 < γ) (hsep : ∀ i j, i ≠ j → γ ≤ ‖z i - z j‖)
    (j : Fin n) :
    SegmentedVDM.energy (lagrangeCoefficientRow z j) ≤
      ((n : ℝ) * (2 / γ) ^ (n - 1)) ^ 2 := by
  classical
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr ⟨j⟩
  let p := Lagrange.basis Finset.univ z j
  have hpdeg : p.natDegree = n - 1 := by
    dsimp [p]
    simpa using Lagrange.natDegree_basis hz.injOn (Finset.mem_univ j)
  have hpM : p.mahlerMeasure ≤ (1 / γ) ^ (n - 1) :=
    lagrangeBasis_mahlerMeasure_le z hzNorm hγ hsep j
  have hcoeff (k : Fin n) : ‖p.coeff k.val‖ ≤ (2 / γ) ^ (n - 1) := by
    calc
      ‖p.coeff k.val‖ ≤ (p.natDegree.choose k.val : ℝ) * p.mahlerMeasure :=
        p.norm_coeff_le_choose_mul_mahlerMeasure k.val
      _ ≤ (2 ^ (n - 1) : ℝ) * (1 / γ) ^ (n - 1) := by
        apply mul_le_mul
        · rw [hpdeg]
          exact_mod_cast Nat.choose_le_two_pow (n - 1) k.val
        · exact hpM
        · exact p.mahlerMeasure_nonneg
        · positivity
      _ = (2 / γ) ^ (n - 1) := by
        rw [div_pow]
        ring
  unfold SegmentedVDM.energy lagrangeCoefficientRow
  change (∑ k : Fin n, ‖p.coeff k.val‖ ^ 2) ≤ _
  calc
    ∑ k : Fin n, ‖p.coeff k.val‖ ^ 2
        ≤ ∑ _k : Fin n, ((2 / γ) ^ (n - 1)) ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      exact pow_le_pow_left₀ (norm_nonneg _) (hcoeff k) 2
    _ ≤ ((n : ℝ) * (2 / γ) ^ (n - 1)) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg ((2 / γ) ^ (n - 1))]

/-- A normalized square power Vandermonde matrix has a quantitative smallest
singular-value bound depending only on the minimum node spacing. -/
theorem powerVandermonde_minimumSingularValue {n : ℕ} (z : Fin n → ℂ)
    (hn : 0 < n) (hzNorm : ∀ j, ‖z j‖ ≤ 1)
    {γ : ℝ} (hγ : 0 < γ) (hsep : ∀ i j, i ≠ j → γ ≤ ‖z i - z j‖) :
    1 / (Real.sqrt n * ((n : ℝ) * (2 / γ) ^ (n - 1))) ≤
      matrixSingularValue (powerVandermonde z) (n - 1) := by
  classical
  have hz : Function.Injective z := by
    intro i j hij
    by_contra hne
    have := hsep i j hne
    rw [hij, sub_self, norm_zero] at this
    linarith
  let C : Matrix (Fin n) (Fin n) ℂ := fun j k => lagrangeCoefficientRow z j k
  have hCV : C * powerVandermonde z = 1 := by
    ext j k
    simp only [Matrix.mul_apply, C, Matrix.one_apply]
    change lagrangeCoefficientRow z j ⬝ᵥ (powerVandermonde z)ᵀ k = _
    exact lagrangeCoefficientRow_interpolates z hz j k
  apply SegmentedVDM.singularValue_ge_of_interpolation
    (powerVandermonde z) C hCV hn
  · positivity
  · intro j
    exact lagrangeCoefficientRow_energy_le z hz hzNorm hγ hsep j

/-- The same lower bound holds for the transpose.  This is proved from the
transposed Lagrange inverse, so it does not rely on an unproved singular-value
invariance principle. -/
theorem powerVandermonde_transpose_minimumSingularValue {n : ℕ} (z : Fin n → ℂ)
    (hn : 0 < n) (hzNorm : ∀ j, ‖z j‖ ≤ 1)
    {γ : ℝ} (hγ : 0 < γ) (hsep : ∀ i j, i ≠ j → γ ≤ ‖z i - z j‖) :
    1 / (Real.sqrt n * ((n : ℝ) * (2 / γ) ^ (n - 1))) ≤
      matrixSingularValue (powerVandermonde z)ᵀ (n - 1) := by
  classical
  have hz : Function.Injective z := by
    intro i j hij
    by_contra hne
    have := hsep i j hne
    rw [hij, sub_self, norm_zero] at this
    linarith
  let C : Matrix (Fin n) (Fin n) ℂ := fun j k => lagrangeCoefficientRow z j k
  have hCV : C * powerVandermonde z = 1 := by
    ext j k
    simp only [Matrix.mul_apply, C, Matrix.one_apply]
    change lagrangeCoefficientRow z j ⬝ᵥ (powerVandermonde z)ᵀ k = _
    exact lagrangeCoefficientRow_interpolates z hz j k
  have hVC : powerVandermonde z * C = 1 := mul_eq_one_comm.mp hCV
  have htrans : Cᵀ * (powerVandermonde z)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hVC, Matrix.transpose_one]
  apply SegmentedVDM.singularValue_ge_of_interpolation
    (powerVandermonde z)ᵀ Cᵀ htrans hn
  · positivity
  · intro k
    have hentry (j : Fin n) :
        ‖(Cᵀ k j)‖ ≤ (2 / γ) ^ (n - 1) := by
      let p := Lagrange.basis Finset.univ z j
      have hpdeg : p.natDegree = n - 1 := by
        dsimp [p]
        simpa using Lagrange.natDegree_basis hz.injOn (Finset.mem_univ j)
      have hpM : p.mahlerMeasure ≤ (1 / γ) ^ (n - 1) :=
        lagrangeBasis_mahlerMeasure_le z hzNorm hγ hsep j
      change ‖p.coeff k.val‖ ≤ _
      calc
        ‖p.coeff k.val‖ ≤ (p.natDegree.choose k.val : ℝ) * p.mahlerMeasure :=
          p.norm_coeff_le_choose_mul_mahlerMeasure k.val
        _ ≤ (2 ^ (n - 1) : ℝ) * (1 / γ) ^ (n - 1) := by
          apply mul_le_mul
          · rw [hpdeg]
            exact_mod_cast Nat.choose_le_two_pow (n - 1) k.val
          · exact hpM
          · exact p.mahlerMeasure_nonneg
          · positivity
        _ = (2 / γ) ^ (n - 1) := by rw [div_pow]; ring
    unfold SegmentedVDM.energy
    calc
      ∑ j : Fin n, ‖Cᵀ k j‖ ^ 2
          ≤ ∑ _j : Fin n, ((2 / γ) ^ (n - 1)) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (hentry j) 2
      _ ≤ ((n : ℝ) * (2 / γ) ^ (n - 1)) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith [sq_nonneg ((2 / γ) ^ (n - 1))]

end

end RandSamp
end LeanNumDetect
