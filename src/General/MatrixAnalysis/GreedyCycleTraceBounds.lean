import General.MatrixAnalysis.HermitianVariational
import General.MatrixAnalysis.TraceExponentialBounds

/-!
Trace-exponential bounds from a uniform spectral floor and an additional floor
on a subspace. The dimension argument is the coordinate-kernel proof of the
Hermitian variational principle. No concentration result is used here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix NormedSpace
open scoped BigOperators InnerProductSpace ComplexOrder

namespace LeanNumDetect.TraceExponential

open FiniteMatrixSampling

noncomputable section

/-- A lower quadratic bound on an r-dimensional subspace forces at least r
eigenvalues above the same threshold, with their multiplicities retained. -/
theorem high_eigenvalue_card_lower {n r : ℕ}
    {S : Matrix (Fin n) (Fin n) ℂ} (hS : S.IsHermitian)
    (U : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hdim : Module.finrank ℂ U = r)
    {c : ℝ} (hsub : ∀ x ∈ U, ‖x‖ = 1 → c ≤ quadratic S x) :
    r ≤ (Finset.univ.filter (fun i => c ≤ hS.eigenvalues i)).card := by
  classical
  let high : Finset (Fin n) := Finset.univ.filter (fun i => c ≤ hS.eigenvalues i)
  by_contra hr
  have hcard : high.card < Module.finrank ℂ U := by
    rw [hdim]
    exact lt_of_not_ge hr
  obtain ⟨x, hx, hnorm, hzero⟩ := exists_unit_mem_coord_zero hS.eigenvectorBasis U high hcard
  let w : Fin n → ℝ := fun i => ‖⟪hS.eigenvectorBasis i, x⟫_ℂ‖ ^ 2
  have hw : ∀ i, 0 ≤ w i := fun i => sq_nonneg _
  have hsum : ∑ i, w i = 1 := by
    simpa only [w, hnorm, one_pow] using hS.eigenvectorBasis.sum_sq_norm_inner_right x
  have hh (i : Fin n) (hi : i ∈ high) : w i = 0 := by simp [w, hzero i hi]
  have hlower (i : Fin n) (hi : i ∉ high) : hS.eigenvalues i < c := by
    have : ¬ c ≤ hS.eigenvalues i := by simpa only [high, Finset.mem_filter,
      Finset.mem_univ, true_and] using hi
    exact lt_of_not_ge this
  have hpos : ∃ i ∈ (Finset.univ : Finset (Fin n)), 0 < w i := by
    by_contra h
    simp only [Finset.mem_univ, true_and, not_exists, not_lt] at h
    have hz (i : Fin n) : w i = 0 := le_antisymm (h i) (hw i)
    simp only [hz, Finset.sum_const_zero] at hsum
    norm_num at hsum
  have hupper : quadratic S x < c := by
    rw [quadratic_eq_sum hS]
    change ∑ i, hS.eigenvalues i * w i < c
    calc
      _ < ∑ i : Fin n, c * w i := by
        apply Finset.sum_lt_sum
        · intro i _
          by_cases hi : i ∈ high
          · simp [hh i hi]
          · exact mul_le_mul_of_nonneg_right (hlower i hi).le (hw i)
        · obtain ⟨i, hi, hp⟩ := hpos
          refine ⟨i, hi, ?_⟩
          have hnot : i ∉ high := by
            intro hmem
            rw [hh i hmem] at hp
            exact (lt_irrefl 0) hp
          exact mul_lt_mul_of_pos_right (hlower i hnot) hp
      _ = c := by rw [← Finset.mul_sum, hsum, mul_one]
  exact (not_lt_of_ge (hsub x hx hnorm)) hupper

/-- The scalar action on a Hermitian matrix preserves its chosen eigenbasis. -/
theorem traceExp_real_smul_eq_sum {n : ℕ} {S : Matrix (Fin n) (Fin n) ℂ}
    (hS : S.IsHermitian) (a : ℝ) :
    traceExp (a • S) = ∑ i, Real.exp (a * hS.eigenvalues i) := by
  rw [traceExp, trace_eq_sum_quadratic (exp (a • S)) hS.eigenvectorBasis]
  apply Finset.sum_congr rfl
  intro i _
  rw [quadratic_exp_smul_eq_sum hS]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hS.eigenvectorBasis.inner_eq_ite, hji]
  · simp

/-- The incomplete cycle contributes r extra eigenvalue floors above the J
complete-cycle floors. This is the terminal trace bound for greedy sampling. -/
theorem traceExp_neg_smul_le_cycle_factor {n r J : ℕ}
    {S : Matrix (Fin n) (Fin n) ℂ} (hS : S.IsHermitian)
    (U : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hdim : Module.finrank ℂ U = r)
    {t η : ℝ} (ht : 0 ≤ t) (hη : 0 ≤ η)
    (hfull : ∀ x : EuclideanSpace ℂ (Fin n),
      (J : ℝ) * η * ‖x‖ ^ 2 ≤ quadratic S x)
    (hsub : ∀ x ∈ U, ((J : ℝ) + 1) * η * ‖x‖ ^ 2 ≤ quadratic S x) :
    traceExp ((-t) • S) ≤ Real.exp (-t * (J : ℝ) * η) *
      ((n : ℝ) - r + r * Real.exp (-t * η)) := by
  classical
  let c : ℝ := ((J : ℝ) + 1) * η
  let high : Finset (Fin n) := Finset.univ.filter (fun i => c ≤ hS.eigenvalues i)
  let low : Finset (Fin n) := Finset.univ.filter (fun i => ¬ c ≤ hS.eigenvalues i)
  let a : ℝ := Real.exp (-t * c)
  let b : ℝ := Real.exp (-t * (J : ℝ) * η)
  have hcard : r ≤ high.card :=
    high_eigenvalue_card_lower hS U hdim (fun x hx hn => by
      simpa only [c, hn, one_pow, mul_one] using hsub x hx)
  have hsumcard : (high.card : ℝ) + (low.card : ℝ) = n := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin n => c ≤ hS.eigenvalues i)
    have hnat : high.card + low.card = n := by simpa [high, low] using h
    exact_mod_cast hnat
  have hall (i : Fin n) : (J : ℝ) * η ≤ hS.eigenvalues i := by
    have h := hfull (hS.eigenvectorBasis i)
    simpa only [quadratic_eigenvector, hS.eigenvectorBasis.orthonormal.1 i,
      one_pow, mul_one] using h
  have hab : a ≤ b := by
    apply Real.exp_le_exp.mpr
    dsimp [c]
    nlinarith
  have hupper : traceExp ((-t) • S) ≤ (high.card : ℝ) * a + (low.card : ℝ) * b := by
    rw [traceExp_real_smul_eq_sum hS]
    calc
      _ ≤ ∑ i : Fin n, if i ∈ high then a else b := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i ∈ high
        · simp only [hi, if_true]
          apply Real.exp_le_exp.mpr
          have hh : c ≤ hS.eigenvalues i := (Finset.mem_filter.mp hi).2
          exact mul_le_mul_of_nonpos_left hh (neg_nonpos.mpr ht)
        · simp only [hi, if_false]
          apply Real.exp_le_exp.mpr
          calc
            _ ≤ -t * ((J : ℝ) * η) :=
              mul_le_mul_of_nonpos_left (hall i) (neg_nonpos.mpr ht)
            _ = _ := by ring
      _ = _ := by
        simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
        have hhigh : (Finset.univ.filter (fun i => i ∈ high)) = high := by ext i; simp
        have hlow : (Finset.univ.filter (fun i => i ∉ high)) = low := by
          ext i
          simp [high, low]
        rw [hhigh, hlow]
  have hcard' : (r : ℝ) ≤ high.card := by exact_mod_cast hcard
  have hcount : (high.card : ℝ) * a + (low.card : ℝ) * b ≤
      (r : ℝ) * a + ((n : ℝ) - r) * b := by
    have h := mul_le_mul_of_nonpos_right hcard' (sub_nonpos.mpr hab)
    have hc := congrArg (fun x : ℝ => x * b) hsumcard
    nlinarith [h, hc]
  have ha : a = b * Real.exp (-t * η) := by
    dsimp [a, b, c]
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (r : ℝ) * a + ((n : ℝ) - r) * b := hupper.trans hcount
    _ = _ := by rw [ha]; dsimp [b]; ring

end

end LeanNumDetect.TraceExponential
