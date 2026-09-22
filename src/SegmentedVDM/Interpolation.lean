import General.MatrixAnalysis.RowDeletion

/-! The finite-dimensional Lagrange-interpolation argument of NumDetect,
`lem:minsvd_bound_by_lagInterp_high_dim`. All norms below are Euclidean;
the coefficient sum is the normalized torus L² norm squared by Parseval. -/

set_option autoImplicit false
open scoped BigOperators
open Matrix LeanNumDetect

namespace SegmentedVDM

noncomputable def energy {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  ∑ i, ‖v i‖ ^ 2

theorem energy_nonneg {ι : Type*} [Fintype ι] (v : ι → ℂ) : 0 ≤ energy v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem energy_pos {ι : Type*} [Fintype ι] (v : ι → ℂ) (hv : v ≠ 0) :
    0 < energy v := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ _,
    sq_pos_of_pos (norm_pos_iff.mpr hi)⟩

theorem dotProduct_norm_sq_le {ι : Type*} [Fintype ι] (c v : ι → ℂ) :
    ‖c ⬝ᵥ v‖ ^ 2 ≤ energy c * energy v := by
  have h := norm_sum_le Finset.univ (fun i => c i * v i)
  simp only [norm_mul] at h
  exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
    (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).2 h).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖c i‖) (fun i => ‖v i‖))

/-- No conjugation is missing: interpolation uses the ordinary transpose. -/
theorem interpolation_energy {ρ ι : Type*} [Fintype ρ] [Fintype ι] [DecidableEq ι]
    (V : Matrix ρ ι ℂ) (C : Matrix ι ρ ℂ) (hCV : C * V = 1) (v : ι → ℂ) :
    energy v ≤ (∑ j, energy (C j)) * energy (V *ᵥ v) := by
  have he : C *ᵥ (V *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hCV, one_mulVec]
  calc
    energy v = ∑ j, ‖C j ⬝ᵥ (V *ᵥ v)‖ ^ 2 := by
      change energy v = energy (C *ᵥ (V *ᵥ v))
      rw [he]
    _ ≤ ∑ j, energy (C j) * energy (V *ᵥ v) :=
      Finset.sum_le_sum fun j _ => dotProduct_norm_sq_le _ _
    _ = _ := (Finset.sum_mul ..).symm

theorem gram_eigenvector_energy {ρ : Type*} [Fintype ρ] {n : ℕ}
    (V : Matrix ρ (Fin n) ℂ) (v : Fin n → ℂ) (eigenvalue : ℝ)
    (he : (Vᴴ * V) *ᵥ v = (eigenvalue : ℂ) • v) :
    energy (V *ᵥ v) = eigenvalue * energy v := by
  change (∑ k, ‖(V *ᵥ v) k‖ ^ 2) = _
  rw [← quadratic_gram]
  unfold quadratic
  rw [he, dotProduct_smul, smul_eq_mul]
  have hh : star v ⬝ᵥ v = (energy v : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul',
      energy, ← Complex.ofReal_pow, ← Complex.ofReal_sum]
  rw [hh]
  simp

/-- The minimum-singular-value bound of the manuscript's
`lem:minsvd_bound_by_lagInterp_high_dim` for a whole family of Lagrange
interpolants, together with the full column rank that the interpolation
identities force as part of the conclusion.  There is no rank hypothesis: the
interpolation identities alone imply both claims.

`C * V = 1` is the Lean form of the interpolation identities
$f_k(\mathbf y_\ell/2\pi)=\delta_{k,\ell}$ of the manuscript's
`defi:high_dim_lagrange`, with `C k` the coefficient vector of $f_k$ and `V`
the Vandermonde matrix on the same frequency and node sets.

The right-hand side is exactly the manuscript's
$(\sum_k \|f_k\|_{L^2(\mathbb T^d)}^2)^{1/2}$: by Parseval on the unit torus
$\mathbb T^d \cong [0,1)^d$ with normalized measure, the squared $L^2$ norm of
the trigonometric polynomial $f_k = \sum_i c_{k,i} e^{2\pi i \mathbf s_i \cdot
\bm\omega}$ with pairwise distinct frequencies equals its coefficient energy,
$\|f_k\|_{L^2(\mathbb T^d)}^2 = \sum_i \|c_{k,i}\|^2 =$ `energy (C k)`.  This
identification is documented rather than proved: no Parseval bridge from
coefficient energies to continuous torus $L^2$ norms of trigonometric
polynomials is formalized in this repository (the `General.Fourier` Parseval
results concern transforms of windowed sums), so `Real.sqrt (energy (C k))` is
the implemented $L^2$ norm here.  The bridge would follow from
`hasSum_sq_fourierCoeffOn`, e.g. through
`LeanNumDetect.hasSum_intervalAngularTransform`, together with the
orthogonality $\int_0^1 e^{2\pi i (s-t) \omega}\,d\omega = \delta_{s,t}$ of
distinct integer frequencies.

The proof applies `interpolation_energy` to a nonzero Gram eigenvector and
`gram_eigenvector_energy` to its energy, giving
$1 \le \bigl(\sum_k \mathrm{energy}(C k)\bigr) \sigma_{\min}(\mathcal V)^2$.
This forces $\sigma_{\min}(\mathcal V) > 0$ (full column rank) and, taking
square roots, $1/\sigma_{\min}(\mathcal V) \le \bigl(\sum_k
\mathrm{energy}(C k)\bigr)^{1/2}$. -/
theorem singularValue_inv_le_lagrangeFamily_l2 {ρ : Type*} [Fintype ρ] {n : ℕ}
    (V : Matrix ρ (Fin n) ℂ) (C : Matrix (Fin n) ρ ℂ)
    (hCV : C * V = 1) (hn : 0 < n) :
    0 < matrixSingularValue V (n - 1) ∧
      1 / matrixSingularValue V (n - 1) ≤ Real.sqrt (∑ k, energy (C k)) := by
  obtain ⟨v, hv, he⟩ := singularValue_gram_eigenvector V (by omega : n - 1 < n)
  have hp := energy_pos v hv
  have h := interpolation_energy V C hCV v
  rw [gram_eigenvector_energy V v _ he] at h
  have hE : 0 ≤ ∑ k, energy (C k) := Finset.sum_nonneg fun _ _ => energy_nonneg _
  have hσ_nonneg := V.toEuclideanLin.singularValues_nonneg (n - 1)
  change 0 ≤ matrixSingularValue V (n - 1) at hσ_nonneg
  have hcancel : 1 ≤ (∑ k, energy (C k)) * matrixSingularValue V (n - 1) ^ 2 := by
    nlinarith
  have hE_sqrt : Real.sqrt (∑ k, energy (C k)) ^ 2 = ∑ k, energy (C k) :=
    Real.sq_sqrt hE
  have hprod : 1 ≤ Real.sqrt (∑ k, energy (C k)) * matrixSingularValue V (n - 1) := by
    have hnonneg : 0 ≤ Real.sqrt (∑ k, energy (C k)) * matrixSingularValue V (n - 1) := by
      positivity
    have hsq : 1 ^ 2 ≤ (Real.sqrt (∑ k, energy (C k)) * matrixSingularValue V (n - 1)) ^ 2 := by
      simpa only [mul_pow, hE_sqrt, one_pow] using hcancel
    exact (sq_le_sq₀ (by norm_num) hnonneg).mp hsq
  have hσpos : 0 < matrixSingularValue V (n - 1) := by
    by_contra hc
    have hσ0 : matrixSingularValue V (n - 1) = 0 :=
      le_antisymm (le_of_not_gt hc) hσ_nonneg
    rw [hσ0, mul_zero] at hprod
    exact absurd hprod (by norm_num)
  exact ⟨hσpos, (div_le_iff₀ hσpos).2 hprod⟩

/-- The uniform-bound corollary of `singularValue_inv_le_lagrangeFamily_l2`:
a per-interpolant bound `energy (C j) ≤ B ^ 2` feeds into the family
root-sum-square and `Real.sqrt (n * B ^ 2) = Real.sqrt n * B`.  A coefficient
norm bound gives the smallest singular value bound, including full column rank;
there is no rank hypothesis hidden in this reduction. -/
theorem singularValue_ge_of_interpolation {ρ : Type*} [Fintype ρ] {n : ℕ}
    (V : Matrix ρ (Fin n) ℂ) (C : Matrix (Fin n) ρ ℂ)
    (hCV : C * V = 1) (hn : 0 < n) {B : ℝ} (hB : 0 < B)
    (hC : ∀ j, energy (C j) ≤ B ^ 2) :
    1 / (Real.sqrt n * B) ≤ matrixSingularValue V (n - 1) := by
  obtain ⟨hσpos, hinv⟩ := singularValue_inv_le_lagrangeFamily_l2 V C hCV hn
  have hsum : (∑ j, energy (C j)) ≤ (n : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin n, B ^ 2 := Finset.sum_le_sum fun j _ => hC j
      _ = _ := by simp
  have hsq : Real.sqrt ((n : ℝ) * B ^ 2) = Real.sqrt n * B := by
    rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hB.le]
  have hR : Real.sqrt (∑ k, energy (C k)) ≤ Real.sqrt n * B :=
    (Real.sqrt_le_sqrt hsum).trans (le_of_eq hsq)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hone : (1 : ℝ) ≤ (Real.sqrt n * B) * matrixSingularValue V (n - 1) :=
    (div_le_iff₀ hσpos).1 (hinv.trans hR)
  exact (div_le_iff₀ (mul_pos (Real.sqrt_pos.2 hnR) hB)).2
    (hone.trans (le_of_eq (mul_comm (Real.sqrt n * B) (matrixSingularValue V (n - 1)))))

end SegmentedVDM
