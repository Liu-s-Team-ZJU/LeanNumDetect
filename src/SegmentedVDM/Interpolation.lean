import General.Fourier.TrigonometricPolynomialParseval
import General.MatrixAnalysis.RowDeletion

/-! The finite-dimensional Lagrange-interpolation argument of NumDetect,
`lem:minsvd_bound_by_lagInterp_high_dim`. All Euclidean norms below are
coefficient-space quantities; the identification of the coefficient energy with
the squared normalized torus `L²` norm is the Parseval theorem
`LeanNumDetect.unitTorusL2Norm_sq_eq` of
`General.Fourier.TrigonometricPolynomialParseval`, applied in
`singularValue_inv_le_lagrangeFamily_l2` to state the manuscript's conclusion in
the genuine `L²(𝕋^d)` function-space norms. -/

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

/-- The coefficient-energy form of the minimum-singular-value bound of the
manuscript's `lem:minsvd_bound_by_lagInterp_high_dim` for a whole family of
Lagrange interpolants, together with the full column rank that the
interpolation identities force as part of the conclusion.  There is no rank
hypothesis: the interpolation identities alone imply both claims.

`C * V = 1` is the Lean form of the interpolation identities
$f_k(\mathbf y_\ell/2\pi)=\delta_{k,\ell}$ of the manuscript's
`defi:high_dim_lagrange`, with `C k` the coefficient vector of $f_k$ and `V`
the Vandermonde matrix on the same frequency and node sets.

The right-hand side is the coefficient root-sum-square
$\bigl(\sum_k \mathrm{energy}(C k)\bigr)^{1/2}$.  The manuscript states the
bound with the genuine torus $L^2$ norms
$(\sum_k \|f_k\|_{L^2(\mathbb T^d)}^2)^{1/2}$; that form is
`singularValue_inv_le_lagrangeFamily_l2`, which converts this bound through
Parseval on the unit torus $\mathbb T^d \cong [0,1)^d$ with normalized measure:
for pairwise distinct frequencies the squared $L^2$ norm of the trigonometric
polynomial $f_k = \sum_i c_{k,i} e^{2\pi i \mathbf s_i \cdot \bm\omega}$
equals its coefficient energy,
$\|f_k\|_{L^2(\mathbb T^d)}^2 = \sum_i \|c_{k,i}\|^2 =$ `energy (C k)`
(`LeanNumDetect.unitTorusL2Norm_sq_eq`).

The proof applies `interpolation_energy` to a nonzero Gram eigenvector and
`gram_eigenvector_energy` to its energy, giving
$1 \le \bigl(\sum_k \mathrm{energy}(C k)\bigr) \sigma_{\min}(\mathcal V)^2$.
This forces $\sigma_{\min}(\mathcal V) > 0$ (full column rank) and, taking
square roots, $1/\sigma_{\min}(\mathcal V) \le \bigl(\sum_k
\mathrm{energy}(C k)\bigr)^{1/2}$. -/
theorem singularValue_inv_le_lagrangeFamily_energy {ρ : Type*} [Fintype ρ] {n : ℕ}
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

/-- The minimum-singular-value bound of the manuscript's
`lem:minsvd_bound_by_lagInterp_high_dim` in the manuscript's own normalization.
Let the pairwise distinct frequency vectors $\Lambda^d$ of
`defi:high_dim_lagrange` be presented by `s : ρ → Fin d → ℤ`
(`hs : Function.Injective s` is the $\Lambda^d$-is-a-set condition), let
`V : Matrix ρ (Fin n) ℂ` be the Vandermonde matrix on those frequencies and
the nodes, and let `C * V = 1` be the interpolation identities
$f_k(\mathbf y_\ell/2\pi)=\delta_{k,\ell}$ with `C k` the coefficient vector of

$$
f_k(\bm\omega) = \sum_i C_{k,i}\, e^{2\pi i\, \mathbf s_i \cdot \bm\omega},
\qquad \bm\omega \in \mathbb T^d \cong [0,1)^d .
$$

Then, together with the full column rank forced by the interpolation
identities,

$$
\frac{1}{\sigma_{\min}(\mathcal V)}\le
\Big(\sum_{k=1}^n\|f_k\|_{L^2(\mathbb T^d)}^2\Big)^{1/2},
\qquad
\|f\|_{L^2(\mathbb T^d)}^2=\int_{\mathbb T^d}\|f(\bm\omega)\|^2\,d\bm\omega ,
$$

exactly the right-hand side of the manuscript.  The conclusion is derived from
the coefficient-energy form `singularValue_inv_le_lagrangeFamily_energy`
through the Parseval bridge `LeanNumDetect.unitTorusL2Norm_sq_eq`: for
pairwise distinct frequencies the squared normalized torus $L^2$ norm of $f_k$
is exactly `energy (C k)`, so the two root-sum-squares coincide.  Distinctness
is essential here: for presentations with repeated frequencies Parseval fails
(`LeanNumDetect.parseval_fails_of_repeated_frequencies`) and the coefficient
energy no longer equals $\|f_k\|_{L^2(\mathbb T^d)}^2$. -/
theorem singularValue_inv_le_lagrangeFamily_l2 {ρ : Type*} [Fintype ρ] {n d : ℕ}
    (s : ρ → Fin d → ℤ) (hs : Function.Injective s)
    (V : Matrix ρ (Fin n) ℂ) (C : Matrix (Fin n) ρ ℂ)
    (hCV : C * V = 1) (hn : 0 < n) :
    0 < matrixSingularValue V (n - 1) ∧
      1 / matrixSingularValue V (n - 1) ≤
        Real.sqrt (∑ k, unitTorusL2Norm (unitTorusTrigPolynomial s (C k)) ^ 2) := by
  obtain ⟨hσpos, hinv⟩ := singularValue_inv_le_lagrangeFamily_energy V C hCV hn
  refine ⟨hσpos, ?_⟩
  have hE : ∀ k : Fin n,
      unitTorusL2Norm (unitTorusTrigPolynomial s (C k)) ^ 2 = energy (C k) := by
    intro k
    rw [unitTorusL2Norm_sq_eq hs (C k)]
    rfl
  simp_rw [hE]
  exact hinv

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
  obtain ⟨hσpos, hinv⟩ := singularValue_inv_le_lagrangeFamily_energy V C hCV hn
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
