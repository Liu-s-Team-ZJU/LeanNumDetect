import RandSamp.LeverageSampling
import RandSamp.MultiClumpModel
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A short clump has a unit coefficient vector annihilating its low moments.
Its Fourier signal consists only of the exponential Taylor remainder. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect.RandSamp

noncomputable section

/-- The first `q-1` moments of a `q`-source clump. -/
def clumpMomentMatrix {q : ℕ} (offset : Fin q → ℝ) :
    Matrix (Fin (q - 1)) (Fin q) ℂ := fun k j => (offset j : ℂ) ^ k.val

theorem exists_unit_clump_moment_kernel {q : ℕ} (hq : 1 ≤ q)
    (offset : Fin q → ℝ) :
    ∃ u : EuclideanSpace ℂ (Fin q), ‖u‖ = 1 ∧
      ∀ k : Fin (q - 1), ∑ j, (offset j : ℂ) ^ k.val * ofLp u j = 0 := by
  let T := (clumpMomentMatrix offset).toEuclideanLin
  have hker : T.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    simpa using (Nat.sub_lt (by omega : 0 < q) Nat.zero_lt_one))
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let u := (‖v‖⁻¹ : ℂ) • v
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hv0
  have hTu : T u = 0 := by
    rw [map_smul, LinearMap.mem_ker.mp hv, smul_zero]
  refine ⟨u, hu, ?_⟩
  intro k
  have h := congrArg (fun w : EuclideanSpace ℂ (Fin (q - 1)) => ofLp w k) hTu
  change (∑ j, (offset j : ℂ) ^ k.val * ofLp u j) = 0 at h
  exact h

theorem exponential_short_remainder_bound {r : ℕ} (hr : 0 < r)
    (t : ℂ) {B : ℝ} (_hB : 0 ≤ B) (ht : ‖t‖ ≤ 1) (htB : ‖t‖ ≤ B) :
    ‖Complex.exp t - ∑ k ∈ Finset.range r, t ^ k / (k.factorial : ℂ)‖ ≤
      2 / (r.factorial : ℝ) * B ^ r := by
  have hcoef : (r.succ : ℝ) * (((r.factorial * r : ℕ) : ℝ)⁻¹) ≤
      2 / (r.factorial : ℝ) := by
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hf : (0 : ℝ) < r.factorial := by positivity
    have hrp : (0 : ℝ) < r := by exact_mod_cast hr
    simp only [Nat.cast_mul, Nat.cast_succ]
    field_simp
    nlinarith
  calc
    ‖Complex.exp t - ∑ k ∈ Finset.range r, t ^ k / (k.factorial : ℂ)‖ ≤
        ‖t‖ ^ r * ((r.succ : ℝ) * (((r.factorial * r : ℕ) : ℝ)⁻¹)) := by
      simpa only [Nat.cast_mul] using Complex.exp_bound ht hr
    _ ≤
        ‖t‖ ^ r * (2 / (r.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hcoef (pow_nonneg (norm_nonneg _) _)
    _ ≤ B ^ r * (2 / (r.factorial : ℝ)) := by gcongr
    _ = 2 / (r.factorial : ℝ) * B ^ r := by ring

theorem clump_low_taylor_action_zero {q : ℕ} (offset : Fin q → ℝ)
    (u : EuclideanSpace ℂ (Fin q))
    (hu : ∀ k : Fin (q - 1), ∑ j, (offset j : ℂ) ^ k.val * ofLp u j = 0)
    (frequency : ℝ) :
    ∑ j, (∑ k ∈ Finset.range (q - 1),
      (Complex.I * ((frequency * offset j : ℝ) : ℂ)) ^ k /
        (k.factorial : ℂ)) * ofLp u j = 0 := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  have hmom := hu ⟨k, Finset.mem_range.mp hk⟩
  have he (j : Fin q) :
      (Complex.I * ((frequency * offset j : ℝ) : ℂ)) ^ k /
          (k.factorial : ℂ) * ofLp u j =
        ((Complex.I * (frequency : ℂ)) ^ k / (k.factorial : ℂ)) *
          ((offset j : ℂ) ^ k * ofLp u j) := by
    push_cast
    rw [show Complex.I * ((frequency : ℂ) * (offset j : ℂ)) =
        (Complex.I * (frequency : ℂ)) * (offset j : ℂ) by ring, mul_pow]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, hmom, mul_zero]

/-- A clump of `q` short real offsets has a unit Fourier coefficient vector
whose full sampled energy is of order `(M B)^(2(q-1))`. The radius `B` need
not itself be small; the actual offsets obey the shortness hypothesis. -/
theorem exists_unit_short_clump_fourier_upper {M q : ℕ} (hq : 2 ≤ q)
    (offset : Fin q → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hoffset : ∀ j, |offset j| ≤ B)
    (hshort : ∀ j, (M : ℝ) * |offset j| ≤ 1) :
    ∃ u : EuclideanSpace ℂ (Fin q), ‖u‖ = 1 ∧
      ‖(fullVandermonde M offset).toEuclideanLin u‖ ≤
        (2 * Real.sqrt (q : ℝ) / ((q - 1).factorial : ℝ)) *
          ((M : ℝ) * B) ^ (q - 1) := by
  obtain ⟨u, hunorm, humom⟩ := exists_unit_clump_moment_kernel (by omega) offset
  let E := 2 / ((q - 1).factorial : ℝ) * ((M : ℝ) * B) ^ (q - 1)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hL1 : (∑ j, ‖ofLp u j‖) ^ 2 ≤ (q : ℝ) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin q => (1 : ℝ))
      (fun j => ‖ofLp u j‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, ← EuclideanSpace.norm_sq_eq, hunorm] at h
    simpa using h
  have hrow (k : Fin (M + 1)) :
      fourierRowEnergy offset k.val (ofLp u) ≤ (q : ℝ) * E ^ 2 := by
    let t := fun j : Fin q => Complex.I * ((((k.val : ℝ) * offset j : ℝ) : ℂ))
    let low := fun j : Fin q => ∑ s ∈ Finset.range (q - 1),
      t j ^ s / (s.factorial : ℂ)
    let rem := fun j : Fin q => Complex.exp (t j) - low j
    have hk : (k.val : ℝ) ≤ M := by exact_mod_cast Nat.le_of_lt_succ k.isLt
    have hrem (j : Fin q) : ‖rem j‖ ≤ E := by
      have htnorm : ‖t j‖ = (k.val : ℝ) * |offset j| := by simp [t]
      apply exponential_short_remainder_bound (by omega : 0 < q - 1) (t j)
        (mul_nonneg (Nat.cast_nonneg M) hB)
      · rw [htnorm]
        exact (mul_le_mul_of_nonneg_right hk (abs_nonneg _)).trans (hshort j)
      · rw [htnorm]
        exact mul_le_mul hk (hoffset j) (abs_nonneg _) (Nat.cast_nonneg M)
    have hlow : ∑ j, low j * ofLp u j = 0 :=
      clump_low_taylor_action_zero offset u humom k.val
    have hroweq : ∑ j, fourierRow offset k.val j * ofLp u j =
        ∑ j, rem j * ofLp u j := by
      dsimp [rem]
      simp only [sub_mul, Finset.sum_sub_distrib, hlow, sub_zero]
      rfl
    have hnorm : ‖∑ j, rem j * ofLp u j‖ ≤ E * ∑ j, ‖ofLp u j‖ := by
      calc
        _ ≤ ∑ j, ‖rem j * ofLp u j‖ := norm_sum_le _ _
        _ = ∑ j, ‖rem j‖ * ‖ofLp u j‖ := by simp only [norm_mul]
        _ ≤ ∑ j, E * ‖ofLp u j‖ :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hrem j) (norm_nonneg _)
        _ = _ := (Finset.mul_sum _ _ _).symm
    rw [fourierRowEnergy, hroweq]
    calc
      _ ≤ (E * ∑ j, ‖ofLp u j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = E ^ 2 * (∑ j, ‖ofLp u j‖) ^ 2 := mul_pow _ _ _
      _ ≤ E ^ 2 * (q : ℝ) := mul_le_mul_of_nonneg_left hL1 (sq_nonneg _)
      _ = _ := by ring
  refine ⟨u, hunorm, ?_⟩
  have hsq : ‖(fullVandermonde M offset).toEuclideanLin u‖ ^ 2 ≤
      (q : ℝ) * E ^ 2 := by
    rw [fullVandermonde_energy, fullGram, quadratic_fourier_mean]
    calc
      _ ≤ ((M + 1 : ℕ) : ℝ)⁻¹ * ∑ _k : Fin (M + 1), (q : ℝ) * E ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hrow k) (by positivity)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have hbound : ‖(fullVandermonde M offset).toEuclideanLin u‖ ≤
      Real.sqrt (q : ℝ) * E := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) hE)).1
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
    exact hsq
  convert hbound using 1
  dsimp [E]
  ring

theorem short_clump_fullVandermonde_minSingularValue_upper {M q : ℕ} (hq : 2 ≤ q)
    (offset : Fin q → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hoffset : ∀ j, |offset j| ≤ B)
    (hshort : ∀ j, (M : ℝ) * |offset j| ≤ 1) :
    matrixSingularValue (fullVandermonde M offset) (q - 1) ≤
      (2 * Real.sqrt (q : ℝ) / ((q - 1).factorial : ℝ)) *
        ((M : ℝ) * B) ^ (q - 1) := by
  obtain ⟨u, hunorm, hubound⟩ := exists_unit_short_clump_fourier_upper
    hq offset hB hoffset hshort
  have h := lastMatrixSingularValue_mul_norm_le (fullVandermonde M offset)
    (by simp; omega) u
  simpa only [Fintype.card_fin, hunorm, mul_one] using h.trans hubound

/-- Extending a coefficient vector by zero along an injective column map
preserves its norm and its Fourier signal. -/
theorem exists_column_embedding_vector {M n q : ℕ} (Y : Fin n → ℝ)
    (e : Fin q → Fin n) (he : Function.Injective e)
    (u : EuclideanSpace ℂ (Fin q)) :
    ∃ w : EuclideanSpace ℂ (Fin n), ‖w‖ = ‖u‖ ∧
      (fullVandermonde M Y).toEuclideanLin w =
        (fullVandermonde M (Y ∘ e)).toEuclideanLin u := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  let w := ∑ j, ofLp u j • b (e j)
  have hv : Orthonormal ℂ (b ∘ e) := b.orthonormal.comp e he
  have hinner : ⟪w, w⟫_ℂ = ∑ j, star (ofLp u j) * ofLp u j := by
    simpa [w, Function.comp_apply, Complex.star_def] using
      hv.inner_sum (ofLp u) (ofLp u) Finset.univ
  have hnorm : ‖w‖ = ‖u‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) w, hinner,
      ← inner_self_eq_norm_sq (𝕜 := ℂ) u,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  refine ⟨w, hnorm, ?_⟩
  ext k
  change ((fullVandermonde M Y) *ᵥ ofLp w) k =
    ((fullVandermonde M (Y ∘ e)) *ᵥ ofLp u) k
  dsimp [w]
  simp only [ofLp_sum, ofLp_smul, Matrix.mulVec_sum, Matrix.mulVec_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [b, EuclideanSpace.basisFun_apply, EuclideanSpace.single,
    PiLp.ofLp_single, Matrix.mulVec_single_one, Matrix.col_apply]
  simp only [Matrix.mulVec, dotProduct, fullVandermonde]
  apply Finset.sum_congr rfl
  intro j _
  simp [fourierRow, Function.comp_apply, mul_comm, mul_assoc]

/-- The least singular value of the complete source matrix is bounded by
any unit signal supported on an injectively indexed subclump. -/
theorem fullVandermonde_minSingularValue_le_subclump_signal {M n q : ℕ}
    (hn : 0 < n) (Y : Fin n → ℝ) (e : Fin q → Fin n)
    (he : Function.Injective e) (u : EuclideanSpace ℂ (Fin q)) (hu : ‖u‖ = 1) :
    matrixSingularValue (fullVandermonde M Y) (n - 1) ≤
      ‖(fullVandermonde M (Y ∘ e)).toEuclideanLin u‖ := by
  obtain ⟨w, hwnorm, hw⟩ := exists_column_embedding_vector Y e he u
  have h := lastMatrixSingularValue_mul_norm_le (fullVandermonde M Y)
    (by simpa using hn) w
  rw [hw] at h
  simpa only [Fintype.card_fin, hwnorm, hu, mul_one] using h

theorem fourierRow_phase_of_lifts {q : ℕ} (Y offset : Fin q → ℝ)
    (center : ℝ) (p : Fin q → ℤ)
    (hrep : ∀ j, Y j = offset j + center + 2 * Real.pi * p j)
    (k : ℕ) (j : Fin q) :
    fourierRow Y k j =
      Complex.exp (Complex.I * ((((k : ℝ) * center : ℝ) : ℂ))) *
        fourierRow offset k j := by
  unfold fourierRow
  rw [← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨(k : ℤ) * p j, ?_⟩
  rw [hrep j]
  push_cast
  ring

/-- Independent integral turns and a common center affect Fourier row
actions only by unit-modulus phases. -/
theorem fullVandermonde_norm_of_lifts {M q : ℕ} (Y offset : Fin q → ℝ)
    (center : ℝ) (p : Fin q → ℤ)
    (hrep : ∀ j, Y j = offset j + center + 2 * Real.pi * p j)
    (u : EuclideanSpace ℂ (Fin q)) :
    ‖(fullVandermonde M Y).toEuclideanLin u‖ =
      ‖(fullVandermonde M offset).toEuclideanLin u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro k _
  change ‖∑ j, (Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
    fourierRow Y k.val j * ofLp u j‖ ^ 2 =
      ‖∑ j, (Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        fourierRow offset k.val j * ofLp u j‖ ^ 2
  simp_rw [fourierRow_phase_of_lifts Y offset center p hrep]
  have he (j : Fin q) : (Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
      (Complex.exp (Complex.I * ((((k.val : ℝ) * center : ℝ) : ℂ))) *
        fourierRow offset k.val j) * ofLp u j =
      Complex.exp (Complex.I * ((((k.val : ℝ) * center : ℝ) : ℂ))) *
        ((Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
          fourierRow offset k.val j * ofLp u j) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum, norm_mul]
  have hp : ‖Complex.exp (Complex.I * ((((k.val : ℝ) * center : ℝ) : ℂ)))‖ = 1 := by
    simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I ((k.val : ℝ) * center)
  rw [hp, one_mul]

/-- A short, injectively indexed subclump supplies the desired upper bound
for the minimum singular value of the entire full matrix. -/
theorem fullVandermonde_minSingularValue_upper_of_lifted_subclump {M n q : ℕ}
    (hn : 0 < n) (hq : 2 ≤ q) (Y : Fin n → ℝ)
    (e : Fin q → Fin n) (he : Function.Injective e)
    (offset : Fin q → ℝ) (center : ℝ) (p : Fin q → ℤ)
    (hrep : ∀ j, Y (e j) = offset j + center + 2 * Real.pi * p j)
    {B : ℝ} (hB : 0 ≤ B) (hoffset : ∀ j, |offset j| ≤ B)
    (hshort : ∀ j, (M : ℝ) * |offset j| ≤ 1) :
    matrixSingularValue (fullVandermonde M Y) (n - 1) ≤
      (2 * Real.sqrt (q : ℝ) / ((q - 1).factorial : ℝ)) *
        ((M : ℝ) * B) ^ (q - 1) := by
  obtain ⟨u, hunorm, hubound⟩ := exists_unit_short_clump_fourier_upper
    hq offset hB hoffset hshort
  apply (fullVandermonde_minSingularValue_le_subclump_signal hn Y e he u hunorm).trans
  rw [fullVandermonde_norm_of_lifts (Y ∘ e) offset center p hrep]
  exact hubound

/-- The maximal clump supplies a minimum-singular-value upper bound with the
exponent `nstar-1`. It uses exactly the angular diameter and comparable-spacing
hypotheses of the multiclump theorem. -/
theorem multiclump_fullVandermonde_minSingularValue_upper {M n A nstar : ℕ}
    (hn : 0 < n) (hnstar : 2 ≤ nstar) (hM : 1 ≤ M)
    (Y : Fin n → ℝ) (P : ClumpPartition n A)
    (hmax : HasMaxClumpSize P nstar) {c0 C0 Δ K : ℝ}
    (hc0 : c0 < 1) (hgeometry : MultiClumpGeometry M c0 C0 Y P)
    (hΔ : 0 < Δ) (hK : 1 ≤ K) (hspacing : ComparableClumpSpacing P Y Δ K) :
    matrixSingularValue (fullVandermonde M Y) (n - 1) ≤
      (2 * Real.sqrt (nstar : ℝ) * K ^ (nstar - 1) /
        ((nstar - 1).factorial : ℝ)) * ((M : ℝ) * Δ) ^ (nstar - 1) := by
  classical
  obtain ⟨a, ha⟩ := hmax.2
  let eQ : Fin nstar ≃ ↥(P.members a) := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin, Fintype.card_coe, ClumpPartition.size] using ha.symm)
  let e : Fin nstar → Fin n := fun j => (eQ j).val
  have he : Function.Injective e := Subtype.val_injective.comp eQ.injective
  have hlabel (j : Fin nstar) : P.label (e j) = a :=
    (P.mem_members a (e j)).1 (eQ j).property
  let j0 : Fin nstar := ⟨0, by omega⟩
  have hwind (j : Fin nstar) := angularTorusDistance_eq_winding (Y (e j)) (Y (e j0))
  choose p hp using hwind
  let offset : Fin nstar → ℝ := fun j => Y (e j) - Y (e j0) + 2 * Real.pi * p j
  have hrep (j : Fin nstar) :
      Y (e j) = offset j + Y (e j0) + 2 * Real.pi * ((-p j : ℤ) : ℝ) := by
    dsimp [offset]
    push_cast
    ring
  have hB : 0 ≤ K * Δ := mul_nonneg (by linarith) hΔ.le
  have hoffset (j : Fin nstar) : |offset j| ≤ K * Δ := by
    rw [← hp j]
    by_cases hij : e j = e j0
    · rw [hij, angularTorusDistance_self]
      exact hB
    · exact (hspacing (e j) (e j0) hij (by rw [hlabel, hlabel])).2
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hshort (j : Fin nstar) : (M : ℝ) * |offset j| ≤ 1 := by
    have hwithin := hgeometry.within (e j) (e j0) (by rw [hlabel, hlabel])
    rw [hp j] at hwithin
    have h := mul_le_mul_of_nonneg_left hwithin hMp.le
    have heq : (M : ℝ) * (c0 / (M : ℝ)) = c0 := by field_simp
    exact (h.trans_eq heq).trans hc0.le
  have hupper := fullVandermonde_minSingularValue_upper_of_lifted_subclump
    hn hnstar Y e he offset (Y (e j0)) (fun j => -p j) hrep hB hoffset hshort
  convert hupper using 1
  rw [show (M : ℝ) * (K * Δ) = K * ((M : ℝ) * Δ) by ring, mul_pow]
  ring

end

end LeanNumDetect.RandSamp
