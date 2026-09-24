import NumDetect.Segmented.Polynomial
import SegmentedVDM.Interpolation
import SegmentedVDM.UniformInterpolation
import NumDetect.Segmented.NeighborFactors
import SegmentedVDM.NeighborFactors

/-! The two interpolation lemmas of Appendix B in the manuscript's polynomial notation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Evaluating the canonical polynomial at an angular node is exactly the
coefficient pairing with the manuscript's segmented Vandermonde column. -/
theorem segmentedPolynomial_angularValue_eq_vandermonde
    {d m r D n : ℕ} (P : SegmentedPolynomial d m r D)
    (node : Fin n → Point d) (j : Fin n) :
    P.angularValue (node j) =
      P.coeff ⬝ᵥ (fun a => segmentedVandermonde m r D node a j) := by
  rw [SegmentedPolynomial.angularValue_eq_angularTrigPolynomial]
  simp only [angularTrigPolynomial, dotProduct, segmentedVandermonde,
    generalizedVandermonde, steeringVector, segmentedFrequency,
    segmentedPolynomialFrequency, dot]
  apply Finset.sum_congr rfl
  intro a _
  congr 1

/-- Appendix B, `lem:minsvd_bound_by_lagInterp_high_dim`, with the actual
segmented Vandermonde matrix and the original Lagrange interpolation values. -/
theorem segmentedPolynomial_lagrange_minimumSingularValue
    {d m r D n : ℕ} (hmD : m < D) (hn : 0 < n)
    (node : Fin n → Point d)
    (F : Fin n → SegmentedPolynomial d m r D)
    (hF : SegmentedPolynomial.IsLagrangeFamily node F) :
    0 < matrixSingularValue (segmentedVandermonde m r D node) (n - 1) ∧
      1 / matrixSingularValue (segmentedVandermonde m r D node) (n - 1) ≤
        Real.sqrt (∑ k, unitTorusL2Norm (F k) ^ 2) := by
  let C : Matrix (Fin n) (SegmentedIndex d m r) ℂ := fun k a => (F k).coeff a
  have hCV : C * segmentedVandermonde m r D node = 1 := by
    ext k j
    change C k ⬝ᵥ (fun a => segmentedVandermonde m r D node a j) =
      (1 : Matrix (Fin n) (Fin n) ℂ) k j
    rw [← segmentedPolynomial_angularValue_eq_vandermonde (F k) node j]
    simpa [C, SegmentedPolynomial.IsLagrangeFamily, Matrix.one_apply] using hF k j
  have h := SegmentedVDM.singularValue_inv_le_lagrangeFamily_l2
    (segmentedPolynomialFrequency d m r D)
    (segmentedPolynomialFrequency_injective hmD)
    (segmentedVandermonde m r D node) C hCV hn
  change 0 < matrixSingularValue (segmentedVandermonde m r D node) (n - 1) ∧
    1 / matrixSingularValue (segmentedVandermonde m r D node) (n - 1) ≤
      Real.sqrt (∑ k, unitTorusL2Norm
        (unitTorusTrigPolynomial (segmentedPolynomialFrequency d m r D)
          (F k).coeff) ^ 2)
  simpa [C] using h

/-- Appendix B, `lem:interpolation_via_svd`, including its interpolation
values and both function-space norm estimates. -/
theorem segmentedPolynomial_interpolation_of_fullColumnRank
    {d m r D n : ℕ} (hmD : m < D) (_hn : 0 < n)
    (node : Fin n → Point d)
    (hfull : Function.Injective
      (segmentedVandermonde m r D node).toEuclideanLin)
    (w : Fin n → ℂ) :
    ∃ P : SegmentedPolynomial d m r D,
      (∀ j, P.angularValue (node j) = w j) ∧
      unitTorusL2Norm P ≤
        Real.sqrt (SegmentedVDM.energy w) /
          matrixSingularValue (segmentedVandermonde m r D node) (n - 1) ∧
      unitTorusLInfNorm P ≤
        Real.sqrt (((r + 1) * (m + 1)) ^ d) *
          Real.sqrt (SegmentedVDM.energy w) /
          matrixSingularValue (segmentedVandermonde m r D node) (n - 1) := by
  classical
  obtain ⟨c, hc, hL2, hLInf⟩ :=
    SegmentedVDM.interpolation_coefficients_of_fullColumnRank
      (segmentedPolynomialFrequency d m r D)
      (segmentedPolynomialFrequency_injective hmD)
      (segmentedVandermonde m r D node) hfull w
  let P : SegmentedPolynomial d m r D := ⟨hmD, c⟩
  refine ⟨P, ?_, ?_, ?_⟩
  · intro j
    rw [segmentedPolynomial_angularValue_eq_vandermonde P node j]
    have hj := hc j
    change c ⬝ᵥ (fun a => segmentedVandermonde m r D node a j) = w j at hj
    simpa [P] using hj
  · change unitTorusL2Norm
        (unitTorusTrigPolynomial (segmentedPolynomialFrequency d m r D) c) ≤ _
    simpa [Fintype.card_fin] using hL2
  · change unitTorusLInfNorm
        (unitTorusTrigPolynomial (segmentedPolynomialFrequency d m r D) c) ≤ _
    simpa [SegmentedIndex, SegmentedCoordinateIndex] using hLInf

end
end NumDetect
end LeanNumDetect

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect
noncomputable section
namespace SegmentedPolynomial

/-- Spreading coefficients over output indices does not increase their
`ℓ¹` mass, even when several inputs map to the same index. -/
private theorem spread_norm_sum_le {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    [DecidableEq ρ] (f : ι → ρ) (c : ι → ℂ) :
    (∑ a : ρ, ‖SegmentedVDM.spread f c a‖) ≤ ∑ i : ι, ‖c i‖ := by
  classical
  have happly : ∀ a : ρ, SegmentedVDM.spread f c a
      = ∑ i, c i * (if a = f i then (1 : ℂ) else 0) := by
    intro a
    show (SegmentedVDM.spread f c).ofLp a = _
    simp only [SegmentedVDM.spread, WithLp.ofLp_sum, WithLp.ofLp_smul,
      PiLp.ofLp_single, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply]
  calc
    (∑ a : ρ, ‖SegmentedVDM.spread f c a‖)
        = ∑ a : ρ, ‖∑ i, c i * (if a = f i then (1 : ℂ) else 0)‖ := by
          simp only [happly]
    _ ≤ ∑ a : ρ, ∑ i, ‖c i * (if a = f i then (1 : ℂ) else 0)‖ :=
      Finset.sum_le_sum fun a _ => norm_sum_le _ _
    _ = ∑ i : ι, ∑ a : ρ, ‖c i * (if a = f i then (1 : ℂ) else 0)‖ :=
      Finset.sum_comm
    _ = ∑ i : ι, ‖c i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      have h1 : ∀ a : ρ, ‖c i * (if a = f i then (1 : ℂ) else 0)‖
          = if a = f i then ‖c i‖ else 0 := by
        intro a
        by_cases h : a = f i
        · rw [if_pos h, if_pos h, mul_one]
        · rw [if_neg h, if_neg h, mul_zero, norm_zero]
      simp only [h1]
      rw [Finset.sum_ite_eq' Finset.univ (f i) (fun _ => ‖c i‖)]
      simp

theorem neighborSetSegmented_polynomial
    {d v M m D : ℕ} {p q : ENNReal} (hpq : ENNReal.HolderConjugate p q)
    (hv : 0 < v) (hmD : m < D)
    (u : Fin (v - 1) → Point d) (huinj : Function.Injective u)
    (hun : ∀ i, 0 < LeanNumDetect.lpNorm q (u i))
    (huro : ∀ i, LeanNumDetect.lpNorm q (u i) ≤
      Real.pi / (2 * (D : ℝ) * (d : ℝ) ^ p.toReal⁻¹))
    (hM : 2 * (d : ℝ) ^ p.toReal⁻¹ * v ≤ (M : ℝ)) :
    ∃ P : SegmentedPolynomial d m M D,
      P.angularValue 0 = 1 ∧
      (∀ i, P.angularValue (u i) = 0) ∧
      P.mass ≤ (Real.sqrt 2) ^ (v - 1) *
        ∏ i : Fin (v - 1), SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i) ∧
      unitTorusL2Norm P ≤
        ((Real.sqrt 2) ^ (v - 1) *
          ∏ i : Fin (v - 1), SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i)) /
          Real.sqrt (((M : ℝ) / v) ^ d * ((m + 1 : ℕ) : ℝ) ^ d) := by
  classical
  have hDposN : 0 < D := by omega
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hDposN
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hdim (i : Fin (v - 1)) : 0 < (d : ℝ) ^ p.toReal⁻¹ := by
    by_contra hnd
    have hz : (d : ℝ) ^ p.toReal⁻¹ = 0 :=
      le_antisymm (le_of_not_gt hnd) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    have h0 : Real.pi / (2 * (D : ℝ) * (d : ℝ) ^ p.toReal⁻¹) = 0 := by
      rw [hz, mul_zero, div_zero]
    have := huro i
    rw [h0] at this
    exact lt_irrefl 0 (lt_of_lt_of_le (hun i) this)
  have hMpos (i : Fin (v - 1)) : 0 < (M : ℝ) :=
    lt_of_lt_of_le (mul_pos (mul_pos (by norm_num) (hdim i)) hvR) hM
  set w : Fin (v - 1) → ℝ := fun i => LeanNumDetect.lpNorm q (u i) with hwdef
  set zN : ℕ := ⌊(M : ℝ) / v⌋₊ with hzNdef
  have hwpos (i : Fin (v - 1)) : 0 < w i := by rw [hwdef]; exact hun i
  have htmin (i : Fin (v - 1)) :
      min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i))
        = min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * LeanNumDetect.lpNorm q (u i))) := by
    rw [hwdef]
  have htb (i : Fin (v - 1)) : 2 * (d : ℝ) ^ p.toReal⁻¹
      ≤ min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) := by
    refine le_min ?_ ?_
    · exact (le_div_iff₀ hvR).mpr hM
    · have hA : w i * (2 * (D : ℝ) * (d : ℝ) ^ p.toReal⁻¹) ≤ Real.pi := by
        have hA0 := (le_div_iff₀
          (mul_pos (mul_pos (by norm_num) hDpos) (hdim i))).mp (huro i)
        exact hA0
      have hA' : 2 * (d : ℝ) ^ p.toReal⁻¹ * ((D : ℝ) * w i) ≤ Real.pi := by
        have he : 2 * (d : ℝ) ^ p.toReal⁻¹ * ((D : ℝ) * w i)
            = w i * (2 * (D : ℝ) * (d : ℝ) ^ p.toReal⁻¹) := by ring
        rw [he]
        exact hA
      exact (le_div_iff₀ (mul_pos hDpos (hwpos i))).2 hA'
  have hut (i : Fin (v - 1)) : w i ≤ Real.pi / ((D : ℝ) * min ((M : ℝ) / v)
      (Real.pi / ((D : ℝ) * w i))) := by
    have hA : min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) * ((D : ℝ) * w i) ≤ Real.pi :=
      (le_div_iff₀ (mul_pos hDpos (hwpos i))).mp (min_le_right _ _)
    have hA' : w i * ((D : ℝ) * min ((M : ℝ) / v)
        (Real.pi / ((D : ℝ) * w i))) ≤ Real.pi := by
      have he : w i * ((D : ℝ) * min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)))
          = min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) * ((D : ℝ) * w i) := by ring
      rw [he]
      exact hA
    have hminpos : 0 < (D : ℝ) * min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) :=
      mul_pos hDpos (lt_min_iff.mpr ⟨div_pos (hMpos i) hvR,
        div_pos Real.pi_pos (mul_pos hDpos (hwpos i))⟩)
    exact (le_div_iff₀ hminpos).2 hA'
  have hnode (i : Fin (v - 1)) : ∃ P : SegmentedPolynomial d 0 ⌊min ((M : ℝ) / v)
      (Real.pi / ((D : ℝ) * w i))⌋₊ D,
      P.angularValue 0 = 1 ∧ P.angularValue (u i) = 0 ∧
      P.mass ≤ Real.sqrt 2 * Real.pi /
        ((D : ℝ) * min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) * w i) :=
    neighborNodeFactor hpq hDposN (hdim i) (t := min ((M : ℝ) / v)
      (Real.pi / ((D : ℝ) * w i))) (htb i) (u i) (hun i) (hut i)
  choose F hF1 hF0 hFm using hnode
  have htbud (i : Fin (v - 1)) :
      ⌊min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i))⌋₊ ≤ zN := by
    apply Nat.floor_mono
    exact min_le_left _ _
  let G : Fin (v - 1) → SegmentedPolynomial d 0 zN D :=
    fun i => (F i).widen le_rfl (htbud i) hDposN
  let Q : SegmentedPolynomial d (0 * (v - 1)) (zN * (v - 1)) D :=
    SegmentedPolynomial.prod (v - 1) G (by simpa using hDposN)
  let Q0 : SegmentedPolynomial d 0 ((v - 1) * zN) D :=
    Q.widen (by simp) (by simp [Nat.mul_comm]) hDposN
  have hzNv : zN * v ≤ M := by
    have h1 : ((zN : ℕ) : ℝ) ≤ (M : ℝ) / v := by
      rw [hzNdef]
      exact Nat.floor_le (div_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg v))
    have h2 : ((zN : ℕ) : ℝ) * v ≤ (M : ℝ) := (le_div_iff₀ hvR).mp h1
    exact_mod_cast h2
  have hzsplit : (v - 1) * zN + zN = v * zN := by
    conv_rhs =>
      rw [show v = v - 1 + 1 from (Nat.sub_add_cancel (Nat.succ_le_of_lt hv)).symm,
        Nat.add_mul, one_mul]
  have hzN1 : (M : ℝ) / v ≤ zN + 1 := by
    have h := Nat.lt_floor_add_one ((M : ℝ) / v)
    rw [← hzNdef] at h
    exact h.le
  have hdenle : ((M : ℝ) / v) ^ d * ((m + 1 : ℕ) : ℝ) ^ d
      ≤ ((((zN + 1) * (m + 1)) ^ d : ℕ) : ℝ) := by
    push_cast
    rw [mul_pow]
    gcongr
  have hDnpos : 0 < ((M : ℝ) / v) ^ d * ((m + 1 : ℕ) : ℝ) ^ d := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst d
      simp
    · have hdim0 : 0 < (d : ℝ) ^ p.toReal⁻¹ :=
        Real.rpow_pos_of_pos (by exact_mod_cast hd) _
      have h1 : 0 < 2 * (d : ℝ) ^ p.toReal⁻¹ * (v : ℝ) :=
        mul_pos (mul_pos (by norm_num) hdim0) hvR
      have hMpos' : 0 < (M : ℝ) := lt_of_lt_of_le h1 hM
      have h2 : 0 < (M : ℝ) / v := div_pos hMpos' hvR
      exact mul_pos (pow_pos h2 d)
        (pow_pos (by exact_mod_cast (by omega : 0 < m + 1)) d)
  have hQ0 (x : Point d) : Q0.angularValue x = ∏ i, (F i).angularValue x := by
    simp only [Q0, Q, G, SegmentedPolynomial.angularValue_widen,
      SegmentedPolynomial.angularValue_prod]
  have hQ01 : Q0.angularValue 0 = 1 := by
    rw [hQ0]
    exact Finset.prod_eq_one fun i _ => hF1 i
  have hQz (j : Fin (v - 1)) : Q0.angularValue (u j) = 0 := by
    rw [hQ0]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact hF0 j
  let wvec : EuclideanSpace ℂ (SegmentedIndex d (0 + m) ((v - 1) * zN + zN)) :=
    SegmentedPolynomial.smoothedSegmentedVector Q0 m zN 0
  have hzLe : (v - 1) * zN + zN ≤ M := by
    rw [hzsplit, Nat.mul_comm]
    exact hzNv
  let Ppre : SegmentedPolynomial d (0 + m) ((v - 1) * zN + zN) D :=
    ⟨by simpa using hmD, fun i => ofLp wvec i⟩
  let P : SegmentedPolynomial d m M D :=
    Ppre.widen (by simp) hzLe hmD
  have hstep (x : Point d) : Q0.angularValue x *
      SegmentedPolynomial.segmentedMeanKernel d m zN D x =
      ofLp wvec ⬝ᵥ SegmentedPolynomial.segmentedSteering d (0 + m) ((v - 1) * zN + zN) D x := by
    have h := SegmentedPolynomial.smoothedSegmentedVector_evaluation Q0 m zN 0 x
    simp only [sub_zero] at h
    rw [← h]
  have hval (x : Point d) : P.angularValue x =
      Q0.angularValue x * SegmentedPolynomial.segmentedMeanKernel d m zN D x := by
    have hstep' : Ppre.angularValue x =
        ofLp wvec ⬝ᵥ SegmentedPolynomial.segmentedSteering d (0 + m) ((v - 1) * zN + zN) D x := by
      rw [SegmentedPolynomial.angularValue_eq_angularTrigPolynomial]
      simp [angularTrigPolynomial, segmentedSteering, segmentedPolynomialFrequency,
        dotProduct, Ppre]
    rw [show P.angularValue x = Ppre.angularValue x from
      SegmentedPolynomial.angularValue_widen Ppre (by simp) hzLe hmD x,
      hstep']
    exact (hstep x).symm
  have hP0 : P.angularValue 0 = 1 := by
    rw [hval, hQ01, SegmentedPolynomial.segmentedMeanKernel_zero, one_mul]
  have hPu (j : Fin (v - 1)) : P.angularValue (u j) = 0 := by
    rw [hval, hQz j, zero_mul]
  have hspreadle (i : SegmentedIndex d 0 ((v - 1) * zN)) :
      (∑ a : SegmentedIndex d (0 + m) ((v - 1) * zN + zN),
        ‖SegmentedPolynomial.segmentedAveragingVector Q0 m zN 0 i a‖) ≤ 1 := by
    refine (spread_norm_sum_le (SegmentedPolynomial.shiftedSegmentedRow Q0 m zN i) _).trans ?_
    have hexp (q : SegmentedPolynomial.SmoothingIndex d m zN) :
        ‖Complex.exp (-Complex.I * (((∑ k,
          (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) * (0 : Point d) k)) : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have hcard : Fintype.card (SegmentedPolynomial.SmoothingIndex d m zN)
        = ((zN + 1) * (m + 1)) ^ d := by
      simp [SegmentedPolynomial.SmoothingIndex, SegmentedIndex, SegmentedCoordinateIndex]
    have hsum : (∑ q : SegmentedPolynomial.SmoothingIndex d m zN,
        ‖Complex.exp (-Complex.I * (((∑ k,
          (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) * (0 : Point d) k)) : ℝ) : ℂ)) /
          (((zN + 1) * (m + 1)) ^ d : ℕ)‖) = 1 := by
      simp only [norm_div, hexp, Complex.norm_natCast, one_div]
      rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
      have hne : ((((zN + 1) * (m + 1)) ^ d : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (by positivity : (((zN + 1) * (m + 1)) ^ d : ℕ) ≠ 0)
      field_simp
    exact le_of_eq hsum
  have hmassvec : P.mass ≤ Q0.mass := by
    rw [show P.mass = Ppre.mass from SegmentedPolynomial.mass_widen Ppre (by simp) hzLe hmD]
    show (∑ a : SegmentedIndex d (0 + m) ((v - 1) * zN + zN), ‖ofLp wvec a‖) ≤ Q0.mass
    have h1 : ∀ a : SegmentedIndex d (0 + m) ((v - 1) * zN + zN),
        ‖ofLp wvec a‖ ≤ ∑ i : SegmentedIndex d 0 ((v - 1) * zN), ‖Q0.coeff i‖ *
          ‖SegmentedPolynomial.segmentedAveragingVector Q0 m zN 0 i a‖ := by
      intro a
      have hsum : ofLp wvec a = ∑ i : SegmentedIndex d 0 ((v - 1) * zN),
          Q0.coeff i • ofLp (SegmentedPolynomial.segmentedAveragingVector Q0 m zN 0 i) a := by
        show (ofLp (∑ i : SegmentedIndex d 0 ((v - 1) * zN),
            Q0.coeff i • SegmentedPolynomial.segmentedAveragingVector Q0 m zN 0 i)) a = _
        rw [WithLp.ofLp_sum, Finset.sum_apply]
        rfl
      rw [hsum]
      refine (norm_sum_le _ _).trans ?_
      exact Finset.sum_le_sum fun i _ => by
        have h := norm_smul (Q0.coeff i)
          (ofLp (SegmentedPolynomial.segmentedAveragingVector Q0 m zN 0 i) a)
        exact le_of_eq h
    calc
      (∑ a : SegmentedIndex d (0 + m) ((v - 1) * zN + zN), ‖ofLp wvec a‖)
          ≤ ∑ a, ∑ i : SegmentedIndex d 0 ((v - 1) * zN), ‖Q0.coeff i‖ *
            ‖SegmentedPolynomial.segmentedAveragingVector Q0 m zN 0 i a‖ :=
        Finset.sum_le_sum fun a _ => h1 a
      _ = ∑ i : SegmentedIndex d 0 ((v - 1) * zN), ∑ a, ‖Q0.coeff i‖ *
          ‖SegmentedPolynomial.segmentedAveragingVector Q0 m zN 0 i a‖ := Finset.sum_comm
      _ = ∑ i : SegmentedIndex d 0 ((v - 1) * zN), ‖Q0.coeff i‖ *
          ∑ a, ‖SegmentedPolynomial.segmentedAveragingVector Q0 m zN 0 i a‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.mul_sum]
      _ ≤ ∑ i : SegmentedIndex d 0 ((v - 1) * zN), ‖Q0.coeff i‖ * 1 :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hspreadle i) (norm_nonneg _)
      _ = Q0.mass := by simp [SegmentedPolynomial.mass]
  have hL2 : unitTorusL2Norm P = ‖wvec‖ := by
    rw [show unitTorusL2Norm P = unitTorusL2Norm Ppre from
      SegmentedPolynomial.l2Norm_widen Ppre (by simp) hzLe hmD]
    change unitTorusL2Norm
      (unitTorusTrigPolynomial
        (segmentedPolynomialFrequency d (0 + m) ((v - 1) * zN + zN) D)
        Ppre.coeff) = ‖wvec‖
    rw [unitTorusL2Norm_eq_sqrt Ppre.frequency_injective Ppre.coeff]
    change Real.sqrt (∑ i, ‖ofLp wvec i‖ ^ 2) = ‖wvec‖
    rw [← EuclideanSpace.norm_sq_eq, Real.sqrt_sq (norm_nonneg wvec)]
  have hnSF (i : Fin (v - 1)) :
      0 ≤ SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i) := by
    unfold SegmentedVDM.neighborScaleFactor
    split_ifs with h
    · exact div_nonneg (by positivity)
        (mul_nonneg (mul_nonneg (hMpos i).le hDpos.le) (hun i).le)
    · exact zero_le_one
  have hfac (i : Fin (v - 1)) :
      Real.sqrt 2 * Real.pi /
        ((D : ℝ) * min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) * w i)
        = Real.sqrt 2 * SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i) := by
    have hMDpos : 0 < (M : ℝ) * (D : ℝ) := mul_pos (hMpos i) hDpos
    have hminpos : 0 < min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) :=
      lt_min_iff.mpr ⟨div_pos (hMpos i) hvR, div_pos Real.pi_pos (mul_pos hDpos (hwpos i))⟩
    by_cases h : LeanNumDetect.lpNorm q (u i) ≤ Real.pi * (v : ℝ) / ((M : ℝ) * (D : ℝ))
    · rw [SegmentedVDM.neighborScaleFactor_of_le h]
      have h1 : min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) = (M : ℝ) / v := by
        refine min_eq_left ((le_div_iff₀ (mul_pos hDpos (hwpos i))).2 ?_)
        have h2 : w i * ((M : ℝ) * (D : ℝ)) ≤ Real.pi * (v : ℝ) :=
          (le_div_iff₀ hMDpos).mp h
        have h3 : ((M : ℝ) / v) * ((D : ℝ) * w i) = w i * ((M : ℝ) * (D : ℝ)) / v := by ring
        rw [h3]
        have h4 : w i * ((M : ℝ) * (D : ℝ)) / v ≤ (Real.pi * (v : ℝ)) / v :=
          div_le_div_of_nonneg_right h2 (Nat.cast_nonneg v)
        have h5 : (Real.pi * (v : ℝ)) / v = Real.pi := mul_div_cancel_right₀ _ hvR.ne'
        rwa [h5] at h4
      rw [h1, show w i = LeanNumDetect.lpNorm q (u i) from rfl]
      field_simp [(hwpos i).ne', hDpos.ne', hvR.ne', (hMpos i).ne']
    · rw [SegmentedVDM.neighborScaleFactor_of_lt (lt_of_not_ge h)]
      have h1 : min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i))
          = Real.pi / ((D : ℝ) * w i) := by
        apply min_eq_right
        have h2 : Real.pi * (v : ℝ) < w i * ((M : ℝ) * (D : ℝ)) :=
          (div_lt_iff₀ hMDpos).mp (lt_of_not_ge h)
        have h3 : Real.pi ≤ ((M : ℝ) / v) * ((D : ℝ) * w i) := by
          have h4 : Real.pi = Real.pi * (v : ℝ) / v := (mul_div_cancel_right₀ _ hvR.ne').symm
          rw [h4]
          have h5 : (Real.pi * (v : ℝ)) / v ≤ w i * ((M : ℝ) * (D : ℝ)) / v :=
            div_le_div_of_nonneg_right h2.le (Nat.cast_nonneg v)
          have h6 : w i * ((M : ℝ) * (D : ℝ)) / v = ((M : ℝ) / v) * ((D : ℝ) * w i) := by ring
          rwa [h6] at h5
        exact (div_le_iff₀ (mul_pos hDpos (hwpos i))).2 h3
      rw [h1]
      field_simp [(hwpos i).ne', hDpos.ne']
  have hBpos : 0 ≤ (Real.sqrt 2) ^ (v - 1) *
      ∏ i : Fin (v - 1), SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i) :=
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) _) (Finset.prod_nonneg fun i _ => hnSF i)
  have hprod : Q0.mass ≤ (Real.sqrt 2) ^ (v - 1) *
      ∏ i : Fin (v - 1), SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i) := by
    have hmassQ : Q0.mass ≤ ∏ i : Fin (v - 1), (F i).mass := by
      calc
        Q0.mass = Q.mass := SegmentedPolynomial.mass_widen Q (by simp)
          (by simp [Nat.mul_comm]) hDposN
        _ ≤ ∏ i : Fin (v - 1), (G i).mass :=
          SegmentedPolynomial.mass_prod_le G (by simpa using hDposN)
        _ = ∏ i : Fin (v - 1), (F i).mass := by
          apply Finset.prod_congr rfl
          intro i _
          exact SegmentedPolynomial.mass_widen (F i) le_rfl (htbud i) hDposN
    calc
      Q0.mass ≤ ∏ i : Fin (v - 1), (F i).mass := hmassQ
      _ ≤ ∏ i : Fin (v - 1), Real.sqrt 2 * Real.pi /
          ((D : ℝ) * min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) * w i) :=
        Finset.prod_le_prod (fun i _ => (F i).mass_nonneg) (fun i _ => hFm i)
      _ = ∏ i : Fin (v - 1), Real.sqrt 2 *
          SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i) :=
        Finset.prod_congr rfl fun i _ => hfac i
      _ = (Real.sqrt 2) ^ (v - 1) *
          ∏ i : Fin (v - 1), SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hnorm : unitTorusL2Norm P ≤
      ((Real.sqrt 2) ^ (v - 1) *
        ∏ i : Fin (v - 1), SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i)) /
        Real.sqrt (((M : ℝ) / v) ^ d * ((m + 1 : ℕ) : ℝ) ^ d) := by
    have h1 : ‖wvec‖ ≤ Q0.mass / Real.sqrt ((((zN + 1) * (m + 1)) ^ d : ℕ) : ℝ) :=
      SegmentedPolynomial.smoothedSegmentedVector_norm_le Q0 m zN 0
    have h2 : Real.sqrt (((M : ℝ) / v) ^ d * ((m + 1 : ℕ) : ℝ) ^ d)
        ≤ Real.sqrt ((((zN + 1) * (m + 1)) ^ d : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt hdenle
    rw [hL2]
    calc
      ‖wvec‖ ≤ Q0.mass / Real.sqrt ((((zN + 1) * (m + 1)) ^ d : ℕ) : ℝ) := h1
      _ ≤ ((Real.sqrt 2) ^ (v - 1) *
          ∏ i : Fin (v - 1), SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i)) /
          Real.sqrt ((((zN + 1) * (m + 1)) ^ d : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hprod (Real.sqrt_nonneg _)
      _ ≤ ((Real.sqrt 2) ^ (v - 1) *
          ∏ i : Fin (v - 1), SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i)) /
          Real.sqrt (((M : ℝ) / v) ^ d * ((m + 1 : ℕ) : ℝ) ^ d) :=
        div_le_div_of_nonneg_left hBpos (Real.sqrt_pos.mpr hDnpos) h2
  refine ⟨P, hP0, hPu, hmassvec.trans hprod, ?_⟩
  exact hnorm

end SegmentedPolynomial
end
end NumDetect
end LeanNumDetect

/-!
The finite-set statement of Appendix B, `lem:neighborset_segmented`.  The
construction theorem uses a one-to-one enumeration of the nonzero neighbors;
this wrapper exposes the manuscript's finite set containing the origin and its
product over the neighbors satisfying the short-distance condition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Replace an enumeration of a finite set with the product over the set. -/
private theorem prod_fin_erase_eq_prod
    {α : Type*} [DecidableEq α] (U : Finset α) (zero : α)
    (e : Fin (U.card - 1) ≃ ↥(U.erase zero)) (f : α → ℝ) :
    (∏ i : Fin (U.card - 1), f (e i).val) =
      ∏ z ∈ U.erase zero, f z := by
  calc
    _ = ∏ z : ↥(U.erase zero), f z :=
      Fintype.prod_equiv e _ _ (fun _ => rfl)
    _ = _ := Finset.prod_coe_sort (U.erase zero) f

/-- Appendix B, `lem:neighborset_segmented`, with the paper's finite set
`U`, its cardinality `v = |U|`, and its product over the short nonzero nodes. -/
theorem neighborSetSegmented_polynomial_finiteSet
    {d M D m : ℕ} {p q : ENNReal}
    (hpq : ENNReal.HolderConjugate p q) (hmD : m < D)
    (U : Finset (Point d)) (hzero : 0 ∈ U)
    (_hshortest : ∀ z ∈ U, ∀ j, z j ∈ Set.Ioc (-Real.pi) Real.pi)
    (hshort : ∀ z ∈ U,
      LeanNumDetect.lpNorm q z ≤
        Real.pi / (2 * (D : ℝ) * (d : ℝ) ^ p.toReal⁻¹))
    (hM : 2 * (d : ℝ) ^ p.toReal⁻¹ * (U.card : ℝ) ≤ (M : ℝ)) :
    ∃ P : SegmentedPolynomial d m M D,
      P (0 : Point d) = 1 ∧
      (∀ z ∈ U, z ≠ 0 →
        P (fun j => z j / (2 * Real.pi)) = 0) ∧
      unitTorusL2Norm P ≤
        ((Real.sqrt 2) ^ (U.card - 1) *
          ∏ z ∈ U.filter (fun z =>
            z ≠ 0 ∧ LeanNumDetect.lpNorm q z ≤
              Real.pi * (U.card : ℝ) / ((M : ℝ) * (D : ℝ))),
            Real.pi * (U.card : ℝ) /
              ((M : ℝ) * (D : ℝ) * LeanNumDetect.lpNorm q z)) /
          Real.sqrt (((M : ℝ) / (U.card : ℝ)) ^ d *
            (((m + 1 : ℕ) : ℝ)) ^ d) := by
  classical
  have hv : 0 < U.card := Finset.card_pos.mpr ⟨0, hzero⟩
  have hcard : Fintype.card ↥(U.erase 0) = U.card - 1 := by
    simpa only [Fintype.card_coe] using Finset.card_erase_of_mem hzero
  let e : Fin (U.card - 1) ≃ ↥(U.erase 0) :=
    (Fintype.equivFinOfCardEq hcard).symm
  let u : Fin (U.card - 1) → Point d := fun i => (e i).val
  have huinj : Function.Injective u := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have hun (i : Fin (U.card - 1)) :
      0 < LeanNumDetect.lpNorm q (u i) := by
    by_contra hn
    have hnormzero : LeanNumDetect.lpNorm q (u i) = 0 :=
      le_antisymm (le_of_not_gt hn) (LeanNumDetect.lpNorm_nonneg q (u i))
    have heq : u i = 0 := by
      funext j
      have hj := LeanNumDetect.lpNorm_apply_le
        (holderConjugate_ne_zero hpq).2 (u i) j
      rw [hnormzero] at hj
      exact abs_eq_zero.mp (le_antisymm hj (abs_nonneg _))
    have hne : u i ≠ 0 := (Finset.mem_erase.mp (e i).property).1
    exact hne heq
  have huro (i : Fin (U.card - 1)) :
      LeanNumDetect.lpNorm q (u i) ≤
        Real.pi / (2 * (D : ℝ) * (d : ℝ) ^ p.toReal⁻¹) :=
    hshort (u i) (Finset.mem_erase.mp (e i).property).2
  obtain ⟨P, hone, hvan, _hmass, hL2⟩ :=
    SegmentedPolynomial.neighborSetSegmented_polynomial
      hpq hv hmD u huinj hun huro hM
  have hprod₁ :
      (∏ i : Fin (U.card - 1),
        SegmentedVDM.neighborScaleFactor q (U.card : ℝ) (M : ℝ) (D : ℝ) (u i)) =
      ∏ z ∈ U.erase 0,
        SegmentedVDM.neighborScaleFactor q (U.card : ℝ) (M : ℝ) (D : ℝ) z := by
    exact prod_fin_erase_eq_prod U (0 : Point d) e
      (fun z => SegmentedVDM.neighborScaleFactor q (U.card : ℝ) (M : ℝ) (D : ℝ) z)
  have hprod₂ :
      (∏ z ∈ U.erase 0,
        SegmentedVDM.neighborScaleFactor q (U.card : ℝ) (M : ℝ) (D : ℝ) z) =
      ∏ z ∈ U.filter (fun z =>
        z ≠ 0 ∧ LeanNumDetect.lpNorm q z ≤
          Real.pi * (U.card : ℝ) / ((M : ℝ) * (D : ℝ))),
        Real.pi * (U.card : ℝ) /
          ((M : ℝ) * (D : ℝ) * LeanNumDetect.lpNorm q z) := by
    let near (z : Point d) : Prop :=
      LeanNumDetect.lpNorm q z ≤
        Real.pi * (U.card : ℝ) / ((M : ℝ) * (D : ℝ))
    let ratio (z : Point d) : ℝ :=
      Real.pi * (U.card : ℝ) /
        ((M : ℝ) * (D : ℝ) * LeanNumDetect.lpNorm q z)
    have hfilter : (U.erase 0).filter near =
        U.filter (fun z => z ≠ 0 ∧ near z) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_erase]
      tauto
    calc
      _ = ∏ z ∈ U.erase 0, if near z then ratio z else 1 := by
        apply Finset.prod_congr rfl
        intro z _
        rfl
      _ = ∏ z ∈ (U.erase 0).filter near, ratio z :=
        (Finset.prod_filter near ratio).symm
      _ = _ := by rw [hfilter]
  refine ⟨P, ?_, ?_, ?_⟩
  · change P (fun _ : Fin d => (0 : ℝ)) = 1
    simpa [SegmentedPolynomial.angularValue] using hone
  · intro z hz hz0
    have hzmem : z ∈ U.erase 0 := Finset.mem_erase.mpr ⟨hz0, hz⟩
    let iz : Fin (U.card - 1) := e.symm ⟨z, hzmem⟩
    have hiz : u iz = z := by simp [u, iz]
    simpa [SegmentedPolynomial.angularValue, hiz] using hvan iz
  · simpa only [hprod₁, hprod₂] using hL2

end
end NumDetect
end LeanNumDetect
