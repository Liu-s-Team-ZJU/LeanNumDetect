import General.Probability.ChernoffSamplingSlack

/-! Auxiliary weights in `[0,1]` transfer a relative lower sampling bound to
unchanged, unweighted sampling. Weight construction is a separate deterministic
result; this module proves the probabilistic transfer. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.FiniteMatrixSampling

noncomputable section

def weightedPopulation {N d : ℕ}
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) (w : Fin N → ℝ) :=
  fun k => (w k : ℂ) • X k

theorem quadratic_nonneg {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) (x : EuclideanSpace ℂ (Fin d)) :
    0 ≤ quadratic A x := by
  simpa only [quadratic, Matrix.toLpLin_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, RCLike.re_eq_complex_re] using
    hA.re_dotProduct_nonneg (ofLp x)

theorem weightedPopulation_posSemidef {N d : ℕ}
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) (w : Fin N → ℝ)
    (hX : ∀ k, (X k).PosSemidef) (hw : ∀ k, 0 ≤ w k) (k : Fin N) :
    (weightedPopulation X w k).PosSemidef := by
  exact (hX k).smul (by exact_mod_cast hw k)

theorem quadratic_mean_eq {N d : ℕ}
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (x : EuclideanSpace ℂ (Fin d)) :
    quadratic (mean X) x = (N : ℝ)⁻¹ * ∑ k, quadratic (X k) x := by
  rw [mean, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    quadratic_smul_matrix]
  congr 1
  simp only [quadratic, map_sum, LinearMap.sum_apply, inner_sum, Complex.re_sum]

theorem mean_posSemidef {N d : ℕ}
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ k, (X k).PosSemidef) : (mean X).PosSemidef := by
  have h : (∑ k, X k).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ (fun k _ => hX k)
  unfold mean
  have hv : (0 : ℂ) ≤ ((N : ℝ)⁻¹ : ℂ) := by
    exact_mod_cast (inv_nonneg.mpr (Nat.cast_nonneg N) : 0 ≤ (N : ℝ)⁻¹)
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using h.smul hv

theorem quadratic_sampleMean_eq {N d m : ℕ}
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) (Ω : Sample N m)
    (x : EuclideanSpace ℂ (Fin d)) :
    quadratic (sampleMean X Ω) x =
      (m : ℝ)⁻¹ * ∑ k ∈ Ω.val, quadratic (X k) x := by
  rw [sampleMean, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    quadratic_smul_matrix]
  congr 1
  simp only [sampleSum, quadratic, map_sum, LinearMap.sum_apply,
    inner_sum, Complex.re_sum]

theorem sampleMean_weighted_le {N d m : ℕ}
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) (w : Fin N → ℝ)
    (hX : ∀ k, (X k).PosSemidef) (hw : ∀ k, w k ≤ 1)
    (Ω : Sample N m) (x : EuclideanSpace ℂ (Fin d)) :
    quadratic (sampleMean (weightedPopulation X w) Ω) x ≤
      quadratic (sampleMean X Ω) x := by
  rw [quadratic_sampleMean_eq, quadratic_sampleMean_eq]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg m))
  apply Finset.sum_le_sum
  intro k hk
  simp only [weightedPopulation, quadratic_smul_matrix]
  exact mul_le_of_le_one_left (quadratic_nonneg (hX k) x) (hw k)

theorem mean_weighted_le {N d : ℕ}
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) (w : Fin N → ℝ)
    (hX : ∀ k, (X k).PosSemidef) (hw : ∀ k, w k ≤ 1)
    (x : EuclideanSpace ℂ (Fin d)) :
    quadratic (mean (weightedPopulation X w)) x ≤ quadratic (mean X) x := by
  rw [quadratic_mean_eq, quadratic_mean_eq]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  apply Finset.sum_le_sum
  intro k _
  simp only [weightedPopulation, quadratic_smul_matrix]
  exact mul_le_of_le_one_left (quadratic_nonneg (hX k) x) (hw k)

theorem mean_weighted_posDef {N d : ℕ} (hN : 0 < N)
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) (w : Fin N → ℝ)
    (hX : ∀ k, (X k).PosSemidef) (hw : ∀ k, 0 < w k)
    (hG : (mean X).PosDef) : (mean (weightedPopulation X w)).PosDef := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨k, _, hk⟩ := Finset.exists_min_image Finset.univ w Finset.univ_nonempty
  have hlow (x : EuclideanSpace ℂ (Fin d)) :
      w k * quadratic (mean X) x ≤ quadratic (mean (weightedPopulation X w)) x := by
    rw [quadratic_mean_eq, quadratic_mean_eq]
    rw [mul_left_comm, Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
    apply Finset.sum_le_sum
    intro j _
    rw [weightedPopulation, quadratic_smul_matrix]
    exact mul_le_mul_of_nonneg_right (hk j (Finset.mem_univ j)) (quadratic_nonneg (hX j) x)
  have hW := mean_posSemidef (weightedPopulation X w)
    (weightedPopulation_posSemidef X w hX (fun j => (hw j).le))
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hW.isHermitian
  intro x hx
  have hp := hG.re_dotProduct_pos hx
  have hl := hlow (toLp 2 x)
  have hpos : 0 < quadratic (mean (weightedPopulation X w)) (toLp 2 x) := by
    have hg : 0 < quadratic (mean X) (toLp 2 x) := by
      simpa only [quadratic, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct,
        dotProduct_comm, ofLp_toLp, RCLike.re_eq_complex_re] using hp
    exact (mul_pos (hw k) hg).trans_le hl
  have him := (RCLike.nonneg_iff.mp (hW.dotProduct_mulVec_nonneg x)).2
  apply RCLike.pos_iff.mpr
  refine ⟨?_, him⟩
  simpa only [quadratic, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct_comm, ofLp_toLp, RCLike.re_eq_complex_re] using hpos

end
end LeanNumDetect.FiniteMatrixSampling
