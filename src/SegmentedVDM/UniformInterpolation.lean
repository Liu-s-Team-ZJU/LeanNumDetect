import SegmentedVDM.Interpolation

/-! Minimum-norm interpolation from a lower frame bound. This is a direct
finite-dimensional proof of the part of NumDetect `lem:interpolation_via_svd`
used to construct localization factors. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix LeanNumDetect
open scoped BigOperators ComplexOrder

namespace SegmentedVDM

theorem gram_posDef_of_frame {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (V : Matrix ρ ι ℂ) {a : ℝ} (ha : 0 < a)
    (hframe : ∀ v, a * energy v ≤ energy (V *ᵥ v)) : (Vᴴ * V).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_conjTranspose_mul_self _, ?_⟩
  intro v hv
  apply RCLike.pos_iff.mpr
  constructor
  · change 0 < quadratic (Vᴴ * V) v
    rw [quadratic_gram]
    exact (mul_pos ha (energy_pos v hv)).trans_le (hframe v)
  · exact (isHermitian_conjTranspose_mul_self V).im_star_dotProduct_mulVec_self v

/-- A cardinal interpolant with coefficient energy at most `1/a`. -/
theorem cardinal_coefficients_of_frame {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    [DecidableEq ι] (V : Matrix ρ ι ℂ) {a : ℝ} (ha : 0 < a)
    (hframe : ∀ v, a * energy v ≤ energy (V *ᵥ v)) (j : ι) :
    ∃ c : ρ → ℂ, (∀ k, c ⬝ᵥ Vᵀ k = if j = k then 1 else 0) ∧ energy c ≤ 1 / a := by
  classical
  let G := Vᴴ * V
  have hG : G.PosDef := gram_posDef_of_frame V ha hframe
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
  let e : ι → ℂ := Pi.single j 1
  let w : ι → ℂ := G⁻¹ *ᵥ e
  have hw : G *ᵥ w = e := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  let c : ρ → ℂ := star (V *ᵥ w)
  have hcV : c ᵥ* V = e := by
    have hh : star w ᵥ* G = star e := by
      rw [← hG.isHermitian.eq, ← Matrix.star_mulVec, hw]
    have he : star e = e := by ext k; simp [e, Pi.single_apply]
    dsimp [c, G] at *
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, hh, he]
  refine ⟨c, ?_, ?_⟩
  · intro k
    change c ⬝ᵥ (fun i => V i k) = _
    have h := congrFun hcV k
    simpa [Matrix.vecMul, e, Pi.single_apply, eq_comm] using h
  · have henergy : energy c = energy (V *ᵥ w) := by
      simp only [energy, c, Pi.star_apply, norm_star]
    have he : energy (V *ᵥ w) = (w j).re := by
      change (∑ k, ‖(V *ᵥ w) k‖ ^ 2) = _
      rw [← quadratic_gram]
      change (star w ⬝ᵥ (G *ᵥ w)).re = _
      rw [hw]
      simp [e, dotProduct, Pi.single_apply]
    have hj : ‖w j‖ ^ 2 ≤ energy w :=
      Finset.single_le_sum (fun i _ => sq_nonneg ‖w i‖) (Finset.mem_univ j)
    have hjR : (w j).re ^ 2 ≤ energy w :=
      (by nlinarith [Complex.sq_norm (w j), sq_nonneg (w j).im, Complex.normSq_apply (w j)] :
        (w j).re ^ 2 ≤ ‖w j‖ ^ 2) |>.trans hj
    have hf := hframe w
    rw [he] at hf
    have hE : 0 ≤ (w j).re := he ▸ energy_nonneg (V *ᵥ w)
    have hbound : (w j).re ≤ 1 / a := by
      apply (le_div_iff₀ ha).2
      by_cases hz : (w j).re = 0
      · simp [hz]
      · have hp : 0 < (w j).re := lt_of_le_of_ne hE (Ne.symm hz)
        have hh := mul_le_mul_of_nonneg_left hjR ha.le
        nlinarith
    rwa [henergy, he]

end SegmentedVDM
