import MultiTuran.MultiClump.ShortenedGrid
import MultiTuran.MultiClump.BoundFormula
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Selector width and the Riemann threshold on shortened blocks -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

def selectorWidthParameter (d : ℕ) (separation : ℝ) : ℕ :=
  2 * ⌈2*Real.pi*d/separation⌉₊

theorem selectorWidthParameter_pos {d : ℕ} (hd : 0 < d) {separation : ℝ} (hseparation : 0 < separation) :
    0 < selectorWidthParameter d separation := by
  have h : (0 : ℝ) < 2*Real.pi*d/separation := by positivity
  have hc : 0 < ⌈2*Real.pi*d/separation⌉₊ := Nat.ceil_pos.mpr h
  unfold selectorWidthParameter
  omega

theorem selectorWidthParameter_separation {d : ℕ} (hd : 0 < d) {separation : ℝ} (hseparation : 0 < separation) :
    4*Real.pi*d/((selectorWidthParameter d separation : ℝ)+1) ≤ separation := by
  have hc := Nat.le_ceil (2*Real.pi*d/separation)
  have hden : (0 : ℝ) < (selectorWidthParameter d separation : ℝ)+1 := by positivity
  have hbase := (div_le_iff₀ hseparation).mp hc
  apply (div_le_iff₀ hden).mpr
  unfold selectorWidthParameter
  push_cast
  nlinarith

theorem selectorWidthParameter_upper {d : ℕ} (hd : 2 ≤ d) {separation : ℝ}
    (hseparation : 0 < separation) (hseparationπ : separation ≤ Real.pi) :
    separation*(selectorWidthParameter d separation : ℝ) ≤ 5*Real.pi*d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have harg : 0 ≤ 2*Real.pi*d/separation := by positivity
  have hc := (Nat.ceil_lt_add_one harg).le
  have hc' := mul_le_mul_of_nonneg_left hc hseparation.le
  have he : separation*(2*Real.pi*d/separation+1) = 2*Real.pi*d+separation := by field_simp
  rw [he] at hc'
  unfold selectorWidthParameter
  push_cast
  nlinarith [Real.pi_pos]

theorem selector_width_fits_blocks {d nStar : ℕ} (G : SegmentedGrid d)
    (hd : 2 ≤ d) (hnStar : 0 < nStar) {separation : ℝ}
    (hseparation : 0 < separation) (hseparationπ : separation ≤ Real.pi)
    (hgap : 16*Real.pi*d*(nStar : ℝ)^2 ≤ separation*G.minThickLength) :
    2*(nStar^2*selectorWidthParameter d separation) < G.minThickLength := by
  have hK := selectorWidthParameter_upper hd hseparation hseparationπ
  have hmul := mul_le_mul_of_nonneg_right hK (sq_nonneg (nStar : ℝ))
  have hL : (0 : ℝ) < G.minThickLength := by exact_mod_cast minThickLength_pos G
  have hresult : 2*((nStar : ℝ)^2*(selectorWidthParameter d separation : ℝ)) < G.minThickLength := by
    apply (mul_lt_mul_iff_right₀ hseparation).mp
    nlinarith only [hmul,hgap,mul_pos hseparation hL]
  exact_mod_cast hresult

def clumpRiemannExpression (d nStar : ℕ) (L τ : ℝ) : ℝ :=
  (nStar : ℝ)^(4*d+5)/L^(d+1) + (nStar : ℝ)^(4*d+1)*τ/L^d

theorem clumpRiemannExpression_nonneg (d nStar : ℕ) {L τ : ℝ}
    (hL : 0 ≤ L) (hτ : 0 ≤ τ) : 0 ≤ clumpRiemannExpression d nStar L τ := by
  unfold clumpRiemannExpression
  positivity

private theorem div_pow_le_of_half {L l A : ℝ} (hL : 0 < L) (hl : 0 < l)
    (hhalf : L ≤ 2*l) (hA : 0 ≤ A) (k : ℕ) :
    A/l^k ≤ 2^k*(A/L^k) := by
  have hp : L^k ≤ 2^k*l^k := by
    simpa only [mul_pow] using pow_le_pow_left₀ hL.le hhalf k
  apply (div_le_iff₀ (pow_pos hl k)).mpr
  calc
    A = A/L^k*L^k := by field_simp
    _ ≤ A/L^k*(2^k*l^k) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

theorem clumpRiemannExpression_le_of_half {d nStar : ℕ} {L l τ : ℝ}
    (hL : 0 < L) (hl : 0 < l) (hhalf : L ≤ 2*l) (hτ : 0 ≤ τ) :
    clumpRiemannExpression d nStar l τ ≤
      2^(d+1)*clumpRiemannExpression d nStar L τ := by
  have h₁ := div_pow_le_of_half hL hl hhalf
    (pow_nonneg (Nat.cast_nonneg nStar) (4*d+5)) (d+1)
  have h₂ := div_pow_le_of_half hL hl hhalf
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg nStar) (4*d+1)) hτ) d
  have htwo : (2 : ℝ)^d ≤ 2^(d+1) := by
    rw [pow_succ]
    nlinarith only [pow_pos (by norm_num : (0 : ℝ) < 2) d]
  unfold clumpRiemannExpression
  calc
    _ ≤ 2^(d+1)*((nStar : ℝ)^(4*d+5)/L^(d+1)) +
        2^d*((nStar : ℝ)^(4*d+1)*τ/L^d) := add_le_add h₁ h₂
    _ ≤ 2^(d+1)*((nStar : ℝ)^(4*d+5)/L^(d+1)) +
        2^(d+1)*((nStar : ℝ)^(4*d+1)*τ/L^d) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_right htwo (show 0 ≤ (nStar : ℝ)^(4*d+1)*τ/L^d by positivity))
    _ = _ := by ring

/-- The paper's single `B_d` hypothesis implies the proved clumpwise
Riemann threshold on every shortened block. Enlarging the absolute
Bernstein constant to at least 24 is harmless. -/
theorem shortenedGrid_riemann_threshold {d nStar : ℕ} (G : SegmentedGrid d)
    (W : ℕ) (hW : 2*W < G.minThickLength) {τ C_B : ℝ}
    (hτ : 0 ≤ τ) (hC_B : 24 ≤ C_B)
    (hcondition : multiClumpBlockConstant d C_B * G.rowCount *
      clumpRiemannExpression d nStar G.minThickLength τ ≤ 1) :
    48*(d : ℝ)*(Real.pi/2)^(2*d)*(shortenedGrid G W).rowCount *
      clumpRiemannExpression d nStar (shortenedGrid G W).minThickLength τ ≤ 1 := by
  have hL : (0 : ℝ) < G.minThickLength := by exact_mod_cast minThickLength_pos G
  have hl : (0 : ℝ) < (shortenedGrid G W).minThickLength := by
    exact_mod_cast minThickLength_pos (shortenedGrid G W)
  have hhalf : (G.minThickLength : ℝ) ≤ 2*(shortenedGrid G W).minThickLength := by
    exact_mod_cast shortenedGrid_minThickLength_half G W hW
  have hrows : ((shortenedGrid G W).rowCount : ℝ) ≤ G.rowCount := by
    exact_mod_cast shortenedGrid_rowCount_le G W
  have hexpr := clumpRiemannExpression_le_of_half (d := d) (nStar := nStar) hL hl hhalf hτ
  have hC0 : 0 ≤ C_B := by linarith
  have hCsqrt : 24 ≤ C_B*(Real.sqrt 108+1) := by
    have h := mul_nonneg hC0 (Real.sqrt_nonneg (108 : ℝ))
    nlinarith only [h,hC_B]
  have hc : 48*(d : ℝ)*(Real.pi/2)^(2*d)*2^(d+1) ≤ multiClumpBlockConstant d C_B := by
    unfold multiClumpBlockConstant
    have hm := mul_le_mul_of_nonneg_right hCsqrt
      (show 0 ≤ 2^(d+2)*(d : ℝ)*(Real.pi/2)^(2*d) by positivity)
    have he : (2 : ℝ)^(d+2) = 4*2^d := by simp only [pow_add, pow_two]; ring
    have he' : (2 : ℝ)^(d+1) = 2*2^d := by rw [pow_succ]; ring
    rw [he] at hm ⊢
    rw [he']
    nlinarith only [hm]
  calc
    _ ≤ 48*(d : ℝ)*(Real.pi/2)^(2*d)*G.rowCount *
        (2^(d+1)*clumpRiemannExpression d nStar G.minThickLength τ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hrows (by positivity)) hexpr
        (clumpRiemannExpression_nonneg d nStar hl.le hτ) (by positivity)
    _ = (48*(d : ℝ)*(Real.pi/2)^(2*d)*2^(d+1))*G.rowCount *
        clumpRiemannExpression d nStar G.minThickLength τ := by ring
    _ ≤ multiClumpBlockConstant d C_B * G.rowCount *
        clumpRiemannExpression d nStar G.minThickLength τ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _))
        (clumpRiemannExpression_nonneg d nStar hL.le hτ)
    _ ≤ 1 := hcondition

theorem minThickLength_le_minAperture {d : ℕ} (G : SegmentedGrid d) :
    G.minThickLength ≤ G.minAperture := by
  obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_inf'
    (show (Finset.univ : Finset (Fin d)).Nonempty from
      ⟨⟨0,G.dimension_pos⟩, Finset.mem_univ _⟩) G.aperture
  change G.minAperture = G.aperture q at hq
  rw [hq]
  have h := (minThickLength_le_coordinateMinLength G q).trans
    (G.coordinateMinLength_le q (G.lastBlock q))
  unfold SegmentedGrid.thickLength SegmentedGrid.aperture at *
  omega

def fullApertureCubeSide (N : ℕ) : ℕ := 2*((N-1)/2)

theorem fullApertureCubeSide_properties {N : ℕ} (hN : 4 ≤ N) :
    Even (fullApertureCubeSide N) ∧ fullApertureCubeSide N+1 ≤ N ∧
      N ≤ 2*fullApertureCubeSide N ∧ N-2 ≤ fullApertureCubeSide N := by
  constructor
  · exact ⟨(N-1)/2, by unfold fullApertureCubeSide; omega⟩
  · have hdiv := Nat.div_add_mod (N-1) 2
    have hmod := Nat.mod_lt (N-1) (by norm_num : 0 < 2)
    unfold fullApertureCubeSide
    omega

theorem fullApertureCubeSide_large {N n : ℕ} (hn : 0 < n) (hN : 16*n ≤ N) :
    8*n ≤ fullApertureCubeSide N := by
  have h := (fullApertureCubeSide_properties (show 4 ≤ N by omega)).2.2.1
  omega

theorem fullApertureCubeSide_gap {d nStar : ℕ} (G : SegmentedGrid d)
    (hnStar : 0 < nStar) {separation : ℝ} (hseparation : 0 < separation) (hN : 4 ≤ G.minAperture)
    (hgap : 16*Real.pi*d*(nStar : ℝ)^2 ≤ separation*G.minThickLength) :
    8*Real.pi*d*nStar/(fullApertureCubeSide G.minAperture : ℝ) ≤ separation := by
  have hL : (G.minThickLength : ℝ) ≤ G.minAperture := by
    exact_mod_cast minThickLength_le_minAperture G
  have hNs := (fullApertureCubeSide_properties hN).2.2.1
  have hNsR : (G.minAperture : ℝ) ≤ 2*(fullApertureCubeSide G.minAperture : ℝ) := by
    exact_mod_cast hNs
  have hs : (0 : ℝ) < fullApertureCubeSide G.minAperture := by
    exact_mod_cast (show 0 < fullApertureCubeSide G.minAperture by omega)
  have hns : (1 : ℝ) ≤ nStar := by exact_mod_cast hnStar
  have hpow : (nStar : ℝ) ≤ (nStar : ℝ)^2 := le_self_pow₀ hns (by norm_num)
  have h₁ := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ 16*Real.pi*d by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hL hseparation.le
  have h₃ := mul_le_mul_of_nonneg_left hNsR hseparation.le
  apply (div_le_iff₀ hs).mpr
  nlinarith only [h₁,hgap,h₂,h₃]

end
end LeanNumDetect.MultiTuran.MultiClump
