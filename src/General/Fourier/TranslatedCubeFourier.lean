import General.Fourier.SeparatedCubeFourierInternal
import MathExtras.NumberTheory.Analysis.SelbergIntervalPoissonClosed

/-!
The translated-cube lower Fourier-frame bound.

The proof uses Barton's `M₃⁻` box minorant, reconstructed from the classical
one-dimensional Vaaler--Selberg pair.  The required one-dimensional analytic
facts and Poisson summation are supplied by the vendored, sorry-free
Vaaler--Selberg development.  This file proves the pointwise box minorization,
tensorizes the lattice sums, and applies the weighted orthogonality reduction.
-/

set_option autoImplicit false

open scoped BigOperators FourierTransform

namespace External

noncomputable section

/-- The integer points in a translated cube containing `N` consecutive
frequencies in every coordinate. -/
abbrev OneSidedCubeFrequency (d N : ℕ) := Fin d → Fin N

/-- Fourier energy on the translated integer cube `{0, ..., N - 1}^d`. -/
noncomputable def translatedCubeFourierEnergy
    {d : ℕ} {ι : Type*} [Fintype ι]
    (N : ℕ) (x : ι → UnitTorusPoint d) (c : ι → ℂ) : ℝ :=
  ∑ n : OneSidedCubeFrequency d N,
    ‖∑ j, c j * Complex.exp
      (-2 * Real.pi * Complex.I *
        (∑ k, (((n k : Fin N) : ℕ) : ℂ) * x j k))‖ ^ 2

end

end External

namespace LeanNumDetect
namespace TranslatedCubeFourier

noncomputable section

open MathExtras.NumberTheory.Analysis
open VaalerBeurlingNonneg
open VaalerSumInvSqProof
open VaalerFejerFT
open VaalerThm16Mechanism
open SelbergIntervalMajorantClosed
open SelbergIntervalPoissonClosed
open LargeSieve

private theorem tailSum_le_inv_add_half {x : ℝ} (hx : 0 < x) :
    tailSum x ≤ (x + 1 / 2)⁻¹ := by
  unfold tailSum
  have hc : 0 < x + 1 / 2 := by linarith
  have hcmp : HasSum
      (fun k : ℕ =>
        (x + 1 / 2 + (k : ℝ))⁻¹ *
          (x + 1 / 2 + (k + 1 : ℝ))⁻¹)
      (x + 1 / 2)⁻¹ :=
    telescope_hasSum hc
  have htail := tailSum_summable hx
  have hle : ∀ k : ℕ,
      (x + (k + 1 : ℕ))⁻¹ ^ 2 ≤
        (x + 1 / 2 + (k : ℝ))⁻¹ *
          (x + 1 / 2 + (k + 1 : ℝ))⁻¹ := by
    intro k
    simp only [Nat.cast_add, Nat.cast_one]
    have ha : 0 < x + 1 / 2 + (k : ℝ) := by positivity
    have hb : 0 < x + 1 / 2 + ((k : ℝ) + 1) := by positivity
    have hm : 0 < x + ((k : ℝ) + 1) := by positivity
    have hleft : (x + ((k : ℝ) + 1))⁻¹ ^ 2 =
        1 / (x + ((k : ℝ) + 1)) ^ 2 := by field_simp
    have hright :
        (x + 1 / 2 + (k : ℝ))⁻¹ *
            (x + 1 / 2 + ((k : ℝ) + 1))⁻¹ =
          1 / ((x + 1 / 2 + (k : ℝ)) *
            (x + 1 / 2 + ((k : ℝ) + 1))) := by field_simp
    rw [hleft, hright]
    apply (div_le_div_iff₀ (sq_pos_of_pos hm) (mul_pos ha hb)).2
    nlinarith
  exact (Summable.tsum_le_tsum hle htail hcmp.summable).trans_eq hcmp.tsum_eq

private theorem one_sub_interpH_le_fejerK_div_two_mul_add_one
    {x : ℝ} (hx : 0 < x) :
    1 - interpH x ≤ fejerK x / (2 * x + 1) := by
  by_cases hs : Real.sin (Real.pi * x) = 0
  · have hH : interpH x = 1 := by
      unfold interpH
      rw [if_pos hs, Real.sign_of_pos hx]
    calc
      1 - interpH x = 0 := by rw [hH]; ring
      _ ≤ fejerK x / (2 * x + 1) :=
        div_nonneg (fejerK_nonneg x) (by linarith)
  · rw [interpH_rewrite VaalerSumInvSqProof.vaalerSumInvSqIdentity_holds hs]
    have hK : fejerK x =
        (Real.sin (Real.pi * x) / Real.pi) ^ 2 * x⁻¹ ^ 2 := by
      unfold fejerK
      rw [if_neg hx.ne']
    rw [hK]
    have htail := tailSum_le_inv_add_half hx
    have hcoef : 0 ≤ (Real.sin (Real.pi * x) / Real.pi) ^ 2 := sq_nonneg _
    have hx0 : x ≠ 0 := hx.ne'
    have hden : 0 < 2 * x + 1 := by linarith
    have hhalf : x + 1 / 2 = (2 * x + 1) / 2 := by ring
    rw [hhalf] at htail
    have hinv : ((2 * x + 1) / 2)⁻¹ = 2 / (2 * x + 1) := by
      field_simp
    rw [hinv] at htail
    have htail2 : 2 * tailSum x ≤ 4 / (2 * x + 1) := by
      calc
        2 * tailSum x ≤ 2 * (2 / (2 * x + 1)) :=
          mul_le_mul_of_nonneg_left htail (by norm_num)
        _ = 4 / (2 * x + 1) := by ring
    have hcore :
        x⁻¹ ^ 2 + 2 * tailSum x - 2 * x⁻¹ ≤
          x⁻¹ ^ 2 / (2 * x + 1) := by
      calc
        x⁻¹ ^ 2 + 2 * tailSum x - 2 * x⁻¹ ≤
            x⁻¹ ^ 2 + 4 / (2 * x + 1) - 2 * x⁻¹ := by linarith
        _ = x⁻¹ ^ 2 / (2 * x + 1) := by
          field_simp [hx.ne']
          ring
    calc
      1 - (1 + (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
          (2 * x⁻¹ - x⁻¹ ^ 2 - 2 * tailSum x)) =
          (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
            (x⁻¹ ^ 2 + 2 * tailSum x - 2 * x⁻¹) := by ring
      _ ≤ (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
            (x⁻¹ ^ 2 / (2 * x + 1)) :=
        mul_le_mul_of_nonneg_left hcore hcoef
      _ = ((Real.sin (Real.pi * x) / Real.pi) ^ 2 * x⁻¹ ^ 2) /
            (2 * x + 1) := by ring

private theorem one_sub_interpH_le_fejerK_div_three
    {x : ℝ} (hx : 1 ≤ x) :
    1 - interpH x ≤ fejerK x / 3 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h := one_sub_interpH_le_fejerK_div_two_mul_add_one hx0
  have hK : 0 ≤ fejerK x := fejerK_nonneg x
  have hden : 0 < 2 * x + 1 := by linarith
  calc
    1 - interpH x ≤ fejerK x / (2 * x + 1) := h
    _ ≤ fejerK x / 3 := by
      apply div_le_div_of_nonneg_left hK (by norm_num) (by linarith)

private theorem fejerK_le_one (x : ℝ) : fejerK x ≤ 1 := by
  rw [fejerK_eq_sincSqPi]
  exact MathExtras.Fourier.sincSqPi_le_one x

private theorem interpH_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ interpH x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [interpH]
  · have h := one_sub_fejerK_le_interpH
      VaalerSumInvSqProof.vaalerSumInvSqIdentity_holds hx
    linarith [fejerK_le_one x]

private theorem interpH_le_one_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    interpH x ≤ 1 := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [interpH]
  · exact interpH_le_one VaalerSumInvSqProof.vaalerSumInvSqIdentity_holds hx

private theorem fejerK_neg_local (x : ℝ) : fejerK (-x) = fejerK x := by
  unfold fejerK
  rw [show Real.pi * -x = -(Real.pi * x) by ring, Real.sin_neg]
  by_cases hx : x = 0
  · subst x
    simp
  · rw [if_neg (neg_ne_zero.mpr hx), if_neg hx, inv_neg]
    ring

/-- The even error term in the Selberg pair. -/
def intervalError (a b δ t : ℝ) : ℝ :=
  (selbergIntervalMajorant a a δ t +
    selbergIntervalMajorant b b δ t) / 2

/-- The central part of the Selberg pair. -/
def intervalCenter (a b δ t : ℝ) : ℝ :=
  selbergIntervalMajorant a b δ t - intervalError a b δ t

private theorem zeroIntervalMajorant_eq_fejerK
    {a δ t : ℝ} (hδ : 0 < δ) :
    selbergIntervalMajorant a a δ t = fejerK (δ * (t - a)) := by
  unfold selbergIntervalMajorant beurlingBClosed
  rw [show δ * (a - t) = -(δ * (t - a)) by ring,
    interpH_neg, fejerK_neg_local]
  ring

private theorem intervalError_eq_fejerK
    {a b δ t : ℝ} (hδ : 0 < δ) :
    intervalError a b δ t =
      (fejerK (δ * (t - a)) + fejerK (δ * (t - b))) / 2 := by
  rw [intervalError, zeroIntervalMajorant_eq_fejerK hδ,
    zeroIntervalMajorant_eq_fejerK hδ]

private theorem intervalCenter_eq_interpH
    {a b δ t : ℝ} (hδ : 0 < δ) :
    intervalCenter a b δ t =
      (interpH (δ * (t - a)) + interpH (δ * (b - t))) / 2 := by
  rw [intervalCenter, intervalError_eq_fejerK hδ]
  unfold selbergIntervalMajorant beurlingBClosed
  rw [show δ * (t - b) = -(δ * (b - t)) by ring,
    fejerK_neg_local]
  ring

private theorem intervalCenter_add_error
    (a b δ t : ℝ) :
    intervalCenter a b δ t + intervalError a b δ t =
      selbergIntervalMajorant a b δ t := by
  simp [intervalCenter]

private theorem intervalCenter_bounds_inside
    {a b δ t : ℝ} (hδ : 0 < δ) (hat : a ≤ t) (htb : t ≤ b) :
    0 ≤ intervalCenter a b δ t ∧ intervalCenter a b δ t ≤ 1 := by
  rw [intervalCenter_eq_interpH hδ]
  have hleft : 0 ≤ δ * (t - a) := mul_nonneg hδ.le (sub_nonneg.mpr hat)
  have hright : 0 ≤ δ * (b - t) := mul_nonneg hδ.le (sub_nonneg.mpr htb)
  constructor
  · linarith [interpH_nonneg_of_nonneg hleft,
      interpH_nonneg_of_nonneg hright]
  · linarith [interpH_le_one_of_nonneg hleft,
      interpH_le_one_of_nonneg hright]

private theorem intervalError_nonneg
    {a b δ t : ℝ} (hδ : 0 < δ) : 0 ≤ intervalError a b δ t := by
  rw [intervalError_eq_fejerK hδ]
  exact div_nonneg (add_nonneg (fejerK_nonneg _) (fejerK_nonneg _)) (by norm_num)

private theorem intervalCenter_abs_outside_le_half_majorant
    {a b δ t : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hwidth : 1 ≤ δ * (b - a)) (hout : t < a ∨ b < t) :
    2 * |intervalCenter a b δ t| ≤
      selbergIntervalMajorant a b δ t := by
  have hId := VaalerSumInvSqProof.vaalerSumInvSqIdentity_holds
  rcases hout with hta | hbt
  · let u := δ * (a - t)
    let v := δ * (b - t)
    have hu : 0 ≤ u := mul_nonneg hδ.le (sub_nonneg.mpr hta.le)
    have hv : 1 ≤ v := by
      dsimp [v]
      nlinarith
    have hv0 : 0 ≤ v := zero_le_one.trans hv
    have hcenter : intervalCenter a b δ t = (interpH v - interpH u) / 2 := by
      rw [intervalCenter_eq_interpH hδ]
      dsimp [u, v]
      rw [show δ * (t - a) = -(δ * (a - t)) by ring, interpH_neg]
      ring
    have herr : intervalError a b δ t = (fejerK u + fejerK v) / 2 := by
      rw [intervalError_eq_fejerK hδ]
      dsimp [u, v]
      rw [show δ * (t - a) = -(δ * (a - t)) by ring,
        show δ * (t - b) = -(δ * (b - t)) by ring,
        fejerK_neg_local, fejerK_neg_local]
    rw [← intervalCenter_add_error a b δ t, hcenter, herr]
    by_cases huv : interpH u ≤ interpH v
    · rw [abs_of_nonneg (by linarith)]
      have huerr : 1 - interpH u ≤ fejerK u := by
        rcases hu.eq_or_lt with hu0 | hu
        · rw [← hu0]
          simp [interpH, fejerK]
        · have hh := one_sub_fejerK_le_interpH hId hu
          linarith
      have hvone := interpH_le_one_of_nonneg hv0
      have hKv : 0 ≤ fejerK v := fejerK_nonneg v
      linarith
    · have hvu : interpH v < interpH u := lt_of_not_ge huv
      rw [abs_of_nonpos (by linarith)]
      have hverr := one_sub_interpH_le_fejerK_div_three hv
      have huone := interpH_le_one_of_nonneg hu
      have hKu : 0 ≤ fejerK u := fejerK_nonneg u
      linarith

  · let u := δ * (t - b)
    let v := δ * (t - a)
    have hu : 0 ≤ u := mul_nonneg hδ.le (sub_nonneg.mpr hbt.le)
    have hv : 1 ≤ v := by
      dsimp [v]
      nlinarith
    have hv0 : 0 ≤ v := zero_le_one.trans hv
    have hcenter : intervalCenter a b δ t = (interpH v - interpH u) / 2 := by
      rw [intervalCenter_eq_interpH hδ]
      dsimp [u, v]
      rw [show δ * (b - t) = -(δ * (t - b)) by ring, interpH_neg]
      ring
    have herr : intervalError a b δ t = (fejerK v + fejerK u) / 2 := by
      rw [intervalError_eq_fejerK hδ]
    rw [← intervalCenter_add_error a b δ t, hcenter, herr]
    by_cases huv : interpH u ≤ interpH v
    · rw [abs_of_nonneg (by linarith)]
      have huerr : 1 - interpH u ≤ fejerK u := by
        rcases hu.eq_or_lt with hu0 | hu
        · rw [← hu0]
          simp [interpH, fejerK]
        · have hh := one_sub_fejerK_le_interpH hId hu
          linarith
      have hvone := interpH_le_one_of_nonneg hv0
      have hKv : 0 ≤ fejerK v := fejerK_nonneg v
      linarith
    · have hvu : interpH v < interpH u := lt_of_not_ge huv
      rw [abs_of_nonpos (by linarith)]
      have hverr := one_sub_interpH_le_fejerK_div_three hv
      have huone := interpH_le_one_of_nonneg hu
      have hKu : 0 ≤ fejerK u := fejerK_nonneg u
      linarith

/-- Barton's `M₃⁻` minorant, written using the center and upper member of
the one-dimensional Selberg pair. -/
def bartonMinorant {d : ℕ} (a b δ : ℝ) (t : Fin d → ℝ) : ℝ :=
  2 * ∏ k, intervalCenter a b δ (t k) -
    ∏ k, selbergIntervalMajorant a b δ (t k)

/-- The tensor-product Selberg majorant for a rectangular integer block. -/
def bartonMajorant {d : ℕ} (a b δ : ℝ) (t : Fin d → ℝ) : ℝ :=
  ∏ k, selbergIntervalMajorant a b δ (t k)

theorem bartonMajorant_nonneg
    {d : ℕ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (t : Fin d → ℝ) : 0 ≤ bartonMajorant a b δ t := by
  exact Finset.prod_nonneg fun k _ =>
    selbergIntervalMajorant_nonneg hab hδ (t k)

theorem boxIndicator_le_bartonMajorant
    {d : ℕ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (t : Fin d → ℝ) :
    (if ∀ k, a < t k ∧ t k ≤ b then 1 else 0) ≤
      bartonMajorant a b δ t := by
  classical
  have hnonneg : ∀ k, 0 ≤ selbergIntervalMajorant a b δ (t k) :=
    fun k => selbergIntervalMajorant_nonneg hab hδ (t k)
  by_cases hin : ∀ k, a < t k ∧ t k ≤ b
  · rw [if_pos hin]
    exact Finset.one_le_prod fun k _ =>
      one_le_selbergIntervalMajorant hδ (hin k).1 (hin k).2
  · rw [if_neg hin]
    exact Finset.prod_nonneg fun k _ => hnonneg k

theorem bartonMinorant_le_boxIndicator
    {d : ℕ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hwidth : 1 ≤ δ * (b - a)) (t : Fin d → ℝ) :
    bartonMinorant a b δ t ≤
      if ∀ k, a ≤ t k ∧ t k ≤ b then 1 else 0 := by
  classical
  let V : Fin d → ℝ := fun k => intervalCenter a b δ (t k)
  let C : Fin d → ℝ := fun k => selbergIntervalMajorant a b δ (t k)
  have hC0 : ∀ k, 0 ≤ C k := fun k =>
    selbergIntervalMajorant_nonneg hab hδ (t k)
  by_cases hin : ∀ k, a ≤ t k ∧ t k ≤ b
  · rw [if_pos hin]
    have hV : ∀ k, 0 ≤ V k ∧ V k ≤ 1 := fun k =>
      intervalCenter_bounds_inside hδ (hin k).1 (hin k).2
    have hVC : ∀ k, V k ≤ C k := by
      intro k
      dsimp [V, C]
      rw [← intervalCenter_add_error a b δ (t k)]
      exact le_add_of_nonneg_right (intervalError_nonneg hδ)
    have hprodV0 : 0 ≤ ∏ k, V k := Finset.prod_nonneg fun k _ => (hV k).1
    have hprodV1 : (∏ k, V k) ≤ 1 := by
      simpa using Finset.prod_le_one (fun k _ => (hV k).1) (fun k _ => (hV k).2)
    have hprodVC : (∏ k, V k) ≤ ∏ k, C k :=
      Finset.prod_le_prod (fun k _ => (hV k).1) (fun k _ => hVC k)
    change 2 * ∏ k, V k - ∏ k, C k ≤ 1
    linarith
  · rw [if_neg hin]
    obtain ⟨k, hk⟩ := not_forall.mp hin
    have hkout : t k < a ∨ b < t k := by
      rcases not_and_or.mp hk with h | h
      · exact Or.inl (lt_of_not_ge h)
      · exact Or.inr (lt_of_not_ge h)
    have hstrong : 2 * |V k| ≤ C k := by
      simpa [V, C] using
        intervalCenter_abs_outside_le_half_majorant hab hδ hwidth hkout
    have hweak : ∀ i, |V i| ≤ C i := by
      intro i
      by_cases hi : a ≤ t i ∧ t i ≤ b
      · dsimp [V, C]
        rw [abs_of_nonneg (intervalCenter_bounds_inside hδ hi.1 hi.2).1]
        rw [← intervalCenter_add_error a b δ (t i)]
        exact le_add_of_nonneg_right (intervalError_nonneg hδ)
      · have hiout : t i < a ∨ b < t i := by
          rcases not_and_or.mp hi with h | h
          · exact Or.inl (lt_of_not_ge h)
          · exact Or.inr (lt_of_not_ge h)
        have hs := intervalCenter_abs_outside_le_half_majorant
          hab hδ hwidth hiout
        simpa [V, C] using (show |intervalCenter a b δ (t i)| ≤
          selbergIntervalMajorant a b δ (t i) by
            linarith [abs_nonneg (intervalCenter a b δ (t i))])
    have hrest :
        (∏ i ∈ Finset.univ.erase k, |V i|) ≤
          ∏ i ∈ Finset.univ.erase k, C i :=
      Finset.prod_le_prod
        (fun i _ => abs_nonneg (V i)) (fun i _ => hweak i)
    have hrest0 : 0 ≤ ∏ i ∈ Finset.univ.erase k, |V i| :=
      Finset.prod_nonneg fun i _ => abs_nonneg (V i)
    have hCk0 : 0 ≤ C k := hC0 k
    have hprodabs : 2 * |∏ i, V i| ≤ ∏ i, C i := by
      rw [Finset.abs_prod]
      rw [← Finset.mul_prod_erase Finset.univ (fun i => |V i|)
          (Finset.mem_univ k),
        ← Finset.mul_prod_erase Finset.univ C (Finset.mem_univ k)]
      calc
        2 * (|V k| * ∏ i ∈ Finset.univ.erase k, |V i|) =
            (2 * |V k|) * ∏ i ∈ Finset.univ.erase k, |V i| := by ring
        _ ≤ C k * ∏ i ∈ Finset.univ.erase k, |V i| :=
          mul_le_mul_of_nonneg_right hstrong hrest0
        _ ≤ C k * ∏ i ∈ Finset.univ.erase k, C i :=
          mul_le_mul_of_nonneg_left hrest hCk0
    change 2 * ∏ i, V i - ∏ i, C i ≤ 0
    have hprodVabs : (∏ i, V i) ≤ |∏ i, V i| := le_abs_self _
    linarith

private theorem selbergModulated_hasSum_zero
    {a b δ θ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hsep : δ ≤ circleDist θ 0) :
    HasSum (fun n : ℤ =>
      (selbergIntervalMajorant a b δ (n : ℝ) : ℂ) * echar θ (n : ℝ)) 0 := by
  have hs := selbergIntervalMajorant_mul_echar_int_summable hab hδ θ
  exact hs.hasSum_iff.mpr
    (tsum_selbergIntervalMajorant_mul_echar_eq_zero hab hδ hsep)

private theorem intervalCenterModulated_hasSum_zero
    {a b δ θ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hsep : δ ≤ circleDist θ 0) :
    HasSum (fun n : ℤ =>
      (intervalCenter a b δ (n : ℝ) : ℂ) * echar θ (n : ℝ)) 0 := by
  have hC := selbergModulated_hasSum_zero hab hδ hsep
  have hA := selbergModulated_hasSum_zero (a := a) (b := a) le_rfl hδ hsep
  have hB := selbergModulated_hasSum_zero (a := b) (b := b) le_rfl hδ hsep
  have hE := (hA.add hB).mul_left (1 / 2 : ℂ)
  have h := hC.sub hE
  have hz : (0 : ℂ) - (1 / 2 : ℂ) * (0 + 0) = 0 := by ring
  rw [hz] at h
  exact HasSum.congr_fun h (fun n => by
    simp only [intervalCenter, intervalError]
    push_cast
    ring)

private theorem selbergUnmodulated_hasSum_mass
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    HasSum (fun n : ℤ => (selbergIntervalMajorant a b δ (n : ℝ) : ℂ))
      (((b - a) + δ⁻¹ : ℝ) : ℂ) := by
  have hs := selbergIntervalMajorant_mul_echar_int_summable hab hδ 0
  have hs' : Summable
      (fun n : ℤ => (selbergIntervalMajorant a b δ (n : ℝ) : ℂ)) := by
    simpa [echar] using hs
  exact hs'.hasSum_iff.mpr
    (tsum_selbergIntervalMajorant_eq_mass hab hδ hδ1)

private theorem intervalCenterUnmodulated_hasSum_length
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    HasSum (fun n : ℤ => (intervalCenter a b δ (n : ℝ) : ℂ))
      ((b - a : ℝ) : ℂ) := by
  have hC := selbergUnmodulated_hasSum_mass hab hδ hδ1
  have hA := selbergUnmodulated_hasSum_mass (a := a) (b := a) le_rfl hδ hδ1
  have hB := selbergUnmodulated_hasSum_mass (a := b) (b := b) le_rfl hδ hδ1
  have hE := (hA.add hB).mul_left (1 / 2 : ℂ)
  have h := hC.sub hE
  have hmass :
      (((b - a) + δ⁻¹ : ℝ) : ℂ) -
          (1 / 2 : ℂ) *
            (((a - a) + δ⁻¹ : ℝ) + ((b - b) + δ⁻¹ : ℝ)) =
        ((b - a : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hmass] at h
  exact HasSum.congr_fun h (fun n => by
    simp only [intervalCenter, intervalError]
    push_cast
    ring)

set_option maxHeartbeats 800000 in
private theorem hasSum_pi_prod
    {α : Type} [Fintype α]
    (f : α → ℤ → ℂ) (s : α → ℂ)
    (h : ∀ i, HasSum (f i) (s i)) :
    HasSum (fun n : α → ℤ => ∏ i, f i (n i)) (∏ i, s i) := by
  classical
  refine Fintype.induction_empty_option
    (P := fun (α : Type) [Fintype α] =>
      ∀ (f : α → ℤ → ℂ) (s : α → ℂ),
        (∀ i, HasSum (f i) (s i)) →
          HasSum (fun n : α → ℤ => ∏ i, f i (n i)) (∏ i, s i))
    ?_ ?_ ?_ α f s h
  · intro α β _ e ih f s h
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let ep : (α → ℤ) ≃ (β → ℤ) := Equiv.piCongrLeft (fun _ => ℤ) e
    have hi := ih (fun i n => f (e i) n) (fun i => s (e i))
      (fun i => h (e i))
    have heqf : (fun n : α → ℤ => ∏ i, f (e i) (n i)) =
        (fun n : β → ℤ => ∏ i, f i (n i)) ∘ ep := by
      funext n
      simpa [ep, Equiv.piCongrLeft] using
        e.prod_comp (fun x : β => f x (n (e.symm x)))
    have heqs : (∏ i : α, s (e i)) = ∏ i : β, s i := by
      exact e.prod_comp (fun i => s i)
    have hi' : HasSum
        ((fun n : β → ℤ => ∏ i, f i (n i)) ∘ ep) (∏ i : α, s (e i)) :=
      heqf ▸ hi
    rw [heqs] at hi'
    exact ep.hasSum_iff.mp hi'
  · intro f s h
    simpa using
      (hasSum_fintype (fun n : PEmpty → ℤ => ∏ i, f i (n i)))
  · intro α _ ih f s h
    let e : (Option α → ℤ) ≃ ℤ × (α → ℤ) := Equiv.piOptionEquivProd
    have hnone := h none
    have hsome := ih (fun i n => f (some i) n) (fun i => s (some i))
      (fun i => h (some i))
    have hjoint : Summable (fun p : ℤ × (α → ℤ) =>
        f none p.1 * ∏ i, f (some i) (p.2 i)) :=
      summable_mul_of_summable_norm
        (f := f none) (g := fun n : α → ℤ => ∏ i, f (some i) (n i))
        hnone.summable.norm hsome.summable.norm
    have htsum := tsum_mul_tsum_of_summable_norm
      (f := f none) (g := fun n : α → ℤ => ∏ i, f (some i) (n i))
      hnone.summable.norm hsome.summable.norm
    rw [hnone.tsum_eq, hsome.tsum_eq] at htsum
    have hp : HasSum (fun p : ℤ × (α → ℤ) =>
        f none p.1 * ∏ i, f (some i) (p.2 i))
        (s none * ∏ i, s (some i)) :=
      hjoint.hasSum_iff.mpr htsum.symm
    have heqf : (fun p : ℤ × (α → ℤ) =>
        f none p.1 * ∏ i, f (some i) (p.2 i)) =
        (fun n : Option α → ℤ => ∏ i, f i (n i)) ∘ e.symm := by
      funext p
      simp [e, Equiv.piOptionEquivProd_symm_apply]
    have heqs : s none * ∏ i, s (some i) = ∏ i, s i := by
      rw [Fintype.prod_option]
    rw [heqf, heqs] at hp
    exact e.symm.hasSum_iff.mp hp

private theorem complex_prod_re {d : ℕ} (f : Fin d → ℝ) :
    (∏ i, (f i : ℂ)).re = ∏ i, f i := by
  have hc : (((∏ i, f i : ℝ) : ℂ)) = ∏ i, (f i : ℂ) := by
    simpa using Complex.ofReal_prod Finset.univ f
  exact (congrArg Complex.re hc.symm).trans (Complex.ofReal_re _)

private theorem complex_pow_re (r : ℝ) (d : ℕ) :
    (((r : ℂ) ^ d).re) = r ^ d := by
  exact (congrArg Complex.re (Complex.ofReal_pow r d).symm).trans
    (Complex.ofReal_re _)

theorem bartonMinorant_hasSum
    {d : ℕ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    HasSum (fun n : Fin d → ℤ => bartonMinorant a b δ (fun k => n k))
      (2 * (b - a) ^ d - ((b - a) + δ⁻¹) ^ d) := by
  have hV1 := intervalCenterUnmodulated_hasSum_length hab hδ hδ1
  have hC1 := selbergUnmodulated_hasSum_mass hab hδ hδ1
  have hV := hasSum_pi_prod (α := Fin d)
    (fun _ n => (intervalCenter a b δ (n : ℝ) : ℂ))
    (fun _ => ((b - a : ℝ) : ℂ)) (fun _ => hV1)
  have hC := hasSum_pi_prod (α := Fin d)
    (fun _ n => (selbergIntervalMajorant a b δ (n : ℝ) : ℂ))
    (fun _ => ((((b - a) + δ⁻¹ : ℝ)) : ℂ)) (fun _ => hC1)
  have hcomplex := (hV.mul_left 2).sub hC
  have hreal := Complex.hasSum_re hcomplex
  convert hreal using 1
  · funext n
    rw [Complex.sub_re, Complex.mul_re]
    norm_num
    rw [complex_prod_re, complex_prod_re]
    simp [bartonMinorant]
  · rw [Complex.sub_re, Complex.mul_re]
    norm_num
    have hbase1 : ((b : ℂ) - a) = ((b - a : ℝ) : ℂ) := by push_cast; rfl
    have hbase2 : (((b - a : ℝ) : ℂ) + (δ : ℂ)⁻¹) =
        (((b - a) + δ⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [hbase1, hbase2, complex_pow_re, complex_pow_re]

theorem bartonMajorant_hasSum
    {d : ℕ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    HasSum (fun n : Fin d → ℤ => bartonMajorant a b δ (fun k => n k))
      (((b - a) + δ⁻¹) ^ d) := by
  have hC1 := selbergUnmodulated_hasSum_mass hab hδ hδ1
  have hC := hasSum_pi_prod (α := Fin d)
    (fun _ n => (selbergIntervalMajorant a b δ (n : ℝ) : ℂ))
    (fun _ => ((((b - a) + δ⁻¹ : ℝ)) : ℂ)) (fun _ => hC1)
  have hreal := Complex.hasSum_re hC
  convert hreal using 1
  · funext n
    rw [complex_prod_re]
    rfl
  · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, complex_pow_re]

theorem bartonMinorantModulated_hasSum_zero
    {d : ℕ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    {u v : Fin d → ℝ}
    (hsep : ∃ k, δ ≤ circleDist (v k - u k) 0) :
    HasSum (fun n : Fin d → ℤ =>
      (bartonMinorant a b δ (fun k => n k) : ℂ) *
        Complex.exp (-2 * Real.pi * Complex.I *
          ∑ k, ((n k : ℤ) : ℂ) * (v k - u k))) 0 := by
  obtain ⟨k, hk⟩ := hsep
  let phase : Fin d → ℤ → ℂ := fun i n => echar (v i - u i) (n : ℝ)
  let Vf : Fin d → ℤ → ℂ := fun i n =>
    (intervalCenter a b δ (n : ℝ) : ℂ) * phase i n
  let Cf : Fin d → ℤ → ℂ := fun i n =>
    (selbergIntervalMajorant a b δ (n : ℝ) : ℂ) * phase i n
  have hVcomp : ∀ i, Summable (Vf i) := by
    intro i
    have hCsum := selbergIntervalMajorant_mul_echar_int_summable
      hab hδ (v i - u i)
    have hAsum := selbergIntervalMajorant_mul_echar_int_summable
      (a := a) (b := a) le_rfl hδ (v i - u i)
    have hBsum := selbergIntervalMajorant_mul_echar_int_summable
      (a := b) (b := b) le_rfl hδ (v i - u i)
    exact hCsum.sub ((hAsum.add hBsum).mul_left (1 / 2 : ℂ)) |>.congr
      (fun n => by simp [Vf, phase, intervalCenter, intervalError]; push_cast; ring)
  have hCcomp : ∀ i, Summable (Cf i) := fun i =>
    (selbergIntervalMajorant_mul_echar_int_summable hab hδ (v i - u i)).congr
      (fun n => by rfl)
  have hVk : HasSum (Vf k) 0 := by
    simpa [Vf, phase] using intervalCenterModulated_hasSum_zero hab hδ hk
  have hCk : HasSum (Cf k) 0 := by
    simpa [Cf, phase] using selbergModulated_hasSum_zero hab hδ hk
  have hVprod := hasSum_pi_prod (α := Fin d) Vf
    (fun i => if i = k then 0 else ∑' n, Vf i n)
    (fun i => by
      by_cases hik : i = k
      · subst i
        simpa using hVk
      · simp [hik]
        exact (hVcomp i).hasSum)
  have hCprod := hasSum_pi_prod (α := Fin d) Cf
    (fun i => if i = k then 0 else ∑' n, Cf i n)
    (fun i => by
      by_cases hik : i = k
      · subst i
        simpa using hCk
      · simp [hik]
        exact (hCcomp i).hasSum)
  have hVzero : (∏ i, if i = k then 0 else ∑' n, Vf i n) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp
  have hCzero : (∏ i, if i = k then 0 else ∑' n, Cf i n) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp
  rw [hVzero] at hVprod
  rw [hCzero] at hCprod
  have h := (hVprod.mul_left 2).sub hCprod
  have hz : (2 : ℂ) * 0 - 0 = 0 := by ring
  rw [hz] at h
  exact HasSum.congr_fun h (fun n => by
    have hphase :
        ∏ i, phase i (n i) =
          Complex.exp (-2 * Real.pi * Complex.I *
            ∑ i, ((n i : ℤ) : ℂ) * (v i - u i)) := by
      simp only [phase, echar, ← Complex.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring
    simp only [bartonMinorant]
    simp only [Vf, Cf, Finset.prod_mul_distrib, hphase]
    push_cast
    ring)

theorem bartonMajorantModulated_hasSum_zero
    {d : ℕ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    {u v : Fin d → ℝ}
    (hsep : ∃ k, δ ≤ circleDist (v k - u k) 0) :
    HasSum (fun n : Fin d → ℤ =>
      (bartonMajorant a b δ (fun k => n k) : ℂ) *
        Complex.exp (-2 * Real.pi * Complex.I *
          ∑ k, ((n k : ℤ) : ℂ) * (v k - u k))) 0 := by
  obtain ⟨k, hk⟩ := hsep
  let phase : Fin d → ℤ → ℂ := fun i n => echar (v i - u i) (n : ℝ)
  let Cf : Fin d → ℤ → ℂ := fun i n =>
    (selbergIntervalMajorant a b δ (n : ℝ) : ℂ) * phase i n
  have hCcomp : ∀ i, Summable (Cf i) := fun i =>
    (selbergIntervalMajorant_mul_echar_int_summable hab hδ (v i - u i)).congr
      (fun n => by rfl)
  have hCk : HasSum (Cf k) 0 := by
    simpa [Cf, phase] using selbergModulated_hasSum_zero hab hδ hk
  have hCprod := hasSum_pi_prod (α := Fin d) Cf
    (fun i => if i = k then 0 else ∑' n, Cf i n)
    (fun i => by
      by_cases hik : i = k
      · subst i
        simpa using hCk
      · simp [hik]
        exact (hCcomp i).hasSum)
  have hCzero : (∏ i, if i = k then 0 else ∑' n, Cf i n) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp
  rw [hCzero] at hCprod
  exact HasSum.congr_fun hCprod (fun n => by
    have hphase :
        ∏ i, phase i (n i) =
          Complex.exp (-2 * Real.pi * Complex.I *
            ∑ i, ((n i : ℤ) : ℂ) * (v i - u i)) := by
      simp only [phase, echar, ← Complex.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring
    simp only [bartonMajorant, Cf, Finset.prod_mul_distrib, hphase]
    push_cast
    ring)

/-- Integer lattice points of the one-sided cube `{0, ..., N - 1}^d`. -/
def oneSidedFrequencyValues (d N : ℕ) : Finset (Fin d → ℤ) := by
  classical
  exact Finset.univ.image fun n : Fin d → Fin N => fun k => (n k : ℤ)

private theorem oneSidedFrequencyValue_injective (d N : ℕ) :
    Function.Injective
      (fun n : Fin d → Fin N => fun k => (n k : ℤ)) := by
  intro n m h
  funext k
  have hk := congrFun h k
  change (((n k : Fin N) : ℕ) : ℤ) = (((m k : Fin N) : ℕ) : ℤ) at hk
  norm_cast at hk
  exact Fin.ext hk

theorem oneSided_mem_iff
    {d N : ℕ} (n : Fin d → ℤ) :
    n ∈ oneSidedFrequencyValues d N ↔
      ∀ k, 0 ≤ n k ∧ n k < N := by
  classical
  constructor
  · intro hn k
    rw [oneSidedFrequencyValues, Finset.mem_image] at hn
    obtain ⟨m, _, rfl⟩ := hn
    constructor
    · change (0 : ℤ) ≤ (m k : ℕ)
      exact Int.natCast_nonneg _
    · change ((m k : ℕ) : ℤ) < (N : ℤ)
      exact_mod_cast (m k).isLt
  · intro hn
    let m : Fin d → Fin N := fun k =>
      ⟨(n k).toNat, by
        have h0 := (hn k).1
        have hlt := (hn k).2
        have hN : N ≠ 0 := by
          intro hN
          subst N
          omega
        exact (Int.toNat_lt_of_ne_zero hN).2 hlt⟩
    rw [oneSidedFrequencyValues, Finset.mem_image]
    refine ⟨m, Finset.mem_univ _, ?_⟩
    funext k
    change ((n k).toNat : ℤ) = n k
    exact Int.toNat_of_nonneg (hn k).1

private theorem translatedCubeFourierEnergy_eq_latticeBlock
    {d N : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → External.UnitTorusPoint d) (c : ι → ℂ) :
    External.translatedCubeFourierEnergy N x c =
      ∑ n ∈ oneSidedFrequencyValues d N,
        ‖SeparatedCubeFourierInternal.integerLatticeFourierValue x c n‖ ^ 2 := by
  classical
  unfold External.translatedCubeFourierEnergy oneSidedFrequencyValues
  rw [Finset.sum_image]
  · rfl
  · intro n _ m _ hnm
    exact oneSidedFrequencyValue_injective d N hnm

theorem unitPeriodicLInfDistance_le_half
    {d : ℕ} (u v : External.UnitTorusPoint d)
    (hu : External.InUnitHalfOpenCube u)
    (hv : External.InUnitHalfOpenCube v) :
    External.unitPeriodicLInfDistance u v ≤ 1 / 2 := by
  unfold External.unitPeriodicLInfDistance
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  intro k
  rw [Real.norm_eq_abs]
  have hcoord : External.unitPeriodicCoordinateDistance (u k) (v k) ≤ 1 / 2 := by
    unfold External.unitPeriodicCoordinateDistance
    by_cases h : |u k - v k| ≤ 1 / 2
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)
  have hcoord0 : 0 ≤ External.unitPeriodicCoordinateDistance (u k) (v k) := by
    exact SeparatedCubeFourierInternal.unitPeriodicCoordinateDistance_nonneg
      (hu k) (hv k)
  rwa [abs_of_nonneg hcoord0]

private theorem phase_cross_term
    {d : ℕ} (n : Fin d → ℤ)
    (u v : External.UnitTorusPoint d) (a b : ℂ) :
    star
        (a * Complex.exp
          (-2 * Real.pi * Complex.I *
            ∑ k, ((n k : ℤ) : ℂ) * u k)) *
        (b * Complex.exp
          (-2 * Real.pi * Complex.I *
            ∑ k, ((n k : ℤ) : ℂ) * v k)) =
      star a * b *
        Complex.exp
          (-2 * Real.pi * Complex.I *
            ∑ k, ((n k : ℤ) : ℂ) * (v k - u k)) := by
  rw [star_mul, Complex.star_def, ← Complex.exp_conj]
  have hconj :
      (starRingEnd ℂ)
          (-2 * Real.pi * Complex.I *
            ∑ k, ((n k : ℤ) : ℂ) * u k) =
        2 * Real.pi * Complex.I *
          ∑ k, ((n k : ℤ) : ℂ) * u k := by
    simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I, map_sum, map_intCast]
    ring
  rw [hconj]
  calc
    _ = star a * b *
        (Complex.exp
            (2 * Real.pi * Complex.I *
              ∑ k, ((n k : ℤ) : ℂ) * u k) *
          Complex.exp
            (-2 * Real.pi * Complex.I *
              ∑ k, ((n k : ℤ) : ℂ) * v k)) := by ac_rfl
    _ = star a * b *
        Complex.exp
          (2 * Real.pi * Complex.I *
              ∑ k, ((n k : ℤ) : ℂ) * u k +
            -2 * Real.pi * Complex.I *
              ∑ k, ((n k : ℤ) : ℂ) * v k) := by rw [Complex.exp_add]
    _ = _ := by
      congr 2
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem translatedCube_lower_of_barton
    {d N : ℕ} {ι : Type*} [Fintype ι]
    (a b δ W : ℝ) (x : ι → External.UnitTorusPoint d) (c : ι → ℂ)
    (hblock : ∀ n : Fin d → ℤ,
      bartonMinorant a b δ (fun k => n k) ≤
        if n ∈ oneSidedFrequencyValues d N then 1 else 0)
    (hsum : HasSum
      (fun n : Fin d → ℤ => bartonMinorant a b δ (fun k => n k)) W)
    (hcross : ∀ i j, i ≠ j →
      HasSum (fun n : Fin d → ℤ =>
        (bartonMinorant a b δ (fun k => n k) : ℂ) *
          Complex.exp (-2 * Real.pi * Complex.I *
            ∑ k, ((n k : ℤ) : ℂ) * (x j k - x i k))) 0) :
    W * External.coefficientEnergy c ≤
      External.translatedCubeFourierEnergy N x c := by
  let w : (Fin d → ℤ) → ℝ := fun n =>
    bartonMinorant a b δ (fun k => n k)
  have hweighted :=
    SeparatedCubeFourierInternal.weighted_lattice_energy_hasSum
      w W x c hsum (fun i j hij => by
        have hc := (hcross i j hij).mul_left (star (c i) * c j)
        have hr := Complex.hasSum_re hc
        convert hr using 1
        · funext n
          rw [phase_cross_term]
          have heq :
              (w n : ℂ) *
                  (star (c i) * c j * Complex.exp
                    (-2 * Real.pi * Complex.I *
                      ∑ k, ((n k : ℤ) : ℂ) * (x j k - x i k))) =
                star (c i) * c j *
                  ((bartonMinorant a b δ (fun k => n k) : ℂ) *
                    Complex.exp
                      (-2 * Real.pi * Complex.I *
                        ∑ k, ((n k : ℤ) : ℂ) * (x j k - x i k))) := by
            dsimp [w]
            push_cast
            ring
          simpa [Complex.mul_re] using congrArg Complex.re heq
        · simp)
  have hle := weighted_series_le_block
    (oneSidedFrequencyValues d N) w
    (fun n => ‖SeparatedCubeFourierInternal.integerLatticeFourierValue x c n‖ ^ 2)
    (W * External.coefficientEnergy c)
    (fun _ => sq_nonneg _)
    (fun n hn => by simpa [hn] using hblock n)
    (fun n hn => by simpa [hn] using hblock n)
    hweighted
  rwa [← translatedCubeFourierEnergy_eq_latticeBlock] at hle

theorem translatedCube_upper_of_barton
    {d N : ℕ} {ι : Type*} [Fintype ι]
    (a b δ W : ℝ) (x : ι → External.UnitTorusPoint d) (c : ι → ℂ)
    (hblock : ∀ n : Fin d → ℤ,
      (if n ∈ oneSidedFrequencyValues d N then 1 else 0) ≤
        bartonMajorant a b δ (fun k => n k))
    (hnonneg : ∀ n : Fin d → ℤ,
      0 ≤ bartonMajorant a b δ (fun k => n k))
    (hsum : HasSum
      (fun n : Fin d → ℤ => bartonMajorant a b δ (fun k => n k)) W)
    (hcross : ∀ i j, i ≠ j →
      HasSum (fun n : Fin d → ℤ =>
        (bartonMajorant a b δ (fun k => n k) : ℂ) *
          Complex.exp (-2 * Real.pi * Complex.I *
            ∑ k, ((n k : ℤ) : ℂ) * (x j k - x i k))) 0) :
    External.translatedCubeFourierEnergy N x c ≤
      W * External.coefficientEnergy c := by
  let w : (Fin d → ℤ) → ℝ := fun n =>
    bartonMajorant a b δ (fun k => n k)
  have hweighted :=
    SeparatedCubeFourierInternal.weighted_lattice_energy_hasSum
      w W x c hsum (fun i j hij => by
        have hc := (hcross i j hij).mul_left (star (c i) * c j)
        have hr := Complex.hasSum_re hc
        convert hr using 1
        · funext n
          rw [phase_cross_term]
          have heq :
              (w n : ℂ) *
                  (star (c i) * c j * Complex.exp
                    (-2 * Real.pi * Complex.I *
                      ∑ k, ((n k : ℤ) : ℂ) * (x j k - x i k))) =
                star (c i) * c j *
                  ((bartonMajorant a b δ (fun k => n k) : ℂ) *
                    Complex.exp
                      (-2 * Real.pi * Complex.I *
                        ∑ k, ((n k : ℤ) : ℂ) * (x j k - x i k))) := by
            dsimp [w]
            push_cast
            ring
          simpa [Complex.mul_re] using congrArg Complex.re heq
        · simp)
  have hle := block_le_weighted_series
    (oneSidedFrequencyValues d N) w
    (fun n => ‖SeparatedCubeFourierInternal.integerLatticeFourierValue x c n‖ ^ 2)
    (W * External.coefficientEnergy c)
    (fun _ => sq_nonneg _)
    (fun n hn => by simpa [hn] using hblock n)
    (fun n => hnonneg n)
    hweighted
  rwa [← translatedCubeFourierEnergy_eq_latticeBlock] at hle

theorem exp_bound
    {d : ℕ} {β : ℝ} (hd : 1 ≤ d) (hβ : 0 < β) :
    (1 + 1 / (2 * β * d)) ^ d ≤ Real.exp (1 / (2 * β)) := by
  have hbase := Real.add_one_le_exp (1 / (2 * β * (d : ℝ)))
  have hp : (1 + 1 / (2 * β * (d : ℝ))) ^ d ≤
      (Real.exp (1 / (2 * β * (d : ℝ)))) ^ d := by
    gcongr
    simpa [add_comm] using hbase
  calc
    (1 + 1 / (2 * β * (d : ℝ))) ^ d ≤
        (Real.exp (1 / (2 * β * (d : ℝ)))) ^ d := hp
    _ = Real.exp ((d : ℝ) * (1 / (2 * β * (d : ℝ)))) := by
      rw [← Real.exp_nat_mul]
    _ = Real.exp (1 / (2 * β)) := by
      congr 1
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
      field_simp

theorem singleton_translatedCube_lower
    {d N : ℕ} {ι : Type*} [Fintype ι] [Subsingleton ι]
    (x : ι → External.UnitTorusPoint d) (c : ι → ℂ) :
    (N ^ d : ℕ) * External.coefficientEnergy c ≤
      External.translatedCubeFourierEnergy N x c := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => simp [External.translatedCubeFourierEnergy,
      External.coefficientEnergy]
  | inr h =>
      let j : ι := Classical.choice h
      have hsum (n : External.OneSidedCubeFrequency d N) :
          (∑ q, c q * Complex.exp
            (-2 * Real.pi * Complex.I *
              ∑ k, (((n k : Fin N) : ℕ) : ℂ) * x q k)) =
            c j * Complex.exp
              (-2 * Real.pi * Complex.I *
                ∑ k, (((n k : Fin N) : ℕ) : ℂ) * x j k) := by
        apply Fintype.sum_eq_single j
        intro q hq
        exact (hq (Subsingleton.elim q j)).elim
      have hcoeff : External.coefficientEnergy c = ‖c j‖ ^ 2 := by
        unfold External.coefficientEnergy
        apply Fintype.sum_eq_single j
        intro q hq
        exact (hq (Subsingleton.elim q j)).elim
      rw [External.translatedCubeFourierEnergy, hcoeff]
      simp_rw [hsum, norm_mul, Complex.norm_exp]
      have hre (n : External.OneSidedCubeFrequency d N) :
          (-2 * Real.pi * Complex.I *
            ∑ k, (((n k : Fin N) : ℕ) : ℂ) * x j k).re = 0 := by
        have hreal :
            (∑ k, (((n k : Fin N) : ℕ) : ℂ) * x j k) =
              ((∑ k, ((n k : Fin N) : ℕ) * x j k : ℝ) : ℂ) := by
          push_cast
          rfl
        rw [hreal]
        simp
      simp_rw [hre, Real.exp_zero, mul_one, Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin]
      simp [nsmul_eq_mul]

theorem singleton_translatedCube_energy_eq
    {d N : ℕ} {ι : Type*} [Fintype ι] [Subsingleton ι]
    (x : ι → External.UnitTorusPoint d) (c : ι → ℂ) :
    External.translatedCubeFourierEnergy N x c =
      (N ^ d : ℕ) * External.coefficientEnergy c := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => simp [External.translatedCubeFourierEnergy,
      External.coefficientEnergy]
  | inr h =>
      let j : ι := Classical.choice h
      have hsum (n : External.OneSidedCubeFrequency d N) :
          (∑ q, c q * Complex.exp
            (-2 * Real.pi * Complex.I *
              ∑ k, (((n k : Fin N) : ℕ) : ℂ) * x q k)) =
            c j * Complex.exp
              (-2 * Real.pi * Complex.I *
                ∑ k, (((n k : Fin N) : ℕ) : ℂ) * x j k) := by
        apply Fintype.sum_eq_single j
        intro q hq
        exact (hq (Subsingleton.elim q j)).elim
      have hcoeff : External.coefficientEnergy c = ‖c j‖ ^ 2 := by
        unfold External.coefficientEnergy
        apply Fintype.sum_eq_single j
        intro q hq
        exact (hq (Subsingleton.elim q j)).elim
      rw [External.translatedCubeFourierEnergy, hcoeff]
      simp_rw [hsum, norm_mul, Complex.norm_exp]
      have hre (n : External.OneSidedCubeFrequency d N) :
          (-2 * Real.pi * Complex.I *
            ∑ k, (((n k : Fin N) : ℕ) : ℂ) * x j k).re = 0 := by
        have hreal :
            (∑ k, (((n k : Fin N) : ℕ) : ℂ) * x j k) =
              ((∑ k, ((n k : Fin N) : ℕ) * x j k : ℝ) : ℂ) := by
          push_cast
          rfl
        rw [hreal]
        simp
      simp_rw [hre, Real.exp_zero, mul_one, Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin]
      simp [nsmul_eq_mul]

end

end TranslatedCubeFourier
end LeanNumDetect

namespace External

noncomputable section

open LeanNumDetect

/-- The translated-cube lower frame bound obtained from Barton's `M₃⁻`
minorant and Vaaler--Selberg Poisson summation. -/
theorem translatedCubeFourier_lowerFrame
    {d N : ℕ} {ι : Type*} [Fintype ι]
    (β : ℝ) (x : ι → UnitTorusPoint d)
    (hd : 1 ≤ d) (hN : 2 ≤ N)
    (hβ : 1 / (2 * Real.log 2) ≤ β)
    (hx : ∀ j, InUnitHalfOpenCube (x j))
    (hsep : ∀ i j, i ≠ j →
      2 * β * d / N ≤ unitPeriodicLInfDistance (x i) (x j)) :
    ∀ c,
      (2 - Real.exp (1 / (2 * β))) * (N ^ d : ℕ) *
          coefficientEnergy c ≤
        translatedCubeFourierEnergy N x c := by
  intro c
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have hexp2 : Real.exp (1 / (2 * β)) ≤ 2 := by
    have harg : 1 / (2 * β) ≤ Real.log 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * β)).2
      have hb := (div_le_iff₀ (mul_pos (by norm_num) hlog0)).1 hβ
      nlinarith
    calc
      Real.exp (1 / (2 * β)) ≤ Real.exp (Real.log 2) :=
        Real.exp_le_exp.mpr harg
      _ = 2 := Real.exp_log (by norm_num)
  have htarget0 : 0 ≤ 2 - Real.exp (1 / (2 * β)) := by linarith
  letI : Decidable (Nontrivial ι) := Classical.dec _
  by_cases hι : Nontrivial ι
  · let δ : ℝ := 2 * β * d / N
    let a : ℝ := -(1 : ℝ) / 2
    let b : ℝ := N - (1 : ℝ) / 2
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    have hab : a ≤ b := by
      dsimp [a, b]
      have hN0 : (0 : ℝ) ≤ N := by positivity
      linarith
    obtain ⟨i, j, hij⟩ := exists_pair_ne ι
    have hδhalf : δ ≤ 1 / 2 :=
      (hsep i j hij).trans
        (TranslatedCubeFourier.unitPeriodicLInfDistance_le_half
          (x i) (x j) (hx i) (hx j))
    have hδ1 : δ ≤ 1 := hδhalf.trans (by norm_num)
    have hβhalf : (1 : ℝ) / 2 < β := by
      have hinv : (1 : ℝ) / 2 < 1 / (2 * Real.log 2) := by
        apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)
          (mul_pos (by norm_num) hlog0)).2
        nlinarith
      exact hinv.trans_le hβ
    have hwidth : 1 ≤ δ * (b - a) := by
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hmain : 1 ≤ 2 * β * (d : ℝ) := by nlinarith
      calc
        1 ≤ 2 * β * (d : ℝ) := hmain
        _ = δ * (b - a) := by
          dsimp [δ, a, b]
          have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
          field_simp
          ring
    let W : ℝ := 2 * (N : ℝ) ^ d - ((N : ℝ) + δ⁻¹) ^ d
    have hsum : HasSum
        (fun n : Fin d → ℤ =>
          TranslatedCubeFourier.bartonMinorant a b δ (fun k => n k)) W := by
      have hs := TranslatedCubeFourier.bartonMinorant_hasSum
        (d := d) hab hδ hδ1
      convert hs using 1 <;> dsimp [W, a, b] <;> ring
    have hblock (n : Fin d → ℤ) :
        TranslatedCubeFourier.bartonMinorant a b δ (fun k => n k) ≤
          if n ∈ TranslatedCubeFourier.oneSidedFrequencyValues d N then 1 else 0 := by
      simp only [TranslatedCubeFourier.oneSided_mem_iff]
      have hs := TranslatedCubeFourier.bartonMinorant_le_boxIndicator
        hab hδ hwidth (fun k => (n k : ℝ))
      have hiff :
          (∀ k, a ≤ (n k : ℝ) ∧ (n k : ℝ) ≤ b) ↔
            ∀ k, 0 ≤ n k ∧ n k < N := by
        constructor
        · intro h k
          have hk := h k
          dsimp [a, b] at hk
          constructor
          · have hneg1R : (-1 : ℝ) < n k := by linarith
            have hneg1 : (-1 : ℤ) < n k := by exact_mod_cast hneg1R
            omega
          · exact_mod_cast (show (n k : ℝ) < N by linarith)
        · intro h k
          have hk := h k
          dsimp [a, b]
          have hk0 : (0 : ℝ) ≤ n k := by exact_mod_cast hk.1
          have hkN : (n k : ℝ) < N := by exact_mod_cast hk.2
          have hkNle : n k ≤ (N : ℤ) - 1 := by omega
          have hkNleR : (n k : ℝ) ≤ (N : ℝ) - 1 := by
            exact_mod_cast hkNle
          constructor <;> linarith
      simpa [hiff] using hs
    have hcross : ∀ i j, i ≠ j →
        HasSum (fun n : Fin d → ℤ =>
          (TranslatedCubeFourier.bartonMinorant a b δ (fun k => n k) : ℂ) *
            Complex.exp (-2 * Real.pi * Complex.I *
              ∑ k, ((n k : ℤ) : ℂ) * (x j k - x i k))) 0 := by
      intro p q hpq
      obtain ⟨k, hk⟩ :=
        SeparatedCubeFourierInternal.exists_coordinate_integer_separation
          (by omega) (hx p) (hx q) (hsep p q hpq)
      apply TranslatedCubeFourier.bartonMinorantModulated_hasSum_zero hab hδ
      refine ⟨k, MathExtras.NumberTheory.Analysis.LargeSieve.le_circleDist_of_forall_int
        (fun m => ?_)⟩
      have h := hk (-m)
      push_cast at h ⊢
      simp only [sub_zero]
      rw [show x q k - x p k - (m : ℝ) =
        -(x p k - x q k + (m : ℝ)) by ring, abs_neg]
      simpa [δ] using h
    have hframe := TranslatedCubeFourier.translatedCube_lower_of_barton
      a b δ W x c hblock hsum hcross
    have hmass :
        (2 - Real.exp (1 / (2 * β))) * (N : ℝ) ^ d ≤ W := by
      have hexp := TranslatedCubeFourier.exp_bound hd hβ0
      have hN0 : (0 : ℝ) < N := by positivity
      have hδinv : δ⁻¹ = (N : ℝ) / (2 * β * d) := by
        dsimp [δ]
        field_simp
      have hfactor :
          ((N : ℝ) + δ⁻¹) ^ d =
            (N : ℝ) ^ d * (1 + 1 / (2 * β * d)) ^ d := by
        rw [hδinv]
        have hbasefactor :
            (N : ℝ) + (N : ℝ) / (2 * β * d) =
              (N : ℝ) * (1 + 1 / (2 * β * d)) := by ring
        rw [hbasefactor]
        rw [mul_pow]
      dsimp [W]
      rw [hfactor]
      nlinarith [pow_nonneg hN0.le d]
    have henergy : 0 ≤ coefficientEnergy c :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    simpa only [Nat.cast_pow] using
      (mul_le_mul_of_nonneg_right hmass henergy).trans hframe
  · haveI : Subsingleton ι := not_nontrivial_iff_subsingleton.mp hι
    have hsingle := TranslatedCubeFourier.singleton_translatedCube_lower
      (N := N) x c
    have hscale :
        (2 - Real.exp (1 / (2 * β))) * (N ^ d : ℕ) * coefficientEnergy c ≤
          (N ^ d : ℕ) * coefficientEnergy c := by
      have henergy : 0 ≤ coefficientEnergy c :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hcoef : 2 - Real.exp (1 / (2 * β)) ≤ 1 := by
        linarith [Real.one_le_exp (show 0 ≤ 1 / (2 * β) by positivity)]
      have hnonneg : 0 ≤ (N ^ d : ℕ) * coefficientEnergy c :=
        mul_nonneg (by positivity) henergy
      calc
        (2 - Real.exp (1 / (2 * β))) * (N ^ d : ℕ) * coefficientEnergy c =
            (2 - Real.exp (1 / (2 * β))) *
              ((N ^ d : ℕ) * coefficientEnergy c) := by ring
        _ ≤ 1 * ((N ^ d : ℕ) * coefficientEnergy c) :=
          mul_le_mul_of_nonneg_right hcoef hnonneg
        _ = (N ^ d : ℕ) * coefficientEnergy c := by ring
    exact hscale.trans hsingle

/-- The translated-cube upper frame bound obtained from the tensor-product
Selberg majorant. -/
theorem translatedCubeFourier_upperFrame
    {d N : ℕ} {ι : Type*} [Fintype ι]
    (β : ℝ) (x : ι → UnitTorusPoint d)
    (hd : 1 ≤ d) (hN : 2 ≤ N)
    (hβ : 1 / (2 * Real.log 2) ≤ β)
    (hx : ∀ j, InUnitHalfOpenCube (x j))
    (hsep : ∀ i j, i ≠ j →
      2 * β * d / N ≤ unitPeriodicLInfDistance (x i) (x j)) :
    ∀ c,
      translatedCubeFourierEnergy N x c ≤
        Real.exp (1 / (2 * β)) * (N ^ d : ℕ) * coefficientEnergy c := by
  intro c
  have hβ0 : 0 < β := by
    have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact (by positivity : 0 < 1 / (2 * Real.log 2)).trans_le hβ
  letI : Decidable (Nontrivial ι) := Classical.dec _
  by_cases hι : Nontrivial ι
  · let δ : ℝ := 2 * β * d / N
    let a : ℝ := -(1 : ℝ) / 2
    let b : ℝ := N - (1 : ℝ) / 2
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    have hab : a ≤ b := by
      dsimp [a, b]
      have hN0 : (0 : ℝ) ≤ N := by positivity
      linarith
    obtain ⟨i, j, hij⟩ := exists_pair_ne ι
    have hδhalf : δ ≤ 1 / 2 :=
      (hsep i j hij).trans
        (TranslatedCubeFourier.unitPeriodicLInfDistance_le_half
          (x i) (x j) (hx i) (hx j))
    have hδ1 : δ ≤ 1 := hδhalf.trans (by norm_num)
    let W : ℝ := ((N : ℝ) + δ⁻¹) ^ d
    have hsum : HasSum
        (fun n : Fin d → ℤ =>
          TranslatedCubeFourier.bartonMajorant a b δ (fun k => n k)) W := by
      have hs := TranslatedCubeFourier.bartonMajorant_hasSum
        (d := d) hab hδ hδ1
      convert hs using 1 <;> dsimp [W, a, b] <;> ring
    have hblock (n : Fin d → ℤ) :
        (if n ∈ TranslatedCubeFourier.oneSidedFrequencyValues d N then 1 else 0) ≤
          TranslatedCubeFourier.bartonMajorant a b δ (fun k => n k) := by
      have hs := TranslatedCubeFourier.boxIndicator_le_bartonMajorant
        hab hδ (fun k => (n k : ℝ))
      have hiff :
          (∀ k, a < (n k : ℝ) ∧ (n k : ℝ) ≤ b) ↔
            ∀ k, 0 ≤ n k ∧ n k < N := by
        constructor
        · intro h k
          have hk := h k
          dsimp [a, b] at hk
          constructor
          · have hneg1R : (-1 : ℝ) < n k := by linarith
            have hneg1 : (-1 : ℤ) < n k := by exact_mod_cast hneg1R
            omega
          · exact_mod_cast (show (n k : ℝ) < N by linarith)
        · intro h k
          have hk := h k
          dsimp [a, b]
          have hk0 : (0 : ℝ) ≤ n k := by exact_mod_cast hk.1
          have hkN : n k ≤ (N : ℤ) - 1 := by omega
          have hkNleR : (n k : ℝ) ≤ (N : ℝ) - 1 := by
            exact_mod_cast hkN
          constructor <;> linarith
      by_cases hn : n ∈ TranslatedCubeFourier.oneSidedFrequencyValues d N
      · rw [if_pos hn]
        have hp := hiff.mpr
          ((TranslatedCubeFourier.oneSided_mem_iff n).mp hn)
        simpa [hp] using hs
      · rw [if_neg hn]
        exact TranslatedCubeFourier.bartonMajorant_nonneg hab hδ _
    have hnonneg (n : Fin d → ℤ) :
        0 ≤ TranslatedCubeFourier.bartonMajorant a b δ (fun k => n k) := by
      exact TranslatedCubeFourier.bartonMajorant_nonneg hab hδ _
    have hcross : ∀ i j, i ≠ j →
        HasSum (fun n : Fin d → ℤ =>
          (TranslatedCubeFourier.bartonMajorant a b δ (fun k => n k) : ℂ) *
            Complex.exp (-2 * Real.pi * Complex.I *
              ∑ k, ((n k : ℤ) : ℂ) * (x j k - x i k))) 0 := by
      intro p q hpq
      obtain ⟨k, hk⟩ :=
        SeparatedCubeFourierInternal.exists_coordinate_integer_separation
          (by omega) (hx p) (hx q) (hsep p q hpq)
      apply TranslatedCubeFourier.bartonMajorantModulated_hasSum_zero hab hδ
      refine ⟨k, MathExtras.NumberTheory.Analysis.LargeSieve.le_circleDist_of_forall_int
        (fun m => ?_)⟩
      have h := hk (-m)
      push_cast at h ⊢
      simp only [sub_zero]
      rw [show x q k - x p k - (m : ℝ) =
        -(x p k - x q k + (m : ℝ)) by ring, abs_neg]
      simpa [δ] using h
    have hframe := TranslatedCubeFourier.translatedCube_upper_of_barton
      a b δ W x c hblock hnonneg hsum hcross
    have hexp := TranslatedCubeFourier.exp_bound hd hβ0
    have hN0 : (0 : ℝ) < N := by positivity
    have hδinv : δ⁻¹ = (N : ℝ) / (2 * β * d) := by
      dsimp [δ]
      field_simp
    have hfactor :
        W = (N : ℝ) ^ d * (1 + 1 / (2 * β * d)) ^ d := by
      dsimp [W]
      rw [hδinv]
      have hbasefactor :
          (N : ℝ) + (N : ℝ) / (2 * β * d) =
            (N : ℝ) * (1 + 1 / (2 * β * d)) := by ring
      rw [hbasefactor, mul_pow]
    have hmass : W ≤ Real.exp (1 / (2 * β)) * (N : ℝ) ^ d := by
      rw [hfactor]
      nlinarith [pow_nonneg hN0.le d]
    have henergy : 0 ≤ coefficientEnergy c :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc
      translatedCubeFourierEnergy N x c ≤ W * coefficientEnergy c := hframe
      _ ≤ (Real.exp (1 / (2 * β)) * (N : ℝ) ^ d) * coefficientEnergy c :=
        mul_le_mul_of_nonneg_right hmass henergy
      _ = Real.exp (1 / (2 * β)) * (N ^ d : ℕ) * coefficientEnergy c := by
        norm_cast
  · haveI : Subsingleton ι := not_nontrivial_iff_subsingleton.mp hι
    rw [TranslatedCubeFourier.singleton_translatedCube_energy_eq]
    have hexp : 1 ≤ Real.exp (1 / (2 * β)) :=
      Real.one_le_exp (by positivity)
    have henergy : 0 ≤ (N ^ d : ℕ) * coefficientEnergy c :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    calc
      (N ^ d : ℕ) * coefficientEnergy c ≤
          Real.exp (1 / (2 * β)) * ((N ^ d : ℕ) * coefficientEnergy c) :=
        le_mul_of_one_le_left henergy hexp
      _ = Real.exp (1 / (2 * β)) * (N ^ d : ℕ) * coefficientEnergy c := by ring

end

end External
