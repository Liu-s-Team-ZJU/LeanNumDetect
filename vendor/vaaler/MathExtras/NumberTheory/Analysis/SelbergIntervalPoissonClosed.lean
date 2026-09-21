/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.SelbergIntervalFourierClosed
import MathExtras.NumberTheory.Analysis.LargeSieveInequality
import MathExtras.Analysis.Fourier.ShiftedPoisson

/-!
# Poisson sampling for the closed Selberg interval majorant

This file supplies the decay and Poisson-summation bridge from the concrete
closed interval majorant to the real-endpoint large sieve.  In particular, no
regularity or Fourier-support fact is postulated: spatial quadratic decay comes
from the Lemma-5 envelope by the Fejer kernel, while Fourier decay is immediate
from the closed compact-band theorem.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology Complex Asymptotics
open scoped FourierTransform BigOperators

namespace MathExtras.NumberTheory.Analysis.SelbergIntervalPoissonClosed

open VaalerThm16Mechanism
open VaalerBeurlingNonneg
open VaalerBeurlingFT
open VaalerExcessFT
open VaalerCor7Closed
open VaalerPoUCancellation
open VaalerSumInvSqProof
open SelbergIntervalMajorantClosed
open SelbergIntervalFourierClosed
open LargeSieve

/-! ## Spatial quadratic decay -/

theorem phi_le_two_mul_fejerK (x : ℝ) : phi x ≤ 2 * fejerK x := by
  rw [phi_eq_excess_add_fejerK]
  have h := abs_excess_le_fejerK VaalerSumInvSqProof.vaalerSumInvSqIdentity_holds x
  have hex : excess x ≤ |excess x| := le_abs_self _
  linarith

theorem intervalSignPair_eq_zero_of_lt {a b x : ℝ} (hxa : x < a) (hab : a ≤ b) :
    intervalSignPair a b x = 0 := by
  unfold intervalSignPair
  have hxb : x < b := lt_of_lt_of_le hxa hab
  rw [Real.sign_of_pos (sub_pos.mpr hxb), Real.sign_of_neg (sub_neg.mpr hxa)]
  norm_num

theorem intervalSignPair_eq_zero_of_gt {a b x : ℝ} (hab : a ≤ b) (hbx : b < x) :
    intervalSignPair a b x = 0 := by
  unfold intervalSignPair
  have hax : a < x := lt_of_le_of_lt hab hbx
  rw [Real.sign_of_neg (sub_neg.mpr hbx), Real.sign_of_pos (sub_pos.mpr hax)]
  norm_num

/-- A shift changes the quadratic tail by at most a factor four once
`|x| >= 2|c|`. -/
theorem inv_sq_sub_le_four_mul_inv_sq {c x : ℝ}
    (hx0 : x ≠ 0) (hxc : 2 * |c| ≤ |x|) :
    ((x - c) ^ 2)⁻¹ ≤ 4 * (x ^ 2)⁻¹ := by
  have hhalf : |x| / 2 ≤ |x - c| := by
    have htri : |x| - |c| ≤ |x - c| := abs_sub_abs_le_abs_sub x c
    have hc : |c| ≤ |x| / 2 := by linarith
    linarith
  have hxabs : 0 < |x| := abs_pos.mpr hx0
  have hsubabs : 0 < |x - c| := lt_of_lt_of_le (by positivity : 0 < |x| / 2) hhalf
  have hsq : (x ^ 2) / 4 ≤ (x - c) ^ 2 := by
    rw [← sq_abs x, ← sq_abs (x - c)]
    nlinarith
  have hleft : 0 < (x ^ 2) / 4 := by positivity
  have hinv := one_div_le_one_div_of_le hleft hsq
  rw [one_div, one_div] at hinv
  calc
    ((x - c) ^ 2)⁻¹ ≤ ((x ^ 2) / 4)⁻¹ := hinv
    _ = 4 * (x ^ 2)⁻¹ := by field_simp

theorem phi_scaled_shift_le {δ c x : ℝ} (hδ : 0 < δ) (hx0 : x ≠ 0)
    (hxc : 2 * |c| ≤ |x|) :
    phi (δ * (x - c)) ≤ 8 * δ⁻¹ ^ 2 * (x ^ 2)⁻¹ := by
  have hsub0 : x - c ≠ 0 := by
    intro h
    have hxeq : x = c := sub_eq_zero.mp h
    rw [hxeq] at hxc hx0
    have : |c| = 0 := by nlinarith [abs_nonneg c]
    exact hx0 (abs_eq_zero.mp this)
  have hy0 : δ * (x - c) ≠ 0 := mul_ne_zero hδ.ne' hsub0
  calc
    phi (δ * (x - c)) ≤ 2 * fejerK (δ * (x - c)) := phi_le_two_mul_fejerK _
    _ ≤ 2 * ((δ * (x - c)) ^ 2)⁻¹ := by
      gcongr
      exact fejerK_le_inv_sq hy0
    _ = 2 * δ⁻¹ ^ 2 * ((x - c) ^ 2)⁻¹ := by
      field_simp [hδ.ne', hsub0]
    _ ≤ 2 * δ⁻¹ ^ 2 * (4 * (x ^ 2)⁻¹) := by
      gcongr
      exact inv_sq_sub_le_four_mul_inv_sq hx0 hxc
    _ = 8 * δ⁻¹ ^ 2 * (x ^ 2)⁻¹ := by ring

theorem phi_scaled_reflected_shift_le {δ c x : ℝ} (hδ : 0 < δ) (hx0 : x ≠ 0)
    (hxc : 2 * |c| ≤ |x|) :
    phi (δ * (c - x)) ≤ 8 * δ⁻¹ ^ 2 * (x ^ 2)⁻¹ := by
  have hsub0 : x - c ≠ 0 := by
    intro h
    have hxeq : x = c := sub_eq_zero.mp h
    rw [hxeq] at hxc hx0
    have : |c| = 0 := by nlinarith [abs_nonneg c]
    exact hx0 (abs_eq_zero.mp this)
  have hy0 : δ * (c - x) ≠ 0 := by
    apply mul_ne_zero hδ.ne'
    simpa only [neg_sub] using neg_ne_zero.mpr hsub0
  calc
    phi (δ * (c - x)) ≤ 2 * fejerK (δ * (c - x)) := phi_le_two_mul_fejerK _
    _ ≤ 2 * ((δ * (c - x)) ^ 2)⁻¹ := by
      gcongr
      exact fejerK_le_inv_sq hy0
    _ = 2 * δ⁻¹ ^ 2 * ((x - c) ^ 2)⁻¹ := by
      rw [mul_pow, show (c - x) ^ 2 = (x - c) ^ 2 by ring]
      field_simp [hδ.ne', hsub0]
    _ ≤ 2 * δ⁻¹ ^ 2 * (4 * (x ^ 2)⁻¹) := by
      gcongr
      exact inv_sq_sub_le_four_mul_inv_sq hx0 hxc
    _ = 8 * δ⁻¹ ^ 2 * (x ^ 2)⁻¹ := by ring

/-- Explicit quadratic tail for the Selberg interval majorant. -/
theorem selbergIntervalMajorant_quadratic_tail
    {a b δ x : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hx : 1 + 2 * max |a| |b| ≤ |x|) :
    selbergIntervalMajorant a b δ x ≤
      8 * δ⁻¹ ^ 2 * (x ^ 2)⁻¹ := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    simp at hx
    have : 0 ≤ max |a| |b| := (abs_nonneg a).trans (le_max_left _ _)
    linarith
  have hxa : 2 * |a| ≤ |x| := by
    have := le_max_left |a| |b|
    linarith
  have hxb : 2 * |b| ≤ |x| := by
    have := le_max_right |a| |b|
    linarith
  have hsign : intervalSignPair a b x = 0 := by
    rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
    · apply intervalSignPair_eq_zero_of_lt (hab := hab)
      have ha : -|a| ≤ a := neg_abs_le a
      have hamax : |a| ≤ max |a| |b| := le_max_left _ _
      have hmax0 : 0 ≤ max |a| |b| := (abs_nonneg a).trans hamax
      have hxabs : |x| = -x := abs_of_neg hxneg
      linarith
    · apply intervalSignPair_eq_zero_of_gt hab
      have hb : b ≤ |b| := le_abs_self b
      have hbmax : |b| ≤ max |a| |b| := le_max_right _ _
      have hmax0 : 0 ≤ max |a| |b| := (abs_nonneg b).trans hbmax
      have hxabs : |x| = x := abs_of_pos hxpos
      linarith
  rw [selbergIntervalMajorant_eq_signPair_add_phi hδ, hsign, zero_add]
  have hleft := phi_scaled_reflected_shift_le hδ hx0 hxb
  have hright := phi_scaled_shift_le hδ hx0 hxa
  nlinarith

/-- The complement of a centered compact interval is a cocompact
neighborhood. -/
theorem eventually_abs_ge_cocompact {R : ℝ} (hR : 0 ≤ R) :
    ∀ᶠ x : ℝ in cocompact ℝ, R ≤ |x| := by
  have hmem : {x : ℝ | R ≤ |x|} ∈ cocompact ℝ := by
    rw [mem_cocompact]
    refine ⟨Set.Icc (-R) R, isCompact_Icc, ?_⟩
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    simp only [Set.mem_setOf_eq]
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      exact hx.le
  exact hmem

/-- Any function which vanishes outside a centered compact interval has
arbitrary polynomial decay along `cocompact`. -/
theorem isBigO_cocompact_of_abs_support {g : ℝ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hsupp : ∀ x : ℝ, R ≤ |x| → g x = 0) (s : ℝ) :
    g =O[cocompact ℝ] (fun x => |x| ^ s) := by
  have hz : g =ᶠ[cocompact ℝ] 0 := by
    filter_upwards [eventually_abs_ge_cocompact hR] with x hx
    exact hsupp x hx
  calc
    g =O[cocompact ℝ] (0 : ℝ → ℂ) := hz.isBigO
    _ =O[cocompact ℝ] (fun x => |x| ^ s) := isBigO_zero _ _

/-- The complexified interval majorant has the `O(|x|^-2)` decay required by
Mathlib's Poisson theorem. -/
theorem selbergIntervalMajorant_isBigO_neg_two
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) :
    (fun x : ℝ => (selbergIntervalMajorant a b δ x : ℂ)) =O[cocompact ℝ]
      (fun x => |x| ^ (-(2 : ℝ))) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨8 * δ⁻¹ ^ 2, ?_⟩
  have hR : 0 ≤ 1 + 2 * max |a| |b| := by
    have hm : 0 ≤ max |a| |b| := (abs_nonneg a).trans (le_max_left _ _)
    positivity
  filter_upwards [eventually_abs_ge_cocompact hR] with x hx
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    simp at hx
    have hm : 0 ≤ max |a| |b| := (abs_nonneg a).trans (le_max_left _ _)
    linarith
  have htail := selbergIntervalMajorant_quadratic_tail hab hδ hx
  have hnonneg := selbergIntervalMajorant_nonneg hab hδ x
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have habsrpow : ‖|x| ^ (-(2 : ℝ))‖ = |x| ^ (-(2 : ℝ)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
  rw [habsrpow]
  have hrpow : |x| ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg x)]
    calc
      (|x| ^ (2 : ℝ))⁻¹ = (|x| ^ (2 : ℕ))⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast |x| 2)
      _ = (x ^ 2)⁻¹ := congrArg Inv.inv (sq_abs x)
  rw [hrpow]
  exact htail

/-! ## Compact Fourier support and modulation -/

/-- Compact Fourier support is stronger than the quadratic decay needed for
Poisson summation. -/
theorem fourier_selbergIntervalMajorant_isBigO_neg_two
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) :
    (𝓕 (fun x : ℝ => (selbergIntervalMajorant a b δ x : ℂ))) =O[cocompact ℝ]
      (fun t => |t| ^ (-(2 : ℝ))) := by
  exact isBigO_cocompact_of_abs_support hδ.le
    (fun t ht => fourier_selbergIntervalMajorant_eq_zero hab hδ ht) (-(2 : ℝ))

/-- Multiplication by the negative exponential character translates the
Fourier transform by `+beta` in the convention used here. -/
theorem fourier_selbergIntervalMajorant_mul_echar
    (a b δ β t : ℝ) :
    𝓕 (fun x : ℝ => (selbergIntervalMajorant a b δ x : ℂ) * echar β x) t =
      𝓕 (fun x : ℝ => (selbergIntervalMajorant a b δ x : ℂ)) (t + β) := by
  rw [fourier_eq_echar_integral, fourier_eq_echar_integral]
  apply integral_congr_ae
  filter_upwards with x
  unfold echar
  calc
    (selbergIntervalMajorant a b δ x : ℂ) *
          Complex.exp (-2 * π * Complex.I * β * x) *
          Complex.exp (-2 * π * Complex.I * t * x) =
        (selbergIntervalMajorant a b δ x : ℂ) *
          (Complex.exp (-2 * π * Complex.I * β * x) *
            Complex.exp (-2 * π * Complex.I * t * x)) := by ring
    _ = (selbergIntervalMajorant a b δ x : ℂ) *
          Complex.exp ((-2 * π * Complex.I * β * x) +
            (-2 * π * Complex.I * t * x)) := by rw [Complex.exp_add]
    _ = (selbergIntervalMajorant a b δ x : ℂ) *
          Complex.exp (-2 * π * Complex.I * ((t + β : ℝ) : ℂ) * (x : ℂ)) := by
          apply congrArg (fun z : ℂ =>
            (selbergIntervalMajorant a b δ x : ℂ) * Complex.exp z)
          push_cast
          ring

theorem selbergIntervalMajorant_mul_echar_isBigO_neg_two
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (β : ℝ) :
    (fun x : ℝ => (selbergIntervalMajorant a b δ x : ℂ) * echar β x)
      =O[cocompact ℝ] (fun x => |x| ^ (-(2 : ℝ))) := by
  rw [Asymptotics.isBigO_iff]
  obtain ⟨C, hC⟩ :=
    Asymptotics.isBigO_iff.mp (selbergIntervalMajorant_isBigO_neg_two hab hδ)
  refine ⟨C, ?_⟩
  filter_upwards [hC] with x hx
  simpa only [norm_mul, norm_echar, mul_one] using hx

/-- The Fourier transform of the modulated majorant is still compactly
supported (now inside the translated band), hence has quadratic decay. -/
theorem fourier_selbergIntervalMajorant_mul_echar_isBigO_neg_two
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (β : ℝ) :
    (𝓕 (fun x : ℝ => (selbergIntervalMajorant a b δ x : ℂ) * echar β x))
      =O[cocompact ℝ] (fun t => |t| ^ (-(2 : ℝ))) := by
  refine isBigO_cocompact_of_abs_support
    (show 0 ≤ δ + |β| by positivity) ?_ (-(2 : ℝ))
  intro t ht
  rw [fourier_selbergIntervalMajorant_mul_echar]
  apply fourier_selbergIntervalMajorant_eq_zero hab hδ
  have htri : |t| - |β| ≤ |t + β| := by
    have := abs_sub_abs_le_abs_sub t (-β)
    simpa only [abs_neg, sub_neg_eq_add] using this
  linarith

/-! ## Integer sampling by Poisson summation -/

theorem selbergIntervalMajorant_int_summable
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) :
    Summable (fun n : ℤ => (selbergIntervalMajorant a b δ (n : ℝ) : ℂ)) := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    ((selbergIntervalMajorant_isBigO_neg_two hab hδ).comp_tendsto
      Int.tendsto_coe_cofinite)

theorem selbergIntervalMajorant_mul_echar_int_summable
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (β : ℝ) :
    Summable (fun n : ℤ =>
      (selbergIntervalMajorant a b δ (n : ℝ) : ℂ) * echar β (n : ℝ)) := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    ((selbergIntervalMajorant_mul_echar_isBigO_neg_two hab hδ β).comp_tendsto
      Int.tendsto_coe_cofinite)

theorem continuous_selbergIntervalMajorant_mul_echar (a b δ β : ℝ) :
    Continuous (fun x : ℝ =>
      (selbergIntervalMajorant a b δ x : ℂ) * echar β x) := by
  apply (Complex.continuous_ofReal.comp
    (selbergIntervalMajorant_continuous a b δ)).mul
  unfold echar
  fun_prop

/-- Poisson summation for the modulated interval majorant, with the translated
Fourier samples displayed explicitly. -/
theorem poisson_selbergIntervalMajorant_mul_echar
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (β : ℝ) :
    (∑' n : ℤ, (selbergIntervalMajorant a b δ (n : ℝ) : ℂ) * echar β (n : ℝ)) =
      ∑' m : ℤ,
        𝓕 (fun x : ℝ => (selbergIntervalMajorant a b δ x : ℂ)) ((m : ℝ) + β) := by
  let g : ℝ → ℂ := fun x =>
    (selbergIntervalMajorant a b δ x : ℂ) * echar β x
  have hp := MathExtras.Fourier.shifted_poisson_summation_rpow_decay
    (f := g) (continuous_selbergIntervalMajorant_mul_echar a b δ β) one_lt_two
    (selbergIntervalMajorant_mul_echar_isBigO_neg_two hab hδ β)
    (fourier_selbergIntervalMajorant_mul_echar_isBigO_neg_two hab hδ β) 0
  calc
    (∑' n : ℤ, (selbergIntervalMajorant a b δ (n : ℝ) : ℂ) * echar β (n : ℝ)) =
        ∑' n : ℤ, g ((0 : ℝ) + (n : ℝ)) := by
          apply tsum_congr
          intro n
          simp only [zero_add, g]
    _ = ∑' n : ℤ, 𝓕 g (n : ℝ) *
          Complex.exp (2 * π * Complex.I * (n : ℂ) * (0 : ℂ)) := hp
    _ = ∑' m : ℤ,
          𝓕 (fun x : ℝ => (selbergIntervalMajorant a b δ x : ℂ)) ((m : ℝ) + β) := by
          apply tsum_congr
          intro m
          rw [fourier_selbergIntervalMajorant_mul_echar]
          simp

/-- Every translated Fourier lattice sample is outside the band when `beta`
is at circle distance at least `delta` from the integers. -/
theorem fourier_lattice_translate_eq_zero
    {a b δ β : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hsep : δ ≤ circleDist β 0) (m : ℤ) :
    𝓕 (fun x : ℝ => (selbergIntervalMajorant a b δ x : ℂ)) ((m : ℝ) + β) = 0 := by
  apply fourier_selbergIntervalMajorant_eq_zero hab hδ
  have hm := circleDist_le_int β 0 (-m)
  have hfar : δ ≤ |β + (m : ℝ)| := by
    exact hsep.trans (by simpa using hm)
  simpa only [add_comm] using hfar

/-- Off-diagonal lattice sampling identity.  This is the exact cancellation
used after expanding the dual large-sieve quadratic form. -/
theorem tsum_selbergIntervalMajorant_mul_echar_eq_zero
    {a b δ β : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hsep : δ ≤ circleDist β 0) :
    (∑' n : ℤ,
      (selbergIntervalMajorant a b δ (n : ℝ) : ℂ) * echar β (n : ℝ)) = 0 := by
  rw [poisson_selbergIntervalMajorant_mul_echar hab hδ β]
  have hzero : (fun m : ℤ =>
      𝓕 (fun x : ℝ => (selbergIntervalMajorant a b δ x : ℂ)) ((m : ℝ) + β)) = 0 := by
    funext m
    exact fourier_lattice_translate_eq_zero hab hδ hsep m
  rw [hzero]
  exact tsum_zero

theorem fourier_selbergIntervalMajorant_zero
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) :
    𝓕 (fun x : ℝ => (selbergIntervalMajorant a b δ x : ℂ)) 0 =
      (((b - a) + δ⁻¹ : ℝ) : ℂ) := by
  rw [fourier_eq_echar_integral]
  have hfun : (fun x : ℝ =>
      (selbergIntervalMajorant a b δ x : ℂ) * echar 0 x) =
      fun x : ℝ => (selbergIntervalMajorant a b δ x : ℂ) := by
    funext x
    simp [echar]
  rw [hfun]
  have hcast : (∫ x : ℝ, (selbergIntervalMajorant a b δ x : ℂ)) =
      Complex.ofReal (∫ x : ℝ, selbergIntervalMajorant a b δ x) :=
    integral_ofReal
  rw [hcast, integral_selbergIntervalMajorant hab hδ]

/-- Diagonal lattice sampling identity: for a band of width at most one, the
integer samples have total mass exactly `(b-a)+delta^-1`. -/
theorem tsum_selbergIntervalMajorant_eq_mass
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑' n : ℤ, (selbergIntervalMajorant a b δ (n : ℝ) : ℂ)) =
      (((b - a) + δ⁻¹ : ℝ) : ℂ) := by
  calc
    (∑' n : ℤ, (selbergIntervalMajorant a b δ (n : ℝ) : ℂ)) =
        ∑' n : ℤ,
          (selbergIntervalMajorant a b δ (n : ℝ) : ℂ) * echar 0 (n : ℝ) := by
            apply tsum_congr
            intro n
            simp [echar]
    _ = ∑' m : ℤ,
          𝓕 (fun x : ℝ => (selbergIntervalMajorant a b δ x : ℂ)) ((m : ℝ) + 0) :=
        poisson_selbergIntervalMajorant_mul_echar hab hδ 0
    _ = 𝓕 (fun x : ℝ => (selbergIntervalMajorant a b δ x : ℂ)) 0 := by
      have hsingle : (∑' m : ℤ,
          𝓕 (fun x : ℝ => (selbergIntervalMajorant a b δ x : ℂ)) ((m : ℝ) + 0)) =
          𝓕 (fun x : ℝ => (selbergIntervalMajorant a b δ x : ℂ))
            (((0 : ℤ) : ℝ) + 0) := by
        apply tsum_eq_single (0 : ℤ)
        intro m hm
        apply fourier_selbergIntervalMajorant_eq_zero hab hδ
        have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
          exact_mod_cast Int.one_le_abs hm
        simpa only [add_zero] using hδ1.trans hm1
      simpa using hsingle
    _ = (((b - a) + δ⁻¹ : ℝ) : ℂ) :=
      fourier_selbergIntervalMajorant_zero hab hδ

end MathExtras.NumberTheory.Analysis.SelbergIntervalPoissonClosed

end
