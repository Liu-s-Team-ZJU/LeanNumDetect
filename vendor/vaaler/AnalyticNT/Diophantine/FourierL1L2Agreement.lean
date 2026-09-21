/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The L¹∩L² agreement of the integral Fourier transform with the L²-extension

This NEW leaf proves a **generic, reusable** Mathlib-gap lemma that is the linchpin of the
Plancherel / L² route to the deep minor-arc residual `GCFTeqJhat` (Vaaler 1985,
eq. (2.31)→(2.32)).

Mathlib has TWO Fourier transforms on `ℝ`:

* the **integral transform** `Real.fourierIntegral f` (notation `𝓕` on functions
  `ℝ → ℂ`), `𝓕 f w = ∫ v, exp(-2π i v w) • f v`, defined for `f ∈ L¹`;
* the **L²-extension** `MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ : Lp ℂ 2 ≃ₗᵢ[ℂ] Lp ℂ 2`,
  the Plancherel isometry (`Lp.norm_fourier_eq`, `Lp.inner_fourier_eq`), defined by
  density of Schwartz functions in `L²`.

For a function `f` which is **both** in `L¹` and in `L²`, these must agree a.e.  Mathlib
proves this only for Schwartz functions (`SchwartzMap.toLp_fourier_eq`); the L¹∩L²
agreement is **absent**.  This file supplies it:

    `fourierIntegral_ae_eq_fourierTransformₗᵢ` :
        `Integrable f → (hf2 : MemLp f 2) →
           ⇑(Lp.fourierTransformₗᵢ ℝ ℂ (hf2.toLp f)) =ᵐ[volume] 𝓕 f`.

## Proof (distributional)

We compare the two locally-integrable functions `f₁ := ⇑(𝓕 T)` (with `T = hf2.toLp f`)
and `f₂ := 𝓕 f` by their integrals against **real** smooth compactly-supported test
functions `g` (`ae_eq_of_integral_contDiff_smul_eq`).  Promote `g` to the **complex**
Schwartz test `G = ofRealCLM ∘ g`; then

* `∫ x, g x • f₁ x = (T : 𝓢') (𝓕 G) = ∫ x, (𝓕 G) x • f x`
  (via `fourier_toTemperedDistribution_eq` + `TemperedDistribution.fourier_apply` +
  `Lp.toTemperedDistribution_apply` + `T =ᵐ f`);
* `∫ x, (𝓕 G) x • f x = ∫ ξ, G ξ • (𝓕 f) ξ = ∫ ξ, g ξ • f₂ ξ`
  (the **Fourier multiplication formula** / self-adjointness
  `VectorFourier.integral_fourierIntegral_smul_eq_flip`).

Both `f₁` (an `L²` element) and `f₂ = 𝓕 f` (continuous, by Riemann–Lebesgue on `L¹`) are
locally integrable, so the test-function characterisation forces `f₁ =ᵐ f₂`.

## Book

Plancherel / self-duality of the Fourier transform; Mathlib
`MeasureTheory.Lp.fourierTransformₗᵢ`, `VectorFourier.integral_fourierIntegral_smul_eq_flip`,
`MeasureTheory.Lp.fourier_toTemperedDistribution_eq`, `ae_eq_of_integral_contDiff_smul_eq`.
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology SchwartzMap
open scoped FourierTransform RealInnerProductSpace

namespace MathExtras.NumberTheory.Analysis.FourierL1L2Agreement

/-! ## §1 — The Fourier multiplication formula for an L¹ function against a Schwartz test -/

/-- **PROVEN — the Fourier multiplication formula (self-adjointness), `L¹`×Schwartz.**

For `f ∈ L¹` and a Schwartz test `g : 𝓢(ℝ, ℂ)`,

    ∫ x, (𝓕 g) x • f x = ∫ ξ, g ξ • (𝓕 f) ξ.

This is `VectorFourier.integral_fourierIntegral_smul_eq_flip` specialised to `ℝ` with the
inner-product bilinear form (whose flip is itself, `flip_innerₗ`), `g` Schwartz (hence
integrable, `SchwartzMap.integrable`) and `f` integrable. -/
theorem integral_fourier_schwartz_smul_eq (f : ℝ → ℂ) (hf : Integrable f)
    (g : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, (𝓕 (fun y => g y)) x • f x)
      = ∫ ξ : ℝ, (g ξ) • (𝓕 f) ξ := by
  have hg : Integrable (fun y => g y) := g.integrable
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (e := Real.fourierChar) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (L := innerₗ ℝ) Real.continuous_fourierChar (innerSL ℝ).continuous₂ hg hf
  simp only [flip_innerₗ] at key
  exact key

/-! ## §2 — `𝓕 f` is continuous (hence locally integrable) for `f ∈ L¹` -/

/-- **PROVEN.**  `𝓕 f` is continuous on `ℝ` whenever `f ∈ L¹` (Riemann–Lebesgue).  This
makes `𝓕 f` locally integrable, the hypothesis the test-function characterisation needs on
the `f₂`-side. -/
theorem continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

/-! ## §3 — The distributional Schwartz-test identity for the L²-extension -/

/-- **PROVEN — the L²-extension transform, tested against a Schwartz function.**

For `T : Lp ℂ 2` and a Schwartz `G : 𝓢(ℝ, ℂ)`,

    (𝓕 T : 𝓢') G = ∫ x, (𝓕 G) x • (T : ℝ → ℂ) x.

Routes the L²-Fourier transform through the tempered-distribution embedding
(`Lp.fourier_toTemperedDistribution_eq`), the transpose definition of the distributional
Fourier transform (`TemperedDistribution.fourier_apply`), and the pairing formula
(`Lp.toTemperedDistribution_apply`). -/
theorem fourierTransformₗᵢ_test_eq (T : Lp (α := ℝ) ℂ 2) (G : 𝓢(ℝ, ℂ)) :
    ((𝓕 T : Lp (α := ℝ) ℂ 2) : 𝓢'(ℝ, ℂ)) G
      = ∫ x : ℝ, (𝓕 G) x • (T : ℝ → ℂ) x := by
  rw [← MeasureTheory.Lp.fourier_toTemperedDistribution_eq T]
  rw [TemperedDistribution.fourier_apply]
  rw [MeasureTheory.Lp.toTemperedDistribution_apply]

/-! ## §4 — The L¹∩L² agreement (the reusable Mathlib-gap lemma) -/

/-- **PROVEN — the L¹∩L² agreement of the integral and L²-extension Fourier transforms.**

For `f : ℝ → ℂ` that is both `L¹` (`Integrable f`) and `L²` (`hf2 : MemLp f 2`), the
representative of the Plancherel L²-extension `Lp.fourierTransformₗᵢ` applied to `hf2.toLp f`
agrees `a.e.` with the integral transform `𝓕 f`:

    ⇑(Lp.fourierTransformₗᵢ ℝ ℂ (hf2.toLp f)) =ᵐ[volume] 𝓕 f.

This is the bridge that lets the L²/Plancherel route compute `𝓕 f` for `L¹∩L²` functions.
Proof: both sides are locally integrable (the L²-element, and `𝓕 f` continuous by
`continuous_fourier_of_integrable`); they integrate equally against every real smooth
compactly-supported test `g` — promote `g` to the complex Schwartz test
`G = ofRealCLM ∘ g`, identify `∫ g • f₁` with `(𝓕 T : 𝓢') G = ∫ (𝓕 G) • f` (via
`fourierTransformₗᵢ_test_eq` and `T =ᵐ f`) and then with `∫ G • (𝓕 f) = ∫ g • f₂` by the
multiplication formula `integral_fourier_schwartz_smul_eq` — so they coincide a.e.
(`ae_eq_of_integral_contDiff_smul_eq`). -/
theorem fourierIntegral_ae_eq_fourierTransformₗᵢ {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2) :
    (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hf2.toLp f)) : ℝ → ℂ)
      =ᵐ[volume] 𝓕 f := by
  set T : Lp (α := ℝ) ℂ 2 := hf2.toLp f with hT
  -- `f₁ = ⇑(𝓕 T)` and `f₂ = 𝓕 f` are both locally integrable.
  have hTf : (T : ℝ → ℂ) =ᵐ[volume] f := hf2.coeFn_toLp
  have hf1_li : LocallyIntegrable (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ T)) volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hf2_li : LocallyIntegrable (𝓕 f) volume :=
    (continuous_fourier_of_integrable hf).locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hf1_li hf2_li ?_
  intro g g_smooth g_cpt
  -- Promote the real test `g` to a complex Schwartz function `G = ofRealCLM ∘ g`.
  have hG₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
  have hG₂ : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ g) := by fun_prop
  set G : 𝓢(ℝ, ℂ) := hG₁.toSchwartzMap hG₂ with hG
  have hGval : ∀ x, (G : ℝ → ℂ) x = ((g x : ℝ) : ℂ) := fun x => rfl
  -- Scalar bridge `G x • y = g x • y`.
  have hscal : ∀ (x : ℝ) (y : ℂ), (G : ℝ → ℂ) x • y = g x • y := by
    intro x y; rw [hGval x]; simp [Complex.real_smul]
  -- `(𝓕 T : 𝓢') G`, expanded two ways.
  have hpair := fourierTransformₗᵢ_test_eq T G
  rw [MeasureTheory.Lp.toTemperedDistribution_apply] at hpair
  -- `hpair : ∫ x, G x • ⇑(𝓕 T) x = ∫ x, (𝓕 G) x • T x`.
  -- LHS chain.
  calc
    (∫ x : ℝ, g x • (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ T)) x)
        = ∫ x : ℝ, (G : ℝ → ℂ) x • (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ T)) x := by
          exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (hscal x _).symm))
    _ = ∫ x : ℝ, (𝓕 (fun y => (G : ℝ → ℂ) y)) x • (T : ℝ → ℂ) x := hpair
    _ = ∫ x : ℝ, (𝓕 (fun y => (G : ℝ → ℂ) y)) x • f x := by
          refine integral_congr_ae ?_
          filter_upwards [hTf] with x hx
          rw [hx]
    _ = ∫ ξ : ℝ, (G : ℝ → ℂ) ξ • (𝓕 f) ξ :=
          integral_fourier_schwartz_smul_eq f hf G
    _ = ∫ x : ℝ, g x • 𝓕 f x :=
          integral_congr_ae (Filter.Eventually.of_forall (fun x => hscal x _))

end MathExtras.NumberTheory.Analysis.FourierL1L2Agreement
