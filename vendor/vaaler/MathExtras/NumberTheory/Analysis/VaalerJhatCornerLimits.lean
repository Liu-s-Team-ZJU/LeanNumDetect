/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerJhatCorner

/-!
# Vaaler eq. (2.27): discharge of `VaalerJhatDerivCornerLimits` (the four removable corner limits)

This NEW leaf discharges the single named residual `VaalerJhatDerivCornerLimits` left open in
`VaalerJhatCorner`, namely the four removable corner limits of the explicit first/second
derivatives `jhatD1`, `jhatD2` of Vaaler's Fejér transform `Ĵ`.  Granting it, the committed
`vaalerJTwoIBPDecay_of_limits` / `jIntegrable_of_limits` close `VaalerJTwoIBPDecay` and
`JIntegrable`.

## The math (the smooth removed-cot factor `ψ`)

Write `ψ(τ) = cos(π τ)/sinc(π τ)`.  On a punctured nbhd of `0`,
`sinc(π τ) = sin(π τ)/(π τ)`, so

    ψ(τ) = cos(π τ)·(π τ)/sin(π τ) = π τ·cot(π τ),

and Vaaler's `Ĵ(τ) = π τ(1−τ)cot(π τ)+τ = (1−τ)·ψ(τ) + τ`.  Since `sinc` is real-analytic at
`0` (`Real.sinc = dslope Real.sin 0`, and the removable singularity of an analytic function is
analytic), `ψ` and hence the smooth completion `Jext τ := (1−τ)·ψ(τ) + τ` are `C^∞` near `0`.
Its derivatives at `0` are the genuine corner limits of `Ĵ'`, `Ĵ''`:

    Ĵ'(0) = 1 − ψ(0) + ψ'(0) = 0,        Ĵ''(0) = −2ψ'(0) + ψ''(0) = −2π²/3.

The corner `{1}` is handled by the exact reflection symmetry `jhatD1(1−u) = jhatD1(u)`,
`jhatD2(1−u) = −jhatD2(u)` (clean algebraic identities of the closed forms), reducing the corner
limits at `1` to those at `0`: `Ĵ'(1) = Ĵ'(0) = 0`, `Ĵ''(1) = −Ĵ''(0) = +2π²/3`.

The single genuinely-hard analytic input is the value `sinc''(0) = −1/3`, which Mathlib does not
carry.  We PROVE it from scratch via the identity `sin x = x·sinc x`: differentiating three times
and evaluating at `0` gives `−cos 0 = 3·sinc''(0)`, i.e. `sinc''(0) = −1/3`.  Everything else is
the product/chain rule on analytic functions.

## Hard constraints honoured

NEW leaf only; nothing existing/committed is edited.  No
`axiom`/`sorry`/`admit`/`native_decide`/`False.elim`/`absurd`/`not_*_input`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6,
eqs (2.27)–(2.28), p. 192.
-/

noncomputable section

open Filter Topology Set
open scoped Topology

namespace MathExtras.NumberTheory.Analysis.VaalerJhatCornerLimits

open MathExtras.NumberTheory.Analysis.VaalerJhatC2Data
open MathExtras.NumberTheory.Analysis.VaalerJhatCorner
open MathExtras.NumberTheory.Analysis.VaalerFejerCoefficientNonneg
open scoped ContDiff

/-! ## §0 — `Real.sinc` is `C^∞`, and `sinc''(0) = −1/3` -/

/-- `Real.sinc` is real-analytic at every point. -/
theorem analyticAt_sinc (x : ℝ) : AnalyticAt ℝ Real.sinc x := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    obtain ⟨p, hp⟩ := Real.analyticAt_sin (x := 0)
    rw [Real.sinc_eq_dslope]
    exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
  · have hden : AnalyticAt ℝ (fun y : ℝ => y) x := analyticAt_id
    have hnum : AnalyticAt ℝ Real.sin x := Real.analyticAt_sin
    have : AnalyticAt ℝ (fun y : ℝ => Real.sin y / y) x := hnum.div hden hx
    refine this.congr ?_
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact (Real.sinc_of_ne_zero hy).symm

/-- `Real.sinc` is `C^∞`. -/
theorem contDiff_sinc : ContDiff ℝ ∞ Real.sinc :=
  contDiff_iff_contDiffAt.2 (fun x => (analyticAt_sinc x).contDiffAt.of_le le_top)

/-- `deriv Real.sinc` is `C^∞`. -/
theorem contDiff_deriv_sinc : ContDiff ℝ ∞ (deriv Real.sinc) :=
  (contDiff_infty_iff_deriv.mp contDiff_sinc).2

/-- `deriv (deriv Real.sinc)` is `C^∞`. -/
theorem contDiff_deriv_deriv_sinc : ContDiff ℝ ∞ (deriv (deriv Real.sinc)) :=
  (contDiff_infty_iff_deriv.mp contDiff_deriv_sinc).2

/-- The defining relation `sin x = x · sinc x`, valid for all `x` (including `0`). -/
theorem sin_eq_id_mul_sinc : Real.sin = fun x : ℝ => x * Real.sinc x := by
  funext x
  rcases eq_or_ne x 0 with hx | hx
  · subst hx; simp
  · rw [Real.sinc_of_ne_zero hx, mul_div_cancel₀ _ hx]

/-- Everywhere: `cos x = sinc x + x · (deriv sinc) x`. -/
theorem cos_eq_sinc_add (x : ℝ) :
    Real.cos x = Real.sinc x + x * deriv Real.sinc x := by
  have hsinc_diff : Differentiable ℝ Real.sinc := contDiff_sinc.differentiable (by decide)
  have hd : HasDerivAt (fun y : ℝ => y * Real.sinc y)
      (Real.sinc x + x * deriv Real.sinc x) x := by
    have h1 : HasDerivAt (fun y : ℝ => y) (1 : ℝ) x := hasDerivAt_id x
    have h2 : HasDerivAt Real.sinc (deriv Real.sinc x) x := (hsinc_diff x).hasDerivAt
    refine ((h1.mul h2).congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl
  have hsin' : HasDerivAt (fun y : ℝ => y * Real.sinc y) (Real.cos x) x := by
    rw [← sin_eq_id_mul_sinc]; exact Real.hasDerivAt_sin x
  exact (hsin'.unique hd)

/-- The function form of `cos = sinc + id·sinc'`. -/
theorem cos_eq_sinc_add_fun :
    Real.cos = fun x : ℝ => Real.sinc x + x * deriv Real.sinc x := by
  funext x; exact cos_eq_sinc_add x

/-- Everywhere: `-sin x = 2·(deriv sinc) x + x·(deriv (deriv sinc)) x`. -/
theorem neg_sin_eq (x : ℝ) :
    -Real.sin x = 2 * deriv Real.sinc x + x * deriv (deriv Real.sinc) x := by
  have hRHS : HasDerivAt (fun y : ℝ => Real.sinc y + y * deriv Real.sinc y)
      (deriv Real.sinc x + (deriv Real.sinc x + x * deriv (deriv Real.sinc) x)) x := by
    have ha : HasDerivAt Real.sinc (deriv Real.sinc x) x :=
      (contDiff_sinc.differentiable (by decide) x).hasDerivAt
    have hb : HasDerivAt (fun y : ℝ => y * deriv Real.sinc y)
        (deriv Real.sinc x + x * deriv (deriv Real.sinc) x) x := by
      have h1 : HasDerivAt (fun y : ℝ => y) (1 : ℝ) x := hasDerivAt_id x
      have h2 : HasDerivAt (deriv Real.sinc) (deriv (deriv Real.sinc) x) x :=
        ((contDiff_deriv_sinc.differentiable (by decide)) x).hasDerivAt
      refine ((h1.mul h2).congr_deriv (by ring)).congr_of_eventuallyEq ?_
      filter_upwards with y
      rfl
    exact ha.add hb
  have hcos' : HasDerivAt (fun y : ℝ => Real.sinc y + y * deriv Real.sinc y)
      (-Real.sin x) x := by
    rw [← cos_eq_sinc_add_fun]; exact Real.hasDerivAt_cos x
  have := hcos'.unique hRHS
  rw [this]; ring

/-- The function form of `-sin = 2·sinc' + id·sinc''`. -/
theorem neg_sin_eq_fun :
    (fun x : ℝ => -Real.sin x) =
      fun x : ℝ => 2 * deriv Real.sinc x + x * deriv (deriv Real.sinc) x := by
  funext x; exact neg_sin_eq x

/-- **The single hard analytic value:** `sinc''(0) = −1/3`. -/
theorem deriv_deriv_sinc_zero : deriv (deriv Real.sinc) 0 = -(1 / 3) := by
  have hRHS : HasDerivAt (fun y : ℝ => 2 * deriv Real.sinc y + y * deriv (deriv Real.sinc) y)
      (2 * deriv (deriv Real.sinc) 0
        + (deriv (deriv Real.sinc) 0 + 0 * deriv (deriv (deriv Real.sinc)) 0)) 0 := by
    have ha : HasDerivAt (fun y : ℝ => 2 * deriv Real.sinc y)
        (2 * deriv (deriv Real.sinc) 0) 0 := by
      have h2 : HasDerivAt (deriv Real.sinc) (deriv (deriv Real.sinc) 0) 0 :=
        ((contDiff_deriv_sinc.differentiable (by decide)) 0).hasDerivAt
      simpa using h2.const_mul (2 : ℝ)
    have hb : HasDerivAt (fun y : ℝ => y * deriv (deriv Real.sinc) y)
        (deriv (deriv Real.sinc) 0 + 0 * deriv (deriv (deriv Real.sinc)) 0) 0 := by
      have h1 : HasDerivAt (fun y : ℝ => y) (1 : ℝ) 0 := hasDerivAt_id 0
      have h2 : HasDerivAt (deriv (deriv Real.sinc)) (deriv (deriv (deriv Real.sinc)) 0) 0 :=
        ((contDiff_deriv_deriv_sinc.differentiable (by decide)) 0).hasDerivAt
      refine ((h1.mul h2).congr_deriv (by ring)).congr_of_eventuallyEq ?_
      filter_upwards with y
      rfl
    exact ha.add hb
  have hLHS' : HasDerivAt (fun y : ℝ => 2 * deriv Real.sinc y + y * deriv (deriv Real.sinc) y)
      (-Real.cos 0) 0 := by
    rw [← neg_sin_eq_fun]
    refine (Real.hasDerivAt_sin (0 : ℝ)).neg.congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl
  have heq := hLHS'.unique hRHS
  rw [Real.cos_zero] at heq
  have h3 : (3 : ℝ) * deriv (deriv Real.sinc) 0 = -1 := by linarith [heq]
  linarith [h3]

/-! ## §1 — The smooth removed-cot factor `ψ` and the completion `Jext` -/

/-- The smooth "removed-cot" factor `ψ(τ) = cos(π τ)/sinc(π τ)`. -/
def psi (τ : ℝ) : ℝ := Real.cos (Real.pi * τ) / Real.sinc (Real.pi * τ)

/-- The smooth completion `Jext(τ) = (1−τ)·ψ(τ) + τ` of `Ĵ` near `0`. -/
def Jext (τ : ℝ) : ℝ := (1 - τ) * psi τ + τ

/-- `ψ(0) = 1`. -/
theorem psi_zero : psi 0 = 1 := by unfold psi; simp

/-- `ψ` is `C^∞` at `0`. -/
theorem contDiffAt_psi_zero : ContDiffAt ℝ ∞ psi 0 := by
  have hnum : ContDiffAt ℝ ∞ (fun τ : ℝ => Real.cos (Real.pi * τ)) 0 :=
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).contDiffAt
  have hden : ContDiffAt ℝ ∞ (fun τ : ℝ => Real.sinc (Real.pi * τ)) 0 :=
    (contDiff_sinc.comp (contDiff_const.mul contDiff_id)).contDiffAt
  have hne : Real.sinc (Real.pi * (0 : ℝ)) ≠ 0 := by simp
  exact hnum.div hden hne

/-- `ψ` is even: `ψ(−τ) = ψ(τ)`. -/
theorem psi_neg (τ : ℝ) : psi (-τ) = psi τ := by
  unfold psi
  rw [mul_neg, Real.cos_neg, Real.sinc_neg]

/-- Whenever `sin(π τ) ≠ 0` (and `τ ≠ 0`), `ψ(τ) = π τ·cos/sin`. -/
theorem psi_eq_of_ne {τ : ℝ} (hτ : τ ≠ 0) (hs : Real.sin (Real.pi * τ) ≠ 0) :
    psi τ = Real.pi * τ * (Real.cos (Real.pi * τ) / Real.sin (Real.pi * τ)) := by
  have hπτ : Real.pi * τ ≠ 0 := mul_ne_zero Real.pi_ne_zero hτ
  unfold psi
  rw [Real.sinc_of_ne_zero hπτ]
  field_simp

/-- On the interior `(0,1)`, the completion equals the literal `vaalerJhat`. -/
theorem Jext_eq_vaalerJhat_interior {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) :
    Jext τ = vaalerJhat τ := by
  have hs : Real.sin (Real.pi * τ) ≠ 0 := sin_pi_ne_zero_interior h0 h1
  unfold Jext
  rw [psi_eq_of_ne (ne_of_gt h0) hs, vaalerJhat, Real.cot_eq_cos_div_sin]
  ring

/-! ## §2 — `Jext` is `C²` at `0`, and its derivatives there -/

/-- `ψ'(0) = 0` (even differentiable function). -/
theorem deriv_psi_zero : deriv psi 0 = 0 := by
  have hdiff : DifferentiableAt ℝ psi 0 := contDiffAt_psi_zero.differentiableAt (by decide)
  have hneg : HasDerivAt (fun τ : ℝ => -τ) (-1 : ℝ) 0 := by
    refine (hasDerivAt_id (0 : ℝ)).neg.congr_of_eventuallyEq ?_
    filter_upwards with τ
    rfl
  have houter : HasDerivAt psi (deriv psi 0) ((-0 : ℝ)) := by
    rw [neg_zero]; exact hdiff.hasDerivAt
  have h1 : HasDerivAt (fun τ : ℝ => psi (-τ)) (deriv psi 0 * (-1)) 0 :=
    houter.comp 0 hneg
  have heq : (fun τ : ℝ => psi (-τ)) = psi := by funext τ; exact psi_neg τ
  rw [heq] at h1
  have hsame := h1.deriv
  -- hsame : deriv psi 0 = deriv psi 0 * (-1)
  linarith [hsame]

/-- `Jext` is `C²` at `0`. -/
theorem contDiffAt_Jext_zero : ContDiffAt ℝ 2 Jext 0 := by
  have hlin : ContDiffAt ℝ ∞ (fun τ : ℝ => (1 - τ)) 0 :=
    (contDiff_const.sub contDiff_id).contDiffAt
  have hmul : ContDiffAt ℝ ∞ (fun τ : ℝ => (1 - τ) * psi τ) 0 := hlin.mul contDiffAt_psi_zero
  have hid : ContDiffAt ℝ ∞ (fun τ : ℝ => τ) 0 := contDiff_id.contDiffAt
  have hsum : ContDiffAt ℝ ∞ Jext 0 := hmul.add hid
  exact hsum.of_le (by decide)

/-- `Jext'(0) = 0`.  (`Ĵ'(0) = 1 − ψ(0) + ψ'(0) = 0`.) -/
theorem deriv_Jext_zero : deriv Jext 0 = 0 := by
  have hpsi : DifferentiableAt ℝ psi 0 := contDiffAt_psi_zero.differentiableAt (by decide)
  have hd : HasDerivAt Jext ((-1) * psi 0 + (1 - 0) * deriv psi 0 + 1) 0 := by
    have hlin : HasDerivAt (fun τ : ℝ => (1 - τ)) (-1 : ℝ) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_sub 1
    have hmul : HasDerivAt (fun τ : ℝ => (1 - τ) * psi τ)
        ((-1) * psi 0 + (1 - 0) * deriv psi 0) 0 := by
      refine (hlin.mul hpsi.hasDerivAt).congr_of_eventuallyEq ?_
      filter_upwards with τ
      rfl
    exact hmul.add (hasDerivAt_id 0)
  rw [hd.deriv, deriv_psi_zero, psi_zero]; ring

/-! ## §3 — The corner-limit value of `Ĵ''` at `0`

`deriv Jext` agrees with `jhatD1` on `(0,1)`, and `deriv (deriv Jext)` agrees with `jhatD2`
there; both are continuous at `0` (since `Jext` is `C²`), with values `0` and `−2π²/3`. -/

/-- `Jext =ᶠ[𝓝 τ] vaalerJhat` for interior `τ ∈ (0,1)`. -/
theorem Jext_eventuallyEq_interior {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) :
    Jext =ᶠ[𝓝 τ] vaalerJhat := by
  have hopen : IsOpen (Set.Ioo (0:ℝ) 1) := isOpen_Ioo
  filter_upwards [hopen.mem_nhds ⟨h0, h1⟩] with s hs
  exact Jext_eq_vaalerJhat_interior hs.1 hs.2

/-- On `(0,1)`, `deriv Jext = jhatD1`. -/
theorem deriv_Jext_eq_jhatD1 {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) :
    deriv Jext τ = jhatD1 τ := by
  rw [(Jext_eventuallyEq_interior h0 h1).deriv_eq]
  exact (hasDerivAt_vaalerJhat_interior h0 h1).deriv

/-- On `(0,1)`, `deriv (deriv Jext) = jhatD2`. -/
theorem deriv_deriv_Jext_eq_jhatD2 {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) :
    deriv (deriv Jext) τ = jhatD2 τ := by
  -- deriv Jext =ᶠ[𝓝 τ] jhatD1 (since both equal on the open interior)
  have heq : deriv Jext =ᶠ[𝓝 τ] jhatD1 := by
    have hopen : IsOpen (Set.Ioo (0:ℝ) 1) := isOpen_Ioo
    filter_upwards [hopen.mem_nhds ⟨h0, h1⟩] with s hs
    exact deriv_Jext_eq_jhatD1 hs.1 hs.2
  rw [heq.deriv_eq]
  exact (hasDerivAt_jhatD1_interior h0 h1).deriv

/-- `deriv Jext` is continuous at `0`. -/
theorem continuousAt_deriv_Jext_zero : ContinuousAt (deriv Jext) 0 := by
  have h : ContDiffAt ℝ 1 (deriv Jext) 0 :=
    contDiffAt_Jext_zero.derivWithin (by decide)
  exact h.continuousAt

/-- `deriv (deriv Jext)` is continuous at `0`. -/
theorem continuousAt_deriv_deriv_Jext_zero : ContinuousAt (deriv (deriv Jext)) 0 := by
  have h1 : ContDiffAt ℝ 1 (deriv Jext) 0 :=
    contDiffAt_Jext_zero.derivWithin (by decide)
  have h0 : ContDiffAt ℝ 0 (deriv (deriv Jext)) 0 :=
    h1.derivWithin (by decide)
  exact h0.continuousAt

/-! ### `ψ''(0) = −2π²/3` via the product relation `ψ·sinc(π·) = cos(π·)`

We compute `ψ''(0)` from `ψ(τ)·sinc(π τ) = cos(π τ)` by differentiating twice at `0`,
using `sinc''(0) = −1/3`. -/

/-- `Cfun τ = cos(π τ)`. -/
def Cfun (τ : ℝ) : ℝ := Real.cos (Real.pi * τ)
/-- `Sfun τ = sinc(π τ)`. -/
def Sfun (τ : ℝ) : ℝ := Real.sinc (Real.pi * τ)

theorem contDiff_Cfun : ContDiff ℝ ∞ Cfun :=
  Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
theorem contDiff_Sfun : ContDiff ℝ ∞ Sfun :=
  contDiff_sinc.comp (contDiff_const.mul contDiff_id)

theorem Sfun_zero : Sfun 0 = 1 := by simp [Sfun]
theorem Cfun_zero : Cfun 0 = 1 := by simp [Cfun]

/-- `deriv Cfun = fun τ => -(π · sin(π τ))` everywhere. -/
theorem deriv_Cfun_fun : deriv Cfun = fun τ : ℝ => -(Real.pi * Real.sin (Real.pi * τ)) := by
  funext τ
  have hlin : HasDerivAt (fun u : ℝ => Real.pi * u) Real.pi τ := by
    simpa using (hasDerivAt_id τ).const_mul Real.pi
  have : HasDerivAt Cfun (-Real.sin (Real.pi * τ) * Real.pi) τ :=
    (Real.hasDerivAt_cos (Real.pi * τ)).comp τ hlin
  rw [this.deriv]; ring

/-- `deriv Sfun = fun τ => π · (deriv sinc)(π τ)` everywhere. -/
theorem deriv_Sfun_fun :
    deriv Sfun = fun τ : ℝ => Real.pi * deriv Real.sinc (Real.pi * τ) := by
  funext τ
  have hlin : HasDerivAt (fun u : ℝ => Real.pi * u) Real.pi τ := by
    simpa using (hasDerivAt_id τ).const_mul Real.pi
  have hsinc : HasDerivAt Real.sinc (deriv Real.sinc (Real.pi * τ)) (Real.pi * τ) :=
    ((contDiff_sinc.differentiable (by decide)) (Real.pi * τ)).hasDerivAt
  have : HasDerivAt Sfun (deriv Real.sinc (Real.pi * τ) * Real.pi) τ :=
    hsinc.comp τ hlin
  rw [this.deriv]; ring

theorem deriv_Cfun_zero : deriv Cfun 0 = 0 := by rw [deriv_Cfun_fun]; simp
/-- `sinc'(0) = 0` (even function). -/
theorem deriv_sinc_zero : deriv Real.sinc 0 = 0 := by
  have heven : (fun x : ℝ => Real.sinc (-x)) = Real.sinc := by funext x; exact Real.sinc_neg x
  have hdiff : DifferentiableAt ℝ Real.sinc 0 :=
    (contDiff_sinc.differentiable (by decide)) 0
  have hneg : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) 0 := by
    refine (hasDerivAt_id (0 : ℝ)).neg.congr_of_eventuallyEq ?_
    filter_upwards with x
    rfl
  have houter : HasDerivAt Real.sinc (deriv Real.sinc 0) ((-0 : ℝ)) := by
    rw [neg_zero]; exact hdiff.hasDerivAt
  have h1 : HasDerivAt (fun x : ℝ => Real.sinc (-x)) (deriv Real.sinc 0 * (-1)) 0 :=
    houter.comp 0 hneg
  rw [heven] at h1
  have hsame : deriv Real.sinc 0 = deriv Real.sinc 0 * (-1) := h1.deriv
  linarith [hsame]

theorem deriv_Sfun_zero : deriv Sfun 0 = 0 := by
  rw [deriv_Sfun_fun]
  simp only [mul_zero, deriv_sinc_zero]

/-- `deriv (deriv Cfun) 0 = −π²`. -/
theorem deriv_deriv_Cfun_zero : deriv (deriv Cfun) 0 = -Real.pi ^ 2 := by
  rw [deriv_Cfun_fun]
  have hlin : HasDerivAt (fun u : ℝ => Real.pi * u) Real.pi (0:ℝ) := by
    simpa using (hasDerivAt_id (0:ℝ)).const_mul Real.pi
  have hsin : HasDerivAt (fun τ : ℝ => Real.sin (Real.pi * τ))
      (Real.cos (Real.pi * 0) * Real.pi) 0 :=
    (Real.hasDerivAt_sin (Real.pi * 0)).comp 0 hlin
  have h : HasDerivAt (fun τ : ℝ => -(Real.pi * Real.sin (Real.pi * τ)))
      (-(Real.pi * (Real.cos (Real.pi * 0) * Real.pi))) 0 := (hsin.const_mul Real.pi).neg
  rw [h.deriv]; simp; ring

/-- `deriv (deriv Sfun) 0 = −π²/3` (uses `sinc''(0) = −1/3`). -/
theorem deriv_deriv_Sfun_zero : deriv (deriv Sfun) 0 = -(Real.pi ^ 2 / 3) := by
  rw [deriv_Sfun_fun]
  have hlin : HasDerivAt (fun u : ℝ => Real.pi * u) Real.pi (0:ℝ) := by
    simpa using (hasDerivAt_id (0:ℝ)).const_mul Real.pi
  have hd2 : HasDerivAt (deriv Real.sinc) (deriv (deriv Real.sinc) (Real.pi * 0)) (Real.pi * 0) :=
    ((contDiff_deriv_sinc.differentiable (by decide)) (Real.pi * 0)).hasDerivAt
  have hcomp : HasDerivAt (fun τ : ℝ => deriv Real.sinc (Real.pi * τ))
      (deriv (deriv Real.sinc) (Real.pi * 0) * Real.pi) 0 := hd2.comp 0 hlin
  have h : HasDerivAt (fun τ : ℝ => Real.pi * deriv Real.sinc (Real.pi * τ))
      (Real.pi * (deriv (deriv Real.sinc) (Real.pi * 0) * Real.pi)) 0 :=
    hcomp.const_mul Real.pi
  rw [h.deriv]
  simp only [mul_zero]
  rw [deriv_deriv_sinc_zero]; ring

/-- `Cfun`, `Sfun`, `ψ` are differentiable everywhere / at `0` as needed. -/
theorem differentiable_Cfun : Differentiable ℝ Cfun := contDiff_Cfun.differentiable (by decide)
theorem differentiable_Sfun : Differentiable ℝ Sfun := contDiff_Sfun.differentiable (by decide)

/-- `ψ` is differentiable on a neighborhood of `0` (on the open set `{Sfun ≠ 0}`). -/
theorem eventually_differentiableAt_psi :
    ∀ᶠ τ : ℝ in 𝓝 (0:ℝ), DifferentiableAt ℝ psi τ := by
  have hUopen : IsOpen {τ : ℝ | Sfun τ ≠ 0} :=
    isOpen_ne_fun contDiff_Sfun.continuous continuous_const
  have hmem : {τ : ℝ | Sfun τ ≠ 0} ∈ 𝓝 (0:ℝ) :=
    hUopen.mem_nhds (by simp [Sfun_zero])
  filter_upwards [hmem] with τ hτ
  have hτ' : Sfun τ ≠ 0 := hτ
  have hloc : psi =ᶠ[𝓝 τ] fun s => Cfun s / Sfun s := by
    filter_upwards [hUopen.mem_nhds hτ'] with s hs
    have : Sfun s ≠ 0 := hs
    unfold psi Cfun Sfun; rfl
  have : DifferentiableAt ℝ (fun s => Cfun s / Sfun s) τ :=
    (differentiable_Cfun τ).div (differentiable_Sfun τ) hτ'
  exact this.congr_of_eventuallyEq hloc.symm

/-- `ψ τ · Sfun τ = Cfun τ` whenever `Sfun τ ≠ 0`; this holds on a nbhd of `0`. -/
theorem psi_mul_Sfun_eventually : (fun τ : ℝ => psi τ * Sfun τ) =ᶠ[𝓝 (0:ℝ)] Cfun := by
  have hne : ∀ᶠ τ : ℝ in 𝓝 (0:ℝ), Sfun τ ≠ 0 := by
    have hcont : ContinuousAt Sfun 0 := contDiff_Sfun.continuous.continuousAt
    exact hcont.eventually_ne (by rw [Sfun_zero]; norm_num)
  filter_upwards [hne] with τ hτ
  unfold psi Sfun Cfun
  unfold Sfun at hτ
  field_simp [hτ]

/-- `ψ` is `C²` on a neighborhood of `0` (so `deriv psi`, `deriv (deriv psi)` are well-defined). -/
theorem contDiffAt_psi_zero' : ContDiffAt ℝ ∞ psi 0 := contDiffAt_psi_zero

/-- **`ψ''(0) = −2π²/3`.**  By differentiating `ψ·Sfun = Cfun` twice at `0`. -/
theorem deriv_deriv_psi_zero : deriv (deriv psi) 0 = -(2 * Real.pi ^ 2 / 3) := by
  -- `ψ` is C² near 0; pick an open nbhd `U` on which `Sfun ≠ 0`, so `ψ = Cfun/Sfun` is C² there.
  -- We use the relation in `=ᶠ` form throughout, transferring `deriv` via `EventuallyEq.deriv_eq`.
  have hψcd : ContDiffAt ℝ ∞ psi 0 := contDiffAt_psi_zero
  -- ψ is C² on a neighborhood: there is an open U ∋ 0 with ContDiffOn / each point ContDiffAt.
  -- We obtain `deriv (ψ Sfun) =ᶠ deriv ψ · Sfun + ψ · deriv Sfun` near 0, then differentiate once.
  -- Establish on a punctured/full nbhd where everything is differentiable.
  -- First: ψ differentiable on a nbhd of 0.
  have hψdiff : ∀ᶠ τ : ℝ in 𝓝 (0:ℝ), DifferentiableAt ℝ psi τ :=
    eventually_differentiableAt_psi
  -- product rule for deriv(ψ·Sfun) on the nbhd
  have hprod : (deriv (fun τ => psi τ * Sfun τ)) =ᶠ[𝓝 (0:ℝ)]
      fun τ => deriv psi τ * Sfun τ + psi τ * deriv Sfun τ := by
    filter_upwards [hψdiff] with τ hτ
    exact deriv_mul hτ (differentiable_Sfun τ)
  -- the product equals Cfun near 0, so derivs agree near 0
  have hderiv1 : (deriv Cfun) =ᶠ[𝓝 (0:ℝ)]
      fun τ => deriv psi τ * Sfun τ + psi τ * deriv Sfun τ :=
    (psi_mul_Sfun_eventually.deriv.symm).trans hprod
  -- Now differentiate hderiv1 at 0.  LHS deriv = deriv (deriv Cfun) 0 = -π².
  -- RHS = deriv (fun τ => deriv ψ τ * Sfun τ + ψ τ * deriv Sfun τ) 0.
  -- Evaluate the RHS derivative using the product/sum rule, needing differentiability of the
  -- factors at 0: deriv ψ, ψ, Sfun, deriv Sfun all differentiable at 0.
  have hψ_d : DifferentiableAt ℝ psi 0 := hψcd.differentiableAt (by decide)
  have hψ_dd : DifferentiableAt ℝ (deriv psi) 0 := by
    have : ContDiffAt ℝ 1 (deriv psi) 0 := hψcd.derivWithin (by decide)
    exact this.differentiableAt (by decide)
  have hS_d : DifferentiableAt ℝ Sfun 0 := differentiable_Sfun 0
  have hS_dd : DifferentiableAt ℝ (deriv Sfun) 0 := by
    have : ContDiffAt ℝ 1 (deriv Sfun) 0 := contDiff_Sfun.contDiffAt.derivWithin (by decide)
    exact this.differentiableAt (by decide)
  -- HasDerivAt of the RHS function at 0
  have hRHS : HasDerivAt (fun τ => deriv psi τ * Sfun τ + psi τ * deriv Sfun τ)
      ((deriv (deriv psi) 0 * Sfun 0 + deriv psi 0 * deriv Sfun 0)
        + (deriv psi 0 * deriv Sfun 0 + psi 0 * deriv (deriv Sfun) 0)) 0 := by
    have hA : HasDerivAt (fun τ => deriv psi τ * Sfun τ)
        (deriv (deriv psi) 0 * Sfun 0 + deriv psi 0 * deriv Sfun 0) 0 :=
      (hψ_dd.hasDerivAt).mul (hS_d.hasDerivAt)
    have hB : HasDerivAt (fun τ => psi τ * deriv Sfun τ)
        (deriv psi 0 * deriv Sfun 0 + psi 0 * deriv (deriv Sfun) 0) 0 :=
      (hψ_d.hasDerivAt).mul (hS_dd.hasDerivAt)
    exact hA.add hB
  -- deriv of LHS (deriv Cfun) at 0 = deriv (deriv Cfun) 0
  have hLHSval : deriv (deriv Cfun) 0 =
      (deriv (deriv psi) 0 * Sfun 0 + deriv psi 0 * deriv Sfun 0)
        + (deriv psi 0 * deriv Sfun 0 + psi 0 * deriv (deriv Sfun) 0) := by
    rw [hderiv1.deriv_eq]
    exact hRHS.deriv
  -- plug in known values
  rw [deriv_deriv_Cfun_zero, Sfun_zero, deriv_psi_zero, deriv_Sfun_zero, psi_zero,
    deriv_deriv_Sfun_zero] at hLHSval
  -- hLHSval : -π² = (ψ''(0)·1 + 0·0) + (0·0 + 1·(-π²/3))
  linarith [hLHSval]

/-- `Jext''(0) = −2π²/3`.  (`Ĵ''(0) = −2ψ'(0) + ψ''(0) = ψ''(0) = −2π²/3`.) -/
theorem deriv_deriv_Jext_zero : deriv (deriv Jext) 0 = -(2 * Real.pi ^ 2 / 3) := by
  -- deriv Jext =ᶠ fun τ => -psi τ + (1-τ)·deriv psi τ + 1  near 0, then differentiate at 0.
  have hψne : ∀ᶠ τ : ℝ in 𝓝 (0:ℝ), DifferentiableAt ℝ psi τ :=
    eventually_differentiableAt_psi
  -- deriv Jext =ᶠ  -psi + (1-·) deriv psi + 1
  have hdJ : (deriv Jext) =ᶠ[𝓝 (0:ℝ)]
      fun τ => -psi τ + (1 - τ) * deriv psi τ + 1 := by
    filter_upwards [hψne] with τ hτ
    have hlin : HasDerivAt (fun s : ℝ => (1 - s)) (-1 : ℝ) τ := by
      simpa using (hasDerivAt_id τ).const_sub 1
    have hmul : HasDerivAt (fun s : ℝ => (1 - s) * psi s)
        ((-1) * psi τ + (1 - τ) * deriv psi τ) τ := by
      refine (hlin.mul hτ.hasDerivAt).congr_of_eventuallyEq ?_
      filter_upwards with s
      rfl
    have hJ : HasDerivAt Jext ((-1) * psi τ + (1 - τ) * deriv psi τ + 1) τ :=
      hmul.add (hasDerivAt_id τ)
    rw [hJ.deriv]; ring
  -- differentiate the RHS at 0
  have hψ_d : DifferentiableAt ℝ psi 0 := contDiffAt_psi_zero.differentiableAt (by decide)
  have hψ_dd : DifferentiableAt ℝ (deriv psi) 0 := by
    have : ContDiffAt ℝ 1 (deriv psi) 0 := contDiffAt_psi_zero.derivWithin (by decide)
    exact this.differentiableAt (by decide)
  have hRHS : HasDerivAt (fun τ => -psi τ + (1 - τ) * deriv psi τ + 1)
      ((-deriv psi 0) + ((-1) * deriv psi 0 + (1 - 0) * deriv (deriv psi) 0) + 0) 0 := by
    have h1 : HasDerivAt (fun τ : ℝ => -psi τ) (-deriv psi 0) 0 := (hψ_d.hasDerivAt).neg
    have hlin : HasDerivAt (fun s : ℝ => (1 - s)) (-1 : ℝ) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_sub 1
    have h2 : HasDerivAt (fun τ : ℝ => (1 - τ) * deriv psi τ)
        ((-1) * deriv psi 0 + (1 - 0) * deriv (deriv psi) 0) 0 :=
      hlin.mul (hψ_dd.hasDerivAt)
    have h3 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 0 := hasDerivAt_const 0 1
    exact (h1.add h2).add h3
  rw [hdJ.deriv_eq, hRHS.deriv, deriv_psi_zero, deriv_deriv_psi_zero]; ring

/-! ## §3b — Removable corner limits at `0` -/

/-- **Corner limit of `Ĵ'` at `0`:** `jhatD1Ext` is continuous within `[0,1]` at `0`. -/
theorem continuousWithinAt_jhatD1Ext_zero :
    ContinuousWithinAt jhatD1Ext (Set.Icc (0:ℝ) 1) 0 := by
  have hval : jhatD1Ext 0 = 0 := by unfold jhatD1Ext; simp
  rw [ContinuousWithinAt, hval]
  have hlim : Tendsto (deriv Jext) (𝓝[Set.Icc (0:ℝ) 1] 0) (𝓝 (deriv Jext 0)) :=
    continuousAt_deriv_Jext_zero.continuousWithinAt
  rw [deriv_Jext_zero] at hlim
  refine hlim.congr' ?_
  -- eventually within 𝓝[Icc 0 1] 0, deriv Jext τ = jhatD1Ext τ
  have hsub : Set.Ico (0:ℝ) 1 ∈ 𝓝[Set.Icc (0:ℝ) 1] 0 := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio (1:ℝ), isOpen_Iio, by norm_num, by
      intro x hx; exact ⟨hx.2.1, hx.1⟩⟩
  filter_upwards [hsub] with x hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · -- x = 0
    rw [← h]
    rw [deriv_Jext_zero]
    unfold jhatD1Ext; simp
  · -- x ∈ (0,1)
    rw [deriv_Jext_eq_jhatD1 h hx.2, jhatD1Ext_interior h hx.2]

/-- **Corner limit of `Ĵ''` at `0`:** `jhatD2Ext` is continuous within `[0,1]` at `0`. -/
theorem continuousWithinAt_jhatD2Ext_zero :
    ContinuousWithinAt jhatD2Ext (Set.Icc (0:ℝ) 1) 0 := by
  have hval : jhatD2Ext 0 = -(2 * Real.pi ^ 2 / 3) := by unfold jhatD2Ext; simp
  rw [ContinuousWithinAt, hval]
  have hlim : Tendsto (deriv (deriv Jext)) (𝓝[Set.Icc (0:ℝ) 1] 0)
      (𝓝 (deriv (deriv Jext) 0)) :=
    continuousAt_deriv_deriv_Jext_zero.continuousWithinAt
  rw [deriv_deriv_Jext_zero] at hlim
  refine hlim.congr' ?_
  have hsub : Set.Ico (0:ℝ) 1 ∈ 𝓝[Set.Icc (0:ℝ) 1] 0 := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio (1:ℝ), isOpen_Iio, by norm_num, by
      intro x hx; exact ⟨hx.2.1, hx.1⟩⟩
  filter_upwards [hsub] with x hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h, deriv_deriv_Jext_zero]
    unfold jhatD2Ext; simp
  · rw [deriv_deriv_Jext_eq_jhatD2 h hx.2, jhatD2Ext_interior h hx.2]

/-! ## §4 — Reflection symmetry: corner limits at `1` from those at `0`

The closed forms satisfy `jhatD1(1−u) = jhatD1(u)` and `jhatD2(1−u) = −jhatD2(u)`. -/

/-- `jhatD1(1−u) = jhatD1(u)` (algebraic identity of the closed form). -/
theorem jhatD1_reflect (u : ℝ) :
    jhatD1 (1 - u) = jhatD1 u := by
  have hcos : Real.cos (Real.pi * (1 - u)) = -Real.cos (Real.pi * u) := by
    rw [mul_sub, mul_one, Real.cos_pi_sub]
  have hsin : Real.sin (Real.pi * (1 - u)) = Real.sin (Real.pi * u) := by
    rw [mul_sub, mul_one, Real.sin_pi_sub]
  unfold jhatD1
  rw [hcos, hsin]
  ring

/-- `jhatD2(1−u) = −jhatD2(u)` (algebraic identity of the closed form). -/
theorem jhatD2_reflect (u : ℝ) :
    jhatD2 (1 - u) = -jhatD2 u := by
  have hcos : Real.cos (Real.pi * (1 - u)) = -Real.cos (Real.pi * u) := by
    rw [mul_sub, mul_one, Real.cos_pi_sub]
  have hsin : Real.sin (Real.pi * (1 - u)) = Real.sin (Real.pi * u) := by
    rw [mul_sub, mul_one, Real.sin_pi_sub]
  unfold jhatD2
  rw [hcos, hsin]
  ring

/-- `jhatD1Ext(1−u) = jhatD1Ext(u)` (on the right piece, corners included). -/
theorem jhatD1Ext_reflect (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 1) :
    jhatD1Ext (1 - u) = jhatD1Ext u := by
  rcases eq_or_lt_of_le hu.1 with h0 | h0
  · -- u = 0 ⇒ 1-u = 1
    rw [← h0]
    unfold jhatD1Ext; norm_num
  · rcases eq_or_lt_of_le hu.2 with h1 | h1
    · -- u = 1 ⇒ 1-u = 0
      rw [h1]
      unfold jhatD1Ext; norm_num
    · -- interior
      rw [jhatD1Ext_interior (by linarith) (by linarith), jhatD1Ext_interior h0 h1,
        jhatD1_reflect u]

/-- `jhatD2Ext(1−u) = −jhatD2Ext(u)` (right piece, corners included). -/
theorem jhatD2Ext_reflect (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 1) :
    jhatD2Ext (1 - u) = -jhatD2Ext u := by
  rcases eq_or_lt_of_le hu.1 with h0 | h0
  · rw [← h0]
    unfold jhatD2Ext; norm_num
  · rcases eq_or_lt_of_le hu.2 with h1 | h1
    · rw [h1]
      unfold jhatD2Ext; norm_num
    · rw [jhatD2Ext_interior (by linarith) (by linarith), jhatD2Ext_interior h0 h1,
        jhatD2_reflect u]

/-- The reflection map `u ↦ 1 − u` is continuous and maps `[0,1]` into `[0,1]` fixing the
neighborhood structure: `𝓝[Icc 0 1] 1` pushes to `𝓝[Icc 0 1] 0` under `u ↦ 1-u`. -/
theorem tendsto_reflect_one :
    Tendsto (fun u : ℝ => 1 - u) (𝓝[Set.Icc (0:ℝ) 1] 1) (𝓝[Set.Icc (0:ℝ) 1] 0) := by
  have hcont : Tendsto (fun u : ℝ => 1 - u) (𝓝[Set.Icc (0:ℝ) 1] 1) (𝓝 (0:ℝ)) := by
    have hca : ContinuousAt (fun u : ℝ => 1 - u) 1 := by fun_prop
    have : Tendsto (fun u : ℝ => 1 - u) (𝓝 (1:ℝ)) (𝓝 (0:ℝ)) := by simpa using hca.tendsto
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hcont ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact ⟨by linarith [hu.2], by linarith [hu.1]⟩

/-- **Corner limit of `Ĵ'` at `1`:** `jhatD1Ext` is continuous within `[0,1]` at `1`. -/
theorem continuousWithinAt_jhatD1Ext_one :
    ContinuousWithinAt jhatD1Ext (Set.Icc (0:ℝ) 1) 1 := by
  -- jhatD1Ext (1 - ·) → jhatD1Ext 0 along 𝓝[Icc] 1, and jhatD1Ext(1-u)=jhatD1Ext u
  have h0 := continuousWithinAt_jhatD1Ext_zero
  -- compose: jhatD1Ext ∘ (1-·) tends to jhatD1Ext 0
  have hcomp : Tendsto (fun u : ℝ => jhatD1Ext (1 - u)) (𝓝[Set.Icc (0:ℝ) 1] 1)
      (𝓝 (jhatD1Ext 0)) :=
    h0.tendsto.comp tendsto_reflect_one
  -- value: jhatD1Ext 0 = 0 = jhatD1Ext 1
  have hval : jhatD1Ext 0 = jhatD1Ext 1 := by unfold jhatD1Ext; norm_num
  rw [hval] at hcomp
  -- rewrite jhatD1Ext (1-u) = jhatD1Ext u eventually
  rw [ContinuousWithinAt]
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact jhatD1Ext_reflect u hu

/-- **Corner limit of `Ĵ''` at `1`:** `jhatD2Ext` is continuous within `[0,1]` at `1`. -/
theorem continuousWithinAt_jhatD2Ext_one :
    ContinuousWithinAt jhatD2Ext (Set.Icc (0:ℝ) 1) 1 := by
  have h0 := continuousWithinAt_jhatD2Ext_zero
  -- jhatD2Ext ∘ (1-·) → jhatD2Ext 0 ; and jhatD2Ext(1-u) = -jhatD2Ext u
  have hcomp : Tendsto (fun u : ℝ => jhatD2Ext (1 - u)) (𝓝[Set.Icc (0:ℝ) 1] 1)
      (𝓝 (jhatD2Ext 0)) :=
    h0.tendsto.comp tendsto_reflect_one
  -- so jhatD2Ext(1-u) → jhatD2Ext 0, and (-jhatD2Ext u) → jhatD2Ext 0,
  -- hence jhatD2Ext u → -jhatD2Ext 0 = jhatD2Ext 1.
  have hval0 : jhatD2Ext 0 = -(2 * Real.pi ^ 2 / 3) := by unfold jhatD2Ext; simp
  have hval1 : jhatD2Ext 1 = 2 * Real.pi ^ 2 / 3 := by unfold jhatD2Ext; norm_num
  -- rewrite jhatD2Ext(1-u) = -jhatD2Ext u
  have hcomp' : Tendsto (fun u : ℝ => -jhatD2Ext u) (𝓝[Set.Icc (0:ℝ) 1] 1)
      (𝓝 (jhatD2Ext 0)) := by
    refine hcomp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact jhatD2Ext_reflect u hu
  -- negate
  have hfin : Tendsto (fun u : ℝ => jhatD2Ext u) (𝓝[Set.Icc (0:ℝ) 1] 1)
      (𝓝 (-jhatD2Ext 0)) := by
    have := hcomp'.neg
    simpa using this
  have hneg : -jhatD2Ext 0 = jhatD2Ext 1 := by rw [hval0, hval1]; ring
  rw [ContinuousWithinAt, ← hneg]
  exact hfin

/-! ## §5 — Assembly: discharge of `VaalerJhatDerivCornerLimits` -/

/-- **DISCHARGE: `VaalerJhatDerivCornerLimits`.** -/
theorem vaalerJhatDerivCornerLimits_holds : VaalerJhatDerivCornerLimits :=
  ⟨continuousWithinAt_jhatD1Ext_zero, continuousWithinAt_jhatD1Ext_one,
    continuousWithinAt_jhatD2Ext_zero, continuousWithinAt_jhatD2Ext_one⟩

/-- **`VaalerJTwoIBPDecay`** — closed via the committed capstone. -/
theorem vaalerJTwoIBPDecay_holds :
    MathExtras.NumberTheory.Analysis.VaalerJDecayBound.VaalerJTwoIBPDecay :=
  vaalerJTwoIBPDecay_of_limits vaalerJhatDerivCornerLimits_holds

/-- **`JIntegrable`** — closed via the committed capstone. -/
theorem jIntegrable_holds : VaalerTheorem6JFT.JIntegrable :=
  jIntegrable_of_limits vaalerJhatDerivCornerLimits_holds

#print axioms deriv_deriv_sinc_zero
#print axioms vaalerJhatDerivCornerLimits_holds
#print axioms vaalerJTwoIBPDecay_holds
#print axioms jIntegrable_holds

end MathExtras.NumberTheory.Analysis.VaalerJhatCornerLimits
