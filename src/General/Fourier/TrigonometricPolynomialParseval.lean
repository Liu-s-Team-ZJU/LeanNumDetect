import General.Fourier.ExponentialWindowOrthogonality
import General.Fourier.SeparatedCubeFourierContinuous
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Parseval bridge for trigonometric polynomials on the unit torus

This file bridges coefficient-space quantities of a finite presentation of a
trigonometric polynomial to genuine function-space norms on the unit torus
`𝕋^d = ℝ^d / ℤ^d` in the manuscript's normalization: with integer frequency
vectors `s i : ℤ^d` and coefficients `c i : ℂ`,

$$
f(\bm\omega) = \sum_i c_i\, e^{2\pi i\, \mathbf s_i \cdot \bm\omega},
\qquad \bm\omega \in \mathbb T^d \cong [0,1)^d .
$$

The unit cube `unitTorus d` is a fundamental domain of volume one, so
integration over it is integration against the torus's normalized Haar
measure.  The main consequences are:

* Parseval `integral_norm_sq_unitTorusTrigPolynomial`:
  $\int_{\mathbb T^d}\|f\|^2 = \sum_i \|c_i\|^2$, hence
  $\|f\|_{L^2(\mathbb T^d)} = $ `Real.sqrt (energy c)` with `energy c` the
  coefficient energy $\sum_i \|c_i\|^2$ (`SegmentedVDM.energy` of the
  coefficient vector); see `unitTorusL2Norm_eq_sqrt`;
* the sup-norm bound `norm_unitTorusTrigPolynomial_le` /
  `unitTorusLInfNorm_le`: $\|f\|_{L^\infty(\mathbb T^d)} \le \sum_i \|c_i\|$,
  the coefficient `ℓ¹` mass (`SegmentedPacket.mass`,
  `SegmentedVDM.Packet.mass`), together with
  `sum_norm_le_sqrt_card_mul_sqrt_sum_norm_sq`, the Cauchy--Schwarz step

  $$
  \sum_i \|c_i\| \le \sqrt{N}\Big(\sum_i \|c_i\|^2\Big)^{1/2},
  $$

  which produces the $\sqrt{|\Lambda^d|}$ factor of manuscript
  `lem:interpolation_via_svd`;
* the integer-frequency orthogonality these rest on: `integral_unitTorusChar`
  and `integral_unitTorusChar_sub`
  ($\int_0^1 e^{2\pi i (s-t)\omega}\,d\omega = \delta_{s,t}$ for $s,t\in\mathbb Z$)
  and its `d`-dimensional product form
  `integral_star_unitTorusAtom_mul_unitTorusAtom`.

## Repeated frequencies

Parseval is **false** for a presentation containing repeated frequency
vectors: the mixed terms between equal frequencies survive.  This repository
explicitly allows repeated frequencies in presentations (coefficients are
collected only when a matrix coefficient row is formed), so the distinctness
hypothesis is stated honestly as `Function.Injective` on the frequency map `s`
and is never assumed away.  `parseval_fails_of_repeated_frequencies` exhibits
a concrete counterexample.  What remains true without any distinctness
hypothesis is the collected form
`integral_norm_sq_unitTorusTrigPolynomial_collected`: collecting the
coefficients at equal frequencies first (`collectedCoeff`) and then applying
Parseval gives $\int_{\mathbb T^d}\|f\|^2 =
\sum_{\mathbf u}\|\sum_{i:\mathbf s_i=\mathbf u} c_i\|^2$.

## Angular convention

The repository evaluates segmented polynomials in the angular normalization
`SegmentedPacket.value D x = ∑ i, c i * exp (i (D s_i + h_i) · x)` on
`x ∈ (-π, π]^d`, while the manuscript writes
$f(\bm\omega) = \sum_i c_i e^{2\pi i \mathbf s_i\cdot\bm\omega}$ on
$\bm\omega\in[0,1)^d$.  The two agree under the angular reduction
$\bm\omega = \mathbf y/2\pi$.  `angularTrigPolynomial` is the evaluation with
the `SegmentedPacket.value` phase convention, and
`unitTorusTrigPolynomial_eq_angularTrigPolynomial` identifies
`unitTorusTrigPolynomial s c ω` with `angularTrigPolynomial s c (2π • ω)`.
The bridge statements phrased directly in the angular convention are
`integral_norm_sq_angularTrigPolynomial_scale` (the `L²(𝕋^d)` statement of
manuscript `lem:minsvd_bound_by_lagInterp_high_dim`,
`lem:interpolation_via_svd`) and `norm_angularTrigPolynomial_le` (the
`L^∞(𝕋^d)` statement of `lem:localization`, cf. `SegmentedPacket.linftyNorm`,
which is the supremum of these evaluation moduli).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators

namespace LeanNumDetect

noncomputable section

/-! ### One-dimensional integer-frequency orthogonality -/

/-- The unit-torus character of integer frequency `n`:
`e_n(x) = exp (2πi n x)`. -/
def unitTorusChar (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((2 * Real.pi) * ((n : ℝ) * x) : ℝ) : ℂ))

/-- Integer-frequency orthogonality on the unit interval:
`∫_0^1 exp (2πi n x) dx = δ_{n,0}`. -/
theorem integral_unitTorusChar (n : ℤ) :
    ∫ x in Set.Icc (0:ℝ) 1, unitTorusChar n x = if n = 0 then 1 else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [if_pos rfl]
    have h : ∀ x : ℝ, unitTorusChar (0:ℤ) x = 1 := by
      intro x
      simp [unitTorusChar]
    rw [integral_congr_ae (Filter.Eventually.of_forall h), setIntegral_const,
      show MeasureTheory.volume.real (Set.Icc (0:ℝ) 1) =
        (MeasureTheory.volume (Set.Icc (0:ℝ) 1)).toReal from rfl,
      Real.volume_Icc]
    simp
  · have hform : ∀ x : ℝ, unitTorusChar n x =
        Complex.exp (((n : ℂ) * (2 * Real.pi * Complex.I)) * x) := by
      intro x
      simp only [unitTorusChar]
      congr 1
      push_cast
      ring
    have hne : (n : ℂ) * (2 * Real.pi * Complex.I) ≠ 0 := by
      refine mul_ne_zero ?_ (mul_ne_zero ?_ Complex.I_ne_zero)
      · exact_mod_cast hn
      · have h2π : ((2:ℝ) * Real.pi) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_pos.ne'
        exact_mod_cast h2π
    have hconv : ∫ x in Set.Icc (0:ℝ) 1, unitTorusChar n x =
        ∫ x in (0:ℝ)..1, unitTorusChar n x := by
      rw [MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)).symm,
        ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    have hkey : ∫ x in (0:ℝ)..1, unitTorusChar n x =
        ∫ x in (0:ℝ)..1,
          Complex.exp (((n : ℂ) * (2 * Real.pi * Complex.I)) * x) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact hform x
    have h1 : Complex.exp (((n : ℂ) * (2 * Real.pi * Complex.I)) * (1:ℝ)) = 1 := by
      have e1 : (((n : ℂ) * (2 * Real.pi * Complex.I)) * (1:ℝ)) =
          (n : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        ring
      rw [e1, Complex.exp_int_mul_two_pi_mul_I]
    have h0 : Complex.exp (((n : ℂ) * (2 * Real.pi * Complex.I)) * (0:ℝ)) = 1 := by
      simp
    rw [hconv, hkey, integral_exp_mul_complex hne, if_neg hn, h1, h0, sub_self,
      zero_div]

/-- Orthogonality of integer frequencies `s` and `t` on the unit interval:
`∫_0^1 exp (2πi (s - t) ω) dω = δ_{s,t}`. -/
theorem integral_unitTorusChar_sub (s t : ℤ) :
    ∫ x in Set.Icc (0:ℝ) 1, unitTorusChar (s - t) x = if s = t then 1 else 0 := by
  rw [integral_unitTorusChar]
  by_cases h : s = t
  · simp [h]
  · simp [h, sub_eq_zero]

/-! ### Product factorization over a coordinate box -/

/-- Fubini factorization over a coordinate box: the integral of a product of
coordinate-wise factors over `Set.univ.pi s` splits as the product of the
one-dimensional restricted integrals.  This is the product structure behind
the `d`-dimensional form of integer-frequency orthogonality. -/
theorem setIntegral_univ_pi_prod_eq {d : ℕ} (s : Fin d → Set ℝ) (g : (k : Fin d) → ℝ → ℂ) :
    ∫ ω in Set.univ.pi s, ∏ k, g k (ω k) = ∏ k, ∫ x in s k, g k x := by
  have h := MeasureTheory.integral_fintype_prod_eq_prod (fun k x => g k x)
    (μ := fun k : Fin d => volume.restrict (s k))
  rw [← Measure.restrict_pi_pi (fun _ : Fin d => (volume : Measure ℝ)) s,
    ← MeasureTheory.volume_pi] at h
  exact h

/-! ### Atoms and trigonometric polynomials on the unit torus -/

/-- A fundamental domain of the unit torus `𝕋^d = ℝ^d / ℤ^d`: the unit cube.
Its `d`-dimensional volume is one (closed versus half-open is immaterial for
integration), so integration over it is integration against the normalized
Haar measure of the torus. -/
def unitTorus (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi fun _ => Set.Icc (0:ℝ) 1

theorem unitTorus_eq_Icc (d : ℕ) : unitTorus d = Set.Icc (0 : Fin d → ℝ) 1 := by
  rw [unitTorus, Set.pi_univ_Icc (fun _ : Fin d => (0:ℝ)) (fun _ => (1:ℝ))]
  rfl

theorem isCompact_unitTorus (d : ℕ) : IsCompact (unitTorus d) := by
  rw [unitTorus_eq_Icc]
  exact isCompact_Icc

/-- A single unit-torus Fourier atom `exp (2πi s · ω)` with integer frequency
vector `s : ℤ^d`. -/
def unitTorusAtom {d : ℕ} (s : Fin d → ℤ) (ω : Fin d → ℝ) : ℂ :=
  Complex.exp (Complex.I * (((2 * Real.pi) * (∑ k, (s k : ℝ) * ω k) : ℝ) : ℂ))

theorem continuous_unitTorusAtom {d : ℕ} (s : Fin d → ℤ) : Continuous (unitTorusAtom s) := by
  show Continuous fun ω : Fin d → ℝ => _
  simp only [unitTorusAtom]
  fun_prop

@[simp]
theorem norm_unitTorusAtom {d : ℕ} (s : Fin d → ℤ) (ω : Fin d → ℝ) :
    ‖unitTorusAtom s ω‖ = 1 := by
  simp [unitTorusAtom, Complex.norm_exp, Complex.mul_re]

/-- The atom factors as a product of one-dimensional characters. -/
theorem unitTorusAtom_eq_prod {d : ℕ} (s : Fin d → ℤ) (ω : Fin d → ℝ) :
    unitTorusAtom s ω = ∏ k, unitTorusChar (s k) (ω k) := by
  simp only [unitTorusAtom, unitTorusChar]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum]

/-- Conjugate pairs combine by subtraction of frequencies; this packages
`exponential_node_inner` at unit coefficients. -/
theorem star_unitTorusAtom_mul_unitTorusAtom {d : ℕ} (s t : Fin d → ℤ) (ω : Fin d → ℝ) :
    star (unitTorusAtom s ω) * unitTorusAtom t ω = unitTorusAtom (t - s) ω := by
  have hreal : (2 * Real.pi) * ((∑ k, (t k : ℝ) * ω k) - (∑ k, (s k : ℝ) * ω k)) =
      (2 * Real.pi) * (∑ k, ((t - s) k : ℝ) * ω k) := by
    rw [← Finset.sum_sub_distrib]
    refine congrArg ((2 * Real.pi) * ·) ?_
    apply Finset.sum_congr rfl
    intro k _
    rw [Pi.sub_apply, Int.cast_sub, sub_mul]
  simp only [unitTorusAtom]
  have h := exponential_node_inner (∑ k, (s k : ℝ) * ω k) (∑ k, (t k : ℝ) * ω k)
    (2 * Real.pi) 1 1
  simp only [one_mul, star_one] at h
  rw [h, hreal]

/-- The `d`-dimensional product form of integer-frequency orthogonality: an
atom integrates to one at frequency zero and to zero otherwise. -/
theorem integral_unitTorusAtom {d : ℕ} (s : Fin d → ℤ) :
    ∫ ω in unitTorus d, unitTorusAtom s ω = if s = 0 then 1 else 0 := by
  have hconv : (fun ω => unitTorusAtom s ω) =ᵐ[volume.restrict (unitTorus d)]
      (fun ω => ∏ k, unitTorusChar (s k) (ω k)) :=
    Filter.Eventually.of_forall fun ω => unitTorusAtom_eq_prod s ω
  rw [integral_congr_ae hconv]
  show ∫ ω in Set.univ.pi fun _ => Set.Icc (0:ℝ) 1,
    ∏ k, unitTorusChar (s k) (ω k) = if s = 0 then 1 else 0
  rw [setIntegral_univ_pi_prod_eq]
  simp_rw [integral_unitTorusChar]
  by_cases h : s = 0
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg (by simpa using hk))

/-- Orthogonality of integer frequency vectors on the unit torus. -/
theorem integral_star_unitTorusAtom_mul_unitTorusAtom {d : ℕ} (s t : Fin d → ℤ) :
    ∫ ω in unitTorus d, star (unitTorusAtom s ω) * unitTorusAtom t ω =
      if s = t then 1 else 0 := by
  have hconv : (fun ω => star (unitTorusAtom s ω) * unitTorusAtom t ω)
      =ᵐ[volume.restrict (unitTorus d)] (fun ω => unitTorusAtom (t - s) ω) :=
    Filter.Eventually.of_forall fun ω => star_unitTorusAtom_mul_unitTorusAtom s t ω
  rw [integral_congr_ae hconv, integral_unitTorusAtom]
  by_cases h : s = t
  · subst h
    simp
  · have hne : ¬(t - s = 0) := by
      rw [sub_eq_zero]
      exact ne_comm.mp h
    rw [if_neg hne, if_neg h]

/-- A finite trigonometric polynomial on the unit torus with integer frequency
vectors: `∑ i, c i * exp (2πi s i · ω)`. -/
def unitTorusTrigPolynomial {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Fin d → ℤ) (c : ι → ℂ) : (Fin d → ℝ) → ℂ :=
  fun ω => ∑ i, c i * unitTorusAtom (s i) ω

/-! ### Parseval on the unit torus -/

private theorem integral_re_const_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (K : ℂ) (G : Ω → ℂ) (hG : Integrable G μ) :
    ∫ ω, (K * G ω).re ∂μ = (K * ∫ ω, G ω ∂μ).re := by
  have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM (hG.const_mul K)
  simp only [integral_const_mul] at h
  exact h

private theorem integrableOn_unitTorus_cross {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Fin d → ℤ) (c : ι → ℂ) (i j : ι) :
    Integrable (fun ω =>
      (star (c i * unitTorusAtom (s i) ω) * (c j * unitTorusAtom (s j) ω)).re)
      (volume.restrict (unitTorus d)) := by
  show IntegrableOn (fun ω =>
      (star (c i * unitTorusAtom (s i) ω) * (c j * unitTorusAtom (s j) ω)).re)
      (unitTorus d)
  apply ContinuousOn.integrableOn_compact (isCompact_unitTorus d)
  have h1 : Continuous (unitTorusAtom (s i)) := continuous_unitTorusAtom _
  have h2 : Continuous (unitTorusAtom (s j)) := continuous_unitTorusAtom _
  fun_prop

/-- The full pair-interaction identity behind Parseval: with repeated
frequencies allowed, the mixed term of two presented atoms survives exactly at
equal frequencies.  This is the honest statement from which both the injective
and the collected forms of Parseval follow. -/
theorem integral_norm_sq_unitTorusTrigPolynomial_eq_sum_ite {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Fin d → ℤ) (c : ι → ℂ) :
    ∫ ω in unitTorus d, ‖unitTorusTrigPolynomial s c ω‖ ^ 2 =
      ∑ i, ∑ j, if s i = s j then (star (c i) * c j).re else 0 := by
  have hint : ∀ i j : ι, Integrable
      (fun ω => (1:ℝ) *
        (star (c i * unitTorusAtom (s i) ω) * (c j * unitTorusAtom (s j) ω)).re)
      (volume.restrict (unitTorus d)) := by
    intro i j
    simpa only [one_mul] using integrableOn_unitTorus_cross s c i j
  have hp : ∀ i j : ι, ∫ ω in unitTorus d,
      (star (c i * unitTorusAtom (s i) ω) * (c j * unitTorusAtom (s j) ω)).re =
      if s i = s j then (star (c i) * c j).re else 0 := by
    intro i j
    have hmul : ∀ ω, star (c i * unitTorusAtom (s i) ω) * (c j * unitTorusAtom (s j) ω) =
        (star (c i) * c j) * (star (unitTorusAtom (s i) ω) * unitTorusAtom (s j) ω) := by
      intro ω
      rw [star_mul]
      ring
    have hG : Integrable (fun ω => star (unitTorusAtom (s i) ω) * unitTorusAtom (s j) ω)
        (volume.restrict (unitTorus d)) := by
      apply ContinuousOn.integrableOn_compact (isCompact_unitTorus d)
      have h1 : Continuous (unitTorusAtom (s i)) := continuous_unitTorusAtom _
      have h2 : Continuous (unitTorusAtom (s j)) := continuous_unitTorusAtom _
      fun_prop
    have hconv : (fun ω =>
        (star (c i * unitTorusAtom (s i) ω) * (c j * unitTorusAtom (s j) ω)).re)
        =ᵐ[volume.restrict (unitTorus d)]
        (fun ω =>
          ((star (c i) * c j) *
            (star (unitTorusAtom (s i) ω) * unitTorusAtom (s j) ω)).re) :=
      Filter.Eventually.of_forall fun ω => by simp only [hmul]
    rw [integral_congr_ae hconv,
      integral_re_const_mul (volume.restrict (unitTorus d))
        (star (c i) * c j) _ hG,
      integral_star_unitTorusAtom_mul_unitTorusAtom]
    by_cases h : s i = s j <;> simp [h]
  have h := SeparatedCubeFourierContinuous.weighted_integral_energy_eq_pair_integrals
    (volume.restrict (unitTorus d)) (fun _ => 1)
    (fun i ω => c i * unitTorusAtom (s i) ω) hint
  simp only [one_mul] at h
  simp only [unitTorusTrigPolynomial]
  rw [h]
  simp_rw [hp]

/-- The diagonal part of the pair interaction: `(star c * c).re = ‖c‖ ^ 2`. -/
theorem star_mul_re_self {c : ℂ} : (star c * c).re = ‖c‖ ^ 2 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

/-- **Parseval on the unit torus.**  The squared `L²(𝕋^d)` norm of a
trigonometric polynomial presented with pairwise distinct integer frequency
vectors equals its coefficient energy: `‖f‖_{L²(𝕋^d)} ^ 2 = energy c`.

Distinctness is essential: repeated frequencies make the mixed terms survive
(`parseval_fails_of_repeated_frequencies`); for presentations with repeated
frequencies use `integral_norm_sq_unitTorusTrigPolynomial_collected`. -/
theorem integral_norm_sq_unitTorusTrigPolynomial {d : ℕ} {ι : Type*} [Fintype ι]
    {s : ι → Fin d → ℤ} (hs : Function.Injective s) (c : ι → ℂ) :
    ∫ ω in unitTorus d, ‖unitTorusTrigPolynomial s c ω‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  letI := Classical.decEq ι
  rw [integral_norm_sq_unitTorusTrigPolynomial_eq_sum_ite]
  have hpair : ∀ i j : ι,
      (if s i = s j then (star (c i) * c j).re else 0) =
        if j = i then (star (c i) * c i).re else 0 := by
    intro i j
    by_cases h : j = i
    · subst h
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun he => h (hs he).symm), if_neg h]
  calc (∑ i : ι, ∑ j : ι, if s i = s j then (star (c i) * c j).re else 0)
      = ∑ i : ι, ∑ j : ι, if j = i then (star (c i) * c i).re else 0 :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpair i j
    _ = ∑ i : ι, (star (c i) * c i).re :=
        Finset.sum_congr rfl fun i _ =>
          (Finset.sum_ite_eq' Finset.univ i (fun _ => (star (c i) * c i).re)).trans
            (if_pos (Finset.mem_univ i))
    _ = ∑ i : ι, ‖c i‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => star_mul_re_self

/-- The genuine `L²(𝕋^d)` norm of a function on the unit torus: the `L²` norm
of its representative on a fundamental domain, with the torus's normalized
Haar measure. -/
noncomputable def unitTorusL2Norm {d : ℕ} (f : (Fin d → ℝ) → ℂ) : ℝ :=
  Real.sqrt (∫ ω in unitTorus d, ‖f ω‖ ^ 2)

/-- Parseval in the form `‖f‖_{L²(𝕋^d)} = Real.sqrt (energy c)`. -/
theorem unitTorusL2Norm_eq_sqrt {d : ℕ} {ι : Type*} [Fintype ι]
    {s : ι → Fin d → ℤ} (hs : Function.Injective s) (c : ι → ℂ) :
    unitTorusL2Norm (unitTorusTrigPolynomial s c) = Real.sqrt (∑ i, ‖c i‖ ^ 2) := by
  rw [unitTorusL2Norm, integral_norm_sq_unitTorusTrigPolynomial hs c]

theorem unitTorusL2Norm_sq_eq {d : ℕ} {ι : Type*} [Fintype ι]
    {s : ι → Fin d → ℤ} (hs : Function.Injective s) (c : ι → ℂ) :
    unitTorusL2Norm (unitTorusTrigPolynomial s c) ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  rw [unitTorusL2Norm, Real.sq_sqrt]
  · exact integral_norm_sq_unitTorusTrigPolynomial hs c
  · exact integral_nonneg fun _ => sq_nonneg _

/-- Parseval phrased with the repository's generic coefficient energy. -/
theorem unitTorusL2Norm_eq_sqrt_coefficientEnergy {d : ℕ} {ι : Type*} [Fintype ι]
    {s : ι → Fin d → ℤ} (hs : Function.Injective s) (c : ι → ℂ) :
    unitTorusL2Norm (unitTorusTrigPolynomial s c) =
      Real.sqrt (External.coefficientEnergy c) :=
  unitTorusL2Norm_eq_sqrt hs c

/-! ### Presentations with repeated frequencies: the collected form -/

/-- The coefficient collected at frequency `u` by a presentation: the sum of
the coefficients of all terms whose frequency vector equals `u`. -/
noncomputable def collectedCoeff {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Fin d → ℤ) (c : ι → ℂ) (u : Fin d → ℤ) : ℂ :=
  ∑ i ∈ Finset.univ.filter (fun i => s i = u), c i

private theorem norm_sum_sq_real_filter {ι : Type*} (t : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ t, z i‖ ^ 2 = ∑ i ∈ t, ∑ j ∈ t, (star (z i) * z j).re := by
  have hh : ((‖∑ i ∈ t, z i‖ ^ 2 : ℝ) : ℂ) = ∑ i ∈ t, ∑ j ∈ t, star (z i) * z j := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul]
    simp only [Finset.mul_sum, Complex.star_def]
  have he := congrArg Complex.re hh
  simpa only [Complex.ofReal_re, Complex.re_sum] using he

/-- Parseval after collecting coefficients at equal frequencies.  For an
arbitrary presentation, repeated frequencies included, the squared `L²(𝕋^d)`
norm equals the coefficient energy of the collected presentation: the sum over
the distinct frequencies `u` of the squared norms of the collected
coefficients.  This is the correct form of Parseval for the repository's
presentations, where repeated frequencies are allowed until coefficients are
collected into a matrix row. -/
theorem integral_norm_sq_unitTorusTrigPolynomial_collected {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Fin d → ℤ) (c : ι → ℂ) :
    ∫ ω in unitTorus d, ‖unitTorusTrigPolynomial s c ω‖ ^ 2 =
      ∑ u ∈ Finset.univ.image s, ‖collectedCoeff s c u‖ ^ 2 := by
  rw [integral_norm_sq_unitTorusTrigPolynomial_eq_sum_ite]
  -- First group the inner sum over the fiber of `i`'s frequency.
  have hinner : ∀ i : ι,
      (∑ j : ι, if s i = s j then (star (c i) * c j).re else 0) =
        ∑ j ∈ Finset.univ.filter (fun j => s j = s i), (star (c i) * c j).re := by
    intro i
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : s i = s j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (ne_comm.mp h)]
  -- Then group both sums over the fibers of the frequency map.
  have hregroup :
      (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => s j = s i), (star (c i) * c j).re) =
        ∑ u ∈ Finset.univ.image s,
          ∑ i ∈ Finset.univ.filter (fun i => s i = u),
            ∑ j ∈ Finset.univ.filter (fun j => s j = u), (star (c i) * c j).re := by
    have hmaps : ∀ i ∈ (Finset.univ : Finset ι), s i ∈ Finset.univ.image s :=
      fun i _ => Finset.mem_image_of_mem s (Finset.mem_univ i)
    rw [← Finset.sum_fiberwise_of_maps_to (g := s) (t := Finset.univ.image s) hmaps]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  simp_rw [hinner]
  rw [hregroup]
  apply Finset.sum_congr rfl
  intro u _
  rw [show ‖collectedCoeff s c u‖ ^ 2 =
      ‖∑ i ∈ Finset.univ.filter (fun i => s i = u), c i‖ ^ 2 by rfl]
  rw [← norm_sum_sq_real_filter (Finset.univ.filter (fun i => s i = u)) c]

/-! ### Sup norm and the Cauchy--Schwarz step -/

/-- Every evaluation modulus is at most the coefficient `ℓ¹` mass by the
triangle inequality.  No distinctness hypothesis on the frequencies is
needed. -/
theorem norm_unitTorusTrigPolynomial_le {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Fin d → ℤ) (c : ι → ℂ) (ω : Fin d → ℝ) :
    ‖unitTorusTrigPolynomial s c ω‖ ≤ ∑ i, ‖c i‖ := by
  unfold unitTorusTrigPolynomial
  refine (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum fun i _ => by
    rw [norm_mul, norm_unitTorusAtom, mul_one]

/-- The `L^∞(𝕋^d)` norm of a function on the unit torus.  The supremum is
taken over all of `ℝ^d`; for the trigonometric polynomials above this agrees
with the supremum over one fundamental domain, since their evaluations are
`1`-periodic in every coordinate. -/
noncomputable def unitTorusLInfNorm {d : ℕ} (f : (Fin d → ℝ) → ℂ) : ℝ :=
  ⨆ x : Fin d → ℝ, ‖f x‖

/-- The `L^∞(𝕋^d)` norm is bounded by the coefficient `ℓ¹` mass.  No
distinctness hypothesis on the frequencies is needed. -/
theorem unitTorusLInfNorm_le {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Fin d → ℤ) (c : ι → ℂ) :
    unitTorusLInfNorm (unitTorusTrigPolynomial s c) ≤ ∑ i, ‖c i‖ :=
  ciSup_le fun x => norm_unitTorusTrigPolynomial_le s c x

/-- The Cauchy--Schwarz step: the coefficient `ℓ¹` mass is at most `√N` times
the square root of the coefficient energy, where `N` is the number of terms.
For a presentation of the frequency set `Λ^d` this is the manuscript's
`√|Λ^d|` factor. -/
theorem sum_norm_le_sqrt_card_mul_sqrt_sum_norm_sq {ι : Type*} [Fintype ι] (c : ι → ℂ) :
    (∑ i, ‖c i‖) ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, ‖c i‖ ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖c i‖) (fun _ => (1:ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_one] at h
  exact h.trans_eq (mul_comm _ _)

/-- The sup norm is at most `√N` times the `L²(𝕋^d)` norm: the manuscript's
`√|Λ^d| ‖f‖_{L²}`-shaped bound of `lem:interpolation_via_svd`. -/
theorem unitTorusLInfNorm_le_sqrt_card_mul_unitTorusL2Norm {d : ℕ} {ι : Type*} [Fintype ι]
    {s : ι → Fin d → ℤ} (hs : Function.Injective s) (c : ι → ℂ) :
    unitTorusLInfNorm (unitTorusTrigPolynomial s c) ≤
      Real.sqrt (Fintype.card ι) * unitTorusL2Norm (unitTorusTrigPolynomial s c) := by
  rw [unitTorusL2Norm_eq_sqrt hs c]
  exact (unitTorusLInfNorm_le s c).trans (sum_norm_le_sqrt_card_mul_sqrt_sum_norm_sq c)

/-! ### The angular convention of `SegmentedPacket.value` -/

/-- A trigonometric polynomial in the repository's angular normalization
`f(x) = ∑ i, c i * exp (i s i · x)` — the phase convention of
`SegmentedPacket.value`, with integer angular frequency vectors (e.g.
`s i k = D * coarse i k + fine i k`). -/
def angularTrigPolynomial {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Fin d → ℤ) (c : ι → ℂ) (x : Fin d → ℝ) : ℂ :=
  ∑ i, c i * Complex.exp (Complex.I * ((∑ k, (s i k : ℝ) * x k : ℝ) : ℂ))

/-- Angular evaluation at `x = 2π • ω` is unit-torus evaluation at `ω`: the
angular reduction `ω = y / (2π)` relating the two conventions. -/
theorem unitTorusTrigPolynomial_eq_angularTrigPolynomial {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Fin d → ℤ) (c : ι → ℂ) (ω : Fin d → ℝ) :
    unitTorusTrigPolynomial s c ω =
      angularTrigPolynomial s c (fun k => 2 * Real.pi * ω k) := by
  simp only [unitTorusTrigPolynomial, angularTrigPolynomial, unitTorusAtom]
  apply Finset.sum_congr rfl
  intro i _
  have hr : ((2 * Real.pi) * (∑ k, (s i k : ℝ) * ω k) : ℝ) =
      ∑ k, (s i k : ℝ) * (2 * Real.pi * ω k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hr]

/-- Parseval for the angular convention under the angular reduction: the
manuscript's `‖f‖_{L²(𝕋^d)}` of the polynomial presented by `P.value D` in
the coordinates `ω = y / (2π)`. -/
theorem integral_norm_sq_angularTrigPolynomial_scale {d : ℕ} {ι : Type*} [Fintype ι]
    {s : ι → Fin d → ℤ} (hs : Function.Injective s) (c : ι → ℂ) :
    ∫ ω in unitTorus d, ‖angularTrigPolynomial s c (fun k => 2 * Real.pi * ω k)‖ ^ 2 =
      ∑ i, ‖c i‖ ^ 2 := by
  simp_rw [← unitTorusTrigPolynomial_eq_angularTrigPolynomial]
  exact integral_norm_sq_unitTorusTrigPolynomial hs c

/-- The coefficient `ℓ¹` mass bounds every angular evaluation modulus: the
`L^∞(𝕋^d)` bound in the angular convention (cf. `SegmentedPacket.linftyNorm`,
which is the supremum of these moduli). -/
theorem norm_angularTrigPolynomial_le {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Fin d → ℤ) (c : ι → ℂ) (x : Fin d → ℝ) :
    ‖angularTrigPolynomial s c x‖ ≤ ∑ i, ‖c i‖ := by
  unfold angularTrigPolynomial
  refine (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum fun i _ => by
    rw [norm_mul]
    have : ‖Complex.exp
        (Complex.I * ((∑ k, (s i k : ℝ) * x k : ℝ) : ℂ))‖ = 1 := by
      simp [Complex.norm_exp, Complex.mul_re]
    rw [this, mul_one]

/-! ### Parseval genuinely fails for duplicate frequencies -/

/-- The distinctness hypothesis in Parseval cannot be dropped: two identical
frequency vectors with unit coefficients present the constant `2` on `𝕋^1`,
whose squared `L²` norm is `4`, while the coefficient energy is `2`.  The
correct replacement is `integral_norm_sq_unitTorusTrigPolynomial_collected`. -/
theorem parseval_fails_of_repeated_frequencies :
    ∃ (d : ℕ) (ι : Type) (_ : Fintype ι) (s : ι → Fin d → ℤ) (c : ι → ℂ),
      ¬ Function.Injective s ∧
        ∫ ω in unitTorus d, ‖unitTorusTrigPolynomial s c ω‖ ^ 2 ≠ ∑ i, ‖c i‖ ^ 2 := by
  refine ⟨1, Fin 2, inferInstance, fun _ _ => 0, fun _ => (1:ℂ), ?_, ?_⟩
  · intro h
    have h01 : ((fun (_ : Fin 2) (_ : Fin 1) => (0:ℤ)) (0 : Fin 2) : Fin 1 → ℤ)
        = (fun (_ : Fin 2) (_ : Fin 1) => (0:ℤ)) 1 := rfl
    have hcong : (0 : Fin 2) = 1 := h h01
    exact absurd hcong (by decide)
  · set s0 : Fin 2 → Fin 1 → ℤ := fun _ _ => 0 with hs0
    set c0 : Fin 2 → ℂ := fun _ => 1 with hc0
    have hval : ∀ ω : Fin 1 → ℝ, unitTorusTrigPolynomial s0 c0 ω = 2 := by
      intro ω
      show (∑ i : Fin 2, c0 i * unitTorusAtom (s0 i) ω) = 2
      rw [Fin.sum_univ_two, hc0, hs0]
      simp [unitTorusAtom]
      norm_num
    have hnorm : ∀ ω : Fin 1 → ℝ, ‖unitTorusTrigPolynomial s0 c0 ω‖ ^ 2 = 4 := by
      intro ω
      rw [hval ω]
      norm_num
    have hl : ∫ ω in unitTorus 1, ‖unitTorusTrigPolynomial s0 c0 ω‖ ^ 2 = 4 := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hnorm), setIntegral_const,
        show MeasureTheory.volume.real (unitTorus 1) =
          (MeasureTheory.volume (unitTorus 1)).toReal from rfl,
        unitTorus_eq_Icc,
        Real.volume_Icc_pi_toReal (fun _ : Fin 1 => by norm_num)]
      simp
    have hr : (∑ i : Fin 2, ‖c0 i‖ ^ 2) = 2 := by
      rw [hc0, Fin.sum_univ_two]
      norm_num
    rw [hl, hr]
    norm_num

end

end LeanNumDetect
