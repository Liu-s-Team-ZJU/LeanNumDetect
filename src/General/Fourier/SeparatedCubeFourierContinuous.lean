import External.SeparatedCubeFourier
import General.Fourier.WeightedOrthogonality

/-!
The continuous, measure-theoretic part of the separated-cube Fourier estimate.

The source proof applies an abstract weighted-orthogonality argument to
Beurling--Selberg minorants and majorants for a cube. This file formalizes that
argument, including the comparison with the actual cube integral and the exact
constants in Li's Theorem 2.3.

Constructing the required multivariate extremal functions is deliberately
separated into `HasBartonCubeCertificates`.  That construction is not currently
available in Mathlib or elsewhere in this project.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace LeanNumDetect
namespace SeparatedCubeFourierContinuous

noncomputable section

/-- The real frequency cube in the normalization of the external theorem. -/
def sourceCube (d : ℕ) (m : ℝ) : Set (Fin d → ℝ) :=
  {ω | ∀ k, |ω k| ≤ m}

theorem sourceCube_eq_Icc (d : ℕ) (m : ℝ) :
    sourceCube d m =
      Set.Icc (fun _ : Fin d => -m) (fun _ : Fin d => m) := by
  ext ω
  simp only [sourceCube, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def]
  constructor
  · intro h
    constructor
    · intro k
      exact (abs_le.mp (h k)).1
    · intro k
      exact (abs_le.mp (h k)).2
  · intro h k
    exact abs_le.mpr ⟨h.1 k, h.2 k⟩

theorem measurableSet_sourceCube (d : ℕ) (m : ℝ) :
    MeasurableSet (sourceCube d m) := by
  rw [sourceCube_eq_Icc]
  exact measurableSet_Icc

theorem isCompact_sourceCube (d : ℕ) (m : ℝ) :
    IsCompact (sourceCube d m) := by
  rw [sourceCube_eq_Icc]
  exact isCompact_Icc

/-- A Fourier atom with the sign and `2π` normalization used by the source. -/
def continuousFourierAtom {d : ℕ}
    (u : External.UnitTorusPoint d) (ω : Fin d → ℝ) : ℂ :=
  Complex.exp
    (-2 * Real.pi * Complex.I * (∑ k, (ω k : ℂ) * u k))

theorem norm_continuousFourierAtom {d : ℕ}
    (u : External.UnitTorusPoint d) (ω : Fin d → ℝ) :
    ‖continuousFourierAtom u ω‖ = 1 := by
  simp [continuousFourierAtom, Complex.norm_exp, Complex.mul_re]

theorem star_continuousFourierAtom_mul_self {d : ℕ}
    (u : External.UnitTorusPoint d) (ω : Fin d → ℝ) :
    star (continuousFourierAtom u ω) * continuousFourierAtom u ω = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, norm_continuousFourierAtom]
  norm_num

/-- The finite Fourier polynomial occurring in the continuous cube energy. -/
def continuousFourierPolynomial
    {d : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → External.UnitTorusPoint d) (c : ι → ℂ)
    (ω : Fin d → ℝ) : ℂ :=
  ∑ j, c j * continuousFourierAtom (x j) ω

theorem continuous_continuousFourierPolynomial
    {d : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → External.UnitTorusPoint d) (c : ι → ℂ) :
    Continuous (continuousFourierPolynomial x c) := by
  unfold continuousFourierPolynomial continuousFourierAtom
  fun_prop

theorem continuousCubeIntegrand_integrableOn
    {d : ℕ} {ι : Type*} [Fintype ι]
    (m : ℝ) (x : ι → External.UnitTorusPoint d) (c : ι → ℂ) :
    IntegrableOn (fun ω => ‖continuousFourierPolynomial x c ω‖ ^ 2)
      (sourceCube d m) := by
  apply ContinuousOn.integrableOn_compact (isCompact_sourceCube d m)
  exact (continuous_continuousFourierPolynomial x c).norm.pow 2 |>.continuousOn

theorem continuousCubeFourierEnergy_eq_integral
    {d : ℕ} {ι : Type*} [Fintype ι]
    (m : ℝ) (x : ι → External.UnitTorusPoint d) (c : ι → ℂ) :
    External.continuousCubeFourierEnergy m x c =
      ∫ ω in sourceCube d m, ‖continuousFourierPolynomial x c ω‖ ^ 2 := by
  rfl

/-- The signed weighted energy used in the abstract minorant/majorant argument. -/
def weightedContinuousFourierEnergy
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w : (Fin d → ℝ) → ℝ)
    (x : ι → External.UnitTorusPoint d) (c : ι → ℂ) : ℝ :=
  ∫ ω, w ω * ‖continuousFourierPolynomial x c ω‖ ^ 2

/-- Pointwise conditions saying that `w` minorizes the cube indicator. -/
def IsCubeMinorant {d : ℕ} (m : ℝ) (w : (Fin d → ℝ) → ℝ) : Prop :=
  (∀ ω ∈ sourceCube d m, w ω ≤ 1) ∧
  ∀ ω ∉ sourceCube d m, w ω ≤ 0

/-- Pointwise conditions saying that `w` majorizes the cube indicator. -/
def IsCubeMajorant {d : ℕ} (m : ℝ) (w : (Fin d → ℝ) → ℝ) : Prop :=
  (∀ ω ∈ sourceCube d m, 1 ≤ w ω) ∧
  ∀ ω ∉ sourceCube d m, 0 ≤ w ω

/-- A signed minorant gives a lower bound for the unweighted cube energy. -/
theorem weightedContinuousFourierEnergy_le_cube
    {d : ℕ} {ι : Type*} [Fintype ι]
    (m : ℝ) (x : ι → External.UnitTorusPoint d) (c : ι → ℂ)
    (w : (Fin d → ℝ) → ℝ)
    (hw : Integrable
      (fun ω => w ω * ‖continuousFourierPolynomial x c ω‖ ^ 2))
    (hminor : IsCubeMinorant m w) :
    weightedContinuousFourierEnergy w x c ≤
      External.continuousCubeFourierEnergy m x c := by
  rw [weightedContinuousFourierEnergy, continuousCubeFourierEnergy_eq_integral,
    ← integral_indicator (measurableSet_sourceCube d m)]
  apply integral_mono hw
    ((continuousCubeIntegrand_integrableOn m x c).integrable_indicator
      (measurableSet_sourceCube d m))
  intro ω
  by_cases hω : ω ∈ sourceCube d m
  · rw [Set.indicator_of_mem hω]
    exact mul_le_of_le_one_left (sq_nonneg _) (hminor.1 ω hω)
  · rw [Set.indicator_of_notMem hω]
    exact mul_nonpos_of_nonpos_of_nonneg (hminor.2 ω hω) (sq_nonneg _)

/-- A signed majorant gives an upper bound for the unweighted cube energy. -/
theorem cube_le_weightedContinuousFourierEnergy
    {d : ℕ} {ι : Type*} [Fintype ι]
    (m : ℝ) (x : ι → External.UnitTorusPoint d) (c : ι → ℂ)
    (w : (Fin d → ℝ) → ℝ)
    (hw : Integrable
      (fun ω => w ω * ‖continuousFourierPolynomial x c ω‖ ^ 2))
    (hmajor : IsCubeMajorant m w) :
    External.continuousCubeFourierEnergy m x c ≤
      weightedContinuousFourierEnergy w x c := by
  rw [weightedContinuousFourierEnergy, continuousCubeFourierEnergy_eq_integral,
    ← integral_indicator (measurableSet_sourceCube d m)]
  apply integral_mono
    ((continuousCubeIntegrand_integrableOn m x c).integrable_indicator
      (measurableSet_sourceCube d m)) hw
  intro ω
  by_cases hω : ω ∈ sourceCube d m
  · rw [Set.indicator_of_mem hω]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hmajor.1 ω hω) (sq_nonneg _)
  · rw [Set.indicator_of_notMem hω]
    exact mul_nonneg (hmajor.2 ω hω) (sq_nonneg _)

/-- Expansion of a weighted continuous energy into all ordered pair moments. -/
theorem weighted_integral_energy_eq_pair_integrals
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (w : Ω → ℝ) (v : ι → Ω → ℂ)
    (hint : ∀ i j, Integrable
      (fun ω => w ω * (star (v i ω) * v j ω).re) μ) :
    (∫ ω, w ω * ‖∑ i, v i ω‖ ^ 2 ∂μ) =
      ∑ i, ∑ j,
        ∫ ω, w ω * (star (v i ω) * v j ω).re ∂μ := by
  classical
  calc
    (∫ ω, w ω * ‖∑ i, v i ω‖ ^ 2 ∂μ) =
        ∫ ω, ∑ i, ∑ j, w ω * (star (v i ω) * v j ω).re ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => by
            change w ω * ‖∑ i, v i ω‖ ^ 2 =
              ∑ i, ∑ j, w ω * (star (v i ω) * v j ω).re
            rw [norm_sum_sq_real, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    _ = ∑ i, ∑ j,
        ∫ ω, w ω * (star (v i ω) * v j ω).re ∂μ := by
          rw [integral_finsetSum Finset.univ]
          · apply Finset.sum_congr rfl
            intro i _
            rw [integral_finsetSum Finset.univ (fun j _ => hint i j)]
          · intro i _
            exact integrable_finsetSum Finset.univ fun j _ => hint i j

/-- Integral analogue of finite weighted orthogonality.  It is stated for
arbitrary atoms so the analytic Fourier-transform calculation can be supplied
independently of the finite-sum algebra. -/
theorem weighted_integral_energy_eq_sum
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (w : Ω → ℝ) (v : ι → Ω → ℂ) (E : ι → ℝ)
    (hint : ∀ i j, Integrable
      (fun ω => w ω * (star (v i ω) * v j ω).re) μ)
    (hdiag : ∀ i,
      (∫ ω, w ω * (star (v i ω) * v i ω).re ∂μ) = E i)
    (hcross : ∀ i j, i ≠ j →
      (∫ ω, w ω * (star (v i ω) * v j ω).re ∂μ) = 0) :
    (∫ ω, w ω * ‖∑ i, v i ω‖ ^ 2 ∂μ) = ∑ i, E i := by
  classical
  have hp (i j : ι) :
      (∫ ω, w ω * (star (v i ω) * v j ω).re ∂μ) =
        if j = i then E i else 0 := by
    by_cases hji : j = i
    · subst j
      simpa using hdiag i
    · rw [if_neg hji]
      exact hcross i j (Ne.symm hji)
  rw [weighted_integral_energy_eq_pair_integrals μ w v hint]
  simp_rw [hp]
  simp

/-- Minimal moment interface for a continuous Fourier weight.  The weight is
integrable with mass `A`, while all cross moments for distinct nodes vanish.
Quantifying over the two scalar coefficients keeps this real-valued interface
independent of a separate complex-integral API.  Diagonal moments are not an
assumption: they follow from the unit norm of `continuousFourierAtom`. -/
def HasContinuousFourierMoments
    {d : ℕ} {ι : Type*} [Fintype ι]
    (A : ℝ) (w : (Fin d → ℝ) → ℝ)
    (x : ι → External.UnitTorusPoint d) : Prop :=
  Integrable w ∧ (∫ ω, w ω) = A ∧
  ∀ i j a b, i ≠ j →
    Integrable (fun ω =>
      w ω *
        (star (a * continuousFourierAtom (x i) ω) *
          (b * continuousFourierAtom (x j) ω)).re) ∧
    (∫ ω,
      w ω *
        (star (a * continuousFourierAtom (x i) ω) *
          (b * continuousFourierAtom (x j) ω)).re) = 0

/-- A weight diagonalizes the finite Fourier family with diagonal value `A`. -/
def HasContinuousWeightedOrthogonality
    {d : ℕ} {ι : Type*} [Fintype ι]
    (A : ℝ) (w : (Fin d → ℝ) → ℝ)
    (x : ι → External.UnitTorusPoint d) : Prop :=
  ∀ c,
    Integrable (fun ω =>
      w ω * ‖continuousFourierPolynomial x c ω‖ ^ 2) ∧
    weightedContinuousFourierEnergy w x c =
      A * External.coefficientEnergy c

/-- Pairwise Fourier moments imply the full weighted energy identity for every
coefficient family. -/
theorem hasContinuousWeightedOrthogonality_of_moments
    {d : ℕ} {ι : Type*} [Fintype ι]
    (A : ℝ) (w : (Fin d → ℝ) → ℝ)
    (x : ι → External.UnitTorusPoint d)
    (hmom : HasContinuousFourierMoments A w x) :
    HasContinuousWeightedOrthogonality A w x := by
  classical
  intro c
  have hdiag_pointwise (i : ι) (a b : ℂ) (ω : Fin d → ℝ) :
      w ω *
          (star (a * continuousFourierAtom (x i) ω) *
            (b * continuousFourierAtom (x i) ω)).re =
        (star a * b).re * w ω := by
    have hcomplex :
        star (a * continuousFourierAtom (x i) ω) *
            (b * continuousFourierAtom (x i) ω) =
          star a * b := by
      rw [star_mul]
      calc
        (star (continuousFourierAtom (x i) ω) * star a) *
            (b * continuousFourierAtom (x i) ω) =
          (star a * b) *
            (star (continuousFourierAtom (x i) ω) *
              continuousFourierAtom (x i) ω) := by ring
        _ = star a * b := by
          rw [star_continuousFourierAtom_mul_self, mul_one]
    rw [hcomplex]
    ring
  have hint (i j : ι) :
      Integrable (fun ω =>
        w ω *
          (star (c i * continuousFourierAtom (x i) ω) *
            (c j * continuousFourierAtom (x j) ω)).re) := by
    by_cases hij : i = j
    · subst j
      exact (hmom.1.const_mul (star (c i) * c i).re).congr
        (Filter.Eventually.of_forall fun ω =>
          (hdiag_pointwise i (c i) (c i) ω).symm)
    · exact (hmom.2.2 i j (c i) (c j) hij).1
  have hdiag (i : ι) :
      (∫ ω,
        w ω *
          (star (c i * continuousFourierAtom (x i) ω) *
            (c i * continuousFourierAtom (x i) ω)).re) =
        A * ‖c i‖ ^ 2 := by
    calc
      _ = ∫ ω, (star (c i) * c i).re * w ω := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω =>
          hdiag_pointwise i (c i) (c i) ω
      _ = (star (c i) * c i).re * ∫ ω, w ω := by
        rw [integral_const_mul]
      _ = A * ‖c i‖ ^ 2 := by
        rw [hmom.2.1, mul_comm]
        congr 1
        rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
          Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hcross (i j : ι) (hij : i ≠ j) :
      (∫ ω,
        w ω *
          (star (c i * continuousFourierAtom (x i) ω) *
            (c j * continuousFourierAtom (x j) ω)).re) = 0 := by
    exact (hmom.2.2 i j (c i) (c j) hij).2
  have henergy := weighted_integral_energy_eq_sum
    volume w
    (fun i ω => c i * continuousFourierAtom (x i) ω)
    (fun i => A * ‖c i‖ ^ 2) hint hdiag hcross
  constructor
  · have hsum : Integrable (fun ω =>
        ∑ i, ∑ j,
          w ω *
            (star (c i * continuousFourierAtom (x i) ω) *
              (c j * continuousFourierAtom (x j) ω)).re) :=
      integrable_finsetSum Finset.univ fun i _ =>
        integrable_finsetSum Finset.univ fun j _ => hint i j
    apply hsum.congr
    exact Filter.Eventually.of_forall fun ω => by
      change (∑ i, ∑ j,
          w ω *
            (star (c i * continuousFourierAtom (x i) ω) *
              (c j * continuousFourierAtom (x j) ω)).re) =
        w ω * ‖continuousFourierPolynomial x c ω‖ ^ 2
      rw [continuousFourierPolynomial, norm_sum_sq_real, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
  · simpa only [weightedContinuousFourierEnergy, continuousFourierPolynomial,
      External.coefficientEnergy, Finset.mul_sum] using henergy

/-- The exact lower and upper bounds follow from a minorizing and a majorizing
weight with the corresponding diagonal masses. -/
theorem continuousCubeFourier_bounds_of_weighted_orthogonality
    {d : ℕ} {ι : Type*} [Fintype ι]
    (m A B : ℝ) (x : ι → External.UnitTorusPoint d)
    (wLower wUpper : (Fin d → ℝ) → ℝ)
    (hminor : IsCubeMinorant m wLower)
    (hmajor : IsCubeMajorant m wUpper)
    (hlower : HasContinuousWeightedOrthogonality A wLower x)
    (hupper : HasContinuousWeightedOrthogonality B wUpper x) :
    (∀ c, A * External.coefficientEnergy c ≤
      External.continuousCubeFourierEnergy m x c) ∧
    ∀ c, External.continuousCubeFourierEnergy m x c ≤
      B * External.coefficientEnergy c := by
  constructor
  · intro c
    rw [← (hlower c).2]
    exact weightedContinuousFourierEnergy_le_cube m x c wLower (hlower c).1 hminor
  · intro c
    rw [← (hupper c).2]
    exact cube_le_weightedContinuousFourierEnergy m x c wUpper (hupper c).1 hmajor

/-- The precise extremal-function input missing from the current library.
The two mass inequalities allow the sharper intermediate constants in Barton's
construction to imply the slightly weaker exponential constants used by Li. -/
def HasBartonCubeCertificates
    {d : ℕ} {ι : Type*} [Fintype ι]
    (m β : ℝ) (x : ι → External.UnitTorusPoint d) : Prop :=
  ∃ (wLower wUpper : (Fin d → ℝ) → ℝ) (lowerMass upperMass : ℝ),
    IsCubeMinorant m wLower ∧
    IsCubeMajorant m wUpper ∧
    (2 - Real.exp (1 / (2 * β))) * (2 * m) ^ d ≤ lowerMass ∧
    upperMass ≤ Real.exp (1 / (2 * β)) * (2 * m) ^ d ∧
    HasContinuousFourierMoments lowerMass wLower x ∧
    HasContinuousFourierMoments upperMass wUpper x

/-- Once the Barton extremal functions and their Fourier support are available,
the continuous half of Li's estimate follows without further analytic
assumptions. -/
theorem continuousCubeFourier_frame_of_barton_certificates
    {d : ℕ} {ι : Type*} [Fintype ι]
    (m β : ℝ) (x : ι → External.UnitTorusPoint d)
    (hcert : HasBartonCubeCertificates m β x) :
    (∀ c,
      (2 - Real.exp (1 / (2 * β))) * (2 * m) ^ d *
          External.coefficientEnergy c ≤
        External.continuousCubeFourierEnergy m x c) ∧
    ∀ c,
      External.continuousCubeFourierEnergy m x c ≤
        Real.exp (1 / (2 * β)) * (2 * m) ^ d *
          External.coefficientEnergy c := by
  rcases hcert with
    ⟨wLower, wUpper, lowerMass, upperMass, hminor, hmajor,
      hlowerMass, hupperMass, hlower, hupper⟩
  have hbounds := continuousCubeFourier_bounds_of_weighted_orthogonality
    m lowerMass upperMass x wLower wUpper hminor hmajor
    (hasContinuousWeightedOrthogonality_of_moments _ _ _ hlower)
    (hasContinuousWeightedOrthogonality_of_moments _ _ _ hupper)
  have henergy_nonneg (c : ι → ℂ) : 0 ≤ External.coefficientEnergy c := by
    unfold External.coefficientEnergy
    positivity
  constructor
  · intro c
    exact (mul_le_mul_of_nonneg_right hlowerMass (henergy_nonneg c)).trans
      (hbounds.1 c)
  · intro c
    exact (hbounds.2 c).trans
      (mul_le_mul_of_nonneg_right hupperMass (henergy_nonneg c))

/-- Equivalent error estimate around the cube volume that is sufficient for
both of the exact source bounds. -/
theorem continuousCubeFourier_frame_of_relative_error
    {d : ℕ} {ι : Type*} [Fintype ι]
    (m β : ℝ) (x : ι → External.UnitTorusPoint d)
    (hm : 0 ≤ m)
    (herror : ∀ c,
      |External.continuousCubeFourierEnergy m x c -
          (2 * m) ^ d * External.coefficientEnergy c| ≤
        (Real.exp (1 / (2 * β)) - 1) * (2 * m) ^ d *
          External.coefficientEnergy c) :
    (∀ c,
      (2 - Real.exp (1 / (2 * β))) * (2 * m) ^ d *
          External.coefficientEnergy c ≤
        External.continuousCubeFourierEnergy m x c) ∧
    ∀ c,
      External.continuousCubeFourierEnergy m x c ≤
        Real.exp (1 / (2 * β)) * (2 * m) ^ d *
          External.coefficientEnergy c := by
  have hbase_nonneg (c : ι → ℂ) :
      0 ≤ (2 * m) ^ d * External.coefficientEnergy c := by
    apply mul_nonneg
    · positivity
    · unfold External.coefficientEnergy
      positivity
  constructor <;> intro c
  · have h := (abs_le.mp (herror c)).1
    nlinarith [hbase_nonneg c]
  · have h := (abs_le.mp (herror c)).2
    nlinarith [hbase_nonneg c]

end

end SeparatedCubeFourierContinuous
end LeanNumDetect
