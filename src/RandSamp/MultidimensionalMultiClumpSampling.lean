import RandSamp.MultidimensionalMultiClumpModel
import RandSamp.LeverageSampling
import RandSamp.SamplingRate

/-! Relative sampling of actual subsets of a frequency cube. All probability
and singular-value transport is proved from the general finite-population
matrix Chernoff theorem. The one-dimensional model is an exact reindexing. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- The normalized full Fourier matrix on `{0,...,M}^d`, with its actual cube labels. -/
def cubeFullVandermonde {d n : ℕ} (M : ℕ) (Y : Fin n → Fin d → ℝ) :
    Matrix (CubeFrequency d M) (Fin n) ℂ :=
  fun k j => (Real.sqrt (((M + 1) ^ d : ℕ) : ℝ) : ℂ)⁻¹ * cubeFourierRow Y k j

/-- Its squared action is the normalized full cube Gram energy. -/
theorem norm_cubeFullVandermonde_sq {d n : ℕ} (M : ℕ) (Y : Fin n → Fin d → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) :
    ‖(cubeFullVandermonde M Y).toEuclideanLin z‖ ^ 2 = FiniteMatrixSampling.quadratic (cubeFullGram M Y) z := by
  rw [EuclideanSpace.norm_sq_eq, cubeFullGram, quadratic_cubeFourier_mean]
  change (∑ k : CubeFrequency d M, ‖∑ j,
    (Real.sqrt (((M + 1)^d : ℕ) : ℝ) : ℂ)⁻¹ * cubeFourierRow Y k j * ofLp z j‖^2) = _
  simp_rw [mul_assoc, ← Finset.mul_sum, norm_mul, mul_pow, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    inv_pow, Real.sq_sqrt (Nat.cast_nonneg ((M + 1)^d))]
  rw [← Finset.mul_sum]
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, cubeFourierRowEnergy]

/-- Relative Gram order for one fixed source tuple and a uniformly sampled cube subset. -/
def CubeRelativeGramEvent {d M n m : ℕ} (Y : Fin n → Fin d → ℝ) (ρ : ℝ)
    (Ω : FiniteSample (CubeFrequency d M) m) : Prop :=
  ∀ z : EuclideanSpace ℂ (Fin n),
    (1 - ρ) * FiniteMatrixSampling.quadratic (cubeFullGram M Y) z ≤
      FiniteMatrixSampling.quadratic (finiteSampleMean (cubeFourierPopulation Y) Ω) z ∧
    FiniteMatrixSampling.quadratic (finiteSampleMean (cubeFourierPopulation Y) Ω) z ≤
      (1 + ρ) * FiniteMatrixSampling.quadratic (cubeFullGram M Y) z

/-- Every ordered singular value is compared with the corresponding full-cube value. -/
def CubeAllSingularValueEvent {d M n m : ℕ} (Y : Fin n → Fin d → ℝ) (ρ : ℝ)
    (Ω : FiniteSample (CubeFrequency d M) m) : Prop :=
  ∀ j : Fin n,
    Real.sqrt (1 - ρ) * matrixSingularValue (cubeFullVandermonde M Y) j.val ≤
      matrixSingularValue (cubeSampledVandermonde m Y Ω.val) j.val ∧
    matrixSingularValue (cubeSampledVandermonde m Y Ω.val) j.val ≤
      Real.sqrt (1 + ρ) * matrixSingularValue (cubeFullVandermonde M Y) j.val

theorem cubeAllSingularValueEvent_of_relativeGramEvent {d M n m : ℕ}
    (Y : Fin n → Fin d → ℝ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (Ω : FiniteSample (CubeFrequency d M) m) (hrelative : CubeRelativeGramEvent Y ρ Ω) :
    CubeAllSingularValueEvent Y ρ Ω := by
  let A := (cubeFullVandermonde M Y).toEuclideanLin
  let B := (cubeSampledVandermonde m Y Ω.val).toEuclideanLin
  have hlower (z : EuclideanSpace ℂ (Fin n)) : Real.sqrt (1 - ρ) * ‖A z‖ ≤ ‖B z‖ := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).1
    rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hρ1)]
    change (1 - ρ) * ‖(cubeFullVandermonde M Y).toEuclideanLin z‖^2 ≤
      ‖(cubeSampledVandermonde m Y Ω.val).toEuclideanLin z‖^2
    rw [norm_cubeFullVandermonde_sq, ← quadratic_cubeFourier_sampleMean]
    exact (hrelative z).1
  have hupper (z : EuclideanSpace ℂ (Fin n)) : ‖B z‖ ≤ Real.sqrt (1 + ρ) * ‖A z‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
    rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 + ρ)]
    change ‖(cubeSampledVandermonde m Y Ω.val).toEuclideanLin z‖^2 ≤
      (1 + ρ) * ‖(cubeFullVandermonde M Y).toEuclideanLin z‖^2
    rw [norm_cubeFullVandermonde_sq, ← quadratic_cubeFourier_sampleMean]
    exact (hrelative z).2
  intro j
  exact singularValues_relative_bounds A B (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hlower hupper j.val

/-- Cube sampling with a leverage bound relative to its actual full Gram.
The rows are reindexed only within the proof; outcomes remain actual cube subsets. -/
theorem cubeFixedSupport_relativeGram_of_leverage {d M n m : ℕ}
    (hn : 0 < n) (hm : 1 ≤ m) (hmN : m ≤ (M + 1)^d) (Y : Fin n → Fin d → ℝ)
    {R ρ δ : ℝ} (hR : 0 < R) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hδ0 : 0 < δ) (_hδ1 : δ < 1) (hG : (cubeFullGram M Y).PosDef)
    (hleverage : ∀ (k : CubeFrequency d M) (z : EuclideanSpace ℂ (Fin n)),
      cubeFourierRowEnergy Y k (ofLp z) ≤ R * FiniteMatrixSampling.quadratic (cubeFullGram M Y) z)
    (hsample : 3 * R / ρ^2 * Real.log (2 * (n : ℝ) / δ) ≤ (m : ℝ)) :
    1 - δ ≤ probability (fun Ω : FiniteSample (CubeFrequency d M) m =>
      CubeRelativeGramEvent Y ρ Ω) := by
  let e := (Fintype.equivFin (CubeFrequency d M)).symm
  have hcard : 0 < Fintype.card (CubeFrequency d M) := by
    rw [card_cubeFrequency]
    exact pow_pos (Nat.succ_pos M) d
  have hmcard : m ≤ Fintype.card (CubeFrequency d M) := by simpa using hmN
  have hMean : mean (fun k => cubeFourierPopulation Y (e k)) = cubeFullGram M Y := by
    rw [← finiteMean_fin, finiteMean_comp_equiv e, cubeFullGram]
  have hSample (Ω : Sample (Fintype.card (CubeFrequency d M)) m) :
      sampleMean (fun k => cubeFourierPopulation Y (e k)) Ω =
        finiteSampleMean (cubeFourierPopulation Y) (finiteSampleEquiv e m Ω) :=
    finiteSampleMean_comp_equiv e (cubeFourierPopulation Y) Ω
  have hprob := sampleMean_relative_bounds_probability hcard hn hm hmcard
    (fun k => cubeFourierPopulation Y (e k)) hR hρ0 hρ1
    (fun k => cubeFourierRowGram_posSemidef Y (e k))
    (by simpa only [hMean] using hG)
    (fun k z => by
      rw [hMean, cubeFourierPopulation, quadratic_cubeFourierRowGram]
      exact hleverage (e k) z)
  have htail := chernoff_failure_bound_of_sample_size (Nat.cast_nonneg m)
    (by exact_mod_cast hn : (0 : ℝ) < n) hR (a := 1) (b := 1)
    (by norm_num) (le_refl 1) hρ0 hδ0
    (by simpa only [one_mul] using hsample)
  simp only [mul_one] at htail
  have h := (sub_le_sub_left htail 1).trans hprob
  rw [← probability_comp_equiv (finiteSampleEquiv e m) (CubeRelativeGramEvent Y ρ)]
  simpa only [CubeRelativeGramEvent, hMean, hSample] using h

theorem cubeFixedSupport_relativeGram_allSingularValues_of_leverage {d M n m : ℕ}
    (hn : 0 < n) (hm : 1 ≤ m) (hmN : m ≤ (M + 1)^d) (Y : Fin n → Fin d → ℝ)
    {R ρ δ : ℝ} (hR : 0 < R) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hG : (cubeFullGram M Y).PosDef)
    (hleverage : ∀ (k : CubeFrequency d M) (z : EuclideanSpace ℂ (Fin n)),
      cubeFourierRowEnergy Y k (ofLp z) ≤ R * FiniteMatrixSampling.quadratic (cubeFullGram M Y) z)
    (hsample : 3 * R / ρ^2 * Real.log (2 * (n : ℝ) / δ) ≤ (m : ℝ)) :
    1 - δ ≤ probability (fun Ω : FiniteSample (CubeFrequency d M) m =>
      CubeRelativeGramEvent Y ρ Ω ∧ CubeAllSingularValueEvent Y ρ Ω) := by
  apply (cubeFixedSupport_relativeGram_of_leverage hn hm hmN Y hR hρ0 hρ1 hδ0 hδ1
    hG hleverage hsample).trans
  apply probability_mono
  intro Ω hΩ
  exact ⟨hΩ, cubeAllSingularValueEvent_of_relativeGramEvent Y hρ0.le hρ1.le Ω hΩ⟩

/-- Leverage loss from summing orthogonal clumps after coordinate iteration. -/
def multidimensionalMultiClumpLeverageConstant (d : ℕ) : ℝ := 1024 * 512 ^ (d - 1)

/-- Explicit dimension-dependent sampling constant, exactly `3072` at dimension one. -/
def multidimensionalMultiClumpSamplingConstant (d : ℕ) : ℝ := 3072 * 512 ^ (d - 1)

@[simp] theorem multidimensionalMultiClumpSamplingConstant_one :
    multidimensionalMultiClumpSamplingConstant 1 = 3072 := by
  norm_num [multidimensionalMultiClumpSamplingConstant]

theorem multidimensionalMultiClumpSamplingConstant_pos (d : ℕ) :
    0 < multidimensionalMultiClumpSamplingConstant d := by
  unfold multidimensionalMultiClumpSamplingConstant
  positivity

/-- The shared success event includes Gram order, every singular value and
all comparable internal spacings simultaneously. The upper exponent is the
tensor-box cancellation exponent; the lower exponent is always `nstar-1`. -/
def MultidimensionalMultiClumpSuccess {d M n A m : ℕ}
    (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A) (nstar : ℕ)
    (lower upper : ℝ → ℝ) (ρ : ℝ) (Ω : FiniteSample (CubeFrequency d M) m) : Prop :=
  CubeRelativeGramEvent Y ρ Ω ∧ CubeAllSingularValueEvent Y ρ Ω ∧
    ∀ K : ℝ, 1 ≤ K → ∀ Δ : ℝ, 0 < Δ → ComparableMultidimensionalClumpSpacing P Y Δ K →
      lower K * Real.sqrt (1 - ρ) * ((M : ℝ) * Δ) ^ (nstar - 1) ≤
        matrixSingularValue (cubeSampledVandermonde m Y Ω.val) (n - 1) ∧
      matrixSingularValue (cubeSampledVandermonde m Y Ω.val) (n - 1) ≤
        upper K * Real.sqrt (1 + ρ) * ((M : ℝ) * Δ) ^ multidimensionalClumpUpperExponent d nstar

/-- The full fixed-node conclusion, with constants chosen before bandwidth,
partition, source coordinates and probability parameters. -/
def MultidimensionalMultiClumpSamplingConclusion (C : ℝ) (d n nstar : ℕ)
    (c0 C0 : ℝ) : Prop :=
  ∃ lower upper : ℝ → ℝ,
    (∀ K : ℝ, 1 ≤ K → 0 < lower K ∧ 0 < upper K) ∧
    ∀ M : ℕ, C0 ≤ (M : ℝ) → ∀ A : ℕ, ∀ P : ClumpPartition n A,
      ∀ Y : Fin n → Fin d → ℝ,
        HasMaxClumpSize P nstar → MultidimensionalMultiClumpGeometry M c0 C0 Y P →
        ∀ (m : ℕ) (ρ δ : ℝ), 1 ≤ m → m ≤ (M + 1)^d →
          0 < ρ → ρ < 1 → 0 < δ → δ < 1 →
          C / ρ^2 * (P.sizePowerSum d : ℝ) * Real.log (2 * (n : ℝ) / δ) ≤ (m : ℝ) →
          1 - δ ≤ probability (fun Ω : FiniteSample (CubeFrequency d M) m =>
            MultidimensionalMultiClumpSuccess Y P nstar lower upper ρ Ω)

/-- Positive definiteness, row leverage and full-matrix spectral bounds suffice
for the sampling transfer. The geometric proof discharges all three inputs. -/
def MultidimensionalMultiClumpDeterministicControl (d n nstar : ℕ) (c0 C0 : ℝ) : Prop :=
  ∃ lower upper : ℝ → ℝ,
    (∀ K : ℝ, 1 ≤ K → 0 < lower K ∧ 0 < upper K) ∧
    ∀ M : ℕ, C0 ≤ (M : ℝ) → ∀ A : ℕ, ∀ P : ClumpPartition n A,
      ∀ Y : Fin n → Fin d → ℝ,
        HasMaxClumpSize P nstar → MultidimensionalMultiClumpGeometry M c0 C0 Y P →
        (cubeFullGram M Y).PosDef ∧
        (∀ (k : CubeFrequency d M) (z : EuclideanSpace ℂ (Fin n)),
          cubeFourierRowEnergy Y k (ofLp z) ≤
            (multidimensionalMultiClumpLeverageConstant d * (P.sizePowerSum d : ℝ)) *
              FiniteMatrixSampling.quadratic (cubeFullGram M Y) z) ∧
        (∀ K : ℝ, 1 ≤ K → ∀ Δ : ℝ, 0 < Δ → ComparableMultidimensionalClumpSpacing P Y Δ K →
          lower K * ((M : ℝ) * Δ) ^ (nstar - 1) ≤
            matrixSingularValue (cubeFullVandermonde M Y) (n - 1) ∧
          matrixSingularValue (cubeFullVandermonde M Y) (n - 1) ≤
            upper K * ((M : ℝ) * Δ) ^ multidimensionalClumpUpperExponent d nstar)

/-- Exact high-dimensional statement with the explicit dimension-dependent
sampling constant, followed by the same geometry quantifiers as in dimension one. -/
def MultidimensionalMultiClumpSamplingStatement : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ n nstar : ℕ, 2 ≤ nstar → nstar ≤ n →
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      MultidimensionalMultiClumpSamplingConclusion
        (multidimensionalMultiClumpSamplingConstant d) d n nstar c0 C0

/-- The extra spectral conclusions use the very same relative Gram event,
without a union bound over spacings or coefficient vectors. -/
theorem multidimensionalMultiClumpSuccess_iff_relativeGram {d M n A m nstar : ℕ}
    (hn : 0 < n) (P : ClumpPartition n A) (Y : Fin n → Fin d → ℝ)
    (lower upper : ℝ → ℝ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hfull : ∀ K : ℝ, 1 ≤ K → ∀ Δ : ℝ, 0 < Δ → ComparableMultidimensionalClumpSpacing P Y Δ K →
      lower K * ((M : ℝ) * Δ) ^ (nstar - 1) ≤
        matrixSingularValue (cubeFullVandermonde M Y) (n - 1) ∧
      matrixSingularValue (cubeFullVandermonde M Y) (n - 1) ≤
        upper K * ((M : ℝ) * Δ) ^ multidimensionalClumpUpperExponent d nstar)
    (Ω : FiniteSample (CubeFrequency d M) m) :
    MultidimensionalMultiClumpSuccess Y P nstar lower upper ρ Ω ↔ CubeRelativeGramEvent Y ρ Ω := by
  constructor
  · exact fun h => h.1
  · intro hrelative
    have hall := cubeAllSingularValueEvent_of_relativeGramEvent Y hρ0 hρ1 Ω hrelative
    refine ⟨hrelative, hall, ?_⟩
    intro K hK Δ hΔ hspacing
    have hf := hfull K hK Δ hΔ hspacing
    have hs := hall (⟨n - 1, by omega⟩ : Fin n)
    constructor
    · calc
        _ = Real.sqrt (1 - ρ) * (lower K * ((M : ℝ) * Δ) ^ (nstar - 1)) := by ring
        _ ≤ Real.sqrt (1 - ρ) * matrixSingularValue (cubeFullVandermonde M Y) (n - 1) :=
          mul_le_mul_of_nonneg_left hf.1 (Real.sqrt_nonneg _)
        _ ≤ _ := hs.1
    · calc
        _ ≤ Real.sqrt (1 + ρ) * matrixSingularValue (cubeFullVandermonde M Y) (n - 1) := hs.2
        _ ≤ Real.sqrt (1 + ρ) *
            (upper K * ((M : ℝ) * Δ) ^ multidimensionalClumpUpperExponent d nstar) :=
          mul_le_mul_of_nonneg_left hf.2 (Real.sqrt_nonneg _)
        _ = _ := by ring

/-- Complete probability transfer from the deterministic geometry estimates. -/
theorem multidimensionalMultiClump_sampling_of_deterministicControl {d n nstar : ℕ}
    (hd : 1 ≤ d) (hn : 0 < n) {c0 C0 : ℝ}
    (hcontrol : MultidimensionalMultiClumpDeterministicControl d n nstar c0 C0) :
    MultidimensionalMultiClumpSamplingConclusion
      (multidimensionalMultiClumpSamplingConstant d) d n nstar c0 C0 := by
  obtain ⟨lower, upper, hpos, hdet⟩ := hcontrol
  refine ⟨lower, upper, hpos, ?_⟩
  intro M hM A P Y hmax hgeom m ρ δ hm hmN hρ0 hρ1 hδ0 hδ1 hsample
  obtain ⟨hG, hleverage, hfull⟩ := hdet M hM A P Y hmax hgeom
  have hS : (0 : ℝ) < P.sizePowerSum d := by
    exact_mod_cast (lt_of_lt_of_le hn (P.n_le_sizePowerSum hd))
  have hR : 0 < multidimensionalMultiClumpLeverageConstant d * (P.sizePowerSum d : ℝ) := by
    unfold multidimensionalMultiClumpLeverageConstant
    positivity
  have hrate : 3 * (multidimensionalMultiClumpLeverageConstant d * (P.sizePowerSum d : ℝ)) /
      ρ^2 * Real.log (2 * (n : ℝ) / δ) ≤ (m : ℝ) := by
    convert hsample using 1
    unfold multidimensionalMultiClumpLeverageConstant multidimensionalMultiClumpSamplingConstant
    ring
  have hp := cubeFixedSupport_relativeGram_allSingularValues_of_leverage hn hm hmN Y
    hR hρ0 hρ1 hδ0 hδ1 hG hleverage hrate
  apply hp.trans
  apply probability_mono
  intro Ω hΩ
  exact (multidimensionalMultiClumpSuccess_iff_relativeGram hn P Y lower upper
    hρ0.le hρ1.le hfull Ω).2 hΩ.1

/-- Closing the geometric deterministic estimates proves the full dimensional
statement without adding any assumption to the final sampling theorem. -/
theorem multidimensionalMultiClump_statement_of_deterministicControl
    (hdet : ∀ d : ℕ, 1 ≤ d → ∀ n nstar : ℕ, 2 ≤ nstar → nstar ≤ n →
      ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
        MultidimensionalMultiClumpDeterministicControl d n nstar c0 C0) :
    MultidimensionalMultiClumpSamplingStatement := by
  intro d hd n nstar hstar hsize
  obtain ⟨c0, C0, hc0, hc1, hC0, hcontrol⟩ := hdet d hd n nstar hstar hsize
  exact ⟨c0, C0, hc0, hc1, hC0,
    multidimensionalMultiClump_sampling_of_deterministicControl hd (by omega) hcontrol⟩

/-- Exact reindexing of the full matrix in dimension one. -/
@[simp] theorem cubeFullVandermonde_one_reindex {n : ℕ} (M : ℕ) (Y : Fin n → ℝ) :
    cubeFullVandermonde M (fun j (_ : Fin 1) => Y j) =
      Matrix.reindex (Equiv.funUnique (Fin 1) (Fin (M + 1))).symm (Equiv.refl (Fin n))
        (fullVandermonde M Y) := by
  ext k j
  simp [cubeFullVandermonde, fullVandermonde, Matrix.reindex_apply,
    Matrix.submatrix, Equiv.funUnique]

@[simp] theorem cubeFourierPopulation_one {M n : ℕ} (Y : Fin n → ℝ)
    (k : CubeFrequency 1 M) :
    cubeFourierPopulation (fun j (_ : Fin 1) => Y j) k = fourierPopulation Y (k 0) := by
  ext i j
  simp [cubeFourierPopulation, fourierPopulation, cubeFourierRowGram, fourierRowGram]

@[simp] theorem cubeFullGram_one {n : ℕ} (M : ℕ) (Y : Fin n → ℝ) :
    cubeFullGram M (fun j (_ : Fin 1) => Y j) = fullGram M Y := by
  rw [cubeFullGram, fullGram, ← finiteMean_fin]
  have h := finiteMean_comp_equiv (Equiv.funUnique (Fin 1) (Fin (M + 1)))
    (fourierPopulation Y)
  have hfun : cubeFourierPopulation (fun j (_ : Fin 1) => Y j) =
      (fun k => fourierPopulation Y ((Equiv.funUnique (Fin 1) (Fin (M + 1))) k)) := by
    funext k
    exact cubeFourierPopulation_one Y k
  rw [hfun]
  exact h

/-- Corresponding full matrices have exactly the same ordered singular values. -/
@[simp] theorem cubeFullVandermonde_one_singularValue {n : ℕ} (M : ℕ) (Y : Fin n → ℝ)
    (i : ℕ) :
    matrixSingularValue (cubeFullVandermonde M (fun j (_ : Fin 1) => Y j)) i =
      matrixSingularValue (fullVandermonde M Y) i := by
  apply congrArg (fun values : ℕ →₀ ℝ => values i)
  apply singularValues_eq_of_norm_eq
  intro z
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [norm_cubeFullVandermonde_sq, cubeFullGram_one, fullVandermonde_energy]

/-- Corresponding sampled subsets have the same empirical Gram matrix. -/
theorem finiteSampleMean_cubeFourier_one {M n m : ℕ} (Y : Fin n → ℝ)
    (Ω : Sample (M + 1) m) :
    finiteSampleMean (cubeFourierPopulation (fun j (_ : Fin 1) => Y j))
      (finiteSampleEquiv (Equiv.funUnique (Fin 1) (Fin (M + 1))).symm m Ω) =
        sampleMean (fourierPopulation Y) Ω := by
  let e := Equiv.funUnique (Fin 1) (Fin (M + 1))
  have hcancel : finiteSampleEquiv e m (finiteSampleEquiv e.symm m Ω) = Ω := by
    apply Subtype.ext
    simp [finiteSampleEquiv_val, Finset.map_map]
  have h := finiteSampleMean_comp_equiv e (fourierPopulation Y)
    (finiteSampleEquiv e.symm m Ω)
  rw [hcancel, finiteSampleMean_fin] at h
  have hfun : cubeFourierPopulation (fun j (_ : Fin 1) => Y j) =
      (fun k => fourierPopulation Y (e k)) := by
    funext k
    exact cubeFourierPopulation_one Y k
  rw [hfun]
  exact h

@[simp] theorem cubeRelativeGramEvent_one {M n m : ℕ} (Y : Fin n → ℝ) (ρ : ℝ)
    (Ω : Sample (M + 1) m) :
    CubeRelativeGramEvent (fun j (_ : Fin 1) => Y j) ρ
      (finiteSampleEquiv (Equiv.funUnique (Fin 1) (Fin (M + 1))).symm m Ω) ↔
        RelativeGramEvent Y ρ Ω := by
  simp only [CubeRelativeGramEvent, RelativeGramEvent, cubeFullGram_one,
    finiteSampleMean_cubeFourier_one]

@[simp] theorem cubeAllSingularValueEvent_one {M n m : ℕ} (Y : Fin n → ℝ) (ρ : ℝ)
    (Ω : Sample (M + 1) m) :
    CubeAllSingularValueEvent (fun j (_ : Fin 1) => Y j) ρ
      (finiteSampleEquiv (Equiv.funUnique (Fin 1) (Fin (M + 1))).symm m Ω) ↔
        AllSingularValueEvent Y ρ Ω := by
  simp only [CubeAllSingularValueEvent, AllSingularValueEvent,
    cubeFullVandermonde_one_singularValue, cubeSampledVandermonde_one_singularValue]

/-- Counting probabilities agree exactly under the dimension-one frequency reindexing. -/
theorem cube_relativeGram_probability_one {M n m : ℕ} (Y : Fin n → ℝ) (ρ : ℝ) :
    probability (fun Ω : FiniteSample (CubeFrequency 1 M) m =>
      CubeRelativeGramEvent (fun j (_ : Fin 1) => Y j) ρ Ω) =
        probability (fun Ω : Sample (M + 1) m => RelativeGramEvent Y ρ Ω) := by
  rw [← probability_comp_equiv
    (finiteSampleEquiv (Equiv.funUnique (Fin 1) (Fin (M + 1))).symm m)
    (CubeRelativeGramEvent (fun j (_ : Fin 1) => Y j) ρ)]
  simp only [cubeRelativeGramEvent_one]

end
end LeanNumDetect.RandSamp
