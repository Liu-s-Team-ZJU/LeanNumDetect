import General.Fourier.FineCubeFrame
import External.TranslatedCubeFourier
import NumDetect.SegmentedVandermonde

/-!
Parity-free algebraic reduction for the discrete cube estimate.

For a one-sided cutoff `K`, the centered sampling set can be represented by the
affine lattice block

`(-K / 2 + ℤ)^d ∩ [-K / 2, K / 2]^d`.

It has the parametrization `α ↦ α - K / 2`, with
`α ∈ {0, ..., K}^d`, for every `K`; no parity split is needed.  Multiplication
of each coefficient by the corresponding center phase is unitary and changes
the shifted-coset Fourier energy exactly into the one-sided cube energy.

The literature input is the translated real-cube estimate registered as
`External.translatedCubeFourier_lowerFrame`.  The results below prove the
normalization, separation scaling, energy identity, and the exact
`HasFineCubeFrame` interface used by the segmented Vandermonde theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect
namespace BartonCubeFrame

noncomputable section

/-- An integer belongs to the translated interval centered at `K / 2` with
radius `(K + 1) / 2` exactly when it is one of `0, ..., K`. -/
theorem integer_mem_translatedInterval_iff (K : ℕ) (z : ℤ) :
    |(z : ℝ) - (K : ℝ) / 2| ≤ ((K + 1 : ℕ) : ℝ) / 2 ↔
      0 ≤ z ∧ z ≤ K := by
  rw [abs_le]
  constructor
  · rintro ⟨hlower, hupper⟩
    have hzLower : -(1 : ℝ) / 2 ≤ (z : ℝ) := by
      push_cast at hlower
      linarith
    have hzUpper : (z : ℝ) ≤ (K : ℝ) + 1 / 2 := by
      push_cast at hupper
      linarith
    constructor
    · by_contra hz
      have hzInt : z ≤ -1 := by omega
      have hzReal : (z : ℝ) ≤ -1 := by exact_mod_cast hzInt
      linarith
    · by_contra hz
      have hzInt : (K : ℤ) + 1 ≤ z := by omega
      have hzReal : (K : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hzInt
      linarith
  · rintro ⟨hlower, hupper⟩
    have hlowerReal : 0 ≤ (z : ℝ) := by exact_mod_cast hlower
    have hupperReal : (z : ℝ) ≤ (K : ℝ) := by exact_mod_cast hupper
    constructor <;> push_cast <;> linarith

/-- The integer points of the translated `d`-cube centered at `K / 2` with
radius `(K + 1) / 2` are exactly `{0, ..., K}^d`. -/
theorem integerPoint_mem_translatedCube_iff
    {d : ℕ} (K : ℕ) (ω : Fin d → ℤ) :
    (∀ k,
      |(ω k : ℝ) - (K : ℝ) / 2| ≤ ((K + 1 : ℕ) : ℝ) / 2) ↔
      ∀ k, 0 ≤ ω k ∧ ω k ≤ K := by
  constructor <;> intro h k
  · exact (integer_mem_translatedInterval_iff K (ω k)).mp (h k)
  · exact (integer_mem_translatedInterval_iff K (ω k)).mpr (h k)

/-- Convert angular representatives in `(-π, π]` to Li's representatives in
`[-1/2, 1/2)`.  The minus sign matches Li's Fourier phase convention. -/
def normalizedAngularPoint {d : ℕ}
    (x : FineCubeFrame.AngularPoint d) : External.UnitTorusPoint d :=
  fun k => -x k / (2 * Real.pi)

theorem normalizedAngularPoint_mem_halfOpenCube
    {d : ℕ} {x : FineCubeFrame.AngularPoint d}
    (hx : FineCubeFrame.InAngularCube x) :
    External.InUnitHalfOpenCube (normalizedAngularPoint x) := by
  intro k
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    nlinarith [Real.pi_pos, (hx k).2]
  · apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    nlinarith [Real.pi_pos, (hx k).1]

theorem normalizedAngularPoint_coordinateDistance
    {u v : ℝ}
    (hu : -Real.pi < u ∧ u ≤ Real.pi)
    (hv : -Real.pi < v ∧ v ≤ Real.pi) :
    External.unitPeriodicCoordinateDistance
        (-u / (2 * Real.pi)) (-v / (2 * Real.pi)) =
      FineCubeFrame.angularPeriodicCoordinateDistance u v /
        (2 * Real.pi) := by
  unfold External.unitPeriodicCoordinateDistance
    FineCubeFrame.angularPeriodicCoordinateDistance
  have hp : 0 < 2 * Real.pi := by positivity
  have habs : |u - v| ≤ 2 * Real.pi := by
    rw [abs_le]
    constructor <;> linarith
  rw [show -u / (2 * Real.pi) - -v / (2 * Real.pi) =
      -(u - v) / (2 * Real.pi) by ring,
    abs_div, abs_neg, abs_of_pos hp]
  rw [show 1 - |u - v| / (2 * Real.pi) =
      (2 * Real.pi - |u - v|) / (2 * Real.pi) by field_simp]
  rw [min_div_div_right hp.le]

theorem normalizedAngularPoint_lInfDistance
    {d : ℕ} {u v : FineCubeFrame.AngularPoint d}
    (hu : FineCubeFrame.InAngularCube u)
    (hv : FineCubeFrame.InAngularCube v) :
    External.unitPeriodicLInfDistance
        (normalizedAngularPoint u) (normalizedAngularPoint v) =
      FineCubeFrame.angularPeriodicLInfDistance u v /
        (2 * Real.pi) := by
  unfold External.unitPeriodicLInfDistance
    FineCubeFrame.angularPeriodicLInfDistance normalizedAngularPoint
  simp_rw [normalizedAngularPoint_coordinateDistance (hu _) (hv _)]
  rw [show (fun k => FineCubeFrame.angularPeriodicCoordinateDistance
      (u k) (v k) / (2 * Real.pi)) =
      (2 * Real.pi)⁻¹ •
        (fun k => FineCubeFrame.angularPeriodicCoordinateDistance
          (u k) (v k)) by
      funext k
      simp [div_eq_inv_mul]]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity))]
  field_simp

/-- Li's translated-cube energy becomes the one-sided angular cube energy
after normalization of the nodes. -/
theorem translatedCubeFourierEnergy_normalizedAngularPoint
    {d K : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → FineCubeFrame.AngularPoint d) (c : ι → ℂ) :
    External.translatedCubeFourierEnergy (K + 1)
        (fun j => normalizedAngularPoint (x j)) c =
      FineCubeFrame.fineCubeFourierEnergy K x c := by
  classical
  unfold External.translatedCubeFourierEnergy
    FineCubeFrame.fineCubeFourierEnergy
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply congrArg Complex.exp
  have hsum :
      (∑ k,
          (((ω k : Fin (K + 1)) : ℕ) : ℂ) *
            normalizedAngularPoint (x j) k) =
        -(∑ k, (((ω k : Fin (K + 1)) : ℕ) : ℂ) * x j k) /
          (2 * (Real.pi : ℂ)) := by
    calc
      _ = ∑ k,
          -((((ω k : Fin (K + 1)) : ℕ) : ℂ) * x j k) /
            (2 * (Real.pi : ℂ)) := by
          apply Finset.sum_congr rfl
          intro k _
          unfold normalizedAngularPoint
          push_cast
          field_simp [Real.pi_ne_zero]
      _ = _ := by rw [← Finset.sum_div, Finset.sum_neg_distrib]
  rw [hsum]
  field_simp [Real.pi_ne_zero]

/-- One coordinate of the finite affine-lattice block
`-K / 2 + {0, ..., K}`. -/
def ShiftedCoordinate (K : ℕ) :=
  {q : ℝ // ∃ n : Fin (K + 1), q = (n : ℝ) - (K : ℝ) / 2}

/-- The canonical parametrization of the shifted block by `{0, ..., K}`. -/
def finToShiftedCoordinate (K : ℕ) (n : Fin (K + 1)) :
    ShiftedCoordinate K :=
  ⟨(n : ℝ) - (K : ℝ) / 2, n, rfl⟩

private theorem finToShiftedCoordinate_injective (K : ℕ) :
    Function.Injective (finToShiftedCoordinate K) := by
  intro n m h
  apply Fin.ext
  have hval := congrArg Subtype.val h
  dsimp [finToShiftedCoordinate] at hval
  have hcast : (n : ℝ) = (m : ℝ) := by linarith
  exact_mod_cast hcast

private theorem finToShiftedCoordinate_surjective (K : ℕ) :
    Function.Surjective (finToShiftedCoordinate K) := by
  intro q
  rcases q.property with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  apply Subtype.ext
  exact hn.symm

/-- The affine-lattice block has exactly `K + 1` coordinates, in canonical
increasing order. -/
noncomputable def finEquivShiftedCoordinate (K : ℕ) :
    Fin (K + 1) ≃ ShiftedCoordinate K :=
  Equiv.ofBijective (finToShiftedCoordinate K)
    ⟨finToShiftedCoordinate_injective K, finToShiftedCoordinate_surjective K⟩

noncomputable instance (K : ℕ) : Fintype (ShiftedCoordinate K) :=
  Fintype.ofEquiv (Fin (K + 1)) (finEquivShiftedCoordinate K)

/-- A frequency in the `d`-dimensional shifted-coset block. -/
abbrev ShiftedCosetFrequency (d K : ℕ) := Fin d → ShiftedCoordinate K

/-- Coordinate value of a shifted-coset frequency. -/
def shiftedCoordinateValue {K : ℕ} (q : ShiftedCoordinate K) : ℝ :=
  q.1

/-- Reindex the shifted-coset block by the one-sided cube `{0, ..., K}^d`. -/
noncomputable def shiftedCosetEquivFineCube (d K : ℕ) :
    ShiftedCosetFrequency d K ≃ FineCubeFrame.FineCubeFrequency d K :=
  Equiv.piCongrRight fun _ => (finEquivShiftedCoordinate K).symm

/-- The shifted-coset block has the same cardinality `(K + 1)^d` as the
one-sided cube, for both even and odd `K`. -/
theorem card_shiftedCosetFrequency (d K : ℕ) :
    Fintype.card (ShiftedCosetFrequency d K) = (K + 1) ^ d := by
  exact
    (Fintype.card_congr (shiftedCosetEquivFineCube d K)).trans (by simp)

theorem shiftedCoordinateValue_eq_index_sub
    {K : ℕ} (q : ShiftedCoordinate K) :
    shiftedCoordinateValue q =
      (((finEquivShiftedCoordinate K).symm q : Fin (K + 1)) : ℝ) -
        (K : ℝ) / 2 := by
  unfold shiftedCoordinateValue
  have h :=
    congrArg Subtype.val
      ((finEquivShiftedCoordinate K).apply_symm_apply q)
  change
    (((finEquivShiftedCoordinate K).symm q : Fin (K + 1)) : ℝ) -
        (K : ℝ) / 2 = q.1 at h
  exact h.symm

/-- Every shifted coordinate lies in the centered real interval. -/
theorem shiftedCoordinateValue_mem_centered
    {K : ℕ} (q : ShiftedCoordinate K) :
    -(K : ℝ) / 2 ≤ shiftedCoordinateValue q ∧
      shiftedCoordinateValue q ≤ (K : ℝ) / 2 := by
  rw [shiftedCoordinateValue_eq_index_sub]
  have hnonneg :
      0 ≤ (((finEquivShiftedCoordinate K).symm q : Fin (K + 1)) : ℝ) := by
    positivity
  have hle :
      (((finEquivShiftedCoordinate K).symm q : Fin (K + 1)) : ℝ) ≤ K := by
    exact_mod_cast
      (Nat.le_of_lt_succ
        ((finEquivShiftedCoordinate K).symm q).isLt)
  constructor <;> linarith

/-- Coordinate form of the parity-free reindexing. -/
theorem shiftedCosetEquivFineCube_value
    {d K : ℕ} (ω : ShiftedCosetFrequency d K) (k : Fin d) :
    shiftedCoordinateValue (ω k) =
      ((((shiftedCosetEquivFineCube d K ω) k : Fin (K + 1)) : ℝ) -
        (K : ℝ) / 2) := by
  exact shiftedCoordinateValue_eq_index_sub (ω k)

/-- Fourier energy sampled on the centered affine-lattice block
`(-K / 2 + ℤ)^d ∩ [-K / 2, K / 2]^d`. -/
noncomputable def shiftedCosetFourierEnergy
    {d : ℕ} {ι : Type*} [Fintype ι]
    (K : ℕ) (x : ι → FineCubeFrame.AngularPoint d)
    (c : ι → ℂ) : ℝ :=
  ∑ ω : ShiftedCosetFrequency d K,
    ‖∑ j, c j * Complex.exp
      (Complex.I *
        ∑ k, ((shiftedCoordinateValue (ω k) : ℝ) : ℂ) * x j k)‖ ^ 2

/-- Unitary coefficient modulation by the scalar frequency shift `s`. -/
noncomputable def modulateCoefficients
    {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ℝ) (x : ι → FineCubeFrame.AngularPoint d)
    (c : ι → ℂ) : ι → ℂ :=
  fun j => c j * Complex.exp
    (Complex.I * ((s * ∑ k, x j k : ℝ) : ℂ))

theorem coefficientEnergy_modulateCoefficients
    {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ℝ) (x : ι → FineCubeFrame.AngularPoint d)
    (c : ι → ℂ) :
    External.coefficientEnergy (modulateCoefficients s x c) =
      External.coefficientEnergy c := by
  unfold External.coefficientEnergy modulateCoefficients
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.norm_exp, Complex.mul_re]

theorem modulateCoefficients_neg_self
    {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ℝ) (x : ι → FineCubeFrame.AngularPoint d)
    (c : ι → ℂ) :
    modulateCoefficients s x (modulateCoefficients (-s) x c) = c := by
  funext j
  unfold modulateCoefficients
  rw [mul_assoc, ← Complex.exp_add]
  have hphase :
      Complex.I * (((-s) * ∑ k, x j k : ℝ) : ℂ) +
          Complex.I * ((s * ∑ k, x j k : ℝ) : ℂ) = 0 := by
    push_cast
    ring
  rw [hphase, Complex.exp_zero, mul_one]

/-- Center modulation turns every shifted-coset Fourier value into the
corresponding one-sided Fourier value. -/
theorem shiftedCosetFourierValue_centerModulation
    {d K : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → FineCubeFrame.AngularPoint d) (c : ι → ℂ)
    (ω : ShiftedCosetFrequency d K) :
    (∑ j, modulateCoefficients ((K : ℝ) / 2) x c j *
        Complex.exp
          (Complex.I *
            ∑ k, ((shiftedCoordinateValue (ω k) : ℝ) : ℂ) * x j k)) =
      ∑ j, c j * Complex.exp
        (Complex.I *
          ∑ k,
            ((((shiftedCosetEquivFineCube d K ω) k : Fin (K + 1)) : ℕ) : ℂ) *
              x j k) := by
  apply Finset.sum_congr rfl
  intro j _
  unfold modulateCoefficients
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  have hfrequency :
      ∑ k,
          ((((shiftedCosetEquivFineCube d K ω) k : Fin (K + 1)) : ℕ) : ℂ) *
            x j k =
        (((K : ℝ) / 2 : ℝ) : ℂ) * ∑ k, x j k +
          ∑ k, ((shiftedCoordinateValue (ω k) : ℝ) : ℂ) * x j k := by
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [shiftedCosetEquivFineCube_value ω k]
    push_cast
    ring
  have hphase :=
    congrArg (fun z : ℂ => Complex.I * z) hfrequency.symm
  push_cast at hphase ⊢
  convert hphase using 1
  all_goals ring

/-- Exact parity-free energy conversion from the centered shifted coset to the
one-sided integer cube. -/
theorem shiftedCosetFourierEnergy_centerModulation
    {d K : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → FineCubeFrame.AngularPoint d) (c : ι → ℂ) :
    shiftedCosetFourierEnergy K x
        (modulateCoefficients ((K : ℝ) / 2) x c) =
      FineCubeFrame.fineCubeFourierEnergy K x c := by
  classical
  unfold shiftedCosetFourierEnergy FineCubeFrame.fineCubeFourierEnergy
  apply Fintype.sum_equiv (shiftedCosetEquivFineCube d K)
  intro ω
  congr 1
  apply congrArg norm
  exact shiftedCosetFourierValue_centerModulation x c ω

/-- The lower frame inequality on the finite shifted coset. -/
def HasShiftedCosetLowerFrameBound
    {d : ℕ} {ι : Type*} [Fintype ι]
    (K : ℕ) (A : ℝ) (x : ι → FineCubeFrame.AngularPoint d) : Prop :=
  ∀ c,
    A * External.coefficientEnergy c ≤
      shiftedCosetFourierEnergy K x c

/-- The corresponding lower frame inequality on the one-sided integer cube. -/
def HasOneSidedLowerFrameBound
    {d : ℕ} {ι : Type*} [Fintype ι]
    (K : ℕ) (A : ℝ) (x : ι → FineCubeFrame.AngularPoint d) : Prop :=
  ∀ c,
    A * External.coefficientEnergy c ≤
      FineCubeFrame.fineCubeFourierEnergy K x c

/-- Shifted-coset and one-sided lower frame bounds are exactly equivalent.
This is the parity-free replacement for reducing to a centered integer cube. -/
theorem hasShiftedCosetLowerFrameBound_iff_oneSided
    {d : ℕ} {ι : Type*} [Fintype ι]
    (K : ℕ) (A : ℝ) (x : ι → FineCubeFrame.AngularPoint d) :
    HasShiftedCosetLowerFrameBound K A x ↔
      HasOneSidedLowerFrameBound K A x := by
  constructor
  · intro h c
    have hc := h (modulateCoefficients ((K : ℝ) / 2) x c)
    rw [coefficientEnergy_modulateCoefficients,
      shiftedCosetFourierEnergy_centerModulation] at hc
    exact hc
  · intro h c
    let c' := modulateCoefficients (-((K : ℝ) / 2)) x c
    have hc := h c'
    have hmod :
        modulateCoefficients ((K : ℝ) / 2) x c' = c := by
      dsimp [c']
      exact modulateCoefficients_neg_self ((K : ℝ) / 2) x c
    have henergy :
        shiftedCosetFourierEnergy K x c =
          FineCubeFrame.fineCubeFourierEnergy K x c' := by
      rw [← hmod,
        shiftedCosetFourierEnergy_centerModulation]
    rw [coefficientEnergy_modulateCoefficients] at hc
    rwa [henergy]

/-- Uniform shifted-coset lower frame property at angular separation `η`. -/
def HasShiftedCosetLowerFrame
    (d K : ℕ) (η A : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (x : ι → FineCubeFrame.AngularPoint d),
    (∀ j, FineCubeFrame.InAngularCube (x j)) →
    (∀ i j, i ≠ j →
      η < FineCubeFrame.angularPeriodicLInfDistance (x i) (x j)) →
    HasShiftedCosetLowerFrameBound K
      (A * (((K + 1) ^ d : ℕ) : ℝ)) x

/-- Uniform one-sided lower frame property at angular separation `η`. -/
def HasOneSidedLowerFrame
    (d K : ℕ) (η A : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (x : ι → FineCubeFrame.AngularPoint d),
    (∀ j, FineCubeFrame.InAngularCube (x j)) →
    (∀ i j, i ≠ j →
      η < FineCubeFrame.angularPeriodicLInfDistance (x i) (x j)) →
    HasOneSidedLowerFrameBound K
      (A * (((K + 1) ^ d : ℕ) : ℝ)) x

theorem hasShiftedCosetLowerFrame_iff_oneSided
    (d K : ℕ) (η A : ℝ) :
    HasShiftedCosetLowerFrame d K η A ↔
      HasOneSidedLowerFrame d K η A := by
  constructor <;> intro h ι _ x hx hsep
  · exact
      (hasShiftedCosetLowerFrameBound_iff_oneSided
        K (A * (((K + 1) ^ d : ℕ) : ℝ)) x).mp
        (h ι x hx hsep)
  · exact
      (hasShiftedCosetLowerFrameBound_iff_oneSided
        K (A * (((K + 1) ^ d : ℕ) : ℝ)) x).mpr
        (h ι x hx hsep)

/-- Translate the parity-free one-sided formulation to the frame interface
used by the segmented Vandermonde proof. -/
theorem hasFineCubeFrame_of_oneSidedLowerFrame
    {d K : ℕ} {η A : ℝ}
    (h : HasOneSidedLowerFrame d K η A) :
    NumDetect.HasFineCubeFrame d K η A := by
  unfold NumDetect.HasFineCubeFrame
  intro ι _ _ x hx hsep c
  have hx' : ∀ j, FineCubeFrame.InAngularCube (x j) := by
    simpa [FineCubeFrame.InAngularCube, NumDetect.InAngularCube] using hx
  have hsep' :
      ∀ i j, i ≠ j →
        η < FineCubeFrame.angularPeriodicLInfDistance (x i) (x j) := by
    simpa [FineCubeFrame.angularPeriodicLInfDistance,
      FineCubeFrame.angularPeriodicCoordinateDistance,
      NumDetect.periodicLInfDistance,
      NumDetect.periodicCoordinateDistance] using hsep
  have hc := h ι x hx' hsep' c
  simpa [HasOneSidedLowerFrameBound,
    FineCubeFrame.fineCubeFourierEnergy,
    External.coefficientEnergy,
    NumDetect.fineCubeEvaluation,
    Matrix.mulVec, dotProduct, SegmentedVDM.energy, mul_comm] using hc

/-- The translated-cube theorem supplies the manuscript fine-cube frame in
every positive dimension, for both parities of `K + 1`. -/
theorem hasFineCubeFrame_of_translatedCube
    {d K : ℕ} {β η : ℝ}
    (hd : 1 ≤ d)
    (hβ : 1 / (2 * Real.log 2) < β)
    (hη : 4 * Real.pi * β * d / (K + 1) ≤ η) :
    NumDetect.HasFineCubeFrame d K η
      (2 - Real.exp (1 / (2 * β))) := by
  by_cases hK : K = 0
  · subst K
    apply NumDetect.hasFineCubeFrame_zero_of_sourceRange d (by omega) β η hβ
    simpa using hη
  · unfold NumDetect.HasFineCubeFrame
    intro ι _ _ x hx hsep c
    have hN : 2 ≤ K + 1 := by omega
    have hx' :
        ∀ j, External.InUnitHalfOpenCube
          (normalizedAngularPoint (x j)) :=
      fun j => normalizedAngularPoint_mem_halfOpenCube (hx j)
    have hsep' :
        ∀ i j, i ≠ j →
          2 * β * d / (K + 1) ≤
            External.unitPeriodicLInfDistance
              (normalizedAngularPoint (x i))
              (normalizedAngularPoint (x j)) := by
      intro i j hij
      rw [normalizedAngularPoint_lInfDistance (hx i) (hx j)]
      apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
      have hangular :
          4 * Real.pi * β * d / (K + 1) <
            FineCubeFrame.angularPeriodicLInfDistance (x i) (x j) :=
        hη.trans_lt (by
          simpa [FineCubeFrame.angularPeriodicLInfDistance,
            FineCubeFrame.angularPeriodicCoordinateDistance,
            NumDetect.periodicLInfDistance,
            NumDetect.periodicCoordinateDistance] using hsep i j hij)
      calc
        (2 * β * d / (K + 1)) * (2 * Real.pi) =
            4 * Real.pi * β * d / (K + 1) := by ring
        _ ≤ FineCubeFrame.angularPeriodicLInfDistance (x i) (x j) :=
          hangular.le
    have hframe :=
      External.translatedCubeFourier_lowerFrame β
        (fun j => normalizedAngularPoint (x j)) hd hN hβ.le hx'
          (by simpa only [Nat.cast_add, Nat.cast_one] using hsep') c
    rw [translatedCubeFourierEnergy_normalizedAngularPoint] at hframe
    simpa [External.coefficientEnergy,
      FineCubeFrame.fineCubeFourierEnergy,
      NumDetect.fineCubeEvaluation, Matrix.mulVec, dotProduct,
      SegmentedVDM.energy, mul_comm] using hframe

end

end BartonCubeFrame
end LeanNumDetect
