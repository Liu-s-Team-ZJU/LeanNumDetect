import General.Fourier.FineCubeFrame
import NumDetectMain.SegmentedProofSupport

/-!
Parity-free algebraic reduction for the discrete cube estimate.

For a one-sided cutoff `K`, the correct centered sampling set is not always an
integer cube.  It is the affine lattice block

`(-K / 2 + ℤ)^d ∩ [-K / 2, K / 2]^d`.

It has the parametrization `α ↦ α - K / 2`, with
`α ∈ {0, ..., K}^d`, for every `K`; no parity split is needed.  Multiplication
of each coefficient by the corresponding center phase is unitary and changes
the shifted-coset Fourier energy exactly into the one-sided cube energy.

The remaining analytic input is isolated in
`HasBartonShiftedCosetLowerFrame`.  It is precisely the lower-frame consequence
of Barton's multivariate cube minorant together with shifted Fejer--Poisson
summation.  Mathlib currently provides one-dimensional Poisson summation and
multidimensional Fourier/Parseval APIs, but not this Fejer convergence theorem
under the weak regularity of Barton's functions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect
namespace BartonCubeFrame

noncomputable section

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

/-- The minimal remaining analytic statement from the shifted Fejer proof.

For `d ≥ 2`, Barton's Theorem 2.2 supplies compactly supported multivariate
minorants.  A multidimensional shifted Fejer--Poisson theorem must then sample
them on `(-K / 2 + ℤ)^d` and eliminate cross terms at the stated torus
separation.  Everything after that analytic assertion is algebraic. -/
def HasBartonShiftedCosetLowerFrame
    (d K : ℕ) (β : ℝ) : Prop :=
  HasShiftedCosetLowerFrame d K
    (4 * Real.pi * β * d / (K + 1))
    (2 - Real.exp (1 / (2 * β)))

/-- The Barton--Fejer shifted-coset statement implies the desired one-sided
frame bound for every cutoff `K`, with no parity condition. -/
theorem oneSidedLowerFrame_of_bartonShiftedCoset
    {d K : ℕ} {β : ℝ}
    (h : HasBartonShiftedCosetLowerFrame d K β) :
    HasOneSidedLowerFrame d K
      (4 * Real.pi * β * d / (K + 1))
      (2 - Real.exp (1 / (2 * β))) :=
  (hasShiftedCosetLowerFrame_iff_oneSided d K
    (4 * Real.pi * β * d / (K + 1))
    (2 - Real.exp (1 / (2 * β)))).mp h

/-- A stronger actual separation parameter can be used without changing the
frame constant. -/
theorem oneSidedLowerFrame_of_bartonShiftedCoset_of_le
    {d K : ℕ} {β η : ℝ}
    (hη : 4 * Real.pi * β * d / (K + 1) ≤ η)
    (h : HasBartonShiftedCosetLowerFrame d K β) :
    HasOneSidedLowerFrame d K η
      (2 - Real.exp (1 / (2 * β))) := by
  intro ι _ x hx hsep
  apply oneSidedLowerFrame_of_bartonShiftedCoset h ι x hx
  intro i j hij
  exact hη.trans_lt (hsep i j hij)

/-- The Barton shifted-coset estimate, at the manuscript separation scale,
supplies exactly the fine-cube frame consumed by the segmented proof. -/
theorem hasFineCubeFrame_of_bartonShiftedCoset
    {d K : ℕ} {β η : ℝ}
    (hη : 4 * Real.pi * β * d / (K + 1) ≤ η)
    (h : HasBartonShiftedCosetLowerFrame d K β) :
    NumDetect.HasFineCubeFrame d K η
      (2 - Real.exp (1 / (2 * β))) :=
  hasFineCubeFrame_of_oneSidedLowerFrame
    (oneSidedLowerFrame_of_bartonShiftedCoset_of_le hη h)

end

end BartonCubeFrame
end LeanNumDetect
