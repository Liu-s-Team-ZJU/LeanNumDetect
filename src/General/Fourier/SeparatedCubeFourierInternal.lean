import External.SeparatedCubeFourier
import General.Fourier.WeightedOrthogonality

/-!
Internal algebraic reduction of the discrete part of Li's separated-cube
Fourier estimate. No external theorem is assumed below.

The finite Fourier energy is expanded as the quadratic form of a tensor product
of one-dimensional centered Dirichlet kernels.  Its diagonal is computed
exactly, leaving a single signed off-diagonal estimate as the analytic core of
the desired lower frame bound.
-/

set_option autoImplicit false

open scoped BigOperators

namespace LeanNumDetect
namespace SeparatedCubeFourierInternal

noncomputable section

/-- The centered one-dimensional Dirichlet kernel in the source normalization. -/
def centeredCoordinateKernel (m u v : ℝ) : ℂ :=
  ∑ n : External.CenteredInteger m,
    Complex.exp
      (-2 * Real.pi * Complex.I * (((n : ℤ) : ℂ) * (v - u)))

/-- The Fourier kernel of the centered integer cube. -/
def centeredCubeKernel {d : ℕ} (m : ℝ)
    (u v : External.UnitTorusPoint d) : ℂ :=
  ∑ ω : External.CenteredCubeFrequency d m,
    Complex.exp
      (-2 * Real.pi * Complex.I *
        ∑ k, ((ω k : ℤ) : ℂ) * (v k - u k))

/-- The centered-cube kernel factors coordinatewise. -/
theorem centeredCubeKernel_eq_prod {d : ℕ} (m : ℝ)
    (u v : External.UnitTorusPoint d) :
    centeredCubeKernel m u v =
      ∏ k, centeredCoordinateKernel m (u k) (v k) := by
  classical
  unfold centeredCubeKernel centeredCoordinateKernel
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]

/-- The cube kernel on the diagonal is the number of sampled frequencies. -/
theorem centeredCubeKernel_self {d : ℕ} (m : ℝ)
    (u : External.UnitTorusPoint d) :
    centeredCubeKernel m u u =
      (Fintype.card (External.CenteredCubeFrequency d m) : ℂ) := by
  simp [centeredCubeKernel]

/-- Wrapped coordinate distance is nonnegative for the source's half-open-cube
representatives. -/
theorem unitPeriodicCoordinateDistance_nonneg
    {u v : ℝ}
    (hu : -(1 : ℝ) / 2 ≤ u ∧ u < (1 : ℝ) / 2)
    (hv : -(1 : ℝ) / 2 ≤ v ∧ v < (1 : ℝ) / 2) :
    0 ≤ External.unitPeriodicCoordinateDistance u v := by
  unfold External.unitPeriodicCoordinateDistance
  have habs : |u - v| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  exact le_min (abs_nonneg _) (by linarith)

/-- The wrapped coordinate distance is bounded by every integer translate of
the ordinary coordinate difference. -/
theorem unitPeriodicCoordinateDistance_le_integerTranslate
    {u v : ℝ}
    (hu : -(1 : ℝ) / 2 ≤ u ∧ u < (1 : ℝ) / 2)
    (hv : -(1 : ℝ) / 2 ≤ v ∧ v < (1 : ℝ) / 2)
    (p : ℤ) :
    External.unitPeriodicCoordinateDistance u v ≤ |u - v - p| := by
  unfold External.unitPeriodicCoordinateDistance
  have habs : |u - v| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  by_cases hp : p = 0
  · subst p
    simp
  rcases lt_or_gt_of_ne hp with hpneg | hppos
  · have hpr : (p : ℝ) ≤ -1 := by exact_mod_cast (show p ≤ -1 by omega)
    have hsign : 0 ≤ u - v - p := by
      have ha := neg_abs_le (u - v)
      linarith
    rw [abs_of_nonneg hsign]
    exact (min_le_right |u - v| (1 - |u - v|)).trans (by
      have ha := neg_abs_le (u - v)
      linarith)
  · have hpr : (1 : ℝ) ≤ p := by exact_mod_cast (show (1 : ℤ) ≤ p by omega)
    have hsign : u - v - p ≤ 0 := by
      have ha := le_abs_self (u - v)
      linarith
    rw [abs_of_nonpos hsign]
    exact (min_le_right |u - v| (1 - |u - v|)).trans (by
      have ha := le_abs_self (u - v)
      linarith)

/-- A lower bound for the periodic sup distance is attained by one coordinate,
and that coordinate is separated from every integer translate. -/
theorem exists_coordinate_integer_separation
    {d : ℕ} (hd : 0 < d)
    {u v : External.UnitTorusPoint d}
    (hu : External.InUnitHalfOpenCube u)
    (hv : External.InUnitHalfOpenCube v)
    {δ : ℝ}
    (hδ : δ ≤ External.unitPeriodicLInfDistance u v) :
    ∃ k, ∀ p : ℤ, δ ≤ |u k - v k - p| := by
  let f : Fin d → ℝ :=
    fun k => External.unitPeriodicCoordinateDistance (u k) (v k)
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨k, hk⟩ := (IsGreatest.pi_norm f).1
  refine ⟨k, fun p => ?_⟩
  have hfk : 0 ≤ f k :=
    unitPeriodicCoordinateDistance_nonneg (hu k) (hv k)
  have hcoord : δ ≤ External.unitPeriodicCoordinateDistance (u k) (v k) := by
    unfold External.unitPeriodicLInfDistance at hδ
    have hknorm : ‖f k‖ = ‖f‖ := hk
    rw [← hknorm] at hδ
    simpa only [Real.norm_eq_abs, abs_of_nonneg hfk] using hδ
  exact hcoord.trans
    (unitPeriodicCoordinateDistance_le_integerTranslate (hu k) (hv k) p)

/-- One summand in the norm-square expansion has the expected kernel phase. -/
private theorem phase_cross_term {d : ℕ} {m : ℝ}
    (ω : External.CenteredCubeFrequency d m)
    (u v : External.UnitTorusPoint d) (a b : ℂ) :
    star
        (a * Complex.exp
          (-2 * Real.pi * Complex.I *
            ∑ k, ((ω k : ℤ) : ℂ) * u k)) *
        (b * Complex.exp
          (-2 * Real.pi * Complex.I *
            ∑ k, ((ω k : ℤ) : ℂ) * v k)) =
      star a * b *
        Complex.exp
          (-2 * Real.pi * Complex.I *
            ∑ k, ((ω k : ℤ) : ℂ) * (v k - u k)) := by
  rw [star_mul, Complex.star_def, ← Complex.exp_conj]
  have hconj :
      (starRingEnd ℂ)
          (-2 * Real.pi * Complex.I *
            ∑ k, ((ω k : ℤ) : ℂ) * u k) =
        2 * Real.pi * Complex.I *
          ∑ k, ((ω k : ℤ) : ℂ) * u k := by
    simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I, map_sum, map_intCast]
    ring
  rw [hconj]
  calc
    _ = star a * b *
        (Complex.exp
            (2 * Real.pi * Complex.I *
              ∑ k, ((ω k : ℤ) : ℂ) * u k) *
          Complex.exp
            (-2 * Real.pi * Complex.I *
              ∑ k, ((ω k : ℤ) : ℂ) * v k)) := by ac_rfl
    _ = star a * b *
        Complex.exp
          (2 * Real.pi * Complex.I *
              ∑ k, ((ω k : ℤ) : ℂ) * u k +
            -2 * Real.pi * Complex.I *
              ∑ k, ((ω k : ℤ) : ℂ) * v k) := by
          rw [Complex.exp_add]
    _ = _ := by
      congr 2
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The Fourier sum at one frequency of the full integer lattice. -/
def integerLatticeFourierValue
    {d : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → External.UnitTorusPoint d) (c : ι → ℂ)
    (ω : Fin d → ℤ) : ℂ :=
  ∑ j, c j * Complex.exp
    (-2 * Real.pi * Complex.I *
      ∑ k, ((ω k : ℤ) : ℂ) * x j k)

/-- The values of the subtype-indexed centered cube, embedded in the full
integer lattice. -/
def centeredFrequencyValues (d : ℕ) (m : ℝ) : Finset (Fin d → ℤ) :=
  by
    classical
    exact Finset.univ.image fun ω : External.CenteredCubeFrequency d m =>
      fun k => (ω k : ℤ)

private theorem centeredFrequencyValue_injective (d : ℕ) (m : ℝ) :
    Function.Injective
      (fun ω : External.CenteredCubeFrequency d m =>
        fun k => (ω k : ℤ)) := by
  intro ω ν h
  funext k
  apply Subtype.ext
  exact congrFun h k

/-- Reindex the source's subtype-valued cube as a finite subset of the full
integer lattice. -/
theorem discreteCubeFourierEnergy_eq_latticeBlock
    {d : ℕ} {ι : Type*} [Fintype ι]
    (m : ℝ) (x : ι → External.UnitTorusPoint d) (c : ι → ℂ) :
    External.discreteCubeFourierEnergy m x c =
      ∑ ω ∈ centeredFrequencyValues d m,
        ‖integerLatticeFourierValue x c ω‖ ^ 2 := by
  classical
  unfold External.discreteCubeFourierEnergy centeredFrequencyValues
  rw [Finset.sum_image]
  · rfl
  · intro ω _ ν _ hων
    exact centeredFrequencyValue_injective d m hων

/-- A scalar lattice weight with vanishing cross terms decouples the weighted
energy into its diagonal coefficient energy.  This is the multidimensional
counterpart of the one-dimensional reduction in
`SeparatedFourierEnergy.lean`. -/
theorem weighted_lattice_energy_hasSum
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w : (Fin d → ℤ) → ℝ) (W : ℝ)
    (x : ι → External.UnitTorusPoint d) (c : ι → ℂ)
    (hw : HasSum w W)
    (hcross : ∀ i j, i ≠ j →
      HasSum
        (fun ω => w ω *
          (star
              (c i * Complex.exp
                (-2 * Real.pi * Complex.I *
                  ∑ k, ((ω k : ℤ) : ℂ) * x i k)) *
            (c j * Complex.exp
              (-2 * Real.pi * Complex.I *
                ∑ k, ((ω k : ℤ) : ℂ) * x j k))).re)
        0) :
    HasSum
      (fun ω => w ω * ‖integerLatticeFourierValue x c ω‖ ^ 2)
      (W * External.coefficientEnergy c) := by
  let v : ι → (Fin d → ℤ) → ℂ := fun i ω =>
    c i * Complex.exp
      (-2 * Real.pi * Complex.I *
        ∑ k, ((ω k : ℤ) : ℂ) * x i k)
  have hexp (i : ι) (ω : Fin d → ℤ) :
      ‖Complex.exp
        (-2 * Real.pi * Complex.I *
          ∑ k, ((ω k : ℤ) : ℂ) * x i k)‖ = 1 := by
    rw [Complex.norm_exp]
    have hre :
        (-2 * Real.pi * Complex.I *
          ∑ k, ((ω k : ℤ) : ℂ) * x i k).re = 0 := by
      have hsum :
          (∑ k, ((ω k : ℤ) : ℂ) * x i k) =
            ((∑ k, (ω k : ℝ) * x i k : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [hsum]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      norm_num
    rw [hre, Real.exp_zero]
  have hdiag (i : ι) :
      HasSum (fun ω => w ω * ‖v i ω‖ ^ 2) (W * ‖c i‖ ^ 2) := by
    simpa only [v, norm_mul, hexp, one_pow, mul_one] using
      hw.mul_right (‖c i‖ ^ 2)
  have hsum := weighted_sum_energy_hasSum w v
    (fun i => W * ‖c i‖ ^ 2) hdiag hcross
  simpa only [integerLatticeFourierValue, v, External.coefficientEnergy,
    Finset.mul_sum] using hsum

/-- Restricting a signed full-lattice minorant to the centered cube gives an
unweighted finite-cube lower bound. -/
theorem discrete_lower_of_weighted_lattice
    {d : ℕ} {ι : Type*} [Fintype ι]
    (m W : ℝ) (x : ι → External.UnitTorusPoint d) (c : ι → ℂ)
    (w : (Fin d → ℤ) → ℝ)
    (hin : ∀ ω ∈ centeredFrequencyValues d m, w ω ≤ 1)
    (hout : ∀ ω ∉ centeredFrequencyValues d m, w ω ≤ 0)
    (hsum : HasSum
      (fun ω => w ω * ‖integerLatticeFourierValue x c ω‖ ^ 2)
      (W * External.coefficientEnergy c)) :
    W * External.coefficientEnergy c ≤
      External.discreteCubeFourierEnergy m x c := by
  have hle := weighted_series_le_block
    (centeredFrequencyValues d m) w
    (fun ω => ‖integerLatticeFourierValue x c ω‖ ^ 2)
    (W * External.coefficientEnergy c)
    (fun _ => sq_nonneg _) hin hout hsum
  rwa [← discreteCubeFourierEnergy_eq_latticeBlock] at hle

/-- The sampled energy is the real part of the finite kernel quadratic form. -/
theorem discreteCubeFourierEnergy_eq_kernel
    {d : ℕ} {ι : Type*} [Fintype ι]
    (m : ℝ) (x : ι → External.UnitTorusPoint d) (c : ι → ℂ) :
    External.discreteCubeFourierEnergy m x c =
      ∑ i, ∑ j,
        (star (c i) * c j * centeredCubeKernel m (x i) (x j)).re := by
  classical
  unfold External.discreteCubeFourierEnergy
  simp_rw [norm_sum_sq_real]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  unfold centeredCubeKernel
  rw [← Complex.re_sum, Finset.mul_sum]
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro ω _
  have hphase := phase_cross_term ω (x i) (x j) (c i) (c j)
  simpa only using hphase

/-- The contribution from all ordered pairs of distinct nodes. -/
def offDiagonalKernelEnergy
    {d : ℕ} {ι : Type*} [Fintype ι]
    (m : ℝ) (x : ι → External.UnitTorusPoint d) (c : ι → ℂ) : ℝ :=
  by
    classical
    exact
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        (star (c i) * c j * centeredCubeKernel m (x i) (x j)).re

/-- Exact diagonal/off-diagonal decomposition of the sampled Fourier energy. -/
theorem discreteCubeFourierEnergy_eq_diagonal_add_offDiagonal
    {d : ℕ} {ι : Type*} [Fintype ι]
    (m : ℝ) (x : ι → External.UnitTorusPoint d) (c : ι → ℂ) :
    External.discreteCubeFourierEnergy m x c =
      Fintype.card (External.CenteredCubeFrequency d m) *
          External.coefficientEnergy c +
        offDiagonalKernelEnergy m x c := by
  classical
  rw [discreteCubeFourierEnergy_eq_kernel]
  unfold External.coefficientEnergy
  have hsplit (i : ι) :
      (∑ j,
          (star (c i) * c j *
            centeredCubeKernel m (x i) (x j)).re) =
        (star (c i) * c i *
            centeredCubeKernel m (x i) (x i)).re +
          ∑ j ∈ Finset.univ.erase i,
            (star (c i) * c j *
              centeredCubeKernel m (x i) (x j)).re := by
    rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  calc
    (∑ i, ∑ j,
        (star (c i) * c j * centeredCubeKernel m (x i) (x j)).re) =
        ∑ i,
          ((star (c i) * c i *
              centeredCubeKernel m (x i) (x i)).re +
            ∑ j ∈ Finset.univ.erase i,
              (star (c i) * c j *
                centeredCubeKernel m (x i) (x j)).re) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hsplit i
    _ = (∑ i,
          (star (c i) * c i *
            centeredCubeKernel m (x i) (x i)).re) +
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          (star (c i) * c j *
            centeredCubeKernel m (x i) (x j)).re := Finset.sum_add_distrib
    _ = Fintype.card (External.CenteredCubeFrequency d m) *
          ∑ i, ‖c i‖ ^ 2 +
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          (star (c i) * c j *
            centeredCubeKernel m (x i) (x j)).re := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [centeredCubeKernel_self]
          have hc : star (c i) * c i = ((‖c i‖ ^ 2 : ℝ) : ℂ) := by
            rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
            rfl
          rw [hc]
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.natCast_re, Complex.natCast_im]
          ring
    _ = _ := by rfl

/-- The precise remaining analytic estimate needed for Li's discrete lower
bound, stated after the exact diagonal has been removed. -/
def HasSharpOffDiagonalBound
    {d : ℕ} {ι : Type*} [Fintype ι]
    (m β : ℝ) (x : ι → External.UnitTorusPoint d) : Prop :=
  ∀ c,
    -(Real.exp (1 / (2 * β)) - 1) *
          Fintype.card (External.CenteredCubeFrequency d m) *
          External.coefficientEnergy c ≤
      offDiagonalKernelEnergy m x c

/-- A sharp off-diagonal estimate closes the discrete lower frame bound with
exactly the constant in Li's Theorem 2.3. -/
theorem discrete_lower_of_sharp_offDiagonal
    {d : ℕ} {ι : Type*} [Fintype ι]
    (m β : ℝ) (x : ι → External.UnitTorusPoint d)
    (hoff : HasSharpOffDiagonalBound m β x) :
    ∀ c,
      (2 - Real.exp (1 / (2 * β))) *
          Fintype.card (External.CenteredCubeFrequency d m) *
          External.coefficientEnergy c ≤
        External.discreteCubeFourierEnergy m x c := by
  intro c
  rw [discreteCubeFourierEnergy_eq_diagonal_add_offDiagonal]
  have h := hoff c
  nlinarith

end

end SeparatedCubeFourierInternal
end LeanNumDetect
