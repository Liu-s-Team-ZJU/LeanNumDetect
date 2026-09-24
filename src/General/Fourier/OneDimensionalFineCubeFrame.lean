import NumDetect.Segmented.ClumpBounds

/-!
The one-dimensional fine-cube frame from the periodic Hilbert inequality.

All finite-dimensional algebra is proved here.  The only analytic input is
`HasPeriodicHilbertSineBound`, the sharp periodic Hilbert inequality for the
cosecant kernel.  In particular, this file does not assume a large-sieve or a
frame inequality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators

namespace LeanNumDetect
namespace OneDimensionalFineCubeFrame

noncomputable section

/-- The off-diagonal periodic Hilbert form in angular coordinates. -/
def periodicHilbertSineForm
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (c : ι → ℂ) : ℂ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i,
    star (c i) * c j / (Real.sin ((x j - x i) / 2) : ℂ)

/-- The sole analytic input: the sharp periodic Hilbert inequality for the
sine kernel.  The angular separation is taken modulo `2π`. -/
def HasPeriodicHilbertSineBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (δ : ℝ) (_hδ : 0 < δ) (x : ι → ℝ),
    (∀ i j, i ≠ j → ∀ p : ℤ,
      δ < |x i - x j - 2 * Real.pi * p|) →
    ∀ c : ι → ℂ,
      ‖periodicHilbertSineForm x c‖ ≤
        (2 * Real.pi / δ) * SegmentedVDM.energy c

/-- A finite angular exponential sum over an arbitrary finite node type. -/
def angularExponentialSum
    {ι : Type} [Fintype ι]
    (x : ι → ℝ) (c : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ j, c j * Complex.exp (Complex.I * ((t * x j : ℝ) : ℂ))

/-- The angular Dirichlet kernel for the consecutive block `{0, ..., N-1}`. -/
def angularDirichletKernel (N : ℕ) (t : ℝ) : ℂ :=
  ∑ k : Fin N, Complex.exp (Complex.I * (((k : ℕ) : ℝ) * t : ℝ))

/-- The complex off-diagonal part of the consecutive-sampling Gram form. -/
def angularOffDiagonalEnergy
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (x : ι → ℝ) (c : ι → ℂ) : ℂ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i,
    star (c i) * c j * angularDirichletKernel N (x j - x i)

private theorem sin_as_exp_difference (t : ℝ) :
    (Real.sin t : ℂ) =
      (Complex.exp (Complex.I * (t : ℂ)) -
        Complex.exp (-(Complex.I * (t : ℂ)))) /
          (2 * Complex.I) := by
  rw [Complex.ofReal_sin]
  unfold Complex.sin
  rw [show -(t : ℂ) * Complex.I =
      -(Complex.I * (t : ℂ)) by ring,
    show (t : ℂ) * Complex.I =
      Complex.I * (t : ℂ) by ring]
  field_simp [Complex.I_ne_zero]
  rw [Complex.I_sq]
  ring

private theorem exp_I_sub_one (t : ℝ) :
    Complex.exp (Complex.I * (t : ℂ)) - 1 =
      2 * Complex.I *
        Complex.exp (Complex.I * ((t / 2 : ℝ) : ℂ)) *
          (Real.sin (t / 2) : ℂ) := by
  rw [sin_as_exp_difference]
  have hplus :
      Complex.exp (Complex.I * ((t / 2 : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((t / 2 : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hminus :
      Complex.exp (Complex.I * ((t / 2 : ℝ) : ℂ)) *
          Complex.exp (-(Complex.I * ((t / 2 : ℝ) : ℂ))) = 1 := by
    rw [← Complex.exp_add]
    simp
  field_simp [Complex.I_ne_zero]
  rw [mul_sub, hplus, hminus]

private theorem sin_half_ne_zero_of_separated
    {δ u v : ℝ} (hδ : 0 < δ)
    (hsep : ∀ p : ℤ, δ < |u - v - 2 * Real.pi * p|) :
    Real.sin ((v - u) / 2) ≠ 0 := by
  intro hsin
  obtain ⟨p, hp⟩ := Real.sin_eq_zero_iff.mp hsin
  have hzero : u - v - 2 * Real.pi * (-p) = 0 := by
    push_cast at hp ⊢
    nlinarith
  have := hsep (-p)
  have hcast : ((-p : ℤ) : ℝ) = -(p : ℝ) := by push_cast; rfl
  rw [hcast, hzero, abs_zero] at this
  linarith

private theorem angularDirichletKernel_eq_sine
    {N : ℕ} {t : ℝ} (hsin : Real.sin (t / 2) ≠ 0) :
    angularDirichletKernel N t =
      Complex.exp
          (Complex.I * ((((N : ℝ) - 1) * t / 2 : ℝ) : ℂ)) *
        ((Real.sin ((N : ℝ) * t / 2) / Real.sin (t / 2) : ℝ) : ℂ) := by
  have hden :
      Complex.exp (Complex.I * (t : ℂ)) ≠ 1 := by
    apply sub_ne_zero.mp
    rw [exp_I_sub_one]
    exact
      mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (by norm_num) Complex.I_ne_zero)
          (Complex.exp_ne_zero _))
        (Complex.ofReal_ne_zero.mpr hsin)
  unfold angularDirichletKernel
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ =>
      Complex.exp (Complex.I * (((k : ℕ) : ℝ) * t : ℝ))) N]
  have hterm (k : ℕ) :
      Complex.exp (Complex.I * (((k : ℕ) : ℝ) * t : ℝ)) =
        Complex.exp (Complex.I * (t : ℂ)) ^ k := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  rw [geom_sum_eq hden]
  rw [← Complex.exp_nat_mul]
  have hnum :
      Complex.exp ((N : ℂ) * (Complex.I * (t : ℂ))) - 1 =
        2 * Complex.I *
          Complex.exp
            (Complex.I * ((((N : ℝ) * t) / 2 : ℝ) : ℂ)) *
          (Real.sin ((N : ℝ) * t / 2) : ℂ) := by
    convert exp_I_sub_one ((N : ℝ) * t) using 1 <;> push_cast <;> ring
  rw [hnum, exp_I_sub_one]
  push_cast
  field_simp [hsin, Complex.I_ne_zero, Complex.exp_ne_zero]
  have hphase :
      Complex.exp (Complex.I * (N : ℂ) * (t : ℂ) / 2) =
        Complex.exp (Complex.I * (t : ℂ) / 2) *
          Complex.exp (Complex.I * (t : ℂ) * ((N : ℂ) - 1) / 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hphase]
  ring

private theorem angular_phase_cross
    (k : ℕ) (u v : ℝ) (a b : ℂ) :
    star
        (a * Complex.exp
          (Complex.I * (((k : ℕ) : ℝ) * u : ℝ))) *
        (b * Complex.exp
          (Complex.I * (((k : ℕ) : ℝ) * v : ℝ))) =
      star a * b *
        Complex.exp
          (Complex.I * (((k : ℕ) : ℝ) * (v - u) : ℝ)) := by
  rw [star_mul, Complex.star_def, ← Complex.exp_conj]
  have hconj :
      (starRingEnd ℂ)
          (Complex.I * (((k : ℕ) : ℝ) * u : ℝ)) =
        -(Complex.I * (((k : ℕ) : ℝ) * u : ℝ)) := by
    simp only [map_mul, Complex.conj_I, map_natCast, map_ofNat,
      Complex.conj_ofReal]
    ring
  rw [hconj]
  calc
    _ = star a * b *
        (Complex.exp
            (-(Complex.I * (((k : ℕ) : ℝ) * u : ℝ))) *
          Complex.exp
            (Complex.I * (((k : ℕ) : ℝ) * v : ℝ))) := by ac_rfl
    _ = star a * b *
        Complex.exp
          (-(Complex.I * (((k : ℕ) : ℝ) * u : ℝ)) +
            Complex.I * (((k : ℕ) : ℝ) * v : ℝ)) := by
          rw [Complex.exp_add]
    _ = _ := by
      congr 2
      push_cast
      ring

/-- The same phase cancellation for an arbitrary real frequency. -/
private theorem angular_phase_cross_real
    (s u v : ℝ) (a b : ℂ) :
    star
        (a * Complex.exp (Complex.I * ((s * u : ℝ) : ℂ))) *
        (b * Complex.exp (Complex.I * ((s * v : ℝ) : ℂ))) =
      star a * b *
        Complex.exp (Complex.I * ((s * (v - u) : ℝ) : ℂ)) := by
  rw [star_mul, Complex.star_def, ← Complex.exp_conj]
  have hconj :
      (starRingEnd ℂ) (Complex.I * ((s * u : ℝ) : ℂ)) =
        -(Complex.I * ((s * u : ℝ) : ℂ)) := by simp
  rw [hconj]
  calc
    _ = star a * b *
        (Complex.exp (-(Complex.I * ((s * u : ℝ) : ℂ))) *
          Complex.exp (Complex.I * ((s * v : ℝ) : ℂ))) := by ac_rfl
    _ = star a * b *
        Complex.exp
          (-(Complex.I * ((s * u : ℝ) : ℂ)) +
            Complex.I * ((s * v : ℝ) : ℂ)) := by
          rw [Complex.exp_add]
    _ = _ := by
      congr 2
      push_cast
      ring

/-- Exact finite-sum expansion of consecutive angular Fourier energy. -/
theorem angularSamplingEnergy_eq_diagonal_add_offDiagonal
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (x : ι → ℝ) (c : ι → ℂ) :
    (∑ k : Fin N, ‖angularExponentialSum x c k‖ ^ 2) =
      (N : ℝ) * SegmentedVDM.energy c +
        (angularOffDiagonalEnergy N x c).re := by
  classical
  have hkernel :
      (∑ k : Fin N, ‖angularExponentialSum x c k‖ ^ 2) =
        ∑ i, ∑ j,
          (star (c i) * c j *
            angularDirichletKernel N (x j - x i)).re := by
    simp_rw [angularExponentialSum, norm_sum_sq_real]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Complex.re_sum]
    apply congrArg Complex.re
    unfold angularDirichletKernel
    calc
      _ = ∑ k : Fin N,
          star (c i) * c j *
            Complex.exp
              (Complex.I * (((k : ℕ) : ℝ) * (x j - x i) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro k _
            exact angular_phase_cross k.val (x i) (x j) (c i) (c j)
      _ = _ := by rw [Finset.mul_sum]
  rw [hkernel]
  unfold angularOffDiagonalEnergy SegmentedVDM.energy
  have hsplit (i : ι) :
      (∑ j,
          (star (c i) * c j *
            angularDirichletKernel N (x j - x i)).re) =
        (N : ℝ) * ‖c i‖ ^ 2 +
          ∑ j ∈ Finset.univ.erase i,
            (star (c i) * c j *
              angularDirichletKernel N (x j - x i)).re := by
    have hdiag :
        (star (c i) * c i *
          angularDirichletKernel N (x i - x i)).re =
          (N : ℝ) * ‖c i‖ ^ 2 := by
      have hc : star (c i) * c i = ((‖c i‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
        rfl
      rw [sub_self, hc]
      simp [angularDirichletKernel]
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
      ring
    rw [← hdiag, add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  simp only [Complex.re_sum]

private theorem sine_exp_difference (t : ℝ) :
    (Real.sin t : ℂ) =
      (Complex.exp (Complex.I * (t : ℂ)) -
        Complex.exp (-(Complex.I * (t : ℂ)))) /
          (2 * Complex.I) := by
  exact sin_as_exp_difference t

private theorem angularDirichletKernel_eq_phaseDifference
    {N : ℕ} {t : ℝ} (hsin : Real.sin (t / 2) ≠ 0) :
    angularDirichletKernel N t =
      (Complex.exp
          (Complex.I * ((((2 * (N : ℝ) - 1) * t) / 2 : ℝ) : ℂ)) -
        Complex.exp (-(Complex.I * ((t / 2 : ℝ) : ℂ)))) /
        (2 * Complex.I * (Real.sin (t / 2) : ℂ)) := by
  rw [angularDirichletKernel_eq_sine hsin]
  simp only [Complex.ofReal_div]
  rw [sine_exp_difference ((N : ℝ) * t / 2)]
  field_simp [hsin, Complex.I_ne_zero]
  have hfirst :
      Complex.exp
          (Complex.I * (((N : ℝ) - 1) * t / 2 : ℝ)) *
          Complex.exp (Complex.I * ((N : ℝ) * t / 2 : ℝ)) =
        Complex.exp
          (Complex.I * ((2 * (N : ℝ) - 1) * t / 2 : ℝ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsecond :
      Complex.exp
          (Complex.I * (((N : ℝ) - 1) * t / 2 : ℝ)) *
          Complex.exp (-(Complex.I * ((N : ℝ) * t / 2 : ℝ))) =
        Complex.exp (-(Complex.I * (t / 2 : ℝ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  apply (div_left_inj' (Complex.ofReal_ne_zero.mpr hsin)).2
  rw [mul_sub]
  congr 1
  · convert hfirst using 1 <;> push_cast <;> ring
  · convert hsecond using 1 <;> push_cast <;> ring

private theorem angularOffDiagonalEnergy_eq_hilbert_difference
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (x : ι → ℝ) (c : ι → ℂ)
    (hsep : ∀ i j, i ≠ j → ∀ p : ℤ,
      δ < |x i - x j - 2 * Real.pi * p|) :
    angularOffDiagonalEnergy N x c =
      (periodicHilbertSineForm x
          (fun j => c j * Complex.exp
            (Complex.I *
              (((2 * (N : ℝ) - 1) * x j / 2 : ℝ) : ℂ))) -
        periodicHilbertSineForm x
          (fun j => c j * Complex.exp
            (-(Complex.I * ((x j / 2 : ℝ) : ℂ))))) /
        (2 * Complex.I) := by
  classical
  let cHigh : ι → ℂ := fun j =>
    c j * Complex.exp
      (Complex.I * (((2 * (N : ℝ) - 1) * x j / 2 : ℝ) : ℂ))
  let cLow : ι → ℂ := fun j =>
    c j * Complex.exp (-(Complex.I * ((x j / 2 : ℝ) : ℂ)))
  have hterm (i j : ι) (hij : i ≠ j) :
      star (c i) * c j * angularDirichletKernel N (x j - x i) =
        (star (cHigh i) * cHigh j /
            (Real.sin ((x j - x i) / 2) : ℂ) -
          star (cLow i) * cLow j /
            (Real.sin ((x j - x i) / 2) : ℂ)) /
          (2 * Complex.I) := by
    have hsine :
        Real.sin ((x j - x i) / 2) ≠ 0 :=
      sin_half_ne_zero_of_separated hδ (hsep i j hij)
    rw [angularDirichletKernel_eq_phaseDifference hsine]
    have hhigh :
        star (cHigh i) * cHigh j =
          star (c i) * c j *
            Complex.exp
              (Complex.I *
                ((((2 * (N : ℝ) - 1) / 2) * (x j - x i) : ℝ) : ℂ)) := by
      dsimp only [cHigh]
      convert
        angular_phase_cross_real
          ((2 * (N : ℝ) - 1) / 2) (x i) (x j) (c i) (c j) using 1 <;>
        push_cast <;> ring
    have hlow :
        star (cLow i) * cLow j =
          star (c i) * c j *
            Complex.exp
              (Complex.I * (((-(1 : ℝ) / 2) * (x j - x i) : ℝ) : ℂ)) := by
      dsimp only [cLow]
      convert
        angular_phase_cross_real
          (-(1 : ℝ) / 2) (x i) (x j) (c i) (c j) using 1 <;>
        push_cast <;> ring
    rw [hhigh, hlow]
    field_simp [hsine, Complex.I_ne_zero]
    congr 1 <;> push_cast <;> ring
  unfold angularOffDiagonalEnergy periodicHilbertSineForm
  change
    (∑ i, ∑ j ∈ Finset.univ.erase i,
      star (c i) * c j * angularDirichletKernel N (x j - x i)) =
    ((∑ i, ∑ j ∈ Finset.univ.erase i,
        star (cHigh i) * cHigh j /
          (Real.sin ((x j - x i) / 2) : ℂ)) -
      (∑ i, ∑ j ∈ Finset.univ.erase i,
        star (cLow i) * cLow j /
          (Real.sin ((x j - x i) / 2) : ℂ))) /
        (2 * Complex.I)
  calc
    _ = ∑ i, ∑ j ∈ Finset.univ.erase i,
        (star (cHigh i) * cHigh j /
              (Real.sin ((x j - x i) / 2) : ℂ) -
            star (cLow i) * cLow j /
              (Real.sin ((x j - x i) / 2) : ℂ)) /
          (2 * Complex.I) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j hj
        exact hterm i j (Finset.ne_of_mem_erase hj).symm
    _ = _ := by
      simp only [div_eq_mul_inv, sub_mul, Finset.sum_sub_distrib,
        Finset.sum_mul]

/-- Aubel--Bölcskei's lower large-sieve inequality in angular normalization. -/
theorem angular_largeSieve_lower_of_periodicHilbertSineBound
    (hHilbert : HasPeriodicHilbertSineBound)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (x : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → ∀ p : ℤ,
      δ < |x i - x j - 2 * Real.pi * p|)
    (c : ι → ℂ) :
    ((N : ℝ) - 2 * Real.pi / δ) * SegmentedVDM.energy c ≤
      ∑ k : Fin N, ‖angularExponentialSum x c k‖ ^ 2 := by
  let cHigh : ι → ℂ := fun j =>
    c j * Complex.exp
      (Complex.I * (((2 * (N : ℝ) - 1) * x j / 2 : ℝ) : ℂ))
  let cLow : ι → ℂ := fun j =>
    c j * Complex.exp (-(Complex.I * ((x j / 2 : ℝ) : ℂ)))
  have hhigh :=
    hHilbert ι δ hδ x hsep cHigh
  have hlow :=
    hHilbert ι δ hδ x hsep cLow
  have henergyHigh :
      SegmentedVDM.energy cHigh = SegmentedVDM.energy c := by
    unfold SegmentedVDM.energy cHigh
    apply Finset.sum_congr rfl
    intro j _
    simp [Complex.norm_exp, Complex.mul_re]
  have henergyLow :
      SegmentedVDM.energy cLow = SegmentedVDM.energy c := by
    unfold SegmentedVDM.energy cLow
    apply Finset.sum_congr rfl
    intro j _
    simp [Complex.norm_exp, Complex.mul_re]
  rw [henergyHigh] at hhigh
  rw [henergyLow] at hlow
  have hoff :
      ‖angularOffDiagonalEnergy N x c‖ ≤
        (2 * Real.pi / δ) * SegmentedVDM.energy c := by
    rw [angularOffDiagonalEnergy_eq_hilbert_difference hδ x c hsep]
    calc
      ‖(periodicHilbertSineForm x cHigh -
          periodicHilbertSineForm x cLow) / (2 * Complex.I)‖
          ≤ (‖periodicHilbertSineForm x cHigh‖ +
              ‖periodicHilbertSineForm x cLow‖) / 2 := by
            simpa [norm_div, norm_mul] using
              (div_le_div_of_nonneg_right
                (norm_sub_le
                  (periodicHilbertSineForm x cHigh)
                  (periodicHilbertSineForm x cLow))
                (by norm_num : (0 : ℝ) ≤ 2))
      _ ≤ (((2 * Real.pi / δ) * SegmentedVDM.energy c) +
              ((2 * Real.pi / δ) * SegmentedVDM.energy c)) / 2 :=
            div_le_div_of_nonneg_right (add_le_add hhigh hlow) (by norm_num)
      _ = (2 * Real.pi / δ) * SegmentedVDM.energy c := by ring
  rw [angularSamplingEnergy_eq_diagonal_add_offDiagonal]
  have hre :
      -(2 * Real.pi / δ) * SegmentedVDM.energy c ≤
        (angularOffDiagonalEnergy N x c).re := by
    have habs := Complex.abs_re_le_norm (angularOffDiagonalEnergy N x c)
    have hneg :
        -‖angularOffDiagonalEnergy N x c‖ ≤
          (angularOffDiagonalEnergy N x c).re := by
      linarith [neg_le_abs (angularOffDiagonalEnergy N x c).re]
    simpa only [neg_mul] using
      (neg_le_neg hoff).trans hneg
  linarith

/-- The source constant is bounded by the Aubel--Bölcskei constant throughout
the full admissible range of `β`. -/
theorem sourceConstant_le_largeSieveConstant
    {β : ℝ} (hβ : 1 / (2 * Real.log 2) < β) :
    2 - Real.exp (1 / (2 * β)) ≤ 1 - 1 / (2 * β) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβpos : 0 < β :=
    (by positivity : 0 < 1 / (2 * Real.log 2)).trans hβ
  have hexp := Real.add_one_le_exp (1 / (2 * β))
  linarith

private theorem periodicSeparation_of_angularCube
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {δ : ℝ} (x : ι → NumDetect.Point 1)
    (hx : ∀ j, NumDetect.InAngularCube (x j))
    (hsep : ∀ i j, i ≠ j →
      δ < NumDetect.periodicLInfDistance (x i) (x j)) :
    ∀ i j, i ≠ j → ∀ p : ℤ,
      δ < |x i 0 - x j 0 - 2 * Real.pi * p| := by
  intro i j hij p
  have hcoord :
      δ < NumDetect.periodicCoordinateDistance (x i 0) (x j 0) := by
    have hnonneg :
        0 ≤ NumDetect.periodicCoordinateDistance (x i 0) (x j 0) := by
      unfold NumDetect.periodicCoordinateDistance
      have habs : |x i 0 - x j 0| ≤ 2 * Real.pi := by
        rw [abs_le]
        constructor <;>
          linarith [(hx i 0).1, (hx i 0).2, (hx j 0).1, (hx j 0).2]
      exact le_min (abs_nonneg _) (sub_nonneg.2 habs)
    have hfun :
        (fun k : Fin 1 =>
            NumDetect.periodicCoordinateDistance (x i k) (x j k)) =
          fun _ => NumDetect.periodicCoordinateDistance (x i 0) (x j 0) := by
      funext k
      exact congrArg
        (fun k => NumDetect.periodicCoordinateDistance (x i k) (x j k))
        (Fin.eq_zero k)
    simpa [NumDetect.periodicLInfDistance, hfun, Real.norm_eq_abs,
      abs_of_nonneg hnonneg] using hsep i j hij
  exact hcoord.trans_le
    (NumDetect.periodicCoordinateDistance_le_integerTranslate
      (hx i 0) (hx j 0) p)

private theorem fineCubeEnergy_eq_angularSamplingEnergy
    {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (x : ι → NumDetect.Point 1) (v : ι → ℂ) :
    SegmentedVDM.energy (NumDetect.fineCubeEvaluation K x *ᵥ v) =
      ∑ k : Fin (K + 1),
        ‖angularExponentialSum (fun j => x j 0) v k‖ ^ 2 := by
  let e := Equiv.funUnique (Fin 1) (Fin (K + 1))
  unfold SegmentedVDM.energy NumDetect.fineCubeEvaluation Matrix.mulVec
    dotProduct angularExponentialSum
  apply Fintype.sum_equiv e
  intro α
  congr 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro j _
  simp [e, mul_comm]

/-- In dimension one, the periodic Hilbert sine bound supplies the exact
fine-cube frame required by the segmented argument for every admissible
`β`, including `K = 0`. -/
theorem hasFineCubeFrame_oneDimensional
    (hHilbert : HasPeriodicHilbertSineBound)
    (K : ℕ) (β η : ℝ)
    (hβ : 1 / (2 * Real.log 2) < β)
    (hη : 4 * Real.pi * β / (K + 1) ≤ η) :
    NumDetect.HasFineCubeFrame 1 K η
      (2 - Real.exp (1 / (2 * β))) := by
  unfold NumDetect.HasFineCubeFrame
  intro ι _ _ x hx hsep v
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβpos : 0 < β :=
    (by positivity : 0 < 1 / (2 * Real.log 2)).trans hβ
  have hηpos : 0 < η :=
    (show 0 < 4 * Real.pi * β / (K + 1) by positivity).trans_le hη
  have hperiodic :
      ∀ i j, i ≠ j → ∀ p : ℤ,
        η < |x i 0 - x j 0 - 2 * Real.pi * p| :=
    periodicSeparation_of_angularCube x hx hsep
  have hsieve :=
    angular_largeSieve_lower_of_periodicHilbertSineBound
      hHilbert (K + 1) hηpos (fun j => x j 0) hperiodic v
  rw [← fineCubeEnergy_eq_angularSamplingEnergy x v] at hsieve
  have hsource :=
    sourceConstant_le_largeSieveConstant hβ
  have hconstant :
      (2 - Real.exp (1 / (2 * β))) * ((K + 1 : ℕ) : ℝ) ≤
        ((K + 1 : ℕ) : ℝ) - 2 * Real.pi / η := by
    have hNpos : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
    have hgap :
        2 * Real.pi / η ≤ ((K + 1 : ℕ) : ℝ) / (2 * β) := by
      rw [div_le_div_iff₀ hηpos (by positivity : 0 < 2 * β)]
      have hη' :
          4 * Real.pi * β / ((K + 1 : ℕ) : ℝ) ≤ η := by
        simpa only [Nat.cast_add, Nat.cast_one] using hη
      have hh := (div_le_iff₀ hNpos).mp hη'
      nlinarith
    calc
      (2 - Real.exp (1 / (2 * β))) * ((K + 1 : ℕ) : ℝ)
          ≤ (1 - 1 / (2 * β)) * ((K + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hsource hNpos.le
      _ ≤ ((K + 1 : ℕ) : ℝ) - 2 * Real.pi / η := by
            calc
              (1 - 1 / (2 * β)) * ((K + 1 : ℕ) : ℝ) =
                  ((K + 1 : ℕ) : ℝ) - ((K + 1 : ℕ) : ℝ) / (2 * β) := by ring
              _ ≤ _ := sub_le_sub_left hgap _
  have henergy := SegmentedVDM.energy_nonneg v
  simpa only [pow_one] using
    (mul_le_mul_of_nonneg_right hconstant henergy).trans hsieve

end

end OneDimensionalFineCubeFrame
end LeanNumDetect
