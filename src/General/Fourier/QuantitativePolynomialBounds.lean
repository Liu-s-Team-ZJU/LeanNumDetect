import General.Fourier.SharpPolynomialEvaluation

/-! Explicit coefficient-to-energy constants on the unit interval. The
constants are finite weighted Legendre sums, with no norm-equivalence choice. -/
set_option autoImplicit false
open scoped Polynomial BigOperators
open Set MeasureTheory
namespace LeanNumDetect.PolynomialEvaluationBounds
noncomputable section

def jetCoefficientEnergyRowSq (s j : ℕ) : ℝ :=
  (j.factorial : ℝ)^2 * ∑ r ∈ Finset.range s,
    (2*(r : ℝ)+1)*((realShiftedLegendre r).coeff j)^2

def jetCoefficientEnergySq (s : ℕ) : ℝ :=
  (Finset.range (s+1)).sup' ⟨0, by simp⟩ (jetCoefficientEnergyRowSq s)

def jetCoefficientEnergyConstant (s : ℕ) : ℝ := Real.sqrt (jetCoefficientEnergySq s)

/-- The coefficient constant is the explicit finite binomial maximum.
The extra row `j = s` vanishes and permits a nonempty maximum also at `s = 0`. -/
theorem jetCoefficientEnergySq_eq_binomial_max (s : ℕ) :
    jetCoefficientEnergySq s =
      (Finset.range (s + 1)).sup' ⟨0, by simp⟩ (fun j =>
        (j.factorial : ℝ)^2 * ∑ r ∈ Finset.range s,
          (2*(r : ℝ)+1)*(r.choose j : ℝ)^2*((r+j).choose r : ℝ)^2) := by
  have hrow (j : ℕ) : jetCoefficientEnergyRowSq s j =
      (j.factorial : ℝ)^2 * ∑ r ∈ Finset.range s,
        (2*(r : ℝ)+1)*(r.choose j : ℝ)^2*((r+j).choose r : ℝ)^2 := by
    unfold jetCoefficientEnergyRowSq
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [realShiftedLegendre_coeff, mul_pow, mul_pow]
    have hsign : ((-1 : ℝ)^j)^2 = 1 := by
      rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
      simp
    rw [hsign]
    ring
  unfold jetCoefficientEnergySq
  simp_rw [hrow]

def legendreCoefficientMass (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (r+1), |(realShiftedLegendre r).coeff j|

def monomialCoefficientEnergySq (s : ℕ) : ℝ :=
  ∑ r ∈ Finset.range s, (2*(r : ℝ)+1)*(legendreCoefficientMass r)^2

def monomialCoefficientEnergyConstant (s : ℕ) : ℝ :=
  Real.sqrt (monomialCoefficientEnergySq s)

theorem jetCoefficientEnergyRowSq_nonneg (s j : ℕ) : 0 ≤ jetCoefficientEnergyRowSq s j := by
  unfold jetCoefficientEnergyRowSq
  positivity

theorem jetCoefficientEnergySq_nonneg (s : ℕ) : 0 ≤ jetCoefficientEnergySq s :=
  (jetCoefficientEnergyRowSq_nonneg s 0).trans
    (Finset.le_sup' (jetCoefficientEnergyRowSq s) (by simp : 0 ∈ Finset.range (s+1)))

theorem jetCoefficientEnergyConstant_nonneg (s : ℕ) : 0 ≤ jetCoefficientEnergyConstant s :=
  Real.sqrt_nonneg _

theorem legendreCoefficientMass_nonneg (r : ℕ) : 0 ≤ legendreCoefficientMass r := by
  unfold legendreCoefficientMass
  positivity

theorem monomialCoefficientEnergySq_nonneg (s : ℕ) : 0 ≤ monomialCoefficientEnergySq s := by
  unfold monomialCoefficientEnergySq
  positivity

theorem monomialCoefficientEnergyConstant_nonneg (s : ℕ) :
    0 ≤ monomialCoefficientEnergyConstant s := Real.sqrt_nonneg _

theorem jetCoefficientEnergyRowSq_mono (j : ℕ) : Monotone (fun s => jetCoefficientEnergyRowSq s j) := by
  intro s t hst
  unfold jetCoefficientEnergyRowSq
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hst)
    (fun r _ _ => by positivity)

theorem jetCoefficientEnergySq_mono : Monotone jetCoefficientEnergySq := by
  intro s t hst
  unfold jetCoefficientEnergySq
  apply Finset.sup'_le
  intro j hj
  exact ((jetCoefficientEnergyRowSq_mono j) hst).trans
    (Finset.le_sup' (jetCoefficientEnergyRowSq t)
      (Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le (by omega))))

theorem jetCoefficientEnergyConstant_mono : Monotone jetCoefficientEnergyConstant := by
  intro s t hst
  exact Real.sqrt_le_sqrt (jetCoefficientEnergySq_mono hst)

theorem monomialCoefficientEnergySq_mono : Monotone monomialCoefficientEnergySq := by
  intro s t hst
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hst)
    (fun r _ _ => by positivity)

theorem monomialCoefficientEnergyConstant_mono : Monotone monomialCoefficientEnergyConstant := by
  intro s t hst
  exact Real.sqrt_le_sqrt (monomialCoefficientEnergySq_mono hst)

theorem realLegendreSum_energy {s : ℕ} (a : Fin s → ℝ) :
    (∫ t in (0 : ℝ)..1, (∑ i : Fin s, a i*(realShiftedLegendre i.val).eval t)^2) =
      ∑ i : Fin s, (a i)^2/(2*(i.val : ℝ)+1) := by
  let P : ℝ[X] := ∑ i : Fin s, a i • realShiftedLegendre i.val
  have heval (t : ℝ) : P.eval t = ∑ i : Fin s, a i*(realShiftedLegendre i.val).eval t := by
    simp [P, Polynomial.eval_finsetSum]
  have hp (i j : Fin s) : legendreIntegralPair i.val (realShiftedLegendre j.val) =
      if i=j then 1/(2*(i.val : ℝ)+1) else 0 := by
    by_cases hij : i=j
    · subst j
      rw [if_pos rfl]
      change (∫ t in (0 : ℝ)..1,
        (realShiftedLegendre i.val).eval t*(realShiftedLegendre i.val).eval t)=_
      simpa only [pow_two] using realShiftedLegendre_sq_integral i.val
    · rw [if_neg hij]
      exact realShiftedLegendre_orthogonal (by intro h; exact hij (Fin.ext h))
  have hpair (i : Fin s) : legendreIntegralPair i.val P = a i/(2*(i.val : ℝ)+1) := by
    simp only [P, map_sum, map_smul, smul_eq_mul]
    simp_rw [hp i]
    simp [div_eq_mul_inv]
  have hf : (fun t : ℝ => (P.eval t)^2) =
      (fun t => ∑ i : Fin s, a i*((realShiftedLegendre i.val).eval t*P.eval t)) := by
    funext t
    nth_rw 1 [pow_two, heval t]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [show (fun t : ℝ => (∑ i : Fin s, a i*(realShiftedLegendre i.val).eval t)^2) =
    (fun t => (P.eval t)^2) by funext t; rw [heval], hf,
    intervalIntegral.integral_finsetSum
      (fun i _ => (show Continuous (fun t : ℝ =>
        a i*((realShiftedLegendre i.val).eval t*P.eval t)) from
          continuous_const.mul ((realShiftedLegendre i.val).continuous.mul P.continuous)).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_const_mul]
  change a i*legendreIntegralPair i.val P=_
  rw [hpair i]
  ring

def complexLegendreSignal {s : ℕ} (a : Fin s → ℂ) (t : ℝ) : ℂ :=
  ∑ i : Fin s, a i*Complex.ofReal ((realShiftedLegendre i.val).eval t)

theorem complexLegendreSignal_energy {s : ℕ} (a : Fin s → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖complexLegendreSignal a t‖^2) =
      ∑ i : Fin s, ‖a i‖^2/(2*(i.val : ℝ)+1) := by
  have hr (t : ℝ) : (complexLegendreSignal a t).re =
      ∑ i : Fin s, (a i).re*(realShiftedLegendre i.val).eval t := by
    simp [complexLegendreSignal, Complex.mul_re]
  have hi (t : ℝ) : (complexLegendreSignal a t).im =
      ∑ i : Fin s, (a i).im*(realShiftedLegendre i.val).eval t := by
    simp [complexLegendreSignal, Complex.mul_im]
  have hn (t : ℝ) : ‖complexLegendreSignal a t‖^2 =
      (∑ i : Fin s, (a i).re*(realShiftedLegendre i.val).eval t)^2+
      (∑ i : Fin s, (a i).im*(realShiftedLegendre i.val).eval t)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hr, hi]
    ring
  simp_rw [hn]
  rw [intervalIntegral.integral_add
    (show IntervalIntegrable (fun t : ℝ =>
      (∑ i : Fin s, (a i).re*(realShiftedLegendre i.val).eval t)^2) volume 0 1 from
      (by fun_prop : Continuous (fun t : ℝ =>
        (∑ i : Fin s, (a i).re*(realShiftedLegendre i.val).eval t)^2)).intervalIntegrable _ _)
    (show IntervalIntegrable (fun t : ℝ =>
      (∑ i : Fin s, (a i).im*(realShiftedLegendre i.val).eval t)^2) volume 0 1 from
      (by fun_prop : Continuous (fun t : ℝ =>
        (∑ i : Fin s, (a i).im*(realShiftedLegendre i.val).eval t)^2)).intervalIntegrable _ _),
    realLegendreSum_energy, realLegendreSum_energy, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem coefficientPolynomial_legendre_expansion {s : ℕ} (hs : 0<s) (a : Fin s → ℂ) :
    ∃ c : Fin s → ℂ,
      (∀ t : ℝ, coefficientPolynomialSignal a t=complexLegendreSignal c t) ∧
      (∀ j : Fin s, a j=∑ r : Fin s, c r*Complex.ofReal ((realShiftedLegendre r.val).coeff j.val)) := by
  have hR := realShiftedLegendre_expansion (realCoefficientPolynomial a)
    (coefficientPolynomial_natDegree_le hs (fun j => (a j).re))
  have hI := realShiftedLegendre_expansion (imaginaryCoefficientPolynomial a)
    (coefficientPolynomial_natDegree_le hs (fun j => (a j).im))
  rw [Nat.sub_add_cancel (show 1≤s from hs)] at hR hI
  obtain ⟨b, hb⟩ := hR
  obtain ⟨d, hd⟩ := hI
  let c : Fin s → ℂ := fun r => Complex.ofReal (b r)+Complex.I*Complex.ofReal (d r)
  refine ⟨c, ?_, ?_⟩
  · intro t
    rw [coefficientPolynomialSignal_eq]
    apply Complex.ext
    · have h := congrArg (Polynomial.eval t) hb
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_smul, smul_eq_mul] at h
      simpa [complexPolynomialSignal, complexLegendreSignal, c, Complex.mul_re] using h.symm
    · have h := congrArg (Polynomial.eval t) hd
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_smul, smul_eq_mul] at h
      simpa [complexPolynomialSignal, complexLegendreSignal, c, Complex.mul_im] using h.symm
  · intro j
    apply Complex.ext
    · have h := congrArg (fun P : ℝ[X] => P.coeff j.val) hb
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul, smul_eq_mul] at h
      have hj : (realCoefficientPolynomial a).coeff j.val=(a j).re := by
        simp [realCoefficientPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
          ← Fin.ext_iff]
      rw [hj] at h
      simpa [c, Complex.mul_re] using h.symm
    · have h := congrArg (fun P : ℝ[X] => P.coeff j.val) hd
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul, smul_eq_mul] at h
      have hj : (imaginaryCoefficientPolynomial a).coeff j.val=(a j).im := by
        simp [imaginaryCoefficientPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
          ← Fin.ext_iff]
      rw [hj] at h
      simpa [c, Complex.mul_im] using h.symm

theorem complex_weighted_sum_norm_sq_le {s : ℕ} (a : Fin s → ℂ) (v w : Fin s → ℝ)
    (hw : ∀ i, 0<w i) :
    ‖∑ i : Fin s, a i*Complex.ofReal (v i)‖^2 ≤
      (∑ i : Fin s, ‖a i‖^2/w i)*(∑ i : Fin s, w i*(v i)^2) := by
  have hn : ‖∑ i : Fin s, a i*Complex.ofReal (v i)‖ ≤
      ∑ i : Fin s, ‖a i‖*|v i| := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      norm_sum_le (f := fun i : Fin s => a i*Complex.ofReal (v i)) Finset.univ
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i : Fin s => ‖a i‖*|v i|)
    (f := fun i : Fin s => ‖a i‖^2/w i)
    (g := fun i : Fin s => w i*(v i)^2)
    (fun i _ => div_nonneg (sq_nonneg _) (hw i).le)
    (fun i _ => mul_nonneg (hw i).le (sq_nonneg _))
    (fun i _ => by
      apply le_of_eq
      rw [mul_pow, sq_abs]
      field_simp [(hw i).ne'])
  exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ =>
    mul_nonneg (norm_nonneg _) (abs_nonneg _)))).2 hn).trans hs

theorem legendreCoefficientMass_eq_binomial_sum (r : ℕ) :
    legendreCoefficientMass r = ∑ j ∈ Finset.range (r+1),
      (r.choose j : ℝ)*((r+j).choose r : ℝ) := by
  unfold legendreCoefficientMass
  apply Finset.sum_congr rfl
  intro j _
  rw [realShiftedLegendre_coeff, abs_mul, abs_mul, abs_pow]
  simp

theorem legendreCoefficientMass_sum_eq {s : ℕ} (r : Fin s) :
    (∑ j : Fin s, |(realShiftedLegendre r.val).coeff j.val|)=legendreCoefficientMass r.val := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => |(realShiftedLegendre r.val).coeff j|)]
  unfold legendreCoefficientMass
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt r.isLt))
  intro j _ hj
  have h : r.val<j := Nat.lt_of_succ_le (by simpa only [Finset.mem_range, not_lt] using hj)
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using h), abs_zero]

theorem jetPolynomial_coefficient_norm_le_energy_explicit {s : ℕ} (hs : 0<s)
    (a : Fin s → ℂ) :
    ‖a‖ ≤ jetCoefficientEnergyConstant s *
      Real.sqrt (∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2) := by
  let b : Fin s → ℂ := fun j => a j/(j.val.factorial : ℂ)
  obtain ⟨c, hf, hc⟩ := coefficientPolynomial_legendre_expansion hs b
  have hfun : jetPolynomialSignal a=complexLegendreSignal c := by
    funext t
    rw [jetPolynomialSignal_eq_coefficientPolynomialSignal]
    exact hf t
  let E : ℝ := ∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2
  have hE : E=∑ r : Fin s, ‖c r‖^2/(2*(r.val : ℝ)+1) := by
    dsimp [E]
    rw [hfun]
    exact complexLegendreSignal_energy c
  have hE0 : 0≤E := by rw [hE]; positivity
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (jetCoefficientEnergyConstant_nonneg s)
    (Real.sqrt_nonneg E))).2
  intro j
  have hcs := complex_weighted_sum_norm_sq_le c
    (fun r => (realShiftedLegendre r.val).coeff j.val)
    (fun r => 2*(r.val : ℝ)+1) (fun r => by positivity)
  rw [← hc j, ← hE] at hcs
  have hjfac : (j.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j.val
  have he : a j=(j.val.factorial : ℂ)*b j := by dsimp [b]; field_simp
  have hsquare : ‖a j‖^2 ≤ jetCoefficientEnergySq s*E := by
    calc
      _ = (j.val.factorial : ℝ)^2*‖b j‖^2 := by
        rw [he, norm_mul, Complex.norm_natCast, mul_pow]
      _ ≤ (j.val.factorial : ℝ)^2*(E*(∑ r : Fin s,
          (2*(r.val : ℝ)+1)*((realShiftedLegendre r.val).coeff j.val)^2)) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = jetCoefficientEnergyRowSq s j.val*E := by
        rw [Fin.sum_univ_eq_sum_range (fun r : ℕ =>
          (2*(r : ℝ)+1)*((realShiftedLegendre r).coeff j.val)^2)]
        unfold jetCoefficientEnergyRowSq
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Finset.le_sup' (jetCoefficientEnergyRowSq s)
          (by simp only [Finset.mem_range]; omega : j.val∈Finset.range (s+1))) hE0
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (jetCoefficientEnergyConstant_nonneg s)
    (Real.sqrt_nonneg E))).1
  rw [mul_pow, jetCoefficientEnergyConstant,
    Real.sq_sqrt (jetCoefficientEnergySq_nonneg s), Real.sq_sqrt hE0]
  exact hsquare

theorem coefficientPolynomial_monomial_mass_le_energy_explicit {s : ℕ} (hs : 0<s)
    (a : Fin s → ℂ) :
    (∑ j : Fin s, ‖a j‖) ≤ monomialCoefficientEnergyConstant s *
      Real.sqrt (∫ t in (0 : ℝ)..1, ‖coefficientPolynomialSignal a t‖^2) := by
  obtain ⟨c, hf, hc⟩ := coefficientPolynomial_legendre_expansion hs a
  let E : ℝ := ∫ t in (0 : ℝ)..1, ‖coefficientPolynomialSignal a t‖^2
  have hE : E=∑ r : Fin s, ‖c r‖^2/(2*(r.val : ℝ)+1) := by
    dsimp [E]
    simp_rw [hf]
    exact complexLegendreSignal_energy c
  have hE0 : 0≤E := by rw [hE]; positivity
  have hmass : (∑ j : Fin s, ‖a j‖) ≤
      ∑ r : Fin s, ‖c r‖*legendreCoefficientMass r.val := by
    calc
      _ ≤ ∑ j : Fin s, ∑ r : Fin s, ‖c r‖*|(realShiftedLegendre r.val).coeff j.val| := by
        apply Finset.sum_le_sum
        intro j _
        rw [hc j]
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
          norm_sum_le (f := fun r : Fin s => c r*Complex.ofReal ((realShiftedLegendre r.val).coeff j.val)) Finset.univ
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        rw [← Finset.mul_sum, legendreCoefficientMass_sum_eq r]
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun r : Fin s => ‖c r‖*legendreCoefficientMass r.val)
    (f := fun r : Fin s => ‖c r‖^2/(2*(r.val : ℝ)+1))
    (g := fun r : Fin s => (2*(r.val : ℝ)+1)*(legendreCoefficientMass r.val)^2)
    (fun r _ => by positivity) (fun r _ => by positivity)
    (fun r _ => by
      apply le_of_eq
      rw [mul_pow]
      field_simp [show (2*(r.val : ℝ)+1)≠0 by positivity])
  rw [← hE, Fin.sum_univ_eq_sum_range (fun r : ℕ =>
    (2*(r : ℝ)+1)*(legendreCoefficientMass r)^2)] at hcs
  change (∑ r : Fin s, ‖c r‖*legendreCoefficientMass r.val)^2 ≤
    E*monomialCoefficientEnergySq s at hcs
  apply hmass.trans
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun r _ =>
    mul_nonneg (norm_nonneg _) (legendreCoefficientMass_nonneg r.val)))
    (mul_nonneg (monomialCoefficientEnergyConstant_nonneg s) (Real.sqrt_nonneg E))).1
  rw [mul_pow, monomialCoefficientEnergyConstant,
    Real.sq_sqrt (monomialCoefficientEnergySq_nonneg s), Real.sq_sqrt hE0]
  exact hcs.trans_eq (by ring)

theorem jetPolynomial_monomial_mass_le_energy_explicit {s : ℕ} (hs : 0<s)
    (a : Fin s → ℂ) :
    (∑ j : Fin s, ‖a j/(j.val.factorial : ℂ)‖) ≤ monomialCoefficientEnergyConstant s *
      Real.sqrt (∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2) := by
  rw [jetPolynomialSignal_eq_coefficientPolynomialSignal]
  exact coefficientPolynomial_monomial_mass_le_energy_explicit hs _

@[simp] theorem jetCoefficientEnergyConstant_zero : jetCoefficientEnergyConstant 0=0 := by
  simp [jetCoefficientEnergyConstant, jetCoefficientEnergySq, jetCoefficientEnergyRowSq]

@[simp] theorem monomialCoefficientEnergyConstant_zero : monomialCoefficientEnergyConstant 0=0 := by
  simp [monomialCoefficientEnergyConstant, monomialCoefficientEnergySq]

@[simp] theorem jetCoefficientEnergyConstant_one : jetCoefficientEnergyConstant 1=1 := by
  have hsq : jetCoefficientEnergySq 1=1 := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro j hj
      have hj' : j=0 ∨ j=1 := by simp only [Finset.mem_range] at hj; omega
      rcases hj' with rfl | rfl <;>
        norm_num [jetCoefficientEnergyRowSq, realShiftedLegendre_coeff]
    · have h := Finset.le_sup' (jetCoefficientEnergyRowSq 1)
        (by simp : 0∈Finset.range (1+1))
      have hz : jetCoefficientEnergyRowSq 1 0=1 := by
        norm_num [jetCoefficientEnergyRowSq, realShiftedLegendre_coeff]
      exact hz.symm.le.trans h
  simp [jetCoefficientEnergyConstant, hsq]

@[simp] theorem monomialCoefficientEnergyConstant_one : monomialCoefficientEnergyConstant 1=1 := by
  norm_num [monomialCoefficientEnergyConstant, monomialCoefficientEnergySq, legendreCoefficientMass,
    realShiftedLegendre_coeff]

theorem jetCoefficientEnergyConstant_ge_one {s : ℕ} (hs : 0<s) :
    1≤jetCoefficientEnergyConstant s := by
  simpa using jetCoefficientEnergyConstant_mono (show 1≤s from hs)

theorem monomialCoefficientEnergyConstant_ge_one {s : ℕ} (hs : 0<s) :
    1≤monomialCoefficientEnergyConstant s := by
  simpa using monomialCoefficientEnergyConstant_mono (show 1≤s from hs)

theorem jetCoefficientEnergyConstant_pos {s : ℕ} (hs : 0<s) :
    0<jetCoefficientEnergyConstant s := zero_lt_one.trans_le (jetCoefficientEnergyConstant_ge_one hs)

theorem monomialCoefficientEnergyConstant_pos {s : ℕ} (hs : 0<s) :
    0<monomialCoefficientEnergyConstant s := zero_lt_one.trans_le (monomialCoefficientEnergyConstant_ge_one hs)

end
end LeanNumDetect.PolynomialEvaluationBounds
