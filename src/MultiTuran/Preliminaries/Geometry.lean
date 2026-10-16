import General.Fourier.PolynomialCrossCorrelation
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Angular geometry for multidimensional segmented Vandermonde matrices

The definitions below use genuine quotient distances.  In particular the
coordinate distance is the minimum of all integral winding distances, including
for representatives outside the principal angular cube.  Manuscript
correspondence: `eq:torus-distance`, `eq:separation-diameter` and the no-wrap
argument in `lem:sv-md-array`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran
noncomputable section

abbrev Point (d : ℕ) := Fin d → ℝ

/-- The manuscript exponential sum, with angular frequencies and no Fourier
normalization factor. -/
def exponentialSum {d n : ℕ} (Y : Fin n → Point d) (c : Fin n → ℂ)
    (t : Point d) : ℂ :=
  ∑ j, c j * Complex.exp (Complex.I * ((∑ q, t q * Y j q : ℝ) : ℂ))

/-- The generalized Vandermonde matrix for an arbitrary ordered frequency
family, using the article's angular exponential convention. -/
def vandermondeMatrix {ι : Type*} {d n : ℕ} (frequency : ι → Point d)
    (Y : Fin n → Point d) : Matrix ι (Fin n) ℂ :=
  fun k j => Complex.exp (Complex.I * ((∑ q, frequency k q * Y j q : ℝ) : ℂ))

/-- Angular distance modulo `2π` in one coordinate. -/
def torusCoordinateDistance (x y : ℝ) : ℝ :=
  ‖((x - y : ℝ) : AddCircle (2 * Real.pi))‖

/-- The angular torus `ℓ∞` distance. -/
def torusLInfDistance {d : ℕ} (x y : Point d) : ℝ :=
  ‖fun q => torusCoordinateDistance (x q) (y q)‖

/-- The minimum angular torus separation of the ordered nodes. -/
def nodeSeparation {d n : ℕ} (Y : Fin n → Point d) : ℝ :=
  sInf {a : ℝ | ∃ i j, i ≠ j ∧ a = torusLInfDistance (Y i) (Y j)}

/-- The maximum angular torus distance between two nodes. -/
def nodeDiameter {d n : ℕ} (Y : Fin n → Point d) : ℝ :=
  sSup (Set.range fun ij : Fin n × Fin n => torusLInfDistance (Y ij.1) (Y ij.2))

/-- Membership in the closed coordinate cube of radius `r`. -/
def InCube {d : ℕ} (r : ℝ) (center x : Point d) : Prop :=
  ∀ q, |x q - center q| ≤ r

/-- Membership in the manuscript's open cube `Qᵈ_r(center)`, defined by the
strict `ℓ∞` norm inequality in `eq:torus-distance`'s surrounding notation. -/
def InOpenCube {d : ℕ} (r : ℝ) (center x : Point d) : Prop :=
  ‖x - center‖ < r

theorem InOpenCube.coordinate_lt {d : ℕ} {r : ℝ} {center x : Point d}
    (h : InOpenCube r center x) (q : Fin d) : |x q - center q| < r := by
  have hq := norm_le_pi_norm (x - center) q
  rw [Real.norm_eq_abs] at hq
  exact hq.trans_lt h

theorem InOpenCube.inCube {d : ℕ} {r : ℝ} {center x : Point d}
    (h : InOpenCube r center x) : InCube r center x :=
  fun q => (h.coordinate_lt q).le

@[simp] theorem torusCoordinateDistance_nonneg (x y : ℝ) :
    0 ≤ torusCoordinateDistance x y := norm_nonneg _

@[simp] theorem torusLInfDistance_nonneg {d : ℕ} (x y : Point d) :
    0 ≤ torusLInfDistance x y := norm_nonneg _

/-- Quotient distance never exceeds a distance between representatives. -/
theorem torusCoordinateDistance_le_abs (x y : ℝ) :
    torusCoordinateDistance x y ≤ |x - y| := by
  exact QuotientAddGroup.norm_mk_le_norm

/-- Every winding distance bounds the quotient distance from above. -/
theorem torusCoordinateDistance_le_winding (x y : ℝ) (p : ℤ) :
    torusCoordinateDistance x y ≤ |x - y - 2 * Real.pi * p| := by
  have he : ((x - y - 2 * Real.pi * p : ℝ) : AddCircle (2 * Real.pi)) =
      ((x - y : ℝ) : AddCircle (2 * Real.pi)) := by
    rw [AddCircle.coe_sub]
    have hz : ((2 * Real.pi * p : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
      rw [mul_comm (2 * Real.pi), ← zsmul_eq_mul, AddCircle.coe_zsmul,
        AddCircle.coe_period, smul_zero]
    rw [hz, sub_zero]
  simpa only [he, Real.norm_eq_abs, torusCoordinateDistance] using
    (QuotientAddGroup.norm_mk_le_norm (m := x - y - 2 * Real.pi * p)
      (S := AddSubgroup.zmultiples (2 * Real.pi)))

/-- The infimum in the manuscript definition is attained by a winding. -/
theorem exists_winding_eq_torusCoordinateDistance (x y : ℝ) :
    ∃ p : ℤ, torusCoordinateDistance x y = |x - y - 2 * Real.pi * p| := by
  refine ⟨round ((2 * Real.pi)⁻¹ * (x - y)), ?_⟩
  unfold torusCoordinateDistance
  rw [AddCircle.norm_eq]
  congr 1
  ring

theorem nodeSeparation_le_pair {d n : ℕ} (Y : Fin n → Point d)
    (i j : Fin n) (hij : i ≠ j) :
    nodeSeparation Y ≤ torusLInfDistance (Y i) (Y j) := by
  apply csInf_le
  · exact ⟨0, by rintro a ⟨i,j,_,rfl⟩; exact norm_nonneg _⟩
  · exact ⟨i,j,hij,rfl⟩

theorem nodeSeparation_nonneg {d n : ℕ} (Y : Fin n → Point d) :
    0 ≤ nodeSeparation Y := by
  apply Real.sInf_nonneg
  rintro a ⟨i,j,_,rfl⟩
  exact norm_nonneg _

/-- A coordinate realizes the `ℓ∞` quotient distance. -/
theorem exists_coordinate_eq_torusLInfDistance {d : ℕ} (hd : 0 < d)
    (x y : Point d) :
    ∃ q, torusLInfDistance x y = torusCoordinateDistance (x q) (y q) := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  obtain ⟨q, _, hq⟩ := Finset.exists_max_image Finset.univ
    (fun q => torusCoordinateDistance (x q) (y q)) Finset.univ_nonempty
  refine ⟨q, le_antisymm ?_ ?_⟩
  · apply (pi_norm_le_iff_of_nonneg (torusCoordinateDistance_nonneg _ _)).2
    intro r
    rw [Real.norm_eq_abs, abs_of_nonneg (torusCoordinateDistance_nonneg _ _)]
    exact hq r (Finset.mem_univ r)
  · simpa only [torusLInfDistance, Real.norm_eq_abs,
      abs_of_nonneg (torusCoordinateDistance_nonneg _ _)] using
      (norm_le_pi_norm (fun q => torusCoordinateDistance (x q) (y q)) q)

/-- The chord bound in the angular normalization used by the manuscript. -/
theorem coordinate_chord_lower (x y : ℝ) :
    (2 / Real.pi) * torusCoordinateDistance x y ≤
      ‖Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ))‖ := by
  have h := PolynomialCrossCorrelation.periodic_chord_lower (x - y)
    (torusCoordinateDistance x y) (torusCoordinateDistance_le_winding x y)
  have he : Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ)) =
      (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) *
        Complex.exp (Complex.I * (y : ℂ)) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  exact h

/-- For each pair, some coordinate has the elementary separated chord used by
the full-cube interpolation argument. -/
theorem exists_coordinate_chord_lower {d n : ℕ} (hd : 0 < d)
    (Y : Fin n → Point d) (i j : Fin n) (hij : i ≠ j) :
    ∃ q, (2 / Real.pi) * nodeSeparation Y ≤
      ‖Complex.exp (Complex.I * (Y i q : ℂ)) -
        Complex.exp (Complex.I * (Y j q : ℂ))‖ := by
  obtain ⟨q,hq⟩ := exists_coordinate_eq_torusLInfDistance hd (Y i) (Y j)
  refine ⟨q, ?_⟩
  calc
    (2 / Real.pi) * nodeSeparation Y ≤
        (2 / Real.pi) * torusLInfDistance (Y i) (Y j) :=
      mul_le_mul_of_nonneg_left (nodeSeparation_le_pair Y i j hij) (by positivity)
    _ = (2 / Real.pi) * torusCoordinateDistance (Y i q) (Y j q) := by rw [hq]
    _ ≤ _ := coordinate_chord_lower _ _

/-- Multiplication by an integer scales a short angular gap exactly. -/
theorem torusCoordinateDistance_mul_nat (M : ℕ) (x y : ℝ)
    (hshort : (M : ℝ) * torusCoordinateDistance x y ≤ Real.pi) :
    torusCoordinateDistance ((M : ℝ) * x) ((M : ℝ) * y) =
      (M : ℝ) * torusCoordinateDistance x y := by
  obtain ⟨p,hp⟩ := exists_winding_eq_torusCoordinateDistance x y
  let a := x - y - 2 * Real.pi * p
  have ha : |(M : ℝ) * a| ≤ |2 * Real.pi| / 2 := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg M), ← hp]
    simpa [abs_of_pos (by positivity : 0 < 2 * Real.pi)] using hshort
  have he : ((((M : ℝ) * a : ℝ)) : AddCircle (2 * Real.pi)) =
      ((((M : ℝ) * x - (M : ℝ) * y : ℝ)) : AddCircle (2 * Real.pi)) := by
    have hrewrite : (M : ℝ) * a = (M : ℝ) * x - (M : ℝ) * y -
        (((M : ℤ) * p : ℤ) : ℝ) * (2 * Real.pi) := by
      dsimp [a]
      push_cast
      ring
    rw [hrewrite, AddCircle.coe_sub, ← zsmul_eq_mul, AddCircle.coe_zsmul,
      AddCircle.coe_period, smul_zero, sub_zero]
  change ‖((((M : ℝ) * x - (M : ℝ) * y : ℝ)) : AddCircle (2 * Real.pi))‖ = _
  rw [← he, (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi)
      (by positivity : 2 * Real.pi ≠ 0)).2 ha,
    abs_mul, abs_of_nonneg (Nat.cast_nonneg M)]
  exact congrArg ((M : ℝ) * ·) hp.symm

/-- The no-wrap condition scales the entire angular `ℓ∞` distance exactly. -/
theorem torusLInfDistance_mul_nat {d : ℕ} (M : ℕ) (x y : Point d)
    (hshort : (M : ℝ) * torusLInfDistance x y ≤ Real.pi) :
    torusLInfDistance (fun q => (M : ℝ) * x q) (fun q => (M : ℝ) * y q) =
      (M : ℝ) * torusLInfDistance x y := by
  have he (q : Fin d) :
      torusCoordinateDistance ((M : ℝ) * x q) ((M : ℝ) * y q) =
        (M : ℝ) * torusCoordinateDistance (x q) (y q) := by
    apply torusCoordinateDistance_mul_nat
    apply le_trans _ hshort
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg M)
    simpa only [torusLInfDistance, Real.norm_eq_abs,
      abs_of_nonneg (torusCoordinateDistance_nonneg _ _)] using
      norm_le_pi_norm (fun q => torusCoordinateDistance (x q) (y q)) q
  unfold torusLInfDistance
  simp_rw [he]
  change ‖(M : ℝ) • (fun q => torusCoordinateDistance (x q) (y q))‖ = _
  rw [norm_smul, Real.norm_natCast]

theorem pair_le_nodeDiameter {d n : ℕ} (Y : Fin n → Point d) (i j : Fin n) :
    torusLInfDistance (Y i) (Y j) ≤ nodeDiameter Y := by
  apply le_csSup
  · exact (Set.finite_range _).bddAbove
  · exact ⟨(i,j),rfl⟩

/-- Minimum separation scales exactly when multiplication by `M` causes no
wrapping of any pairwise angular distance. -/
theorem nodeSeparation_mul_nat {d n : ℕ} (M : ℕ) (Y : Fin n → Point d)
    (hshort : (M : ℝ) * nodeDiameter Y ≤ Real.pi) :
    nodeSeparation (fun j q => (M : ℝ) * Y j q) = (M : ℝ) * nodeSeparation Y := by
  classical
  have hpair (i j : Fin n) :
      torusLInfDistance (fun q => (M : ℝ) * Y i q) (fun q => (M : ℝ) * Y j q) =
        (M : ℝ) * torusLInfDistance (Y i) (Y j) := by
    apply torusLInfDistance_mul_nat
    exact (mul_le_mul_of_nonneg_left (pair_le_nodeDiameter Y i j)
      (Nat.cast_nonneg M)).trans hshort
  by_cases hn : 2 ≤ n
  · let S := {a : ℝ | ∃ i j : Fin n, i ≠ j ∧ a = torusLInfDistance (Y i) (Y j)}
    have hS : S.Finite := by
      apply (Set.finite_range (fun ij : Fin n × Fin n =>
        torusLInfDistance (Y ij.1) (Y ij.2))).subset
      rintro a ⟨i,j,_,rfl⟩
      exact ⟨(i,j),rfl⟩
    have hne : S.Nonempty := by
      refine ⟨_,⟨⟨0,by omega⟩,⟨1,by omega⟩,?_,rfl⟩⟩
      intro h
      exact Nat.zero_ne_one (by simpa only [Fin.mk.injEq] using h)
    obtain ⟨i,j,hij,hmin⟩ := hne.csInf_mem hS
    change nodeSeparation Y = torusLInfDistance (Y i) (Y j) at hmin
    apply le_antisymm
    · calc
        nodeSeparation (fun j q => (M : ℝ) * Y j q) ≤
            torusLInfDistance (fun q => (M : ℝ) * Y i q)
              (fun q => (M : ℝ) * Y j q) := nodeSeparation_le_pair _ _ _ hij
        _ = (M : ℝ) * nodeSeparation Y := by rw [hpair, hmin]
    · apply le_csInf
      · exact ⟨_,⟨i,j,hij,rfl⟩⟩
      · rintro a ⟨i',j',hij',rfl⟩
        rw [hpair]
        exact mul_le_mul_of_nonneg_left (nodeSeparation_le_pair Y i' j' hij')
          (Nat.cast_nonneg M)
  · have hsub : Subsingleton (Fin n) := by
      apply Fin.subsingleton_iff_le_one.mpr
      omega
    have hempty (Z : Fin n → Point d) :
        {a : ℝ | ∃ i j, i ≠ j ∧ a = torusLInfDistance (Z i) (Z j)} = ∅ := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists,
        not_and]
      intro i j hij
      exact (hij (hsub.elim i j)).elim
    simp [nodeSeparation, hempty]

/-- A common enclosing cube bounds the torus diameter by twice its radius. -/
theorem nodeDiameter_le_of_cube {d n : ℕ} (Y : Fin n → Point d)
    (center : Point d) {r : ℝ} (hr : 0 ≤ r) (hY : ∀ j, InCube r center (Y j)) :
    nodeDiameter Y ≤ 2 * r := by
  apply Real.sSup_le
  · rintro a ⟨⟨i,j⟩,rfl⟩
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*r)).2
    intro q
    rw [Real.norm_eq_abs, abs_of_nonneg (torusCoordinateDistance_nonneg _ _)]
    refine (torusCoordinateDistance_le_abs _ _).trans ?_
    have h := abs_sub (Y i q - center q) (Y j q - center q)
    have he : (Y i q - center q) - (Y j q - center q) = Y i q - Y j q := by ring
    rw [he] at h
    linarith [hY i q, hY j q]
  · positivity

/-- The localized angular cube in `lem:sv-md-array` implies its no-wrap
condition at `M₀ = floor(N_min/n)` for every `n ≥ 4`. -/
theorem noWrap_of_small_cube {d n : ℕ} (Y : Fin n → Point d)
    (center : Point d) (Nmin Ω : ℕ) (hΩ : 0 < Ω) (hNΩ : Nmin ≤ Ω)
    (hn : 4 ≤ n)
    (hY : ∀ j, InCube (2 * Real.pi / (Ω : ℝ)) center (Y j)) :
    ((Nmin / n : ℕ) : ℝ) * nodeDiameter Y ≤ Real.pi := by
  have hΩ' : (0 : ℝ) < Ω := by exact_mod_cast hΩ
  have hdiam : nodeDiameter Y ≤ 4 * Real.pi / (Ω : ℝ) := by
    convert nodeDiameter_le_of_cube Y center (by positivity) hY using 1 <;> ring
  have hfour : 4 * (Nmin / n) ≤ Ω := by
    calc
      4 * (Nmin / n) ≤ n * (Nmin / n) := Nat.mul_le_mul_right _ hn
      _ ≤ Nmin := Nat.mul_div_le Nmin n
      _ ≤ Ω := hNΩ
  have hfour' : (4 : ℝ) * ((Nmin / n : ℕ) : ℝ) ≤ Ω := by exact_mod_cast hfour
  calc
    ((Nmin / n : ℕ) : ℝ) * nodeDiameter Y ≤
        ((Nmin / n : ℕ) : ℝ) * (4 * Real.pi / (Ω : ℝ)) :=
      mul_le_mul_of_nonneg_left hdiam (Nat.cast_nonneg _)
    _ = (4 * ((Nmin / n : ℕ) : ℝ) * Real.pi) / (Ω : ℝ) := by ring
    _ ≤ Real.pi := (div_le_iff₀ hΩ').2
      (by nlinarith [Real.pi_pos])

end
end LeanNumDetect.MultiTuran
