import General.Fourier.FiniteTorusGrid
import General.Fourier.PhaseEstimates
import Mathlib.Analysis.Fourier.ZMod

/-!
# Exact finite-grid expansions of continuous Fourier atoms

An angular Fourier atom with frequencies `0, …, M` has an exact expansion
over a deterministic uniform grid with `O(M²)` points and coefficient `ℓ¹`
mass at most two.  The proof uses a nearby grid atom and Fourier inversion
of their small residual.  In particular it needs neither a trigonometric
Bernstein inequality nor a discretization error in the final representation.
-/

set_option autoImplicit false

open scoped BigOperators

namespace LeanNumDetect

noncomputable section

/-- The unnormalized angular Fourier atom on `0, …, M`. -/
def fourierAtom (M : ℕ) (y : ℝ) (k : Fin (M + 1)) : ℂ :=
  Complex.exp (Complex.I * (((k : ℝ) * y : ℝ) : ℂ))

@[simp] theorem norm_fourierAtom (M : ℕ) (y : ℝ) (k : Fin (M + 1)) :
    ‖fourierAtom M y k‖ = 1 := by
  simp [fourierAtom, Complex.norm_exp, Complex.mul_re]

/-- The oversampling factor of the exact atomic grid. -/
def fourierAtomicGridFactor (M : ℕ) : ℕ := Nat.ceil (4 * Real.pi * M) + 1

/-- Number of equally spaced angular nodes in the exact atomic grid. -/
def fourierAtomicGridSize (M : ℕ) : ℕ := fourierAtomicGridFactor M * (M + 1)

theorem fourierAtomicGridFactor_pos (M : ℕ) : 0 < fourierAtomicGridFactor M := by
  unfold fourierAtomicGridFactor
  omega

theorem fourierAtomicGridSize_pos (M : ℕ) : 0 < fourierAtomicGridSize M := by
  exact Nat.mul_pos (fourierAtomicGridFactor_pos M) (Nat.succ_pos M)

/-- The angular coordinate of a node of the exact atomic grid. -/
def fourierAtomicGridPoint (M : ℕ) (j : Fin (fourierAtomicGridSize M)) : ℝ :=
  2 * Real.pi * (j : ℝ) / fourierAtomicGridSize M

/-- The deterministic finite dictionary of grid Fourier atoms. -/
def fourierAtomicGrid (M : ℕ) (j : Fin (fourierAtomicGridSize M))
    (k : Fin (M + 1)) : ℂ := fourierAtom M (fourierAtomicGridPoint M j) k

@[simp] theorem norm_fourierAtomicGrid (M : ℕ)
    (j : Fin (fourierAtomicGridSize M)) (k : Fin (M + 1)) :
    ‖fourierAtomicGrid M j k‖ = 1 := norm_fourierAtom _ _ _

/-- A common column normalization has the same coordinate modulus everywhere. -/
@[simp] theorem norm_scaled_fourierAtomicGrid (M : ℕ) (w : ℂ)
    (j : Fin (fourierAtomicGridSize M)) (k : Fin (M + 1)) :
    ‖w * fourierAtomicGrid M j k‖ = ‖w‖ := by
  rw [norm_mul, norm_fourierAtomicGrid, mul_one]

/-- Every normalized dictionary column has exactly its expected squared norm. -/
theorem sum_norm_sq_scaled_fourierAtomicGrid (M : ℕ) (w : ℂ)
    (j : Fin (fourierAtomicGridSize M)) :
    (∑ k : Fin (M + 1), ‖w * fourierAtomicGrid M j k‖ ^ 2) =
      (M + 1) * ‖w‖ ^ 2 := by simp

/-- The coarse DFT grid is contained in the oversampled grid. -/
def fourierAtomicBaseIndex (M : ℕ) (l : ZMod (M + 1)) :
    Fin (fourierAtomicGridSize M) :=
  ⟨fourierAtomicGridFactor M * l.val,
    Nat.mul_lt_mul_of_pos_left l.val_lt (fourierAtomicGridFactor_pos M)⟩

/-- The embedded coarse atom is exactly the standard finite Fourier character. -/
theorem fourierAtomicGrid_base (M : ℕ) (l : ZMod (M + 1)) (k : Fin (M + 1)) :
    fourierAtomicGrid M (fourierAtomicBaseIndex M l) k =
      (ZMod.stdAddChar (l * (k.val : ZMod (M + 1))) : ℂ) := by
  have hq : (fourierAtomicGridFactor M : ℂ) ≠ 0 := by
    exact_mod_cast (fourierAtomicGridFactor_pos M).ne'
  have hn : ((M + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero M)
  have he : l * (k.val : ZMod (M + 1)) =
      ((l.val * k.val : ℕ) : ZMod (M + 1)) := by simp
  rw [he]
  have hc := ZMod.stdAddChar_coe (N := M + 1) ((l.val * k.val : ℕ) : ℤ)
  simp only [Int.cast_natCast] at hc
  rw [hc]
  unfold fourierAtomicGrid fourierAtom fourierAtomicGridPoint fourierAtomicBaseIndex
    fourierAtomicGridSize
  simp only [Nat.cast_mul, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_ofNat]
  congr 1
  field_simp

/-- Normalized Fourier coefficients of a vector on the coarse DFT grid. -/
def fourierAtomicCoefficients (M : ℕ) (r : Fin (M + 1) → ℂ)
    (l : ZMod (M + 1)) : ℂ :=
  ((M + 1 : ℕ) : ℂ)⁻¹ *
    ZMod.dft (fun k : ZMod (M + 1) => r ⟨k.val, k.val_lt⟩) l

/-- Exact Fourier inversion, with the coarse atoms embedded in the fine grid. -/
theorem fourierAtomicCoefficients_expand (M : ℕ) (r : Fin (M + 1) → ℂ)
    (k : Fin (M + 1)) :
    (∑ l : ZMod (M + 1), fourierAtomicCoefficients M r l *
      fourierAtomicGrid M (fourierAtomicBaseIndex M l) k) = r k := by
  simp_rw [fourierAtomicGrid_base, fourierAtomicCoefficients]
  rw [show (∑ l : ZMod (M + 1),
      ((M + 1 : ℕ) : ℂ)⁻¹ *
        ZMod.dft (fun h : ZMod (M + 1) => r ⟨h.val, h.val_lt⟩) l *
        (ZMod.stdAddChar (l * (k.val : ZMod (M + 1))) : ℂ)) =
      ((M + 1 : ℕ) : ℂ)⁻¹ * ∑ l : ZMod (M + 1),
        (ZMod.stdAddChar (l * (k.val : ZMod (M + 1))) : ℂ) *
          ZMod.dft (fun h : ZMod (M + 1) => r ⟨h.val, h.val_lt⟩) l by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring]
  have h := congrFun (ZMod.dft.symm_apply_apply
    (fun h : ZMod (M + 1) => r ⟨h.val, h.val_lt⟩)) (k.val : ZMod (M + 1))
  rw [ZMod.invDFT_apply] at h
  simpa only [smul_eq_mul, ZMod.val_natCast_of_lt k.isLt] using h

/-- The coefficient mass of the normalized finite Fourier transform is no
greater than the coordinate mass of the input. -/
theorem sum_norm_fourierAtomicCoefficients_le (M : ℕ) (r : Fin (M + 1) → ℂ) :
    (∑ l : ZMod (M + 1), ‖fourierAtomicCoefficients M r l‖) ≤
      ∑ k : Fin (M + 1), ‖r k‖ := by
  let S := ∑ k : ZMod (M + 1), ‖r ⟨k.val, k.val_lt⟩‖
  have hn : (0 : ℝ) < M + 1 := by positivity
  have hl (l : ZMod (M + 1)) :
      ‖fourierAtomicCoefficients M r l‖ ≤ (M + 1 : ℝ)⁻¹ * S := by
    unfold fourierAtomicCoefficients
    rw [norm_mul, norm_inv]
    have hnorm : ‖((M + 1 : ℕ) : ℂ)‖ = (M + 1 : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (M + 1)
    rw [hnorm]
    apply mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hn.le)
    unfold S
    rw [ZMod.dft_apply]
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro k _
    simp
  calc
    _ ≤ ∑ _l : ZMod (M + 1), (M + 1 : ℝ)⁻¹ * S :=
      Finset.sum_le_sum fun l _ => hl l
    _ = S := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      field_simp
    _ = _ := by
      exact (Fintype.sum_equiv (ZMod.finEquiv (M + 1)).toEquiv
        (fun k : Fin (M + 1) => ‖r k‖)
        (fun k : ZMod (M + 1) => ‖r ⟨k.val, k.val_lt⟩‖)
        (fun k => by rfl)).symm

/-- Collecting coefficients with repeated dictionary indices preserves the
represented vector and does not increase the coefficient `ℓ¹` mass. -/
theorem exists_collected_atomic_expansion {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (a : κ → α → ℂ) (f : ι → κ) (c : ι → ℂ) :
    ∃ b : κ → ℂ,
      (∀ k, (∑ j, b j * a j k) = ∑ i, c i * a (f i) k) ∧
      (∑ j, ‖b j‖) ≤ ∑ i, ‖c i‖ := by
  classical
  refine ⟨fun j => ∑ i, if f i = j then c i else 0, ?_, ?_⟩
  · intro k
    simp_rw [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp
  · calc
      _ ≤ ∑ j : κ, ∑ i : ι, ‖if f i = j then c i else 0‖ :=
        Finset.sum_le_sum fun j _ => norm_sum_le _ _
      _ = _ := by
        rw [Finset.sum_comm]
        have hh (i : ι) (j : κ) : ‖if f i = j then c i else 0‖ =
            if f i = j then ‖c i‖ else 0 := by split_ifs <;> simp
        simp_rw [hh]
        simp

/-- The sampling grid admits a nearby atom whose coordinate residual has
total mass at most one. -/
theorem exists_fourierAtomicGrid_small_residual (M : ℕ) (y : ℝ) :
    ∃ j : Fin (fourierAtomicGridSize M),
      (∑ k : Fin (M + 1), ‖fourierAtom M y k - fourierAtomicGrid M j k‖) ≤ 1 := by
  let t := toIcoMod Real.two_pi_pos 0 y
  obtain ⟨j, hj⟩ := exists_interval_grid_near Real.two_pi_pos
    (fourierAtomicGridSize_pos M)
    (toIcoMod_mem_Ico' Real.two_pi_pos y).1
    (toIcoMod_mem_Ico' Real.two_pi_pos y).2
  refine ⟨j, ?_⟩
  have hj' : |t - fourierAtomicGridPoint M j| ≤
      2 * Real.pi / fourierAtomicGridSize M := hj
  have hw (k : Fin (M + 1)) : fourierAtom M y k = fourierAtom M t k := by
    unfold fourierAtom t
    simpa only [Int.cast_natCast] using
      (exp_I_int_mul_toIcoMod (k.val : ℤ) y).symm
  have he (k : Fin (M + 1)) :
      ‖fourierAtom M y k - fourierAtomicGrid M j k‖ ≤
        M * (2 * Real.pi / fourierAtomicGridSize M) := by
    rw [hw]
    unfold fourierAtom fourierAtomicGrid
    have h := norm_exp_I_mul_sub_le ((k : ℝ) * t)
      ((k : ℝ) * fourierAtomicGridPoint M j)
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)] at h
    refine h.trans (mul_le_mul ?_ hj' (abs_nonneg _) (by positivity))
    exact_mod_cast (Nat.le_of_lt_succ k.isLt)
  have hq : (0 : ℝ) < fourierAtomicGridFactor M := by
    exact_mod_cast fourierAtomicGridFactor_pos M
  have hn : (0 : ℝ) < M + 1 := by positivity
  have hc : 2 * Real.pi * M ≤ (fourierAtomicGridFactor M : ℝ) := by
    have h := Nat.le_ceil (4 * Real.pi * (M : ℝ))
    have hM : (0 : ℝ) ≤ M := by positivity
    unfold fourierAtomicGridFactor
    push_cast
    nlinarith [Real.pi_pos]
  calc
    _ ≤ ∑ _k : Fin (M + 1), M * (2 * Real.pi / fourierAtomicGridSize M) :=
      Finset.sum_le_sum fun k _ => he k
    _ = (2 * Real.pi * M) / fourierAtomicGridFactor M := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        fourierAtomicGridSize, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp
    _ ≤ 1 := (div_le_iff₀ hq).2 (by simpa using hc)

/-- Every off-grid Fourier atom has an exact representation in the deterministic
finite dictionary with coefficient mass at most two. -/
theorem exists_fourierAtom_grid_expansion (M : ℕ) (y : ℝ) :
    ∃ c : Fin (fourierAtomicGridSize M) → ℂ,
      (∀ k : Fin (M + 1),
        (∑ j, c j * fourierAtomicGrid M j k) = fourierAtom M y k) ∧
      (∑ j, ‖c j‖) ≤ 2 := by
  classical
  obtain ⟨j, hj⟩ := exists_fourierAtomicGrid_small_residual M y
  let r : Fin (M + 1) → ℂ := fun k => fourierAtom M y k - fourierAtomicGrid M j k
  let f : Unit ⊕ ZMod (M + 1) → Fin (fourierAtomicGridSize M) :=
    Sum.elim (fun _ => j) (fourierAtomicBaseIndex M)
  let d : Unit ⊕ ZMod (M + 1) → ℂ :=
    Sum.elim (fun _ => 1) (fourierAtomicCoefficients M r)
  obtain ⟨c, hc, hm⟩ := exists_collected_atomic_expansion (fourierAtomicGrid M) f d
  refine ⟨c, ?_, ?_⟩
  · intro k
    rw [hc, Fintype.sum_sum_type]
    simp only [f, d, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique, one_mul]
    rw [fourierAtomicCoefficients_expand]
    dsimp [r]
    ring
  · have hr : (∑ l : ZMod (M + 1), ‖fourierAtomicCoefficients M r l‖) ≤ 1 :=
      (sum_norm_fourierAtomicCoefficients_le M r).trans hj
    apply hm.trans
    rw [Fintype.sum_sum_type]
    simp only [d, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique, norm_one]
    linarith

/-- The deterministic dictionary is of quadratic size in the bandwidth. -/
theorem fourierAtomicGridSize_le (M : ℕ) :
    (fourierAtomicGridSize M : ℝ) ≤ (4 * Real.pi * M + 2) * (M + 1) := by
  have h := (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 4 * Real.pi * M)).le
  unfold fourierAtomicGridSize fourierAtomicGridFactor
  push_cast
  apply mul_le_mul_of_nonneg_right ?_ (by positivity)
  linarith

/-- A finite linear combination of continuous atoms retains an exact grid
expansion, with coefficient mass inflated by at most a factor of two. -/
theorem exists_fourierPolynomial_grid_expansion {ι : Type*} [Fintype ι]
    (M : ℕ) (y : ι → ℝ) (z : ι → ℂ) :
    ∃ c : Fin (fourierAtomicGridSize M) → ℂ,
      (∀ k : Fin (M + 1),
        (∑ j, c j * fourierAtomicGrid M j k) = ∑ i, z i * fourierAtom M (y i) k) ∧
      (∑ j, ‖c j‖) ≤ 2 * ∑ i, ‖z i‖ := by
  classical
  have h (i : ι) := exists_fourierAtom_grid_expansion M (y i)
  choose c hc hm using h
  refine ⟨fun j => ∑ i, z i * c i j, ?_, ?_⟩
  · intro k
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hc]
  · calc
      _ ≤ ∑ j : Fin (fourierAtomicGridSize M), ∑ i : ι, ‖z i * c i j‖ :=
        Finset.sum_le_sum fun j _ => norm_sum_le _ _
      _ = ∑ i : ι, ‖z i‖ * ∑ j, ‖c i j‖ := by
        simp_rw [norm_mul]
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
      _ ≤ ∑ i : ι, ‖z i‖ * 2 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hm i) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring

/-- Multiplying all atoms by a common normalization preserves the expansion
and its coefficient-mass bound. -/
theorem exists_scaled_fourierAtom_grid_expansion (M : ℕ) (y : ℝ) (w : ℂ) :
    ∃ c : Fin (fourierAtomicGridSize M) → ℂ,
      (∀ k : Fin (M + 1),
        (∑ j, c j * (w * fourierAtomicGrid M j k)) = w * fourierAtom M y k) ∧
      (∑ j, ‖c j‖) ≤ 2 := by
  obtain ⟨c, hc, hm⟩ := exists_fourierAtom_grid_expansion M y
  refine ⟨c, ?_, hm⟩
  intro k
  calc
    _ = w * ∑ j, c j * fourierAtomicGrid M j k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [hc]

end

end LeanNumDetect
