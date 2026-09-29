import RandSamp.CubeRandomModel
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! The Cartesian DFT grid, its characters, and the normalized sampled matrix.
The index group has exactly `N ^ d` elements; its additive group structure keeps
all column differences in that same grid. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.RandSamp

noncomputable section

/-- Frequency and grid indices for a Cartesian DFT grid. -/
abbrev DFTIndex (d N : ℕ) := Fin d → ZMod N

@[simp] theorem card_dftIndex (d N : ℕ) [NeZero N] :
    Fintype.card (DFTIndex d N) = N ^ d := by
  simp [DFTIndex]

/-- The grid character at offset `q`, evaluated at frequency `k`. -/
def dftCharacter {d N : ℕ} [NeZero N] (q k : DFTIndex d N) : ℂ :=
  ZMod.stdAddChar (∑ r, k r * q r)

@[simp] theorem norm_dftCharacter {d N : ℕ} [NeZero N]
    (q k : DFTIndex d N) : ‖dftCharacter q k‖ = 1 := by
  exact Circle.norm_coe _

@[simp] theorem dftCharacter_zero {d N : ℕ} [NeZero N]
    (k : DFTIndex d N) : dftCharacter 0 k = 1 := by
  simp [dftCharacter]

/-- The explicit exponential formula has the same sign and normalization as
`cubeFourierRow` at the Cartesian grid nodes. -/
theorem dftCharacter_exp {d N : ℕ} [NeZero N] (q k : DFTIndex d N) :
    dftCharacter q k = Complex.exp (2 * Real.pi * Complex.I *
      (∑ r, (((k r).val : ℝ) * ((q r).val : ℝ)) : ℝ) / N) := by
  have he : (∑ r, k r * q r) =
      ((∑ r, (k r).val * (q r).val : ℕ) : ZMod N) := by
    simp
  rw [dftCharacter, he]
  have h := ZMod.stdAddChar_coe (N := N) ((∑ r, (k r).val * (q r).val : ℕ) : ℤ)
  simpa only [Int.cast_natCast, Nat.cast_sum, Nat.cast_mul, Int.cast_sum, Int.cast_mul, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_natCast] using h

/-- Grid coordinates are the real angular representatives `2π j / N`. -/
def dftGridNodes {d N : ℕ} [NeZero N] (q : DFTIndex d N) (r : Fin d) : ℝ :=
  2 * Real.pi * (q r).val / N

/-- The abstract grid character is exactly the manuscript's cube Fourier row. -/
theorem cubeFourierRow_dftGrid {d M s : ℕ} (Y : Fin s → DFTIndex d (M + 1))
    (k : CubeFrequency d M) (j : Fin s) :
    cubeFourierRow (fun j => dftGridNodes (Y j)) k j = dftCharacter (Y j) k := by
  rw [dftCharacter_exp]
  unfold cubeFourierRow dftGridNodes
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_ofNat]
  simp_rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  simp only [ZMod.val, Nat.cast_add, Nat.cast_one]
  ring

/-- The one-dimensional character uses precisely the original DFT phase. -/
theorem dftCharacter_one {N : ℕ} [NeZero N] (q k : DFTIndex 1 N) :
    dftCharacter q k = Complex.exp (2 * Real.pi * Complex.I *
      (((k 0).val : ℝ) * ((q 0).val : ℝ)) / N) := by
  simpa only [Fin.sum_univ_one, Complex.ofReal_mul] using dftCharacter_exp q k

/-- A grid character is an additive character in its frequency argument. -/
def dftAddChar {d N : ℕ} [NeZero N] (q : DFTIndex d N) :
    AddChar (DFTIndex d N) ℂ where
  toFun := dftCharacter q
  map_zero_eq_one' := by simp [dftCharacter]
  map_add_eq_mul' := by
    intro a b
    simp [dftCharacter, add_mul, Finset.sum_add_distrib, AddChar.map_add_eq_mul]

/-- Every nonzero grid offset has zero full-population character sum. -/
theorem sum_dftCharacter_eq_zero {d N : ℕ} [NeZero N]
    {q : DFTIndex d N} (hq : q ≠ 0) : ∑ k, dftCharacter q k = 0 := by
  classical
  apply AddChar.sum_eq_zero_of_ne_one (ψ := dftAddChar q)
  intro he
  have hq' : ∃ r, q r ≠ 0 := by
    by_contra h
    push Not at h
    exact hq (funext h)
  obtain ⟨r, hr⟩ := hq'
  have hh := congrArg (fun χ : AddChar (DFTIndex d N) ℂ => χ (Pi.single r 1)) he
  have hz : ZMod.stdAddChar (q r) = ZMod.stdAddChar (0 : ZMod N) := by
    simpa [dftAddChar, dftCharacter, Pi.single_apply] using hh
  exact hr (ZMod.injective_stdAddChar hz)

/-- Complex Gram entries depend only on the difference of the column indices. -/
theorem dftCharacter_sub {d N : ℕ} [NeZero N]
    (i j k : DFTIndex d N) :
    star (dftCharacter i k) * dftCharacter j k = dftCharacter (j - i) k := by
  rw [dftCharacter, dftCharacter, dftCharacter]
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
    AddChar.map_sub_eq_div, div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  exact (Complex.inv_eq_conj (norm_dftCharacter i k)).symm

/-- The sampled Cartesian DFT matrix has row normalization `1 / sqrt m`. -/
def dftSampledMatrix {d N : ℕ} [NeZero N] (m : ℕ)
    (Ω : Finset (DFTIndex d N)) : Matrix Ω (DFTIndex d N) ℂ :=
  fun k j => (Real.sqrt (m : ℝ) : ℂ)⁻¹ * dftCharacter j k.val

/-- Every sampled matrix entry is the normalized multidimensional DFT
exponential appearing in the manuscript. -/
theorem dftSampledMatrix_apply_exp {d N : ℕ} [NeZero N] (m : ℕ)
    (Ω : Finset (DFTIndex d N)) (k : Ω) (j : DFTIndex d N) :
    dftSampledMatrix m Ω k j = (Real.sqrt (m : ℝ) : ℂ)⁻¹ *
      Complex.exp (2 * Real.pi * Complex.I *
        (∑ r, (((k.val r).val : ℝ) * ((j r).val : ℝ)) : ℝ) / N) := by
  rw [dftSampledMatrix, dftCharacter_exp]

/-- Selecting grid nodes in the DFT matrix gives exactly the existing sampled
cube Fourier matrix, without changing normalization or singular values. -/
theorem dftSampledMatrix_eq_cubeSampledVandermonde {d M s : ℕ} (m : ℕ)
    (Y : Fin s → DFTIndex d (M + 1)) (Ω : Finset (CubeFrequency d M)) :
    (fun k j => dftSampledMatrix m Ω k (Y j)) =
      cubeSampledVandermonde m (fun j => dftGridNodes (Y j)) Ω := by
  ext k j
  simp only [dftSampledMatrix, cubeSampledVandermonde, cubeFourierRow_dftGrid]

/-- Its Gram entry is the average sampled character at the column offset. -/
theorem dftSampledMatrix_gram {d N m : ℕ} [NeZero N]
    (Ω : Finset (DFTIndex d N)) (i j : DFTIndex d N) :
    (∑ k : Ω, star (dftSampledMatrix m Ω k i) * dftSampledMatrix m Ω k j) =
      (m : ℂ)⁻¹ * ∑ k ∈ Ω, dftCharacter (j - i) k := by
  simp only [dftSampledMatrix, star_mul]
  have hc : star ((Real.sqrt (m : ℝ) : ℂ)⁻¹) =
      ((Real.sqrt (m : ℝ) : ℂ)⁻¹) := by simp
  rw [hc]
  simp_rw [show ∀ a b c : ℂ, b * a * (a * c) = a ^ 2 * (b * c) by intros; ring,
    dftCharacter_sub, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
    inv_pow, Real.sq_sqrt (Nat.cast_nonneg m), Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [← Finset.mul_sum, Finset.sum_coe_sort]

/-- Every sampled column has unit squared norm when the sample has size `m > 0`. -/
theorem dftSampledMatrix_gram_self {d N m : ℕ} [NeZero N]
    (hm : 0 < m) (Ω : FiniteMatrixSampling.FiniteSample (DFTIndex d N) m)
    (j : DFTIndex d N) :
    (∑ k : Ω.val, star (dftSampledMatrix m Ω.val k j) *
      dftSampledMatrix m Ω.val k j) = 1 := by
  rw [dftSampledMatrix_gram, sub_self]
  simp [Ω.prop, ne_of_gt hm]

/-- There are exactly `N ^ d - 1` nonzero character offsets. -/
@[simp] theorem card_nonzero_dftIndex (d N : ℕ) [NeZero N] :
    Fintype.card {q : DFTIndex d N // q ≠ 0} = N ^ d - 1 := by
  classical
  simp [Fintype.card_subtype_compl]

end

end LeanNumDetect.RandSamp
