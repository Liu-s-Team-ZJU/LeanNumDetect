import General.Fourier.TranslatedCubeFourier

/-!
Full Fourier-frame bounds on the frequency cube `{0,...,M}^d`, used in
`thm:fixed-separated-singular-values-higher-dimensional`.  The existing proved
Barton minorant gives `2*M^d - (M+c)^d`; Bernoulli's inequality weakens this
constant to the manuscript's `(M+c)^(d-1)*(M-(2*d-1)*c)`.  Closed-band
orthogonality includes non-strict wrap-around separation directly.
-/

set_option autoImplicit false

open scoped BigOperators

namespace LeanNumDetect.RandSamp

noncomputable section

/-- Wrap-around infinity separation: each distinct pair has one coordinate
separated from every integer translate by at least `Δ`. -/
def CubeAngularSeparated {d s : ℕ} (Δ : ℝ) (Y : Fin s → Fin d → ℝ) : Prop :=
  ∀ i j, i ≠ j → ∃ r : Fin d, ∀ p : ℤ,
    Δ ≤ |Y i r - Y j r + 2 * Real.pi * p|

/-- Unnormalized Fourier energy over the full integer frequency cube. -/
def cubeFullFourierEnergy {d s : ℕ} (M : ℕ) (Y : Fin s → Fin d → ℝ)
    (z : Fin s → ℂ) : ℝ :=
  ∑ k : Fin d → Fin (M + 1),
    ‖∑ j, Complex.exp (Complex.I *
      ((∑ r, ((k r : ℕ) : ℝ) * Y j r : ℝ) : ℂ)) * z j‖ ^ 2

open TranslatedCubeFourier
open MathExtras.NumberTheory.Analysis
open SelbergIntervalMajorantClosed VaalerThm16Mechanism VaalerCor7Closed LargeSieve

private theorem one_le_selberg_closed
    {a b δ t : ℝ} (hab : a < b) (hδ : 0 < δ) (hat : a ≤ t) (htb : t ≤ b) :
    1 ≤ selbergIntervalMajorant a b δ t := by
  rcases hat.eq_or_lt with rfl | hat
  · rw [selbergIntervalMajorant_eq_signPair_add_phi hδ]
    have hsign : intervalSignPair a b a = 1 / 2 := by
      simp [intervalSignPair, Real.sign_of_pos (sub_pos.mpr hab)]
    rw [hsign]
    simp only [sub_self, mul_zero, phi_zero]
    have hnonneg : 0 ≤ VaalerBeurlingNonneg.phi (δ * (b - a)) :=
      vaalerBeurlingMajorant_closed.nonneg (δ * (b - a))
    linarith
  · exact one_le_selbergIntervalMajorant hδ hat htb

private theorem integer_cube_mem_iff {d M : ℕ} (n : Fin d → ℤ) :
    n ∈ oneSidedFrequencyValues d (M + 1) ↔
      ∀ k, (0 : ℝ) ≤ n k ∧ (n k : ℝ) ≤ M := by
  rw [oneSided_mem_iff]
  constructor
  · intro h k
    constructor
    · exact_mod_cast (h k).1
    · have hk : n k ≤ (M : ℤ) := by have := (h k).2; omega
      exact_mod_cast hk
  · intro h k
    have hk0 : 0 ≤ n k := by exact_mod_cast (h k).1
    have hkM : n k ≤ (M : ℤ) := by exact_mod_cast (h k).2
    exact ⟨hk0, by omega⟩

private theorem normalized_cube_separation {d s : ℕ} {Δ : ℝ}
    {Y : Fin s → Fin d → ℝ} (hsep : CubeAngularSeparated Δ Y)
    {i j : Fin s} (hij : i ≠ j) :
    ∃ r, Δ / (2 * Real.pi) ≤
      circleDist (-Y j r / (2 * Real.pi) - -Y i r / (2 * Real.pi)) 0 := by
  obtain ⟨r, hr⟩ := hsep i j hij
  refine ⟨r, le_circleDist_of_forall_int fun p => ?_⟩
  have hp := hr (-p)
  have hπ : 0 < 2 * Real.pi := by positivity
  have heq : -Y j r / (2 * Real.pi) - -Y i r / (2 * Real.pi) - 0 - (p : ℝ) =
      (Y i r - Y j r + 2 * Real.pi * (-p : ℤ)) / (2 * Real.pi) := by
    push_cast
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hπ]
  exact div_le_div_of_nonneg_right hp hπ.le

private theorem translated_cube_energy_eq {d M s : ℕ}
    (Y : Fin s → Fin d → ℝ) (z : Fin s → ℂ) :
    External.translatedCubeFourierEnergy (M + 1)
      (fun j r => -Y j r / (2 * Real.pi)) z = cubeFullFourierEnergy M Y z := by
  unfold External.translatedCubeFourierEnergy cubeFullFourierEnergy
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm (z j)]
  congr 2
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- Bernoulli's inequality compares the Barton mass to the explicit lower
constant in the higher-dimensional manuscript theorem. -/
theorem cubeLower_le_bartonMass {d : ℕ} (hd : 1 ≤ d) {M c : ℝ}
    (hM : 0 ≤ M) (hc : 0 ≤ c) :
    (M + c) ^ (d - 1) * (M - (2 * (d : ℝ) - 1) * c) ≤
      2 * M ^ d - (M + c) ^ d := by
  have hb := pow_add_mul_le_add_pow (a := M + c) (b := -c)
    (by positivity : 0 ≤ M + c) (by linarith : 0 ≤ 2 * (M + c) + -c) d
  rw [add_neg_cancel_right] at hb
  have hp : (M + c) ^ d = (M + c) ^ (d - 1) * (M + c) := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  rw [hp] at hb ⊢
  nlinarith only [hb]

/-- Exact manuscript lower and upper Fourier-frame constants on the full
frequency cube. This theorem allows the lower constant to be nonpositive;
the stronger Rayleigh condition in the final theorem makes it positive. -/
theorem cube_separated_full_energy_bounds {d M s : ℕ} (hd : 1 ≤ d) (hM : 0 < M)
    {Δ : ℝ} (hΔ : 0 < Δ) (hΔupper : Δ ≤ 2 * Real.pi)
    (hwidth : 2 * Real.pi ≤ Δ * M)
    (Y : Fin s → Fin d → ℝ) (hsep : CubeAngularSeparated Δ Y) (z : Fin s → ℂ) :
    (((M : ℝ) + 2 * Real.pi / Δ) ^ (d - 1) *
        ((M : ℝ) - (2 * (d : ℝ) - 1) * (2 * Real.pi / Δ))) *
        (∑ j, ‖z j‖ ^ 2) ≤ cubeFullFourierEnergy M Y z ∧
      cubeFullFourierEnergy M Y z ≤
        ((M : ℝ) + 2 * Real.pi / Δ) ^ d * (∑ j, ‖z j‖ ^ 2) := by
  let q := Δ / (2 * Real.pi)
  let x : Fin s → External.UnitTorusPoint d := fun j r => -Y j r / (2 * Real.pi)
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := (div_le_one (by positivity)).2 hΔupper
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hqwidth : 1 ≤ q * ((M : ℝ) - 0) := by
    dsimp [q]
    rw [sub_zero, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    simpa using hwidth
  have hqinv : q⁻¹ = 2 * Real.pi / Δ := by simp [q, inv_div]
  have hcross (i j : Fin s) (hij : i ≠ j) :
      ∃ k, q ≤ circleDist (x j k - x i k) 0 := normalized_cube_separation hsep hij
  have hminor : ∀ n : Fin d → ℤ,
      bartonMinorant 0 M q (fun k => n k) ≤
        if n ∈ oneSidedFrequencyValues d (M + 1) then 1 else 0 := by
    intro n
    have h := bartonMinorant_le_boxIndicator hMreal.le hq hqwidth (fun k => (n k : ℝ))
    simpa only [integer_cube_mem_iff] using h
  have hmajor : ∀ n : Fin d → ℤ,
      (if n ∈ oneSidedFrequencyValues d (M + 1) then 1 else 0) ≤
        bartonMajorant 0 M q (fun k => n k) := by
    intro n
    by_cases hn : n ∈ oneSidedFrequencyValues d (M + 1)
    · rw [if_pos hn]
      apply Finset.one_le_prod
      intro k _
      have hk := (integer_cube_mem_iff n).1 hn k
      exact one_le_selberg_closed hMreal hq hk.1 hk.2
    · rw [if_neg hn]
      exact bartonMajorant_nonneg hMreal.le hq _
  have hlo := translatedCube_lower_of_barton 0 M q
    (2 * (M : ℝ) ^ d - ((M : ℝ) + q⁻¹) ^ d) x z hminor
    (by simpa only [sub_zero] using bartonMinorant_hasSum (d := d) hMreal.le hq hq1)
    (fun i j hij => bartonMinorantModulated_hasSum_zero hMreal.le hq (hcross i j hij))
  have hhi := translatedCube_upper_of_barton 0 M q (((M : ℝ) + q⁻¹) ^ d) x z
    hmajor (fun n => bartonMajorant_nonneg hMreal.le hq _)
    (by simpa only [sub_zero] using bartonMajorant_hasSum (d := d) hMreal.le hq hq1)
    (fun i j hij => bartonMajorantModulated_hasSum_zero hMreal.le hq (hcross i j hij))
  have hcoeff := cubeLower_le_bartonMass hd hMreal.le (by positivity : 0 ≤ q⁻¹)
  have henergy : 0 ≤ External.coefficientEnergy z :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hlo' := (mul_le_mul_of_nonneg_right hcoeff henergy).trans hlo
  simpa only [x, translated_cube_energy_eq, hqinv, External.coefficientEnergy] using
    And.intro hlo' hhi

end

end LeanNumDetect.RandSamp
