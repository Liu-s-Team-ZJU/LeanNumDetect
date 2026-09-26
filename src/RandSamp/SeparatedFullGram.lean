import General.Fourier.TranslatedCubeFourier

/-!
The full consecutive-frequency frame bounds used in
`thm:fixed-separated-singular-values`.  The proof specializes the proved
Vaaler--Selberg majorant and minorant to the interval `[0,M]`.  In particular,
it includes non-strict separation without an additional external theorem.
-/

set_option autoImplicit false

open scoped BigOperators

namespace LeanNumDetect.RandSamp

noncomputable section

/-- Angular separation on the circle, independent of the chosen real lifts. -/
def AngularSeparated {s : ℕ} (Δ : ℝ) (Y : Fin s → ℝ) : Prop :=
  ∀ i j, i ≠ j → ∀ p : ℤ, Δ ≤ |Y i - Y j + 2 * Real.pi * p|

/-- The unnormalized full Fourier energy on the consecutive rows `0,...,M`. -/
def fullFourierEnergy {s : ℕ} (M : ℕ) (Y : Fin s → ℝ) (z : Fin s → ℂ) : ℝ :=
  ∑ k : Fin (M + 1),
    ‖∑ j, Complex.exp (Complex.I * (((k : ℕ) : ℝ) * Y j : ℝ)) * z j‖ ^ 2

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

private theorem integer_block_mem_iff {M : ℕ} (n : Fin 1 → ℤ) :
    n ∈ oneSidedFrequencyValues 1 (M + 1) ↔
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

private theorem normalized_separation {s : ℕ} {Δ : ℝ} {Y : Fin s → ℝ}
    (hsep : AngularSeparated Δ Y) {i j : Fin s} (hij : i ≠ j) :
    Δ / (2 * Real.pi) ≤ circleDist (-Y j / (2 * Real.pi) - -Y i / (2 * Real.pi)) 0 := by
  apply le_circleDist_of_forall_int
  intro p
  have hp := hsep i j hij (-p)
  have hπ : 0 < 2 * Real.pi := by positivity
  have heq : -Y j / (2 * Real.pi) - -Y i / (2 * Real.pi) - 0 - (p : ℝ) =
      (Y i - Y j + 2 * Real.pi * (-p : ℤ)) / (2 * Real.pi) := by
    push_cast
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hπ]
  exact div_le_div_of_nonneg_right hp hπ.le

private theorem translated_energy_eq {M s : ℕ} (Y : Fin s → ℝ) (z : Fin s → ℂ) :
    External.translatedCubeFourierEnergy (M + 1)
      (fun j (_ : Fin 1) => -Y j / (2 * Real.pi)) z = fullFourierEnergy M Y z := by
  unfold External.translatedCubeFourierEnergy fullFourierEnergy
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin (M + 1)))
  intro n
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm (z j)]
  congr 2
  simp only [Fin.sum_univ_one]
  push_cast
  change -2 * ↑Real.pi * Complex.I * (↑↑(n 0) * (-↑(Y j) / (2 * ↑Real.pi))) =
    Complex.I * (↑↑(n 0) * ↑(Y j))
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- The exact two-sided Selberg frame bound for consecutive Fourier rows.
The separation condition is non-strict; the proof uses the closed-band
vanishing of the Vaaler--Selberg Fourier transform. -/
theorem separated_full_energy_bounds {M s : ℕ} (hM : 0 < M)
    {Δ : ℝ} (hΔ : 0 < Δ) (hΔupper : Δ ≤ 2 * Real.pi)
    (hwidth : 2 * Real.pi ≤ Δ * M)
    (Y : Fin s → ℝ) (hsep : AngularSeparated Δ Y) (z : Fin s → ℂ) :
    ((M : ℝ) - 2 * Real.pi / Δ) * (∑ j, ‖z j‖ ^ 2) ≤
        fullFourierEnergy M Y z ∧
      fullFourierEnergy M Y z ≤
        ((M : ℝ) + 2 * Real.pi / Δ) * (∑ j, ‖z j‖ ^ 2) := by
  let q := Δ / (2 * Real.pi)
  let x : Fin s → External.UnitTorusPoint 1 := fun j _ => -Y j / (2 * Real.pi)
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := (div_le_one (by positivity)).2 hΔupper
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hqwidth : 1 ≤ q * ((M : ℝ) - 0) := by
    dsimp [q]
    rw [sub_zero, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    simpa using hwidth
  have hqinv : q⁻¹ = 2 * Real.pi / Δ := by simp [q, inv_div]
  have hcross (i j : Fin s) (hij : i ≠ j) :
      ∃ k, q ≤ circleDist (x j k - x i k) 0 :=
    ⟨0, normalized_separation hsep hij⟩
  have hminor : ∀ n : Fin 1 → ℤ,
      bartonMinorant 0 M q (fun k => n k) ≤
        if n ∈ oneSidedFrequencyValues 1 (M + 1) then 1 else 0 := by
    intro n
    have h := bartonMinorant_le_boxIndicator hMreal.le hq hqwidth (fun k => (n k : ℝ))
    simpa only [integer_block_mem_iff] using h
  have hmajor : ∀ n : Fin 1 → ℤ,
      (if n ∈ oneSidedFrequencyValues 1 (M + 1) then 1 else 0) ≤
        bartonMajorant 0 M q (fun k => n k) := by
    intro n
    by_cases hn : n ∈ oneSidedFrequencyValues 1 (M + 1)
    · rw [if_pos hn]
      apply Finset.one_le_prod
      intro k _
      have hk := (integer_block_mem_iff n).1 hn k
      exact one_le_selberg_closed hMreal hq hk.1 hk.2
    · rw [if_neg hn]
      exact bartonMajorant_nonneg hMreal.le hq _
  have hlo := translatedCube_lower_of_barton 0 M q ((M : ℝ) - q⁻¹) x z
    hminor (by
      simpa only [sub_zero, pow_one,
        show 2 * (M : ℝ) - ((M : ℝ) + q⁻¹) = (M : ℝ) - q⁻¹ by ring] using
          bartonMinorant_hasSum (d := 1) hMreal.le hq hq1)
    (fun i j hij => bartonMinorantModulated_hasSum_zero hMreal.le hq (hcross i j hij))
  have hhi := translatedCube_upper_of_barton 0 M q ((M : ℝ) + q⁻¹) x z
    hmajor (fun n => bartonMajorant_nonneg hMreal.le hq _)
    (by simpa using bartonMajorant_hasSum (d := 1) hMreal.le hq hq1)
    (fun i j hij => bartonMajorantModulated_hasSum_zero hMreal.le hq (hcross i j hij))
  simpa only [x, translated_energy_eq, hqinv, External.coefficientEnergy] using And.intro hlo hhi

end

end LeanNumDetect.RandSamp
