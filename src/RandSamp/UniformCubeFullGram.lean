import General.Fourier.LatticeSelbergMinorant
import RandSamp.CubeGramBounds

/-! Sharper deterministic cube bounds for uniform random sampling. The lower
Selberg interval is enlarged to the open interval `(-1,M+1)`, preserving its
integer points while improving its mass. The one-dimensional constant is
exactly `(M+3/2-2π/Δ)/(M+1)`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.RandSamp
noncomputable section
open TranslatedCubeFourier LatticeSelbergMinorant
open MathExtras.NumberTheory.Analysis
open SelbergIntervalMajorantClosed SelbergIntervalPoissonClosed LargeSieve

private theorem oneSidedFrequencyValue_injective (d N : ℕ) :
    Function.Injective
      (fun n : Fin d → Fin N => fun k => (n k : ℤ)) := by
  intro n m h
  funext k
  have hk := congrFun h k
  change (((n k : Fin N) : ℕ) : ℤ) = (((m k : Fin N) : ℕ) : ℤ) at hk
  norm_cast at hk
  exact Fin.ext hk

private theorem translatedCubeFourierEnergy_eq_latticeBlock
    {d N : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → External.UnitTorusPoint d) (c : ι → ℂ) :
    External.translatedCubeFourierEnergy N x c =
      ∑ n ∈ oneSidedFrequencyValues d N,
        ‖SeparatedCubeFourierInternal.integerLatticeFourierValue x c n‖ ^ 2 := by
  classical
  unfold External.translatedCubeFourierEnergy oneSidedFrequencyValues
  rw [Finset.sum_image]
  · rfl
  · intro n _ m _ hnm
    exact oneSidedFrequencyValue_injective d N hnm


private theorem phase_cross_term
    {d : ℕ} (n : Fin d → ℤ)
    (u v : External.UnitTorusPoint d) (a b : ℂ) :
    star
        (a * Complex.exp
          (-2 * Real.pi * Complex.I *
            ∑ k, ((n k : ℤ) : ℂ) * u k)) *
        (b * Complex.exp
          (-2 * Real.pi * Complex.I *
            ∑ k, ((n k : ℤ) : ℂ) * v k)) =
      star a * b *
        Complex.exp
          (-2 * Real.pi * Complex.I *
            ∑ k, ((n k : ℤ) : ℂ) * (v k - u k)) := by
  rw [star_mul, Complex.star_def, ← Complex.exp_conj]
  have hconj :
      (starRingEnd ℂ)
          (-2 * Real.pi * Complex.I *
            ∑ k, ((n k : ℤ) : ℂ) * u k) =
        2 * Real.pi * Complex.I *
          ∑ k, ((n k : ℤ) : ℂ) * u k := by
    simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I, map_sum, map_intCast]
    ring
  rw [hconj]
  calc
    _ = star a * b *
        (Complex.exp
            (2 * Real.pi * Complex.I *
              ∑ k, ((n k : ℤ) : ℂ) * u k) *
          Complex.exp
            (-2 * Real.pi * Complex.I *
              ∑ k, ((n k : ℤ) : ℂ) * v k)) := by ac_rfl
    _ = star a * b *
        Complex.exp
          (2 * Real.pi * Complex.I *
              ∑ k, ((n k : ℤ) : ℂ) * u k +
            -2 * Real.pi * Complex.I *
              ∑ k, ((n k : ℤ) : ℂ) * v k) := by rw [Complex.exp_add]
    _ = _ := by
      congr 2
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring


private theorem translatedCube_lower_of_latticeMinorant
    {d N : ℕ} {ι : Type*} [Fintype ι]
    (W : ℝ) (w : (Fin d → ℤ) → ℝ) (x : ι → External.UnitTorusPoint d) (c : ι → ℂ)
    (hblock : ∀ n : Fin d → ℤ,
      w n ≤
        if n ∈ oneSidedFrequencyValues d N then 1 else 0)
    (hsum : HasSum
      (fun n : Fin d → ℤ => w n) W)
    (hcross : ∀ i j, i ≠ j →
      HasSum (fun n : Fin d → ℤ =>
        (w n : ℂ) *
          Complex.exp (-2 * Real.pi * Complex.I *
            ∑ k, ((n k : ℤ) : ℂ) * (x j k - x i k))) 0) :
    W * External.coefficientEnergy c ≤
      External.translatedCubeFourierEnergy N x c := by
  have hweighted :=
    SeparatedCubeFourierInternal.weighted_lattice_energy_hasSum
      w W x c hsum (fun i j hij => by
        have hc := (hcross i j hij).mul_left (star (c i) * c j)
        have hr := Complex.hasSum_re hc
        convert hr using 1
        · funext n
          rw [phase_cross_term]
          have heq :
              (w n : ℂ) *
                  (star (c i) * c j * Complex.exp
                    (-2 * Real.pi * Complex.I *
                      ∑ k, ((n k : ℤ) : ℂ) * (x j k - x i k))) =
                star (c i) * c j *
                  ((w n : ℂ) *
                    Complex.exp
                      (-2 * Real.pi * Complex.I *
                        ∑ k, ((n k : ℤ) : ℂ) * (x j k - x i k))) := by
            ring
          simpa [Complex.mul_re] using congrArg Complex.re heq
        · simp)
  have hle := weighted_series_le_block
    (oneSidedFrequencyValues d N) w
    (fun n => ‖SeparatedCubeFourierInternal.integerLatticeFourierValue x c n‖ ^ 2)
    (W * External.coefficientEnergy c)
    (fun _ => sq_nonneg _)
    (fun n hn => by simpa [hn] using hblock n)
    (fun n hn => by simpa [hn] using hblock n)
    hweighted
  rwa [← translatedCubeFourierEnergy_eq_latticeBlock] at hle


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


/-- Improved normalized full-cube lower constant, retaining the manuscript's
one-dimensional value exactly. -/
def uniformCubeLower (d M : ℕ) (Δ : ℝ) : ℝ :=
  (((M : ℝ) + 2 * Real.pi / Δ) ^ (d - 1) *
    ((M : ℝ) + (3 / 2 : ℝ) * d - (2 * (d : ℝ) - 1) * (2 * Real.pi / Δ))) /
      ((M : ℝ) + 1) ^ d

theorem uniformCubeLower_one (M : ℕ) (Δ : ℝ) :
    uniformCubeLower 1 M Δ =
      ((M : ℝ) + 3 / 2 - 2 * Real.pi / Δ) / (M + 1) := by
  norm_num [uniformCubeLower]

theorem uniformCubeLower_pos {d M : ℕ} (hd : 1 ≤ d) (hM : 1 ≤ M)
    {Δ : ℝ}
    (hΔ : 2 * Real.pi * (2 * (d : ℝ) - 1) / ((M : ℝ) + (3 / 2 : ℝ) * d) < Δ) :
    0 < uniformCubeLower d M Δ := by
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hd1 : 0 < 2 * (d : ℝ) - 1 := by linarith
  have hden : 0 < (M : ℝ) + (3 / 2 : ℝ) * d := by linarith
  have hΔ0 : 0 < Δ := (by positivity : 0 < 2 * Real.pi * (2 * (d : ℝ) - 1) /
    ((M : ℝ) + (3 / 2 : ℝ) * d)).trans hΔ
  have hcross := (div_lt_iff₀ hden).mp hΔ
  have hc : (2 * (d : ℝ) - 1) * (2 * Real.pi / Δ) <
      (M : ℝ) + (3 / 2 : ℝ) * d := by
    rw [← mul_div_assoc, div_lt_iff₀ hΔ0]
    nlinarith [hcross]
  unfold uniformCubeLower
  exact div_pos (mul_pos (pow_pos (by positivity) _) (sub_pos.mpr hc)) (by positivity)

/-- The enlarged-open-interval Selberg pair yields the sharper full cube
bounds without an additional width hypothesis. -/
theorem uniform_cube_full_energy_bounds {d M s : ℕ}
    (hd : 1 ≤ d) (hM : 0 < M) {Δ : ℝ}
    (hΔ : 0 < Δ) (hΔupper : Δ ≤ 2 * Real.pi)
    (Y : Fin s → Fin d → ℝ) (hsep : CubeAngularSeparated Δ Y) (z : Fin s → ℂ) :
    (((M : ℝ) + 2 * Real.pi / Δ) ^ (d - 1) *
        ((M : ℝ) + (3 / 2 : ℝ) * d -
          (2 * (d : ℝ) - 1) * (2 * Real.pi / Δ))) *
        (∑ j, ‖z j‖ ^ 2) ≤ cubeFullFourierEnergy M Y z ∧
      cubeFullFourierEnergy M Y z ≤
        ((M : ℝ) + 2 * Real.pi / Δ) ^ d * (∑ j, ‖z j‖ ^ 2) := by
  classical
  let q := Δ / (2 * Real.pi)
  let x : Fin s → External.UnitTorusPoint d := fun j r => -Y j r / (2 * Real.pi)
  let U : ℤ → ℝ := fun n => selbergIntervalMajorant 0 M q n
  let L : ℤ → ℝ := fun n => intervalMinorant (-1) (M + 1) q n
  let w : (Fin d → ℤ) → ℝ := tensorMinorant U L
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := (div_le_one (by positivity)).2 hΔupper
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hinterval : (-1 : ℝ) < (M : ℝ) + 1 := by linarith
  have hqinv : q⁻¹ = 2 * Real.pi / Δ := by simp [q, inv_div]
  have hcross (i j : Fin s) (hij : i ≠ j) :
      ∃ k, q ≤ circleDist (x j k - x i k) 0 := normalized_cube_separation hsep hij
  have hU0 (n : ℤ) : 0 ≤ U n := selbergIntervalMajorant_nonneg hMr.le hq _
  have hU (n : ℤ) : (if 0 ≤ n ∧ n ≤ (M : ℤ) then 1 else 0) ≤ U n := by
    split
    · rename_i hn
      exact one_le_majorant_closed hMr hq (by exact_mod_cast hn.1) (by exact_mod_cast hn.2)
    · exact hU0 n
  have hL (n : ℤ) : L n ≤ if 0 ≤ n ∧ n ≤ (M : ℤ) then 1 else 0 := by
    have h := intervalMinorant_le_openIndicator hinterval hq (n : ℝ)
    have heq : ((-1 : ℝ) < n ∧ (n : ℝ) < (M : ℝ) + 1) ↔ 0 ≤ n ∧ n ≤ (M : ℤ) := by
      constructor
      · intro hn
        have h1 : (-1 : ℤ) < n := by exact_mod_cast hn.1
        have h2 : n < (M : ℤ) + 1 := by exact_mod_cast hn.2
        omega
      · intro hn
        constructor
        · exact_mod_cast (show (-1 : ℤ) < n by omega)
        · exact_mod_cast (show n < (M : ℤ) + 1 by omega)
    simpa only [heq] using h
  have hblock (n : Fin d → ℤ) : w n ≤
      if n ∈ oneSidedFrequencyValues d (M + 1) then 1 else 0 := by
    have h := tensorMinorant_le_indicator U L (fun n => 0 ≤ n ∧ n ≤ (M : ℤ)) hU0 hU hL n
    have heq : n ∈ oneSidedFrequencyValues d (M + 1) ↔ ∀ k, 0 ≤ n k ∧ n k ≤ (M : ℤ) := by
      rw [oneSided_mem_iff]
      simp only [Nat.cast_add, Nat.cast_one]
      constructor <;> intro hn k <;> have := hn k <;> omega
    simpa only [heq, w] using h
  have hUsum : HasSum (fun n : ℤ => (U n : ℂ)) (((M : ℝ) + q⁻¹ : ℝ) : ℂ) := by
    simpa [U] using majorant_hasSum (a := 0) hMr.le hq hq1
  have hLsum : HasSum (fun n : ℤ => (L n : ℂ)) (((M : ℝ) + 2 - q⁻¹ : ℝ) : ℂ) := by
    convert intervalMinorant_hasSum hinterval.le hq hq1 using 1
    push_cast
    ring
  have hmass := tensorMinorant_hasSum (d := d) U L ((M : ℝ) + q⁻¹) ((M : ℝ) + 2 - q⁻¹) hUsum hLsum
  have hmod (i j : Fin s) (hij : i ≠ j) : HasSum (fun n : Fin d → ℤ =>
      (w n : ℂ) * Complex.exp (-2 * Real.pi * Complex.I *
        ∑ k, ((n k : ℤ) : ℂ) * (x j k - x i k))) 0 := by
    obtain ⟨k, hk⟩ := hcross i j hij
    simpa only [w, Complex.ofReal_sub] using
      tensorMinorantModulated_hasSum_zero U L (fun k => x j k - x i k)
      (fun k => selbergIntervalMajorant_mul_echar_int_summable hMr.le hq _)
      (fun k => intervalMinorantModulated_summable hinterval.le hq _)
      k (majorantModulated_hasSum_zero hMr.le hq hk)
      (intervalMinorantModulated_hasSum_zero hinterval.le hq hk)
  have hlo := translatedCube_lower_of_latticeMinorant _ w x z hblock hmass hmod
  have hmajor : ∀ n : Fin d → ℤ,
      (if n ∈ oneSidedFrequencyValues d (M + 1) then 1 else 0) ≤
        bartonMajorant 0 M q (fun k => n k) := by
    intro n
    by_cases hn : n ∈ oneSidedFrequencyValues d (M + 1)
    · rw [if_pos hn]
      apply Finset.one_le_prod
      intro k _
      have hk := (integer_cube_mem_iff n).1 hn k
      exact one_le_majorant_closed hMr hq hk.1 hk.2
    · rw [if_neg hn]
      exact bartonMajorant_nonneg hMr.le hq _
  have hhi := translatedCube_upper_of_barton 0 M q (((M : ℝ) + q⁻¹) ^ d) x z
    hmajor (fun n => bartonMajorant_nonneg hMr.le hq _)
    (by simpa only [sub_zero] using bartonMajorant_hasSum (d := d) hMr.le hq hq1)
    (fun i j hij => bartonMajorantModulated_hasSum_zero hMr.le hq (hcross i j hij))
  have hp : ((M : ℝ) + q⁻¹) ^ d =
      ((M : ℝ) + q⁻¹) ^ (d - 1) * ((M : ℝ) + q⁻¹) := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  have hcoeff : ((M : ℝ) + q⁻¹) ^ (d - 1) *
      ((M : ℝ) + (3 / 2 : ℝ) * d - (2 * (d : ℝ) - 1) * q⁻¹) ≤
      ((M : ℝ) + q⁻¹) ^ d - d *
        (((M : ℝ) + q⁻¹) - ((M : ℝ) + 2 - q⁻¹)) * ((M : ℝ) + q⁻¹) ^ (d - 1) := by
    rw [hp]
    have hpow : 0 ≤ ((M : ℝ) + q⁻¹) ^ (d - 1) := by positivity
    have hd0 : (0 : ℝ) ≤ d := by positivity
    nlinarith [mul_nonneg hd0 hpow]
  have henergy : 0 ≤ External.coefficientEnergy z :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hlo' := (mul_le_mul_of_nonneg_right hcoeff henergy).trans hlo
  simpa only [x, translated_cube_energy_eq, hqinv, External.coefficientEnergy] using
    And.intro hlo' hhi


/-- Full-Gram bounds used by the simultaneous off-grid sampling theorem.
The deterministic statement also holds when the lower bound is nonpositive. -/
theorem uniform_cube_full_gram_bounds {d M s : ℕ}
    (hd : 1 ≤ d) (hM : 1 ≤ M) {Δ : ℝ}
    (hΔ : 0 < Δ) (hΔupper : Δ ≤ 2 * Real.pi)
    (Y : Fin s → Fin d → ℝ) (hsep : CubeAngularSeparated Δ Y)
    (z : EuclideanSpace ℂ (Fin s)) :
    uniformCubeLower d M Δ * ‖z‖ ^ 2 ≤
        FiniteMatrixSampling.quadratic (cubeFullGram M Y) z ∧
      FiniteMatrixSampling.quadratic (cubeFullGram M Y) z ≤
        cubeSeparatedUpper d M Δ * ‖z‖ ^ 2 := by
  have he := uniform_cube_full_energy_bounds (M := M) hd (by omega) hΔ hΔupper Y hsep (WithLp.ofLp z)
  have hmean : FiniteMatrixSampling.quadratic (cubeFullGram M Y) z =
      (((M : ℝ) + 1) ^ d)⁻¹ * cubeFullFourierEnergy M Y (WithLp.ofLp z) := by
    rw [cubeFullGram, quadratic_cubeFourier_mean]
    rfl
  rw [hmean, EuclideanSpace.norm_sq_eq]
  have hN : 0 ≤ (((M : ℝ) + 1) ^ d)⁻¹ := by positivity
  constructor
  · calc
      uniformCubeLower d M Δ * (∑ j, ‖WithLp.ofLp z j‖ ^ 2) =
          (((M : ℝ) + 1) ^ d)⁻¹ *
            ((((M : ℝ) + 2 * Real.pi / Δ) ^ (d - 1) *
              ((M : ℝ) + (3 / 2 : ℝ) * d -
                (2 * (d : ℝ) - 1) * (2 * Real.pi / Δ))) *
              (∑ j, ‖WithLp.ofLp z j‖ ^ 2)) := by
        unfold uniformCubeLower
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he.1 hN
  · calc
      (((M : ℝ) + 1) ^ d)⁻¹ * cubeFullFourierEnergy M Y (WithLp.ofLp z) ≤
          (((M : ℝ) + 1) ^ d)⁻¹ *
            (((M : ℝ) + 2 * Real.pi / Δ) ^ d * (∑ j, ‖WithLp.ofLp z j‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left he.2 hN
      _ = cubeSeparatedUpper d M Δ * (∑ j, ‖WithLp.ofLp z j‖ ^ 2) := by
        unfold cubeSeparatedUpper
        ring

end
end LeanNumDetect.RandSamp
