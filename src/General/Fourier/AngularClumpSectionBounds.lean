import General.Fourier.ClumpJetApproximation
import General.Fourier.SmallFrequencyEvaluationBounds
import General.Fourier.PolynomialCrossCorrelation
import Mathlib.Tactic

/-!
# Gap-free bounds for angular Fourier sections

Small companion evolutions provide integer-grid row bounds and polynomial
approximations through collisions of the projected frequencies. Angular
shortness is expressed by individual integer windings, so these reusable
analytic statements do not prescribe a torus model or require distinct
coordinate projections.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators InnerProductSpace Matrix.Norms.Operator
open Matrix WithLp Set

namespace LeanNumDetect.AngularClumpSectionBounds
open ClumpJetApproximation SmallFrequencyEvaluationBounds
noncomputable section

/-- Every source has a lift within the prescribed radius of the center. -/
def WithinAngularClump {s : ℕ} (M : ℕ) (node : Fin s → ℝ) (center r : ℝ) : Prop :=
  ∀ j, ∃ p : ℤ, |node j - center + 2 * Real.pi * p| ≤ r / (M : ℝ)

theorem scaled_frequency_norm_le {s M : ℕ} (hM : 0 < M)
    (node : Fin s → ℝ) (center r : ℝ) (hr : 0 ≤ r) (p : Fin s → ℤ)
    (hp : ∀ j, |node j - center + 2 * Real.pi * p j| ≤ r / (M : ℝ)) :
    ‖fun j => Complex.I * (((M : ℝ) *
      (node j - center + 2 * Real.pi * p j) : ℝ) : ℂ)‖ ≤ r := by
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  apply (pi_norm_le_iff_of_nonneg hr).2
  intro j
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hMR]
  simpa only [mul_comm] using (le_div_iff₀ hMR).1 (hp j)

theorem evolutionVector_coordinate_norm {s M : ℕ} (hs : 0 < s)
    (frequency jet : Fin s → ℂ) (center : ℝ) (k : Fin (M + 1)) :
    ‖evolutionVector hs M frequency jet center k‖ =
      ‖evolutionSignal hs frequency jet ((k.val : ℝ) / M)‖ := by
  have hphase : ‖Complex.exp (Complex.I * (((k.val : ℝ) * center : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  simp only [evolutionVector, ofLp_toLp, norm_mul, hphase, one_mul, evolutionSignal]

theorem evolutionVector_norm_sq {s M : ℕ} (hs : 0 < s)
    (frequency jet : Fin s → ℂ) (center : ℝ) :
    ‖evolutionVector hs M frequency jet center‖ ^ 2 =
      ∑ l ∈ Finset.range (M + 1), ‖evolutionSignal hs frequency jet ((l : ℝ) / M)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [evolutionVector_coordinate_norm]
  exact Fin.sum_univ_eq_sum_range
    (fun l : ℕ => ‖evolutionSignal hs frequency jet ((l : ℝ) / M)‖ ^ 2) (M + 1)

/-- Absolute row constant `512`, valid even when projected nodes coincide. -/
theorem exists_angularClump_row_bounds (s : ℕ) (hs : 0 < s) :
    ∃ r B : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < B ∧
      ∀ (M : ℕ), B ≤ (M : ℝ) → 0 < M →
        ∀ (node : Fin s → ℝ) (center : ℝ), WithinAngularClump M node center r →
          ∀ u ∈ ClusteredVandermonde.clusterSubspace M node,
            ∀ k : Fin (M + 1), (M + 1 : ℝ) * ‖u k‖ ^ 2 ≤
              512 * (s : ℝ) ^ 2 * ‖u‖ ^ 2 := by
  obtain ⟨r, B, c, hr, hr1, hB, hc, hbounds⟩ := smallFrequency_grid_jet_bounds hs
  refine ⟨r, B, hr, hr1, hB, ?_⟩
  intro M hsize hM node center hwithin u hu k
  obtain ⟨coefficient, rfl⟩ := clusterSubspace_coefficient_representation node u hu
  choose p hp using hwithin
  let frequency : Fin s → ℂ := fun j => Complex.I * (((M : ℝ) *
    (node j - center + 2 * Real.pi * p j) : ℝ) : ℂ)
  let jet := ExponentialCompanion.initialJet frequency coefficient
  have hfrequency : ‖frequency‖ ≤ r := scaled_frequency_norm_le hM node center r hr.le p hp
  have heq := angularSignal_eq_evolutionVector hs hM node coefficient center p
  change angularSignal M node coefficient = evolutionVector hs M frequency jet center at heq
  rw [heq, evolutionVector_coordinate_norm, evolutionVector_norm_sq]
  exact (hbounds frequency jet M hfrequency hM hsize).2 k.val (by omega)

/-- A sufficiently short section has a relative polynomial approximation
whose coefficients are controlled by the actual section norm. -/
theorem angularClump_polynomial_approximation {s M : ℕ} (hs : 0 < s) (hM : 0 < M)
    (node : Fin s → ℝ) (center r D ε : ℝ) (hr : 0 ≤ r) (_hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hclose : ∀ frequency : Fin s → ℂ, ‖frequency‖ ≤ r →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ j : Fin s,
        ‖NormedSpace.exp ((t : ℂ) • ExponentialCompanion.generator frequency) ⟨0, hs⟩ j -
          (t : ℂ) ^ j.val / (j.val.factorial : ℂ)‖ ≤ ε)
    (hjet : ∀ frequency jet : Fin s → ℂ, ‖frequency‖ ≤ r →
      ‖jet‖ ≤ D / Real.sqrt (M + 1 : ℝ) * ‖evolutionVector hs M frequency jet 0‖)
    (hwithin : WithinAngularClump M node center r)
    (u : EuclideanSpace ℂ (Fin (M + 1)))
    (hu : u ∈ ClusteredVandermonde.clusterSubspace M node) :
    ∃ c : Fin s → ℂ,
      ‖u - PolynomialCrossCorrelation.modulatedPolynomial M center c‖ ≤
        ((s : ℝ) * ε * D) * ‖u‖ ∧
      (∑ j, ‖c j‖) ≤ ((s : ℝ) * D / Real.sqrt (M + 1 : ℝ)) * ‖u‖ := by
  classical
  obtain ⟨coefficient, rfl⟩ := clusterSubspace_coefficient_representation node u hu
  choose p hp using hwithin
  let frequency : Fin s → ℂ := fun j => Complex.I * (((M : ℝ) *
    (node j - center + 2 * Real.pi * p j) : ℝ) : ℂ)
  let jet := ExponentialCompanion.initialJet frequency coefficient
  have hfrequency : ‖frequency‖ ≤ r := scaled_frequency_norm_le hM node center r hr p hp
  have heq := angularSignal_eq_evolutionVector hs hM node coefficient center p
  change angularSignal M node coefficient = evolutionVector hs M frequency jet center at heq
  have hjet' : ‖jet‖ ≤ D / Real.sqrt (M + 1 : ℝ) * ‖angularSignal M node coefficient‖ := by
    rw [heq, evolutionVector_norm_eq hs]
    exact hjet frequency jet hfrequency
  have hsqrt : 0 < Real.sqrt (M + 1 : ℝ) := by positivity
  refine ⟨jetCoefficient jet, ?_, ?_⟩
  · rw [heq]
    have herr := evolutionVector_polynomial_approximation hs hM frequency jet center ε hε
      (hclose frequency hfrequency)
    have hnorm : ‖jet‖ ≤ D / Real.sqrt (M + 1 : ℝ) *
        ‖evolutionVector hs M frequency jet center‖ := by rwa [heq] at hjet'
    calc
      _ ≤ Real.sqrt (M + 1 : ℝ) * ((s : ℝ) * ε * ‖jet‖) := herr
      _ ≤ Real.sqrt (M + 1 : ℝ) * ((s : ℝ) * ε *
          (D / Real.sqrt (M + 1 : ℝ) * ‖evolutionVector hs M frequency jet center‖)) := by
        gcongr
      _ = _ := by field_simp
  · exact (jetCoefficient_sum_norm_le jet).trans
      ((mul_le_mul_of_nonneg_left hjet' (Nat.cast_nonneg s)).trans_eq (by ring))

theorem exists_angularClump_polynomial_bounds (s : ℕ) (hs : 0 < s)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r Q L : ℝ, 0 < r ∧ 0 < Q ∧ 0 < L ∧
      ∀ (M : ℕ), Q ≤ (M : ℝ) → 0 < M →
        ∀ (node : Fin s → ℝ) (center : ℝ), WithinAngularClump M node center r →
          ∀ u ∈ ClusteredVandermonde.clusterSubspace M node,
            ∃ c : Fin s → ℂ,
              ‖u - PolynomialCrossCorrelation.modulatedPolynomial M center c‖ ≤ ε * ‖u‖ ∧
              (∑ j, ‖c j‖) ≤ L / Real.sqrt (M + 1 : ℝ) * ‖u‖ := by
  obtain ⟨η, Q, D, hη, hQ, hD, hjet⟩ := exists_evolutionVector_jet_bounds hs
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  obtain ⟨r, hr, hclose⟩ := ExponentialCompanion.exists_uniform_jet_radius hs
    (ε / ((s : ℝ) * D)) (by positivity)
  refine ⟨min r η, Q, (s : ℝ) * D, lt_min hr hη, hQ, by positivity, ?_⟩
  intro M hsize hM node center hwithin u hu
  obtain ⟨c, herr, hcoeff⟩ := angularClump_polynomial_approximation hs hM node center
    (min r η) D (ε / ((s : ℝ) * D)) (le_of_lt (lt_min hr hη)) hD.le
    (by positivity)
    (fun frequency hf => hclose frequency (hf.trans (min_le_left _ _)))
    (fun frequency jet hf => hjet M hsize hM frequency jet (hf.trans (min_le_right _ _)))
    hwithin u hu
  refine ⟨c, ?_, hcoeff⟩
  convert herr using 1
  field_simp

theorem WithinAngularClump.mono {s M : ℕ} (hM : 0 < M)
    {node : Fin s → ℝ} {center r R : ℝ} (h : WithinAngularClump M node center r)
    (hr : r ≤ R) : WithinAngularClump M node center R := by
  intro j
  obtain ⟨p, hp⟩ := h j
  exact ⟨p, hp.trans (div_le_div_of_nonneg_right hr (by positivity))⟩

/-- Common thresholds provide both row evaluation and cross-subspace bounds
for every allowed cardinality. Additional radius and resolution requirements
can be imposed before the thresholds are chosen. -/
theorem angularClump_section_thresholds (n nstar : ℕ) (hn : 0 < n) (hnstar : 0 < nstar)
    (B b : ℕ → ℝ) (hb : ∀ s, 1 ≤ s → s ≤ nstar → 0 < b s) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      (∀ s, 1 ≤ s → s ≤ nstar → B s ≤ C0 ∧ c0 ≤ b s) ∧
      (∀ (s M : ℕ), 0 < s → s ≤ nstar → C0 ≤ (M : ℝ) →
        ∀ (node : Fin s → ℝ) (center : ℝ), WithinAngularClump M node center c0 →
          ∀ u ∈ ClusteredVandermonde.clusterSubspace M node,
            ∀ k : Fin (M + 1), (M + 1 : ℝ) * ‖u k‖ ^ 2 ≤
              512 * (s : ℝ) ^ 2 * ‖u‖ ^ 2) ∧
      (∀ (s t M : ℕ), 0 < s → s ≤ nstar → 0 < t → t ≤ nstar → C0 ≤ (M : ℝ) →
        ∀ (node : Fin s → ℝ) (node' : Fin t → ℝ) (x y : ℝ),
          WithinAngularClump M node x c0 → WithinAngularClump M node' y c0 →
          (∀ p : ℤ, C0 / (M : ℝ) ≤ |y - x - 2 * Real.pi * p|) →
          ∀ u ∈ ClusteredVandermonde.clusterSubspace M node,
            ∀ v ∈ ClusteredVandermonde.clusterSubspace M node',
              ‖⟪u, v⟫_ℂ‖ ≤ (1 / (2 * (n : ℝ))) * ‖u‖ * ‖v‖) := by
  classical
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let ε : ℝ := 1 / (32 * (n : ℝ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  choose rR QR hrR hrR1 hQR hrow using
    fun i : Fin nstar => exists_angularClump_row_bounds (i.val + 1) (by omega)
  choose rP QP DP hrP hQP hDP happrox using
    fun i : Fin nstar => exists_angularClump_polynomial_bounds (i.val + 1) (by omega) ε hε
  let f : Fin nstar → ℝ := fun i => max 1 (max (DP i) (max |QP i| (max |QR i|
    (max |B (i.val + 1)| (max (rP i)⁻¹ (max (rR i)⁻¹ (b (i.val + 1))⁻¹))))))
  obtain ⟨L, hL⟩ := (Set.finite_range f).bddAbove
  have hbounds (i : Fin nstar) : 1 ≤ L ∧ DP i ≤ L ∧ |QP i| ≤ L ∧ |QR i| ≤ L ∧
      |B (i.val + 1)| ≤ L ∧ (rP i)⁻¹ ≤ L ∧ (rR i)⁻¹ ≤ L ∧
        (b (i.val + 1))⁻¹ ≤ L := by
    have h := hL (Set.mem_range_self i)
    simpa only [f, max_le_iff] using h
  have hL1 : 1 ≤ L := (hbounds ⟨0, hnstar⟩).1
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  let T := max (n : ℝ) (max L (64 * (n : ℝ) * Real.pi * L ^ 2))
  have hnT : (n : ℝ) ≤ T := le_max_left _ _
  have hLT : L ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hcrossT : 64 * (n : ℝ) * Real.pi * L ^ 2 ≤ T :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hT0 : 0 < T := hL0.trans_le hLT
  have hT1 : 1 ≤ T := hL1.trans hLT
  have hsmall : 1 / (2 * T) ≤ 1 / L := by
    apply one_div_le_one_div_of_le hL0
    linarith
  have hinv (x : ℝ) (hx : 0 < x) (h : x⁻¹ ≤ L) : 1 / L ≤ x := by
    apply (div_le_iff₀ hL0).2
    have hh := mul_le_mul_of_nonneg_left h hx.le
    simpa only [mul_inv_cancel₀ hx.ne', mul_comm x L] using hh
  have hsmallP (i : Fin nstar) : 1 / (2 * T) ≤ rP i :=
    hsmall.trans (hinv (rP i) (hrP i) (hbounds i).2.2.2.2.2.1)
  have hsmallR (i : Fin nstar) : 1 / (2 * T) ≤ rR i :=
    hsmall.trans (hinv (rR i) (hrR i) (hbounds i).2.2.2.2.2.2.1)
  refine ⟨1 / (2 * T), T, by positivity,
    (div_lt_one (by positivity : 0 < 2 * T)).2 (by linarith), hnT, ?_, ?_, ?_⟩
  · intro s hs hsmax
    let i : Fin nstar := ⟨s - 1, by omega⟩
    have hi : i.val + 1 = s := by dsimp [i]; omega
    rcases hbounds i with ⟨_, _, _, _, hBi, _, _, hbi⟩
    constructor
    · exact (le_abs_self (B s)).trans ((hi ▸ hBi).trans hLT)
    · exact hsmall.trans (hinv (b s) (hb s hs hsmax) (hi ▸ hbi))
  · intro s M hs hsmax hM node center hwithin u hu k
    let i : Fin nstar := ⟨s - 1, by omega⟩
    have hi : i.val + 1 = s := by dsimp [i]; omega
    have hMR : 0 < (M : ℝ) := hT0.trans_le hM
    have hMN : 0 < M := by exact_mod_cast hMR
    have hQRi : QR i ≤ (M : ℝ) :=
      (le_abs_self _).trans ((hbounds i).2.2.2.1.trans (hLT.trans hM))
    have h := hrow i
    rw [hi] at h
    exact h M hQRi hMN node center (hwithin.mono hMN (hsmallR i)) u hu k
  · intro s t M hs hsmax ht htmax hM node node' x y hwithin hwithin' hsep u hu v hv
    let i : Fin nstar := ⟨s - 1, by omega⟩
    let j : Fin nstar := ⟨t - 1, by omega⟩
    have hi : i.val + 1 = s := by dsimp [i]; omega
    have hj : j.val + 1 = t := by dsimp [j]; omega
    have hMR : 0 < (M : ℝ) := hT0.trans_le hM
    have hMN : 0 < M := by exact_mod_cast hMR
    have hQi : QP i ≤ (M : ℝ) :=
      (le_abs_self _).trans ((hbounds i).2.2.1.trans (hLT.trans hM))
    have hQj : QP j ≤ (M : ℝ) :=
      (le_abs_self _).trans ((hbounds j).2.2.1.trans (hLT.trans hM))
    have hai := happrox i
    have haj := happrox j
    rw [hi] at hai
    rw [hj] at haj
    obtain ⟨c, huc, hcnorm⟩ := hai M hQi hMN node x (hwithin.mono hMN (hsmallP i)) u hu
    obtain ⟨d, hvd, hdnorm⟩ := haj M hQj hMN node' y (hwithin'.mono hMN (hsmallP j)) v hv
    have hsqrt : 0 < Real.sqrt (M + 1 : ℝ) := by positivity
    have hcnorm' : (∑ k, ‖c k‖) ≤ L / Real.sqrt (M + 1 : ℝ) * ‖u‖ :=
      hcnorm.trans (by gcongr; exact (hbounds i).2.1)
    have hdnorm' : (∑ k, ‖d k‖) ≤ L / Real.sqrt (M + 1 : ℝ) * ‖v‖ :=
      hdnorm.trans (by gcongr; exact (hbounds j).2.1)
    have hpoly := PolynomialCrossCorrelation.inner_modulatedPolynomial_norm_le hMN c d x y
      (T / M) (by positivity) hsep
    have hpoly' : ‖⟪PolynomialCrossCorrelation.modulatedPolynomial M x c,
        PolynomialCrossCorrelation.modulatedPolynomial M y d⟫_ℂ‖ ≤
        (Real.pi * L ^ 2 / T) * ‖u‖ * ‖v‖ := by
      have hratio : (M : ℝ) / (M + 1 : ℝ) ≤ 1 := by
        apply (div_le_one (by positivity)).2
        linarith
      calc
        _ ≤ (Real.pi / (T / M)) * (L / Real.sqrt (M + 1 : ℝ) * ‖u‖) *
            (L / Real.sqrt (M + 1 : ℝ) * ‖v‖) := hpoly.trans (by gcongr)
        _ = (Real.pi * L ^ 2 / T) * ((M : ℝ) / (M + 1 : ℝ)) * ‖u‖ * ‖v‖ := by
          field_simp
          rw [Real.sq_sqrt (by positivity : 0 ≤ (M + 1 : ℝ))]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio
            (show 0 ≤ Real.pi * L ^ 2 / T by positivity)
    have hκ : Real.pi * L ^ 2 / T ≤ 1 / (64 * (n : ℝ)) := by
      apply (div_le_div_iff₀ hT0 (by positivity)).2
      nlinarith [hcrossT]
    have hpoly'' : ‖⟪PolynomialCrossCorrelation.modulatedPolynomial M x c,
        PolynomialCrossCorrelation.modulatedPolynomial M y d⟫_ℂ‖ ≤
        (1 / (64 * (n : ℝ))) * ‖u‖ * ‖v‖ :=
      hpoly'.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hκ (norm_nonneg u)) (norm_nonneg v))
    have hresult := PolynomialCrossCorrelation.inner_approximation_bound u v
      (PolynomialCrossCorrelation.modulatedPolynomial M x c)
      (PolynomialCrossCorrelation.modulatedPolynomial M y d) hε.le huc hvd hpoly''
    have heps : (1 / (64 * (n : ℝ)) + 2 * ε + ε ^ 2) ≤ 1 / (2 * (n : ℝ)) := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      dsimp [ε]
      field_simp
      nlinarith
    exact hresult.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right heps (norm_nonneg u)) (norm_nonneg v))

end
end LeanNumDetect.AngularClumpSectionBounds
