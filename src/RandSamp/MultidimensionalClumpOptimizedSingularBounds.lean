import RandSamp.MultidimensionalClumpSingularBounds
import RandSamp.CubeClumpLeverage
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Clump-local cardinal interpolation and almost-orthogonal energy assembly.
The lower coefficient depends on dimension and maximal clump size only.
The earlier global interpolation and sharpness interfaces remain unchanged. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators InnerProductSpace ComplexOrder
open Matrix WithLp

namespace LeanNumDetect.RandSamp
noncomputable section
open MultidimensionalTrigonometricInterpolation SeparatedAngularFrequency

/-- The center contributes mass one, so there are exactly `n-1` factors
of mass at most two. This includes a singleton packet. -/
theorem cube_globalPacket_mass_le_predecessor {d n : ℕ} (Q : ℕ)
    (Y : Fin n → Fin d → ℝ) (i : Fin n) (r : Fin n → Fin d)
    (q : Fin n → ℕ) (hq : ∀ j, q j ≤ Q) (scale : Fin n → ℝ)
    (hscale0 : ∀ j, 0 ≤ scale j)
    (hden : ∀ j, j ≠ i → 0 < ‖Complex.exp (Complex.I * ((q j : ℝ) * Y i (r j) : ℝ)) -
      Complex.exp (Complex.I * ((q j : ℝ) * Y j (r j) : ℝ))‖)
    (hscale : ∀ j, j ≠ i → scale j ≤
      ‖Complex.exp (Complex.I * ((q j : ℝ) * Y i (r j) : ℝ)) -
        Complex.exp (Complex.I * ((q j : ℝ) * Y j (r j) : ℝ))‖) :
    (CubePacket.globalPacket Q Y i r q hq scale).mass ≤ (2 : ℝ) ^ (n - 1) := by
  classical
  rw [CubePacket.globalPacket, CubePacket.mass_prod,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [ite_true, CubePacket.mass_one, mul_one]
  calc
    _ ≤ ∏ _j ∈ Finset.univ.erase i, (2 : ℝ) := Finset.prod_le_prod
      (fun _ _ => CubePacket.mass_nonneg _) (fun j hj => by
        have hji := Finset.ne_of_mem_erase hj
        simp only [if_neg hji]
        exact CubePacket.scaled_coordinateFactor_mass_le Q (r j) (q j) (hq j)
          (Y i (r j)) (Y j (r j)) (hscale0 j) (hden j hji) (hscale j hji))
    _ = _ := by simp

/-- Keeping the square root of the cube averaging ratio gives its exact
dimension factor. An upper bound on the source count may be used uniformly. -/
theorem cube_minimumSingularValue_lower_of_packets_explicit {d n nstar M Q L : ℕ}
    (hn : 0 < n) (hns : n ≤ nstar) (hL : 0 < L) (hband : Q + L ≤ M + 1)
    (hratio : M + 1 ≤ 2 * L) (Y : Fin n → Fin d → ℝ)
    (G : Fin n → CubePacket d Q) (w : Fin n → ℝ) {b massBound : ℝ}
    (hb : 0 ≤ b) (hmassBound : 0 < massBound) (hw : ∀ i, b ≤ w i)
    (hmass : ∀ i, (G i).mass ≤ massBound)
    (hvalue : ∀ i j, (G i).value (Y j) = if i = j then (w i : ℂ) else 0) :
    b / (Real.sqrt (nstar : ℝ) * massBound * Real.sqrt ((2 : ℝ) ^ d)) ≤
      matrixSingularValue (cubeFullVandermonde M Y) (n - 1) := by
  classical
  let V := cubeFullVandermonde M Y
  let N : ℝ := (((M + 1) ^ d : ℕ) : ℝ)
  let R : ℝ := (((L ^ d : ℕ) : ℝ))
  have hN : 0 < N := by dsimp [N]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  let H := fun i : Fin n => (G i).averagedVector hband (Y i)
  let C : Matrix (Fin n) (CubeFrequency d M) ℂ :=
    fun i k => (Real.sqrt N : ℂ) * ofLp (H i) k
  have hNcomplex : (Real.sqrt N : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hN).ne'
  have hCV : C * V = Matrix.diagonal (fun i => (w i : ℂ)) := by
    ext i j
    change (∑ k : CubeFrequency d M, ((Real.sqrt N : ℂ) * ofLp (H i) k) *
      ((Real.sqrt N : ℂ)⁻¹ * cubeFourierRow Y k j)) = _
    have ht (k : CubeFrequency d M) : ((Real.sqrt N : ℂ) * ofLp (H i) k) *
        ((Real.sqrt N : ℂ)⁻¹ * cubeFourierRow Y k j) =
        ofLp (H i) k * cubeFourierRow Y k j := by field_simp
    simp_rw [ht]
    change (ofLp (H i)) ⬝ᵥ (fun k => exponential (fun r => (k r).val) (Y j)) = _
    by_cases hij : i = j
    · subst j
      rw [CubePacket.averagedVector_evaluation_center hL, hvalue]
      simp [Matrix.diagonal]
    · rw [CubePacket.averagedVector_evaluation, hvalue, if_neg hij, zero_mul]
      simp [Matrix.diagonal, hij]
  have hnorm (i : Fin n) : ‖H i‖ ≤ massBound * Real.sqrt R⁻¹ :=
    ((G i).averagedVector_norm_le hL hband (Y i)).trans
      (mul_le_mul_of_nonneg_right (hmass i) (Real.sqrt_nonneg _))
  have hNR : N ≤ (2 : ℝ) ^ d * R := by
    have h := Nat.pow_le_pow_left hratio d
    dsimp [N, R]
    exact_mod_cast (by simpa only [Nat.mul_pow] using h)
  have hC (i : Fin n) :
      SegmentedVDM.energy (C i) ≤ (massBound * Real.sqrt ((2 : ℝ) ^ d)) ^ 2 := by
    have hH : ‖H i‖ ^ 2 ≤ massBound ^ 2 * R⁻¹ := by
      have h := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hnorm i)
      simpa only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ R⁻¹)] using h
    have hCE : SegmentedVDM.energy (C i) = N * ‖H i‖ ^ 2 := by
      unfold SegmentedVDM.energy C
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hN.le]
      rw [← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq]
    rw [hCE, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ) ^ d)]
    have hRratio : N * R⁻¹ ≤ (2 : ℝ) ^ d := by
      rw [← div_eq_mul_inv]
      exact (div_le_iff₀ hR).mpr hNR
    calc
      _ ≤ N * (massBound ^ 2 * R⁻¹) := mul_le_mul_of_nonneg_left hH hN.le
      _ = massBound ^ 2 * (N * R⁻¹) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hRratio (sq_nonneg _)
  obtain ⟨z, hz, he⟩ := exists_unit_vector_norm_sq_eq_singularValue_sq V
    (i := n - 1) (by simpa using Nat.sub_lt hn Nat.zero_lt_one)
  have henergy := diagonal_interpolation_energy_lower V C w hCV hb hw hC (ofLp z)
  change b ^ 2 * (∑ i, ‖ofLp z i‖ ^ 2) ≤
    (n : ℝ) * (massBound * Real.sqrt ((2 : ℝ) ^ d)) ^ 2 *
      (∑ k, ‖(V *ᵥ ofLp z) k‖ ^ 2) at henergy
  rw [← EuclideanSpace.norm_sq_eq, hz, one_pow, mul_one] at henergy
  have heEnergy : (∑ k, ‖(V *ᵥ ofLp z) k‖ ^ 2) = ‖V.toEuclideanLin z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  rw [heEnergy, he] at henergy
  have hnsR : (n : ℝ) ≤ nstar := by exact_mod_cast hns
  have henergy' : b ^ 2 ≤ (nstar : ℝ) * (massBound * Real.sqrt ((2 : ℝ) ^ d)) ^ 2 *
      V.toEuclideanLin.singularValues (n - 1) ^ 2 :=
    henergy.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hnsR (sq_nonneg _)) (sq_nonneg _))
  have hden : 0 < Real.sqrt (nstar : ℝ) * massBound * Real.sqrt ((2 : ℝ) ^ d) := by
    have : 0 < nstar := lt_of_lt_of_le hn hns
    positivity
  apply (div_le_iff₀ hden).mpr
  apply (sq_le_sq₀ hb (mul_nonneg (V.toEuclideanLin.singularValues_nonneg _) hden.le)).mp
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg nstar)]
  nlinarith only [henergy']

/-- A coordinate attaining the periodic infinity distance supplies a local
cardinal factor at the single blow-up frequency `Q`. -/
theorem cube_short_pair_chord {d t M Q : ℕ} (hd : 1 ≤ d)
    (hQM : (Q : ℝ) ≤ (M : ℝ)) (Y : Fin t → Fin d → ℝ)
    (hwithin : ∀ i j, (M : ℝ) * multidimensionalAngularTorusDistance (Y i) (Y j) ≤ 1)
    {Δ scaleLower : ℝ}
    (hgap : ∀ i j, i ≠ j → Δ ≤ multidimensionalAngularTorusDistance (Y i) (Y j))
    (hscaleLower : scaleLower ≤ (2 / Real.pi) * (Q : ℝ) * Δ)
    (i j : Fin t) (hij : i ≠ j) :
    ∃ r : Fin d, scaleLower ≤
      ‖Complex.exp (Complex.I * (((Q : ℝ) * Y i r : ℝ) : ℂ)) -
        Complex.exp (Complex.I * (((Q : ℝ) * Y j r : ℝ) : ℂ))‖ := by
  obtain ⟨r, hr⟩ := multidimensionalAngularTorusDistance_attained hd (Y i) (Y j)
  obtain ⟨p, hp⟩ := angularTorusDistance_eq_winding (Y i r) (Y j r)
  let θ := Y i r - Y j r + 2 * Real.pi * p
  have hθ : |θ| = multidimensionalAngularTorusDistance (Y i) (Y j) := hp.symm.trans hr
  have hθgap : Δ ≤ |θ| := by rw [hθ]; exact hgap i j hij
  have hθshort : |(Q : ℝ) * θ| ≤ Real.pi := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg Q), hθ]
    exact ((mul_le_mul_of_nonneg_right hQM
      (multidimensionalAngularTorusDistance_nonneg hd _ _)).trans
      (hwithin i j)).trans (by linarith [Real.pi_gt_three])
  have hchord := short_integer_frequency_chord_lower Q θ Δ hθgap hθshort
  refine ⟨r, ?_⟩
  rw [integer_phase_difference_norm]
  have hphase := integer_frequency_phase_winding Q (Y i r - Y j r) p
  change Complex.exp (Complex.I * (((Q : ℝ) * θ : ℝ) : ℂ)) = _ at hphase
  rw [← hphase]
  exact hscaleLower.trans hchord

/-- On the short angular interval supplied by the clump geometry, the
unit-circle chord loses at most one tenth of the angle. -/
theorem cube_unit_angle_chord_lower {θ : ℝ} (hθ : |θ| ≤ 1) :
    (9 / 10 : ℝ) * |θ| ≤ ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ := by
  have hhalf : |θ / 2| ≤ Real.pi := by
    rw [abs_div]
    norm_num
    linarith [Real.pi_gt_three]
  have hsin := Real.sin_ge_sub_cube (by positivity : 0 ≤ |θ| / 2)
  have hsq : |θ| ^ 2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ (abs_nonneg θ) (by norm_num)).mpr hθ
  have hcube : |θ| ^ 3 ≤ |θ| := by
    nlinarith [mul_le_mul_of_nonneg_right hsq (abs_nonneg θ)]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.abs_sin_eq_sin_abs_of_abs_le_pi hhalf, abs_div]
  norm_num
  nlinarith [abs_nonneg θ]

/-- The tighter local chord estimate uses only the existing clump width
bound; no extra geometric assumption is introduced. -/
theorem cube_short_pair_chord_tight {d t M Q : ℕ} (hd : 1 ≤ d)
    (hQM : (Q : ℝ) ≤ (M : ℝ)) (Y : Fin t → Fin d → ℝ)
    (hwithin : ∀ i j, (M : ℝ) * multidimensionalAngularTorusDistance (Y i) (Y j) ≤ 1)
    {Δ scaleLower : ℝ}
    (hgap : ∀ i j, i ≠ j → Δ ≤ multidimensionalAngularTorusDistance (Y i) (Y j))
    (hscaleLower : scaleLower ≤ (9 / 10 : ℝ) * (Q : ℝ) * Δ)
    (i j : Fin t) (hij : i ≠ j) :
    ∃ r : Fin d, scaleLower ≤
      ‖Complex.exp (Complex.I * (((Q : ℝ) * Y i r : ℝ) : ℂ)) -
        Complex.exp (Complex.I * (((Q : ℝ) * Y j r : ℝ) : ℂ))‖ := by
  obtain ⟨r, hr⟩ := multidimensionalAngularTorusDistance_attained hd (Y i) (Y j)
  obtain ⟨p, hp⟩ := angularTorusDistance_eq_winding (Y i r) (Y j r)
  let θ := Y i r - Y j r + 2 * Real.pi * p
  have hθ : |θ| = multidimensionalAngularTorusDistance (Y i) (Y j) := hp.symm.trans hr
  have hθgap : Δ ≤ |θ| := by rw [hθ]; exact hgap i j hij
  have hθshort : |(Q : ℝ) * θ| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg Q), hθ]
    exact (mul_le_mul_of_nonneg_right hQM
      (multidimensionalAngularTorusDistance_nonneg hd _ _)).trans (hwithin i j)
  have hchord := cube_unit_angle_chord_lower hθshort
  have hscaledGap : (9 / 10 : ℝ) * (Q : ℝ) * Δ ≤ (9 / 10 : ℝ) * |(Q : ℝ) * θ| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg Q), ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hθgap (by positivity)
  refine ⟨r, ?_⟩
  rw [integer_phase_difference_norm]
  have hphase := integer_frequency_phase_winding Q (Y i r - Y j r) p
  change Complex.exp (Complex.I * (((Q : ℝ) * θ : ℝ) : ℂ)) = _ at hphase
  rw [← hphase]
  exact hscaleLower.trans (hscaledGap.trans hchord)

/-- Half-band interpolation leaves half the cube available for averaging.
The blow-up frequency is at least four, so its floor loss is at most one fifth. -/
theorem cube_interpolation_half_bandwidth_parameters {n M : ℕ} (hn : 0 < n)
    (hM : 8 * n ≤ M) :
    0 < M / (2 * n) ∧ M / (2 * n) ≤ M ∧
      2 * M ≤ 5 * n * (M / (2 * n)) ∧
      n * (M / (2 * n)) + (M / 2 + 1) ≤ M + 1 ∧
      M + 1 ≤ 2 * (M / 2 + 1) := by
  let Q := M / (2 * n)
  have hden : 0 < 2 * n := by omega
  have hQ4 : 4 ≤ Q := (Nat.le_div_iff_mul_le hden).mpr (by omega)
  have hQM : Q ≤ M := Nat.div_le_self _ _
  have hprod : 2 * (n * Q) ≤ M := by
    simpa only [Q, Nat.mul_assoc] using Nat.mul_div_le M (2 * n)
  have hlt : M < (Q + 1) * (2 * n) :=
    (Nat.div_lt_iff_lt_mul hden).mp (Nat.lt_succ_self Q)
  have hqge : 4 * n ≤ n * Q := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left n hQ4
  have hlow : 2 * M ≤ 5 * n * Q := by nlinarith
  refine ⟨by omega, hQM, hlow, ?_, ?_⟩
  · change n * Q + (M / 2 + 1) ≤ M + 1
    omega
  · omega

/-- A uniform local lower bound, including singleton clumps, with no factor
depending on the number of other clumps or the total source count. -/
theorem cube_local_clump_singular_lower {d t M nstar : ℕ}
    (hd : 1 ≤ d) (ht : 0 < t) (hts : t ≤ nstar)
    (hM : 8 * nstar ≤ M) (Y : Fin t → Fin d → ℝ)
    (hwithin : ∀ i j, (M : ℝ) * multidimensionalAngularTorusDistance (Y i) (Y j) ≤ 1)
    {Δ : ℝ} (hΔ : 0 < Δ) (hshort : (M : ℝ) * Δ ≤ 1)
    (hgap : ∀ i j, i ≠ j → Δ ≤ multidimensionalAngularTorusDistance (Y i) (Y j)) :
    (((M : ℝ) * Δ) / (3 * (nstar : ℝ))) ^ (nstar - 1) /
        (Real.sqrt (nstar : ℝ) * (2 : ℝ) ^ (nstar - 1) * Real.sqrt ((2 : ℝ) ^ d)) ≤
      matrixSingularValue (cubeFullVandermonde M Y) (t - 1) := by
  classical
  have hs : 0 < nstar := lt_of_lt_of_le ht hts
  have hsR : 0 < (nstar : ℝ) := by exact_mod_cast hs
  have hM0 : 0 < M := by omega
  obtain ⟨hQ0, hQM, hMQ, hbudget, hratio⟩ :=
    cube_interpolation_half_bandwidth_parameters hs hM
  let Q := M / (2 * nstar)
  let L := M / 2 + 1
  let scaleLower := ((M : ℝ) * Δ) / (3 * (nstar : ℝ))
  have hscale0 : 0 < scaleLower := by dsimp [scaleLower]; positivity
  have hscale1 : scaleLower ≤ 1 := by
    dsimp [scaleLower]
    apply (div_le_iff₀ (by positivity)).mpr
    have hs1 : (1 : ℝ) ≤ nstar := by exact_mod_cast hs
    nlinarith
  have hscaled : scaleLower ≤ (9 / 10 : ℝ) * (Q : ℝ) * Δ := by
    have hMQreal : 2 * (M : ℝ) ≤ 5 * (nstar : ℝ) * (Q : ℝ) := by exact_mod_cast hMQ
    dsimp [scaleLower]
    apply (div_le_iff₀ (by positivity)).mpr
    have hmul := mul_le_mul_of_nonneg_right hMQreal hΔ.le
    have hprod : 0 ≤ (nstar : ℝ) * (Q : ℝ) * Δ := by positivity
    field_simp
    nlinarith
  have hpairs : ∀ i j : Fin t, ∃ r : Fin d, j ≠ i → scaleLower ≤
      ‖Complex.exp (Complex.I * (((Q : ℝ) * Y i r : ℝ) : ℂ)) -
        Complex.exp (Complex.I * (((Q : ℝ) * Y j r : ℝ) : ℂ))‖ := by
    intro i j
    by_cases hji : j = i
    · exact ⟨⟨0, hd⟩, by simp [hji]⟩
    · obtain ⟨r, hr⟩ := cube_short_pair_chord_tight hd (by exact_mod_cast hQM) Y hwithin hgap
        hscaled i j (Ne.symm hji)
      exact ⟨r, fun _ => hr⟩
  choose r hr using hpairs
  let G := fun i : Fin t => CubePacket.globalPacket Q Y i (r i) (fun _ => Q)
    (fun _ => le_rfl) (fun _ => scaleLower)
  let w := fun _ : Fin t => scaleLower ^ (t - 1)
  have hdenPos (i j : Fin t) (hji : j ≠ i) :
      0 < ‖Complex.exp (Complex.I * (((Q : ℝ) * Y i (r i j) : ℝ) : ℂ)) -
        Complex.exp (Complex.I * (((Q : ℝ) * Y j (r i j) : ℝ) : ℂ))‖ :=
    hscale0.trans_le (hr i j hji)
  have hmass (i : Fin t) : (G i).mass ≤ (2 : ℝ) ^ (nstar - 1) := by
    exact (cube_globalPacket_mass_le_predecessor Q Y i (r i) (fun _ => Q)
      (fun _ => le_rfl) (fun _ => scaleLower) (fun _ => hscale0.le) (hdenPos i)
      (hr i)).trans (pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_right hts 1))
  have hvalue (i j : Fin t) : (G i).value (Y j) = if i = j then (w i : ℂ) else 0 := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      dsimp [G]
      rw [CubePacket.globalPacket_value_center Q Y i (r i) (fun _ => Q)
        (fun _ => le_rfl) (fun _ => scaleLower)
        (fun j hji => norm_pos_iff.mp (hdenPos i j hji))]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      simp only [ite_true, mul_one]
      rw [Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))]
      simp [w]
    · rw [if_neg hij]
      exact CubePacket.globalPacket_value_other Q Y i j (Ne.symm hij) (r i)
        (fun _ => Q) (fun _ => le_rfl) (fun _ => scaleLower)
  have hw (i : Fin t) : scaleLower ^ (nstar - 1) ≤ w i :=
    pow_le_pow_of_le_one hscale0.le hscale1 (Nat.sub_le_sub_right hts 1)
  have hband : t * Q + L ≤ M + 1 :=
    (Nat.add_le_add_right (Nat.mul_le_mul_right Q hts) L).trans hbudget
  exact cube_minimumSingularValue_lower_of_packets_explicit ht hts (by omega)
    hband hratio Y G w (by positivity) (by positivity) hw hmass hvalue

/-- The optimized coefficient for periodic one-norm within-clump spacing.
Only dimension and maximal clump size occur in this coefficient. -/
def multidimensionalClumpOptimizedLowerConstant (d nstar : ℕ) : ℝ :=
  3 / (Real.sqrt (10 * (nstar : ℝ)) * (2 : ℝ) ^ (nstar - 1) *
    Real.sqrt ((2 : ℝ) ^ d) * (3 * (nstar : ℝ) * (d : ℝ)) ^ (nstar - 1))

theorem multidimensionalClumpOptimizedLowerConstant_pos {d nstar : ℕ}
    (hd : 1 ≤ d) (hnstar : 0 < nstar) :
    0 < multidimensionalClumpOptimizedLowerConstant d nstar := by
  unfold multidimensionalClumpOptimizedLowerConstant
  positivity

/-- Local spectral lower bounds assemble with the exact square root of
the proved clump energy coefficient. -/
theorem cube_singular_lower_of_clump_energy_general {d n A M : ℕ} (hn : 0 < n)
    (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A) {b γ : ℝ}
    (hb : 0 ≤ b) (hγ : 0 ≤ γ)
    (hlocal : ∀ a, b ≤ matrixSingularValue
      (cubeFullVandermonde M (P.multidimensionalNodes Y a)) (P.size a - 1))
    (henergy : ∀ z : EuclideanSpace ℂ (Fin n),
      γ * (∑ a, ‖P.cubeSignal M Y z a‖ ^ 2) ≤
        ‖cubeFourierSignal M Y (ofLp z)‖ ^ 2) :
    Real.sqrt γ * b ≤ matrixSingularValue (cubeFullVandermonde M Y) (n - 1) := by
  let N : ℝ := (M + 1 : ℝ) ^ d
  have hN : 0 < N := by dsimp [N]; positivity
  have hlocalSq (z : EuclideanSpace ℂ (Fin n)) (a : Fin A) :
      b ^ 2 * ‖P.coefficients a z‖ ^ 2 ≤ N⁻¹ * ‖P.cubeSignal M Y z a‖ ^ 2 := by
    have h := lastMatrixSingularValue_mul_norm_le
      (cubeFullVandermonde M (P.multidimensionalNodes Y a))
      (by simpa using P.size_pos a) (P.coefficients a z)
    have hnorm : b * ‖P.coefficients a z‖ ≤
        ‖(cubeFullVandermonde M (P.multidimensionalNodes Y a)).toEuclideanLin
          (P.coefficients a z)‖ :=
      (mul_le_mul_of_nonneg_right (hlocal a) (norm_nonneg _)).trans
        (by simpa only [Fintype.card_fin] using h)
    have hs := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hnorm
    rw [mul_pow, norm_cubeFullVandermonde_sq, ← cubeFourierSignal_average_energy] at hs
    exact hs
  let V := cubeFullVandermonde M Y
  obtain ⟨z, hz, he⟩ := exists_unit_vector_norm_sq_eq_singularValue_sq V
    (i := n - 1) (by simpa using Nat.sub_lt hn Nat.zero_lt_one)
  have hsum : b ^ 2 * ‖z‖ ^ 2 ≤ N⁻¹ * ∑ a, ‖P.cubeSignal M Y z a‖ ^ 2 := by
    calc
      _ = ∑ a, b ^ 2 * ‖P.coefficients a z‖ ^ 2 := by
        rw [← Finset.mul_sum, P.sum_coefficients_norm_sq]
      _ ≤ ∑ a, N⁻¹ * ‖P.cubeSignal M Y z a‖ ^ 2 :=
        Finset.sum_le_sum fun a _ => hlocalSq z a
      _ = _ := by rw [← Finset.mul_sum]
  have hhalf : γ * (N⁻¹ * ∑ a, ‖P.cubeSignal M Y z a‖ ^ 2) ≤
      ‖V.toEuclideanLin z‖ ^ 2 := by
    rw [norm_cubeFullVandermonde_sq, ← cubeFourierSignal_average_energy]
    have h := mul_le_mul_of_nonneg_left (henergy z) (inv_nonneg.mpr hN.le)
    simpa only [mul_left_comm] using h
  rw [hz, one_pow, mul_one] at hsum
  rw [he] at hhalf
  have hβ : 0 ≤ Real.sqrt γ * b := by positivity
  apply (sq_le_sq₀ hβ (V.toEuclideanLin.singularValues_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt hγ]
  change γ * b ^ 2 ≤ matrixSingularValue V (n - 1) ^ 2
  exact (mul_le_mul_of_nonneg_left hsum hγ).trans hhalf

/-- The earlier half-energy assembly remains available with its original
normalization. -/
theorem cube_singular_lower_of_clump_energy {d n A M : ℕ} (hn : 0 < n)
    (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A) {b : ℝ} (hb : 0 ≤ b)
    (hlocal : ∀ a, b ≤ matrixSingularValue
      (cubeFullVandermonde M (P.multidimensionalNodes Y a)) (P.size a - 1))
    (henergy : ∀ z : EuclideanSpace ℂ (Fin n),
      (1 / 2 : ℝ) * (∑ a, ‖P.cubeSignal M Y z a‖ ^ 2) ≤
        ‖cubeFourierSignal M Y (ofLp z)‖ ^ 2) :
    b / Real.sqrt 2 ≤ matrixSingularValue (cubeFullVandermonde M Y) (n - 1) := by
  have h := cube_singular_lower_of_clump_energy_general hn Y P hb (by norm_num) hlocal henergy
  convert h using 1
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  ring

/-- The optimized full-cube lower bound for infinity spacing uses only
local interpolation and the almost-orthogonal clump energy comparison. -/
theorem cube_multiclump_singular_lower_optimized_normalized {d n A M nstar : ℕ}
    (hd : 1 ≤ d) (hn : 0 < n) (hnstar : 2 ≤ nstar)
    (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A)
    (hmax : HasMaxClumpSize P nstar) {c0 C0 Δ : ℝ}
    (hM : 8 * nstar ≤ M) (hc0 : c0 ≤ 1)
    (hgeom : MultidimensionalMultiClumpGeometry M c0 C0 Y P)
    (hΔ : 0 < Δ) (hgap : MultidimensionalClumpSpacingLowerBound P Y Δ)
    (henergy : ∀ z : EuclideanSpace ℂ (Fin n),
      (9 / 10 : ℝ) * (∑ a, ‖P.cubeSignal M Y z a‖ ^ 2) ≤
        ‖cubeFourierSignal M Y (ofLp z)‖ ^ 2) :
    3 * (((M : ℝ) * Δ) / (3 * (nstar : ℝ))) ^ (nstar - 1) /
      (Real.sqrt (10 * (nstar : ℝ)) * (2 : ℝ) ^ (nstar - 1) * Real.sqrt ((2 : ℝ) ^ d)) ≤
        matrixSingularValue (cubeFullVandermonde M Y) (n - 1) := by
  have hM0 : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hshort := cube_clump_normalized_spacing_le_one hnstar hM0 Y P hmax hc0 hgeom hgap
  have hlocal (a : Fin A) :
      (((M : ℝ) * Δ) / (3 * (nstar : ℝ))) ^ (nstar - 1) /
        (Real.sqrt (nstar : ℝ) * (2 : ℝ) ^ (nstar - 1) * Real.sqrt ((2 : ℝ) ^ d)) ≤
          matrixSingularValue (cubeFullVandermonde M (P.multidimensionalNodes Y a))
            (P.size a - 1) := by
    apply cube_local_clump_singular_lower hd (P.size_pos a) (hmax.1 a) hM _ ?_
      hΔ hshort ?_
    · intro i j
      have hsame : P.label (P.enumeration a i).val = P.label (P.enumeration a j).val := by
        rw [P.enumeration_label, P.enumeration_label]
      have hwidth := mul_le_mul_of_nonneg_left
        (hgeom.within (P.enumeration a i).val (P.enumeration a j).val hsame) hM0.le
      have heq : (M : ℝ) * (c0 / (M : ℝ)) = c0 := by field_simp
      exact (hwidth.trans_eq heq).trans hc0
    · intro i j hij
      apply hgap (P.enumeration a i).val (P.enumeration a j).val
      · intro heq
        exact hij ((P.enumeration a).injective (Subtype.ext heq))
      · rw [P.enumeration_label, P.enumeration_label]
  have h := cube_singular_lower_of_clump_energy_general hn Y P (by positivity)
    (by norm_num) hlocal henergy
  convert h using 1
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 9),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10)]
  norm_num
  ring

/-- Periodic one-norm spacing contributes exactly one dimension factor to
the clump-local scale. The coefficient is independent of total source count. -/
theorem cube_multiclump_singular_lower_optimized {d n A M nstar : ℕ}
    (hd : 1 ≤ d) (hn : 0 < n) (hnstar : 2 ≤ nstar)
    (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A)
    (hmax : HasMaxClumpSize P nstar) {c0 C0 Δ : ℝ}
    (hM : 8 * nstar ≤ M) (hc0 : c0 ≤ 1)
    (hgeom : MultidimensionalMultiClumpGeometry M c0 C0 Y P)
    (hΔ : 0 < Δ) (hgap : MultidimensionalClumpL1SpacingLowerBound P Y Δ)
    (henergy : ∀ z : EuclideanSpace ℂ (Fin n),
      (9 / 10 : ℝ) * (∑ a, ‖P.cubeSignal M Y z a‖ ^ 2) ≤
        ‖cubeFourierSignal M Y (ofLp z)‖ ^ 2) :
    multidimensionalClumpOptimizedLowerConstant d nstar * ((M : ℝ) * Δ) ^ (nstar - 1) ≤
      matrixSingularValue (cubeFullVandermonde M Y) (n - 1) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have h := cube_multiclump_singular_lower_optimized_normalized hd hn hnstar Y P hmax hM hc0
    hgeom (div_pos hΔ hdR) (multidimensionalClumpSpacingLowerBound_of_l1 hd P Y hgap) henergy
  convert h using 1
  unfold multidimensionalClumpOptimizedLowerConstant
  rw [div_pow, mul_pow, mul_pow]
  ring

end

end LeanNumDetect.RandSamp
