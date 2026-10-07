import General.Fourier.MultidimensionalTaylorBounds
import General.Fourier.MultidimensionalTrigonometricInterpolation
import General.Fourier.SeparatedAngularFrequency
import RandSamp.MultidimensionalMultiClumpSampling
import RandSamp.MultidimensionalClumpPhase

/-! Constructive spectral estimates for arbitrary-dimensional clumps. The
lower bound uses exact coordinate-wise cardinal interpolation; the optional
upper bound uses only dimension counting and tensor Taylor approximation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators InnerProductSpace ComplexOrder
open Matrix WithLp

namespace LeanNumDetect.RandSamp
noncomputable section

open MultidimensionalTaylorBounds

/-- The tensor Taylor kernel gives a full-cube upper bound whenever the
box-moment count is smaller than the source count. -/
theorem exists_unit_short_cube_clump_upper {d M s q : ℕ}
    (hq : 0 < q) (hcard : q ^ d < s) (offset : Fin s → Fin d → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hoffset : ∀ j r, |offset j r| ≤ B)
    (hshort : ∀ j r, (M : ℝ) * |offset j r| ≤ 1) :
    ∃ u : EuclideanSpace ℂ (Fin s), ‖u‖ = 1 ∧
      ‖(cubeFullVandermonde M offset).toEuclideanLin u‖ ≤
        (Real.sqrt (s : ℝ) * (d : ℝ) * (3 : ℝ) ^ d * 2 /
          (q.factorial : ℝ)) * ((M : ℝ) * B) ^ q := by
  obtain ⟨u, hu, hrow⟩ := exists_unit_tensor_fourier_row_upper hq hcard offset
    (Nat.cast_nonneg M) hB hoffset hshort
  let E := (Real.sqrt (s : ℝ) * (d : ℝ) * (3 : ℝ) ^ d * 2 /
    (q.factorial : ℝ)) * ((M : ℝ) * B) ^ q
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have henergy (k : CubeFrequency d M) : cubeFourierRowEnergy offset k (ofLp u) ≤ E ^ 2 := by
    have hfreq (r : Fin d) : |((k r).val : ℝ)| ≤ (M : ℝ) := by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast Nat.le_of_lt_succ (k r).isLt
    have h := hrow (fun r => ((k r).val : ℝ)) hfreq
    exact (sq_le_sq₀ (norm_nonneg _) hE).mpr h
  refine ⟨u, hu, ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) hE).mp
  rw [norm_cubeFullVandermonde_sq, cubeFullGram, quadratic_cubeFourier_mean]
  calc
    _ ≤ (((M : ℝ) + 1) ^ d)⁻¹ * ∑ _k : CubeFrequency d M, E ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => henergy k) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, card_cubeFrequency, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_add, Nat.cast_one]
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

theorem short_cube_clump_minimumSingularValue_upper {d M s q : ℕ}
    (hq : 0 < q) (hcard : q ^ d < s) (offset : Fin s → Fin d → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hoffset : ∀ j r, |offset j r| ≤ B)
    (hshort : ∀ j r, (M : ℝ) * |offset j r| ≤ 1) :
    matrixSingularValue (cubeFullVandermonde M offset) (s - 1) ≤
      (Real.sqrt (s : ℝ) * (d : ℝ) * (3 : ℝ) ^ d * 2 /
        (q.factorial : ℝ)) * ((M : ℝ) * B) ^ q := by
  obtain ⟨u, hu, hb⟩ := exists_unit_short_cube_clump_upper hq hcard offset hB hoffset hshort
  have h := lastMatrixSingularValue_mul_norm_le (cubeFullVandermonde M offset)
    (by simp; omega) u
  simpa only [Fintype.card_fin, hu, mul_one] using h.trans hb

open MultidimensionalTrigonometricInterpolation SeparatedAngularFrequency

/-- Phase differences have the same norm as the chord of their relative phase. -/
theorem integer_phase_difference_norm (q : ℕ) (x y : ℝ) :
    ‖Complex.exp (Complex.I * (((q : ℝ) * x : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (((q : ℝ) * y : ℝ) : ℂ))‖ =
    ‖Complex.exp (Complex.I * (((q : ℝ) * (x - y) : ℝ) : ℂ)) - 1‖ := by
  have he : Complex.exp (Complex.I * (((q : ℝ) * x : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (((q : ℝ) * y : ℝ) : ℂ)) =
    (Complex.exp (Complex.I * (((q : ℝ) * (x - y) : ℝ) : ℂ)) - 1) *
      Complex.exp (Complex.I * (((q : ℝ) * y : ℝ) : ℂ)) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]

/-- Each source pair admits one coordinate cardinal factor. The frequency
may depend on the pair; local factors share the same blow-up frequency. -/
theorem exists_clump_pair_frequency {d n A M Q : ℕ}
    (hd : 1 ≤ d) (hQ : 0 < Q) (hQM : (Q : ℝ) ≤ (M : ℝ))
    (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A)
    {c0 C0 Δ scaleLower : ℝ} (hM : 0 < (M : ℝ)) (hc0 : c0 ≤ 1)
    (hgeom : MultidimensionalMultiClumpGeometry M c0 C0 Y P)
    (_hΔ : 0 < Δ) (hC0 : 0 < C0)
    (hgap : MultidimensionalClumpSpacingLowerBound P Y Δ)
    (hscaleLower : scaleLower ≤ (2 / Real.pi) * (Q : ℝ) * Δ)
    (hband : 2 * Real.pi ≤ (Q + 1 : ℝ) * (C0 / (M : ℝ)))
    (i j : Fin n) (hij : i ≠ j) :
    ∃ r : Fin d, ∃ q : ℕ, q ≤ Q ∧
      (if P.label i = P.label j then scaleLower else 1) ≤
        ‖Complex.exp (Complex.I * (((q : ℝ) * Y i r : ℝ) : ℂ)) -
          Complex.exp (Complex.I * (((q : ℝ) * Y j r : ℝ) : ℂ))‖ := by
  by_cases hsame : P.label i = P.label j
  · obtain ⟨r, hr⟩ := multidimensionalAngularTorusDistance_attained hd (Y i) (Y j)
    obtain ⟨p, hp⟩ := angularTorusDistance_eq_winding (Y i r) (Y j r)
    let θ := Y i r - Y j r + 2 * Real.pi * p
    have hθ : |θ| = multidimensionalAngularTorusDistance (Y i) (Y j) := by
      exact hp.symm.trans hr
    have hθgap : Δ ≤ |θ| := by rw [hθ]; exact hgap i j hij hsame
    have hθshort : |(Q : ℝ) * θ| ≤ Real.pi := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg Q), hθ]
      have hwidth := hgeom.within i j hsame
      have hw0 := multidimensionalAngularTorusDistance_nonneg hd (Y i) (Y j)
      have hqdist := mul_le_mul_of_nonneg_right hQM hw0
      have hbound : (M : ℝ) * multidimensionalAngularTorusDistance (Y i) (Y j) ≤ 1 := by
        have h := mul_le_mul_of_nonneg_left hwidth hM.le
        have hc : (M : ℝ) * (c0 / (M : ℝ)) = c0 := by field_simp
        exact (h.trans_eq hc).trans hc0
      exact (hqdist.trans hbound).trans (by linarith [Real.pi_gt_three])
    have hchord := short_integer_frequency_chord_lower Q θ Δ hθgap hθshort
    refine ⟨r, Q, le_rfl, ?_⟩
    rw [if_pos hsame, integer_phase_difference_norm]
    have hphase := integer_frequency_phase_winding Q (Y i r - Y j r) p
    change Complex.exp (Complex.I * (((Q : ℝ) * θ : ℝ) : ℂ)) = _ at hphase
    rw [← hphase]
    exact hscaleLower.trans hchord
  · obtain ⟨r, hr⟩ := multidimensionalAngularTorusDistance_attained hd (Y i) (Y j)
    have hη : 0 < C0 / (M : ℝ) := div_pos hC0 hM
    have hsep (p : ℤ) : C0 / (M : ℝ) ≤ |(Y i r - Y j r) - 2 * Real.pi * p| := by
      have h := (hgeom.between i j hsame).trans (hr ▸ angularTorusDistance_le_winding (Y i r) (Y j r) (-p))
      convert h using 1; congr 1; push_cast; ring
    obtain ⟨q, _, hq, hchord⟩ := exists_separated_integer_frequency
      (Y i r - Y j r) (C0 / (M : ℝ)) hη hsep Q hQ hband
    refine ⟨r, q, hq, ?_⟩
    rw [if_neg hsame, integer_phase_difference_norm]
    exact hchord

/-- A conservative geometric threshold for exact cardinal interpolation. -/
def multidimensionalClumpLowerThreshold (n : ℕ) : ℝ :=
  max (8 * (n : ℝ)) (8 * Real.pi * (n : ℝ))

/-- The sharp worst-case lower coefficient for periodic one-norm spacing. -/
def multidimensionalClumpLowerConstant (d n nstar : ℕ) : ℝ :=
  1 / (Real.sqrt (n : ℝ) * (2 : ℝ) ^ (n + d) *
    (16 * Real.pi * (n : ℝ) * (d : ℝ)) ^ (nstar - 1))

theorem multidimensionalClumpLowerConstant_pos {d n nstar : ℕ} (hd : 1 ≤ d) (hn : 0 < n) :
    0 < multidimensionalClumpLowerConstant d n nstar := by
  unfold multidimensionalClumpLowerConstant
  positivity

/-- Uniformly bounded cube packets with exact diagonal evaluations give a
normalized full-cube lower bound. Averaging controls the coefficient norm
independently of the ambient bandwidth. -/
theorem cube_minimumSingularValue_lower_of_packets {d n M Q L : ℕ}
    (hn : 0 < n) (hL : 0 < L) (hband : Q + L ≤ M + 1)
    (hratio : M + 1 ≤ 2 * L) (Y : Fin n → Fin d → ℝ)
    (G : Fin n → CubePacket d Q) (w : Fin n → ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hw : ∀ i, b ≤ w i)
    (hmass : ∀ i, (G i).mass ≤ (2 : ℝ) ^ n)
    (hvalue : ∀ i j, (G i).value (Y j) = if i = j then (w i : ℂ) else 0) :
    b / (Real.sqrt (n : ℝ) * (2 : ℝ) ^ (n + d)) ≤
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
  have hnorm (i : Fin n) : ‖H i‖ ≤ (2 : ℝ) ^ n * Real.sqrt R⁻¹ :=
    ((G i).averagedVector_norm_le hL hband (Y i)).trans
      (mul_le_mul_of_nonneg_right (hmass i) (Real.sqrt_nonneg _))
  have hNR : N ≤ (2 : ℝ) ^ d * R := by
    have h := Nat.pow_le_pow_left hratio d
    dsimp [N, R]
    exact_mod_cast (by simpa only [Nat.mul_pow] using h)
  have hC (i : Fin n) : SegmentedVDM.energy (C i) ≤ ((2 : ℝ) ^ (n + d)) ^ 2 := by
    have hH : ‖H i‖ ^ 2 ≤ ((2 : ℝ) ^ n) ^ 2 * R⁻¹ := by
      have h := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hnorm i)
      simpa only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ R⁻¹)] using h
    have hCE : SegmentedVDM.energy (C i) = N * ‖H i‖ ^ 2 := by
      unfold SegmentedVDM.energy C
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hN.le]
      rw [← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq]
    rw [hCE]
    have hRratio : N * R⁻¹ ≤ (2 : ℝ) ^ d := by
      rw [← div_eq_mul_inv]
      exact (div_le_iff₀ hR).mpr hNR
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    calc
      _ ≤ N * (((2 : ℝ) ^ n) ^ 2 * R⁻¹) :=
        mul_le_mul_of_nonneg_left hH hN.le
      _ = ((2 : ℝ) ^ n) ^ 2 * (N * R⁻¹) := by ring
      _ ≤ ((2 : ℝ) ^ n) ^ 2 * (2 : ℝ) ^ d :=
        mul_le_mul_of_nonneg_left hRratio (sq_nonneg _)
      _ ≤ ((2 : ℝ) ^ n) ^ 2 * ((2 : ℝ) ^ d) ^ 2 := by
        gcongr
        nlinarith
      _ = _ := by rw [pow_add, mul_pow]
  obtain ⟨z, hz, he⟩ := exists_unit_vector_norm_sq_eq_singularValue_sq V
    (i := n - 1) (by simpa using Nat.sub_lt hn Nat.zero_lt_one)
  have henergy := diagonal_interpolation_energy_lower V C w hCV hb hw hC (ofLp z)
  change b ^ 2 * (∑ i, ‖ofLp z i‖ ^ 2) ≤
    (n : ℝ) * ((2 : ℝ) ^ (n + d)) ^ 2 *
      (∑ k, ‖(V *ᵥ ofLp z) k‖ ^ 2) at henergy
  rw [← EuclideanSpace.norm_sq_eq, hz, one_pow, mul_one] at henergy
  have heEnergy : (∑ k, ‖(V *ᵥ ofLp z) k‖ ^ 2) = ‖V.toEuclideanLin z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  rw [heEnergy] at henergy
  rw [he] at henergy
  change b ^ 2 ≤ (n : ℝ) * ((2 : ℝ) ^ (n + d)) ^ 2 * V.toEuclideanLin.singularValues (n - 1) ^ 2 at henergy
  have hden : 0 < Real.sqrt (n : ℝ) * (2 : ℝ) ^ (n + d) := by positivity
  apply (div_le_iff₀ hden).mpr
  apply (sq_le_sq₀ hb (mul_nonneg (V.toEuclideanLin.singularValues_nonneg _) hden.le)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  nlinarith only [henergy]

/-- Integer bandwidth allocation leaves at least half the cube available for
averaging while keeping every pair frequency below one quarter bandwidth. -/
theorem cube_interpolation_bandwidth_parameters {n M : ℕ} (hn : 0 < n)
    (hM : 8 * n ≤ M) :
    0 < M / (4 * n) ∧ M / (4 * n) ≤ M ∧
      M ≤ 8 * n * (M / (4 * n)) ∧
      n * (M / (4 * n)) + (M / 2 + 1) ≤ M + 1 ∧
      M + 1 ≤ 2 * (M / 2 + 1) := by
  let Q := M / (4 * n)
  have hden : 0 < 4 * n := by omega
  have hQ2 : 2 ≤ Q := (Nat.le_div_iff_mul_le hden).mpr (by omega)
  have hQM : Q ≤ M := Nat.div_le_self _ _
  have hprod : 4 * (n * Q) ≤ M := by
    simpa only [Q, Nat.mul_assoc] using Nat.mul_div_le M (4 * n)
  have hlt : M < (Q + 1) * (4 * n) :=
    (Nat.div_lt_iff_lt_mul hden).mp (Nat.lt_succ_self Q)
  have hqge : 4 * n ≤ 4 * n * Q := Nat.le_mul_of_pos_right _ (by omega)
  have hlow : M ≤ 8 * n * Q := by nlinarith
  refine ⟨by omega, hQM, hlow, ?_, ?_⟩
  · change n * Q + (M / 2 + 1) ≤ M + 1
    omega
  · omega

/-- Pairwise lower spacing and a maximal nonsingleton clump bound the
normalized smallest within-clump spacing by one. -/
theorem cube_clump_normalized_spacing_le_one {d n A M nstar : ℕ}
    (hnstar : 2 ≤ nstar) (hM : 0 < (M : ℝ)) (Y : Fin n → Fin d → ℝ)
    (P : ClumpPartition n A) (hmax : HasMaxClumpSize P nstar)
    {c0 C0 Δ : ℝ} (hc0 : c0 ≤ 1)
    (hgeom : MultidimensionalMultiClumpGeometry M c0 C0 Y P)
    (hgap : MultidimensionalClumpSpacingLowerBound P Y Δ) :
    (M : ℝ) * Δ ≤ 1 := by
  obtain ⟨a, ha⟩ := hmax.2
  have hsize : 2 ≤ P.size a := by omega
  let ki : Fin (P.size a) := ⟨0, by omega⟩
  let kj : Fin (P.size a) := ⟨1, by omega⟩
  let i : Fin n := (P.enumeration a ki).val
  let j : Fin n := (P.enumeration a kj).val
  have hij : i ≠ j := by
    intro h
    have he : P.enumeration a ki = P.enumeration a kj := Subtype.ext h
    have h' := (P.enumeration a).injective he
    have h'' := congrArg Fin.val h'
    change (0 : ℕ) = 1 at h''
    omega
  have hlabel : P.label i = P.label j := by
    dsimp [i, j]
    rw [P.enumeration_label, P.enumeration_label]
  have h := (hgap i j hij hlabel).trans (hgeom.within i j hlabel)
  have hscaled := mul_le_mul_of_nonneg_left h hM.le
  have he : (M : ℝ) * (c0 / (M : ℝ)) = c0 := by field_simp
  exact (hscaled.trans_eq he).trans hc0


/-- Exact cardinal packets give the sharp worst-case exponent for the
periodic infinity-norm within-clump spacing. -/
theorem cube_multiclump_singular_lower_normalized {d n A M nstar : ℕ}
    (hd : 1 ≤ d) (hn : 0 < n) (hnstar : 2 ≤ nstar)
    (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A)
    (hmax : HasMaxClumpSize P nstar) {c0 C0 Δ : ℝ}
    (hM : multidimensionalClumpLowerThreshold n ≤ (M : ℝ))
    (hC0 : multidimensionalClumpLowerThreshold n ≤ C0)
    (hc0 : c0 ≤ 1)
    (hgeom : MultidimensionalMultiClumpGeometry M c0 C0 Y P)
    (hΔ : 0 < Δ) (hgap : MultidimensionalClumpSpacingLowerBound P Y Δ) :
    (((M : ℝ) * Δ) / (16 * Real.pi * (n : ℝ))) ^ (nstar - 1) /
        (Real.sqrt (n : ℝ) * (2 : ℝ) ^ (n + d)) ≤
      matrixSingularValue (cubeFullVandermonde M Y) (n - 1) := by
  classical
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hM8 : 8 * (n : ℝ) ≤ (M : ℝ) := (le_max_left _ _).trans hM
  have hM0 : 0 < (M : ℝ) := lt_of_lt_of_le (by positivity) hM8
  have hMnat : 8 * n ≤ M := by exact_mod_cast hM8
  obtain ⟨hQ0, hQM, hMQ, hbudget, hratio⟩ := cube_interpolation_bandwidth_parameters hn hMnat
  let Q := M / (4 * n)
  let L := M / 2 + 1
  let scaleLower := ((M : ℝ) * Δ) / (16 * Real.pi * (n : ℝ))
  have hscale0 : 0 < scaleLower := by dsimp [scaleLower]; positivity
  have hscale1 : scaleLower ≤ 1 := by
    have hshort := cube_clump_normalized_spacing_le_one hnstar hM0 Y P hmax hc0 hgeom hgap
    dsimp [scaleLower]
    apply (div_le_iff₀ (by positivity)).mpr
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_gt_three]
  have hscaled : scaleLower ≤ (2 / Real.pi) * (Q : ℝ) * Δ := by
    have hMQreal : (M : ℝ) ≤ 8 * (n : ℝ) * (Q : ℝ) := by exact_mod_cast hMQ
    dsimp [scaleLower]
    apply (div_le_iff₀ (by positivity)).mpr
    have hmul := mul_le_mul_of_nonneg_right hMQreal hΔ.le
    field_simp
    nlinarith
  have hC0eight : 8 * Real.pi * (n : ℝ) ≤ C0 := (le_max_right _ _).trans hC0
  have hC00 : 0 < C0 := lt_of_lt_of_le (by positivity) hC0eight
  have hband : 2 * Real.pi ≤ (Q + 1 : ℝ) * (C0 / (M : ℝ)) := by
    have hden : 0 < 4 * n := by omega
    have hlt : M < (Q + 1) * (4 * n) :=
      (Nat.div_lt_iff_lt_mul hden).mp (Nat.lt_succ_self Q)
    have hltR : (M : ℝ) < ((Q : ℝ) + 1) * (4 * (n : ℝ)) := by exact_mod_cast hlt
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hM0).mpr
    have hC := mul_le_mul_of_nonneg_left hC0eight (by positivity : 0 ≤ (Q : ℝ) + 1)
    calc
      2 * Real.pi * (M : ℝ) ≤
          2 * Real.pi * (((Q : ℝ) + 1) * (4 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hltR.le (by positivity)
      _ = ((Q : ℝ) + 1) * (8 * Real.pi * (n : ℝ)) := by ring
      _ ≤ _ := hC
  have hpairs : ∀ i j : Fin n, ∃ r : Fin d, ∃ q : ℕ, q ≤ Q ∧
      (j ≠ i → (if P.label j = P.label i then scaleLower else 1) ≤
        ‖Complex.exp (Complex.I * (((q : ℝ) * Y i r : ℝ) : ℂ)) -
          Complex.exp (Complex.I * (((q : ℝ) * Y j r : ℝ) : ℂ))‖) := by
    intro i j
    by_cases hji : j = i
    · exact ⟨⟨0, hd⟩, 0, Nat.zero_le _, by simp [hji]⟩
    · obtain ⟨r, q, hq, hb⟩ := exists_clump_pair_frequency hd hQ0
        (by exact_mod_cast hQM) Y P hM0 hc0 hgeom hΔ hC00 hgap hscaled hband i j (Ne.symm hji)
      exact ⟨r, q, hq, fun _ => by simpa only [eq_comm] using hb⟩
  choose r q hq hb using hpairs
  let scale := fun i j : Fin n => if P.label j = P.label i then scaleLower else 1
  have hscalePos (i j : Fin n) : 0 < scale i j := by dsimp [scale]; split_ifs <;> positivity
  have hdenPos (i j : Fin n) (hji : j ≠ i) :
      0 < ‖Complex.exp (Complex.I * (((q i j : ℝ) * Y i (r i j) : ℝ) : ℂ)) -
          Complex.exp (Complex.I * (((q i j : ℝ) * Y j (r i j) : ℝ) : ℂ))‖ :=
    (hscalePos i j).trans_le (hb i j hji)
  let G := fun i : Fin n => CubePacket.globalPacket Q Y i (r i) (q i) (hq i) (scale i)
  let w := fun i : Fin n => scaleLower ^ (P.size (P.label i) - 1)
  have hmass (i : Fin n) : (G i).mass ≤ (2 : ℝ) ^ n :=
    CubePacket.globalPacket_mass_le Q Y i (r i) (q i) (hq i) (scale i)
      (fun j => (hscalePos i j).le) (hdenPos i) (hb i)
  have hvalue (i j : Fin n) : (G i).value (Y j) = if i = j then (w i : ℂ) else 0 := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      dsimp [G]
      rw [CubePacket.globalPacket_value_center Q Y i (r i) (q i) (hq i) (scale i)
        (fun j hji => norm_pos_iff.mp (hdenPos i j hji))]
      have hprod := P.prod_local_scaling i (scaleLower : ℂ)
      change (∏ j, if j = i then (1 : ℂ) else (scale i j : ℂ)) =
        (scaleLower ^ (P.size (P.label i) - 1) : ℝ)
      rw [Complex.ofReal_pow]
      calc
        _ = ∏ j, if j = i then (1 : ℂ) else
            if P.label j = P.label i then (scaleLower : ℂ) else 1 := by
          apply Finset.prod_congr rfl
          intro j _
          dsimp [scale]
          split_ifs <;> rfl
        _ = _ := hprod
    · rw [if_neg hij]
      exact CubePacket.globalPacket_value_other Q Y i j (Ne.symm hij) (r i) (q i) (hq i) (scale i)
  have hw (i : Fin n) : scaleLower ^ (nstar - 1) ≤ w i :=
    pow_le_pow_of_le_one hscale0.le hscale1 (Nat.sub_le_sub_right (hmax.1 (P.label i)) 1)
  exact cube_minimumSingularValue_lower_of_packets hn (by omega)
    hbudget hratio Y G w (by positivity) hw hmass hvalue

/-- Periodic one-norm separation gives a geometry-free sharp lower bound,
with an explicit dimension factor from the infinity-norm conversion. -/
theorem cube_multiclump_singular_lower {d n A M nstar : ℕ}
    (hd : 1 ≤ d) (hn : 0 < n) (hnstar : 2 ≤ nstar)
    (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A)
    (hmax : HasMaxClumpSize P nstar) {c0 C0 Δ : ℝ}
    (hM : multidimensionalClumpLowerThreshold n ≤ (M : ℝ))
    (hC0 : multidimensionalClumpLowerThreshold n ≤ C0)
    (hc0 : c0 ≤ 1)
    (hgeom : MultidimensionalMultiClumpGeometry M c0 C0 Y P)
    (hΔ : 0 < Δ) (hgap : MultidimensionalClumpL1SpacingLowerBound P Y Δ) :
    multidimensionalClumpLowerConstant d n nstar * ((M : ℝ) * Δ) ^ (nstar - 1) ≤
      matrixSingularValue (cubeFullVandermonde M Y) (n - 1) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have h := cube_multiclump_singular_lower_normalized hd hn hnstar Y P hmax hM hC0 hc0 hgeom
    (div_pos hΔ hdR) (multidimensionalClumpSpacingLowerBound_of_l1 hd P Y hgap)
  convert h using 1
  unfold multidimensionalClumpLowerConstant
  rw [div_pow, mul_pow, mul_pow]
  ring


/-- Distinct periodic coordinates have distinct unit complex phases. -/
theorem angularTorusDistance_phase_ne {x y : ℝ} (h : 0 < angularTorusDistance x y) :
    Complex.exp (Complex.I * (x : ℂ)) ≠ Complex.exp (Complex.I * (y : ℂ)) := by
  intro he
  obtain ⟨p, hp⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have him := congrArg Complex.im hp
  have hreal : x - y + 2 * Real.pi * ((-p : ℤ) : ℝ) = 0 := by
    norm_num [Complex.add_im, Complex.mul_im, Complex.mul_re] at him
    push_cast
    linarith
  have hgap := angularTorusDistance_le_winding x y (-p)
  rw [hreal, abs_zero] at hgap
  linarith

/-- Coordinate cardinal interpolation proves global column independence
without clump assumptions or spacing-dependent bandwidth. -/
theorem multidimensionalDistinct_cubeFullVandermonde_mulVec_injective {d n M : ℕ}
    (hd : 1 ≤ d) (hM : n ≤ M) (Y : Fin n → Fin d → ℝ)
    (hY : DistinctMultidimensionalAngularNodes Y) :
    Function.Injective (cubeFullVandermonde M Y).mulVec := by
  classical
  have hpairs : ∀ i j : Fin n, ∃ r : Fin d,
      (j ≠ i → Complex.exp (Complex.I * (Y i r : ℂ)) ≠
        Complex.exp (Complex.I * (Y j r : ℂ))) := by
    intro i j
    by_cases hji : j = i
    · exact ⟨⟨0, hd⟩, by simp [hji]⟩
    · obtain ⟨r, hr⟩ := multidimensionalAngularTorusDistance_attained hd (Y i) (Y j)
      exact ⟨r, fun _ => angularTorusDistance_phase_ne (hr ▸ hY i j (Ne.symm hji))⟩
  choose r hr using hpairs
  let G := fun i : Fin n => CubePacket.globalPacket 1 Y i (r i) (fun _ => 1)
    (fun _ => le_rfl) (fun _ => 1)
  have hden (i j : Fin n) (hji : j ≠ i) :
      Complex.exp (Complex.I * (((1 : ℕ) : ℝ) * Y i (r i j) : ℝ)) -
        Complex.exp (Complex.I * (((1 : ℕ) : ℝ) * Y j (r i j) : ℝ)) ≠ 0 := by
    simp only [Nat.cast_one, one_mul, sub_ne_zero]
    exact hr i j hji
  have hvalue (i j : Fin n) : (G i).value (Y j) = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      dsimp [G]
      rw [CubePacket.globalPacket_value_center _ _ _ _ _ _ _ (hden i)]
      simp
    · rw [if_neg hij]
      exact CubePacket.globalPacket_value_other _ _ _ _ (Ne.symm hij) _ _ _ _
  have hband : n * 1 + 1 ≤ M + 1 := by omega
  let N : ℝ := (((M + 1) ^ d : ℕ) : ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  let H := fun i : Fin n => (G i).averagedVector hband (Y i)
  let C : Matrix (Fin n) (CubeFrequency d M) ℂ :=
    fun i k => (Real.sqrt N : ℂ) * ofLp (H i) k
  have hsqrt : (Real.sqrt N : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hN).ne'
  have hCV : C * cubeFullVandermonde M Y = 1 := by
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
      rw [CubePacket.averagedVector_evaluation_center (by omega), hvalue]
      simp
    · rw [CubePacket.averagedVector_evaluation, hvalue, if_neg hij, zero_mul]
      simp [hij]
  intro u v huv
  have h := congrArg (fun w => C *ᵥ w) huv
  simpa only [Matrix.mulVec_mulVec, hCV, Matrix.one_mulVec] using h


/-- Distinct periodic multidimensional sources give a strictly positive full
cube Gram matrix whenever the bandwidth is at least the source count. -/
theorem cube_fullGram_posDef_of_distinct {d n M : ℕ}
    (hd : 1 ≤ d) (hM : n ≤ M) (Y : Fin n → Fin d → ℝ)
    (hY : DistinctMultidimensionalAngularNodes Y) :
    (cubeFullGram M Y).PosDef := by
  rw [cubeFullGram_eq_cubeFullVandermonde_gram]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (multidimensionalDistinct_cubeFullVandermonde_mulVec_injective hd hM Y hY)

end
end LeanNumDetect.RandSamp
