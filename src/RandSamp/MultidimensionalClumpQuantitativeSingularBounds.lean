import RandSamp.MultidimensionalClumpOptimizedSingularBounds

/-! Explicit-bandwidth local interpolation and three-quarter clump energy.
The extra bandwidth reduces the floor loss without strengthening separation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix WithLp
open LeanNumDetect.FiniteMatrixSampling
open scoped BigOperators InnerProductSpace ComplexOrder
namespace LeanNumDetect.RandSamp
noncomputable section
open MultidimensionalTrigonometricInterpolation SeparatedAngularFrequency

theorem cube_interpolation_half_bandwidth_parameters_quantitative {n M : ℕ} (hn : 0 < n)
    (hM : 16 * n ≤ M) :
    0 < M / (2 * n) ∧ M / (2 * n) ≤ M ∧
      4 * M ≤ 9 * n * (M / (2 * n)) ∧
      n * (M / (2 * n)) + (M / 2 + 1) ≤ M + 1 ∧
      M + 1 ≤ 2 * (M / 2 + 1) := by
  obtain ⟨hQ0,hQM,_hMQ,hbudget,hratio⟩ :=
    cube_interpolation_half_bandwidth_parameters hn (by omega : 8*n ≤ M)
  let Q := M / (2*n)
  have hden : 0 < 2*n := by omega
  have hQ8 : 8 ≤ Q := (Nat.le_div_iff_mul_le hden).mpr (by omega)
  have hlt : M < (Q+1)*(2*n) :=
    (Nat.div_lt_iff_lt_mul hden).mp (Nat.lt_succ_self Q)
  have hqge : 8*n ≤ n*Q := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left n hQ8
  refine ⟨hQ0,hQM,?_,hbudget,hratio⟩
  change 4*M ≤ 9*n*Q
  nlinarith

theorem cube_local_clump_singular_lower_quantitative {d t M nstar : ℕ}
    (hd : 1 ≤ d) (ht : 0 < t) (hts : t ≤ nstar)
    (hM : 16 * nstar ≤ M) (Y : Fin t → Fin d → ℝ)
    (hwithin : ∀ i j, (M : ℝ) * multidimensionalAngularTorusDistance (Y i) (Y j) ≤ 1)
    {Δ : ℝ} (hΔ : 0 < Δ) (hshort : (M : ℝ) * Δ ≤ 1)
    (hgap : ∀ i j, i ≠ j → Δ ≤ multidimensionalAngularTorusDistance (Y i) (Y j)) :
    (((M : ℝ) * Δ) / ((5 / 2 : ℝ) * (nstar : ℝ))) ^ (nstar - 1) /
        (Real.sqrt (nstar : ℝ) * (2 : ℝ) ^ (nstar - 1) * Real.sqrt ((2 : ℝ) ^ d)) ≤
      matrixSingularValue (cubeFullVandermonde M Y) (t - 1) := by
  classical
  have hs : 0 < nstar := lt_of_lt_of_le ht hts
  have hsR : 0 < (nstar : ℝ) := by exact_mod_cast hs
  have hM0 : 0 < M := by omega
  obtain ⟨hQ0, hQM, hMQ, hbudget, hratio⟩ :=
    cube_interpolation_half_bandwidth_parameters_quantitative hs hM
  let Q := M / (2 * nstar)
  let L := M / 2 + 1
  let scaleLower := ((M : ℝ) * Δ) / ((5 / 2 : ℝ) * (nstar : ℝ))
  have hscale0 : 0 < scaleLower := by dsimp [scaleLower]; positivity
  have hscale1 : scaleLower ≤ 1 := by
    dsimp [scaleLower]
    apply (div_le_iff₀ (by positivity)).mpr
    have hs1 : (1 : ℝ) ≤ nstar := by exact_mod_cast hs
    nlinarith
  have hscaled : scaleLower ≤ (9 / 10 : ℝ) * (Q : ℝ) * Δ := by
    have hMQreal : 4 * (M : ℝ) ≤ 9 * (nstar : ℝ) * (Q : ℝ) := by exact_mod_cast hMQ
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

def multidimensionalClumpQuantitativeLowerConstant (d nstar : ℕ) : ℝ :=
  Real.sqrt 3 / (2 * Real.sqrt (nstar : ℝ) * (2 : ℝ) ^ (nstar - 1) *
    Real.sqrt ((2 : ℝ) ^ d) * ((5 / 2 : ℝ) * (nstar : ℝ) * (d : ℝ)) ^ (nstar - 1))

theorem multidimensionalClumpQuantitativeLowerConstant_pos {d nstar : ℕ}
    (hd : 1 ≤ d) (hnstar : 0 < nstar) :
    0 < multidimensionalClumpQuantitativeLowerConstant d nstar := by
  unfold multidimensionalClumpQuantitativeLowerConstant
  positivity

theorem cube_multiclump_singular_lower_quantitative_normalized {d n A M nstar : ℕ}
    (hd : 1 ≤ d) (hn : 0 < n) (hnstar : 2 ≤ nstar)
    (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A)
    (hmax : HasMaxClumpSize P nstar) {c0 C0 Δ : ℝ}
    (hM : 16 * nstar ≤ M) (hc0 : c0 ≤ 1)
    (hgeom : MultidimensionalMultiClumpGeometry M c0 C0 Y P)
    (hΔ : 0 < Δ) (hgap : MultidimensionalClumpSpacingLowerBound P Y Δ)
    (henergy : ∀ z : EuclideanSpace ℂ (Fin n),
      (3 / 4 : ℝ) * (∑ a, ‖P.cubeSignal M Y z a‖ ^ 2) ≤
        ‖cubeFourierSignal M Y (ofLp z)‖ ^ 2) :
    Real.sqrt 3 * (((M : ℝ) * Δ) / ((5 / 2 : ℝ) * (nstar : ℝ))) ^ (nstar - 1) /
      (2 * Real.sqrt (nstar : ℝ) * (2 : ℝ) ^ (nstar - 1) * Real.sqrt ((2 : ℝ) ^ d)) ≤
        matrixSingularValue (cubeFullVandermonde M Y) (n - 1) := by
  have hM0 : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hshort := cube_clump_normalized_spacing_le_one hnstar hM0 Y P hmax hc0 hgeom hgap
  have hlocal (a : Fin A) :
      (((M : ℝ) * Δ) / ((5 / 2 : ℝ) * (nstar : ℝ))) ^ (nstar - 1) /
        (Real.sqrt (nstar : ℝ) * (2 : ℝ) ^ (nstar - 1) * Real.sqrt ((2 : ℝ) ^ d)) ≤
          matrixSingularValue (cubeFullVandermonde M (P.multidimensionalNodes Y a))
            (P.size a - 1) := by
    apply cube_local_clump_singular_lower_quantitative hd (P.size_pos a) (hmax.1 a) hM _ ?_
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
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num
  ring

/-- Periodic one-norm spacing contributes exactly one dimension factor to
the clump-local scale. The coefficient is independent of total source count. -/
theorem cube_multiclump_singular_lower_quantitative {d n A M nstar : ℕ}
    (hd : 1 ≤ d) (hn : 0 < n) (hnstar : 2 ≤ nstar)
    (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A)
    (hmax : HasMaxClumpSize P nstar) {c0 C0 Δ : ℝ}
    (hM : 16 * nstar ≤ M) (hc0 : c0 ≤ 1)
    (hgeom : MultidimensionalMultiClumpGeometry M c0 C0 Y P)
    (hΔ : 0 < Δ) (hgap : MultidimensionalClumpL1SpacingLowerBound P Y Δ)
    (henergy : ∀ z : EuclideanSpace ℂ (Fin n),
      (3 / 4 : ℝ) * (∑ a, ‖P.cubeSignal M Y z a‖ ^ 2) ≤
        ‖cubeFourierSignal M Y (ofLp z)‖ ^ 2) :
    multidimensionalClumpQuantitativeLowerConstant d nstar * ((M : ℝ) * Δ) ^ (nstar - 1) ≤
      matrixSingularValue (cubeFullVandermonde M Y) (n - 1) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have h := cube_multiclump_singular_lower_quantitative_normalized hd hn hnstar Y P hmax hM hc0
    hgeom (div_pos hΔ hdR) (multidimensionalClumpSpacingLowerBound_of_l1 hd P Y hgap) henergy
  convert h using 1
  unfold multidimensionalClumpQuantitativeLowerConstant
  rw [div_pow, mul_pow, mul_pow]
  ring

theorem multidimensionalClumpOptimizedLowerConstant_le_quantitative
    {d nstar : ℕ} (hd : 1 ≤ d) (hnstar : 2 ≤ nstar) :
    multidimensionalClumpOptimizedLowerConstant d nstar ≤
      multidimensionalClumpQuantitativeLowerConstant d nstar := by
  have hs : 0 < (nstar : ℝ) := by exact_mod_cast (show 0 < nstar by omega)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hroot0 : 0 ≤ Real.sqrt 3 * Real.sqrt 10 := by positivity
  have hrootSq : (Real.sqrt 3 * Real.sqrt 10)^2 = (30 : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
    norm_num
  have hroot : (5 : ℝ) ≤ Real.sqrt 3 * Real.sqrt 10 := by nlinarith
  have hfactor : (6 / 5 : ℝ) ≤ (6 / 5 : ℝ)^(nstar-1) := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 6/5)
      (show 1 ≤ nstar-1 by omega)
  have hpow : (6/5 : ℝ) * ((5/2 : ℝ)*(nstar : ℝ)*(d : ℝ))^(nstar-1) ≤
      (3*(nstar : ℝ)*(d : ℝ))^(nstar-1) := by
    rw [show (3*(nstar : ℝ)*(d : ℝ)) =
      (6/5 : ℝ)*((5/2 : ℝ)*(nstar : ℝ)*(d : ℝ)) by ring,
      mul_pow (6/5 : ℝ) ((5/2 : ℝ)*(nstar : ℝ)*(d : ℝ)) (nstar-1)]
    exact mul_le_mul_of_nonneg_right hfactor (by positivity)
  have hbase : (6 : ℝ)*((5/2 : ℝ)*(nstar : ℝ)*(d : ℝ))^(nstar-1) ≤
      (Real.sqrt 3*Real.sqrt 10)*(3*(nstar : ℝ)*(d : ℝ))^(nstar-1) := by
    calc
      _ = 5*((6/5 : ℝ)*((5/2 : ℝ)*(nstar : ℝ)*(d : ℝ))^(nstar-1)) := by ring
      _ ≤ 5*(3*(nstar : ℝ)*(d : ℝ))^(nstar-1) :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right hroot (by positivity)
  unfold multidimensionalClumpOptimizedLowerConstant multidimensionalClumpQuantitativeLowerConstant
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10)]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h := mul_le_mul_of_nonneg_left hbase
    (show 0 ≤ Real.sqrt (nstar : ℝ)*2^(nstar-1)*Real.sqrt ((2 : ℝ)^d) by positivity)
  convert h using 1 <;> ring

theorem cube_multiclump_singular_lower_quantitative_originalConstant {d n A M nstar : ℕ}
    (hd : 1 ≤ d) (hn : 0 < n) (hnstar : 2 ≤ nstar)
    (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A)
    (hmax : HasMaxClumpSize P nstar) {c0 Csep Δ : ℝ}
    (hM : 16*nstar ≤ M) (hc0 : c0 ≤ 1)
    (hgeom : MultidimensionalMultiClumpGeometry M c0 Csep Y P)
    (hΔ : 0 < Δ) (hgap : MultidimensionalClumpL1SpacingLowerBound P Y Δ)
    (henergy : ∀ z : EuclideanSpace ℂ (Fin n),
      (3/4 : ℝ)*(∑ a, ‖P.cubeSignal M Y z a‖^2) ≤
        ‖cubeFourierSignal M Y (ofLp z)‖^2) :
    multidimensionalClumpOptimizedLowerConstant d nstar*((M : ℝ)*Δ)^(nstar-1) ≤
      matrixSingularValue (cubeFullVandermonde M Y) (n-1) := by
  exact (mul_le_mul_of_nonneg_right
    (multidimensionalClumpOptimizedLowerConstant_le_quantitative hd hnstar)
    (by positivity)).trans
    (cube_multiclump_singular_lower_quantitative hd hn hnstar Y P hmax hM hc0 hgeom hΔ hgap henergy)

end
end LeanNumDetect.RandSamp
