import RandSamp.ClumpSubspaceGeometry
import RandSamp.LeverageSampling
import RandSamp.SingularValues
import RandSamp.ClumpSignals
import RandSamp.MultiClumpAssembly
import General.Fourier.SingleClumpVandermonde

/-! Constructive single-clump spectral lower bounds.

The fully proved segmented Vandermonde estimate yields a positive constant
for each clump size. Taking a finite minimum up to `nstar` gives the common
constant needed by the multi-clump theorem. The factor `32πe` is a convenient
normalization; no original BG theorem or spacing-ratio hypothesis is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators InnerProductSpace
open Matrix WithLp Set

namespace LeanNumDetect.RandSamp
noncomputable section

theorem canonicalAngle_nodes_injective {s : ℕ} (Y : Fin s → ℝ)
    (hY : DistinctAngularNodes Y) : Function.Injective (fun j => canonicalAngle (Y j)) := by
  intro i j hij
  change canonicalAngle (Y i) = canonicalAngle (Y j) at hij
  by_contra hne
  have hpos := (distinctAngularNodes_iff_distance_pos Y).1 hY i j hne
  have hzero : angularTorusDistance (Y i) (Y j) = 0 := by
    rw [← angularTorusDistance_canonicalAngle, hij, angularTorusDistance_self]
  exact hpos.ne' hzero

theorem source_vandermonde_canonicalAngle {s : ℕ} (M : ℕ) (Y : Fin s → ℝ) :
    ClusteredVandermonde.vandermonde M (fun j => canonicalAngle (Y j)) =
      ClusteredVandermonde.vandermonde M Y := by
  ext k j
  exact fourierRow_canonicalAngle Y k.val j

/-- For a fixed upper clump size, the constructive packet estimate gives a
positive lower coefficient uniform across all smaller clumps. Its dependence
on `nstar` is permitted by the manuscript; no BG result is assumed. -/
theorem singleClump_lower_thresholds (nstar : ℕ) :
    ∃ d : ℝ, 0 < d ∧
      ∀ (s : ℕ), 0 < s → s ≤ nstar → ∃ B : ℝ, 1 ≤ B ∧
        ∀ (M : ℕ), B ≤ (M : ℝ) →
          ∀ (Y : Fin s → ℝ), DistinctAngularNodes Y →
            ∀ c Δ : ℝ, 0 < c → c ≤ 1 / (s : ℝ) → 0 < Δ →
              (∀ i j, angularTorusDistance (Y i) (Y j) ≤ c / M) →
              (∀ i j, i ≠ j → Δ ≤ angularTorusDistance (Y i) (Y j)) →
              d * Real.sqrt (M : ℝ) *
                  ((M : ℝ) * Δ / (32 * Real.pi * Real.exp 1)) ^ (s - 1) ≤
                matrixSingularValue (ClusteredVandermonde.vandermonde M Y) (s - 1) := by
  classical
  by_cases hstar : nstar = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro s hs hsstar
    omega
  have hstar0 : 0 < nstar := Nat.pos_of_ne_zero hstar
  letI : Nonempty (Fin nstar) := ⟨⟨0, hstar0⟩⟩
  let b : ℝ := 32 * Real.pi * Real.exp 1
  have hb : 0 < b := by dsimp [b]; positivity
  let f : Fin nstar → ℝ := fun i => min 1
    (SingleClumpVandermonde.lowerCoefficient (i.val + 1) * b ^ i.val)
  have hf (i : Fin nstar) : 0 < f i :=
    lt_min (by norm_num) (mul_pos (SingleClumpVandermonde.lowerCoefficient_pos (by omega))
      (pow_pos hb _))
  obtain ⟨i0, _, hi0⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  let d := f i0
  refine ⟨d, hf i0, ?_⟩
  intro s hs hsstar
  let i : Fin nstar := ⟨s - 1, by omega⟩
  have hi : i.val + 1 = s := by dsimp [i]; omega
  have himin : d ≤ f i := hi0 i (Finset.mem_univ _)
  have hd1 : d ≤ 1 := himin.trans (min_le_left _ _)
  have hdcoeff : d ≤ SingleClumpVandermonde.lowerCoefficient s * b ^ (s - 1) := by
    have h := himin.trans (min_le_right _ _)
    simpa only [f, hi, i] using h
  refine ⟨(2 * s : ℕ), by exact_mod_cast (show 1 ≤ 2 * s by omega), ?_⟩
  intro M hM Y _hY c Δ hc hcsize hΔ hdiam hgap
  have hN : 2 * s ≤ M := by exact_mod_cast hM
  have hM1 : 1 ≤ M := by omega
  have hMR : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  by_cases hsone : s = 1
  · clear hdcoeff himin hi i
    subst s
    have h := SingleClumpVandermonde.minimumSingularValue_singleton_lower M Y
    change Real.sqrt (M : ℝ) ≤
      matrixSingularValue (ClusteredVandermonde.vandermonde M Y) 0 at h
    simp only [Nat.sub_self, pow_zero, mul_one]
    exact (mul_le_mul_of_nonneg_right hd1 (Real.sqrt_nonneg _) |>.trans_eq (one_mul _)).trans h
  have hs2 : 2 ≤ s := by omega
  let j0 : Fin s := ⟨0, hs⟩
  let j1 : Fin s := ⟨1, by omega⟩
  have hj : j0 ≠ j1 := by intro h; have := congrArg Fin.val h; dsimp [j0, j1] at this; omega
  have hdelta : Δ ≤ c / M := (hgap j0 j1 hj).trans (hdiam j0 j1)
  have hc1 : c ≤ 1 := hcsize.trans ((div_le_one hsR).2 hs1)
  have hscale1 : (M : ℝ) * Δ ≤ 1 := by
    have h := (le_div_iff₀ hMR).1 hdelta
    have hMc : (M : ℝ) * Δ ≤ c := by simpa only [mul_comm] using h
    exact hMc.trans hc1
  have hscale : ((M : ℝ) / s) * Δ ≤ Real.pi := by
    have h : (M : ℝ) * Δ / s ≤ 1 := (div_le_one hsR).2 (hscale1.trans hs1)
    calc
      ((M : ℝ) / s) * Δ = (M : ℝ) * Δ / s := by ring
      _ ≤ Real.pi := h.trans (by linarith [Real.pi_gt_three])
  have hw : 0 ≤ c / (M : ℝ) := by positivity
  have hwpi : c / (M : ℝ) ≤ Real.pi / 2 := by
    have h := (div_le_one hMR).2 (hc1.trans (by exact_mod_cast hM1))
    exact h.trans (by nlinarith [Real.pi_gt_three])
  have hgap' (j k : Fin s) (hjk : j ≠ k) (p : ℤ) :
      Δ ≤ |Y j - Y k - 2 * Real.pi * p| := by
    have h := (le_angularTorusDistance_iff _ _ _).1 (hgap j k hjk) (-p)
    simpa only [Int.cast_neg, mul_neg, ← sub_eq_add_neg] using h
  have hdiam' (j k : Fin s) : ∃ p : ℤ, |Y j - Y k - 2 * Real.pi * p| ≤ c / M := by
    obtain ⟨p, hp⟩ := (angularTorusDistance_le_iff _ _ _).1 (hdiam j k)
    exact ⟨-p, by simpa only [Int.cast_neg, mul_neg, sub_neg_eq_add] using hp⟩
  have h := SingleClumpVandermonde.periodic_minimumSingularValue_lower_factored
    hs hN Y hΔ hw hwpi hscale hgap' hdiam'
  change SingleClumpVandermonde.lowerCoefficient s * Real.sqrt (M : ℝ) *
      ((M : ℝ) * Δ) ^ (s - 1) ≤
        matrixSingularValue (ClusteredVandermonde.vandermonde M Y) (s - 1) at h
  have hcoeff : d / b ^ (s - 1) ≤ SingleClumpVandermonde.lowerCoefficient s :=
    (div_le_iff₀ (pow_pos hb _)).2 hdcoeff
  calc
    d * Real.sqrt (M : ℝ) * ((M : ℝ) * Δ / (32 * Real.pi * Real.exp 1)) ^ (s - 1) =
        (d / b ^ (s - 1)) * (Real.sqrt (M : ℝ) * ((M : ℝ) * Δ) ^ (s - 1)) := by
      change d * Real.sqrt (M : ℝ) * ((M : ℝ) * Δ / b) ^ (s - 1) = _
      rw [div_pow]
      ring
    _ ≤ SingleClumpVandermonde.lowerCoefficient s *
        (Real.sqrt (M : ℝ) * ((M : ℝ) * Δ) ^ (s - 1)) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ ≤ _ := by simpa only [mul_assoc] using h

/-- The constructive clump lower bound gives a uniform lower estimate for the
unnormalized integer-frequency energy of every coefficient vector. -/
theorem singleClump_energy_lower_of_minimumSingularValue {s M : ℕ} (hs : 0 < s)
    (Y : Fin s → ℝ) {d Δ : ℝ} (hd : 0 ≤ d) (hΔ : 0 ≤ Δ)
    (hsv : d * Real.sqrt (M : ℝ) *
      ((M : ℝ) * Δ / (32 * Real.pi * Real.exp 1)) ^ (s - 1) ≤
        matrixSingularValue (ClusteredVandermonde.vandermonde M Y) (s - 1))
    (z : EuclideanSpace ℂ (Fin s)) :
    (d * Real.sqrt (M : ℝ) *
      ((M : ℝ) * Δ / (32 * Real.pi * Real.exp 1)) ^ (s - 1)) ^ 2 * ‖z‖ ^ 2 ≤
      ∑ k : Fin (M + 1), fourierRowEnergy Y k.val (ofLp z) := by
  have hnorm := lastMatrixSingularValue_mul_norm_le (ClusteredVandermonde.vandermonde M Y)
    (by simpa using hs) z
  simp only [Fintype.card_fin] at hnorm
  have hlower := (mul_le_mul_of_nonneg_right hsv (norm_nonneg z)).trans hnorm
  have hcoef : 0 ≤ d * Real.sqrt (M : ℝ) *
      ((M : ℝ) * Δ / (32 * Real.pi * Real.exp 1)) ^ (s - 1) := by positivity
  have hsq := (sq_le_sq₀ (mul_nonneg hcoef (norm_nonneg z)) (norm_nonneg _)).2 hlower
  rw [mul_pow, matrix_action_norm_sq_eq_energy] at hsq
  exact hsq

/-- Integer full-frequency normalization loses at most a factor two in the
constructive lower coefficient once `M ≥ 1`. -/
theorem singleClump_normalized_energy_lower_of_minimumSingularValue {s M : ℕ}
    (hs : 0 < s) (hM : 1 ≤ M) (Y : Fin s → ℝ) {d Δ : ℝ}
    (hd : 0 ≤ d) (hΔ : 0 ≤ Δ)
    (hsv : d * Real.sqrt (M : ℝ) *
      ((M : ℝ) * Δ / (32 * Real.pi * Real.exp 1)) ^ (s - 1) ≤
        matrixSingularValue (ClusteredVandermonde.vandermonde M Y) (s - 1))
    (z : EuclideanSpace ℂ (Fin s)) :
    (d / 2 * ((M : ℝ) * Δ / (32 * Real.pi * Real.exp 1)) ^ (s - 1)) ^ 2 * ‖z‖ ^ 2 ≤
      ‖fullFourierSignal M Y z‖ ^ 2 := by
  have hraw := singleClump_energy_lower_of_minimumSingularValue hs Y hd hΔ hsv z
  have he : (∑ k : Fin (M + 1), fourierRowEnergy Y k.val (ofLp z)) =
      ((M + 1 : ℕ) : ℝ) * ‖fullFourierSignal M Y z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact (fullFourierSignal_coordinate_energy M Y z k).symm
  rw [he] at hraw
  have hDM : ((M + 1 : ℕ) : ℝ) ≤ 4 * (M : ℝ) := by
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    push_cast
    linarith
  have hsq : ((M + 1 : ℕ) : ℝ) *
      ((d / 2 * ((M : ℝ) * Δ / (32 * Real.pi * Real.exp 1)) ^ (s - 1)) ^ 2 * ‖z‖ ^ 2) ≤
      (d * Real.sqrt (M : ℝ) *
        ((M : ℝ) * Δ / (32 * Real.pi * Real.exp 1)) ^ (s - 1)) ^ 2 * ‖z‖ ^ 2 := by
    have hmult := mul_le_mul_of_nonneg_right hDM
      (sq_nonneg (d * ((M : ℝ) * Δ / (32 * Real.pi * Real.exp 1)) ^ (s - 1) * ‖z‖))
    simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg M)]
    nlinarith
  exact le_of_mul_le_mul_left (hsq.trans hraw) (by positivity)

/-- With a clump of size at least two, the proposed geometry forces
`MΔ ≤ c0`; this uses just the internal lower spacing assumption. -/
theorem multiClump_scaledGap_le {n nstar A M : ℕ} (hnstar : 2 ≤ nstar)
    {c0 C0 Δ : ℝ} (hM : 0 < (M : ℝ)) (Y : Fin n → ℝ) (P : ClumpPartition n A)
    (hmax : HasMaxClumpSize P nstar) (hgeom : MultiClumpGeometry M c0 C0 Y P)
    (hgap : ∀ i j, i ≠ j → P.label i = P.label j →
      Δ ≤ angularTorusDistance (Y i) (Y j)) : (M : ℝ) * Δ ≤ c0 := by
  obtain ⟨a, ha⟩ := hmax.2
  have hs : 2 ≤ P.size a := by omega
  let i : Fin (P.size a) := ⟨0, by omega⟩
  let j : Fin (P.size a) := ⟨1, by omega⟩
  have hij : i ≠ j := by intro he; have := congrArg Fin.val he; dsimp [i, j] at this; omega
  have hval : (P.enumeration a i).val ≠ (P.enumeration a j).val := by
    intro he
    exact hij ((P.enumeration a).injective (Subtype.ext he))
  have hlabel : P.label (P.enumeration a i).val = P.label (P.enumeration a j).val := by
    rw [P.enumeration_label, P.enumeration_label]
  have hdelta := (hgap _ _ hval hlabel).trans (hgeom.within _ _ hlabel)
  simpa only [mul_comm] using (le_div_iff₀ hM).1 hdelta

/-- Combine the local constructive lower bounds with the half-energy comparison.
The coefficient `d/4` safely covers both normalization and the clump sum. -/
theorem multiClump_energy_lower_of_clump_singular_lower {n nstar A M : ℕ}
    (hn : 0 < n) (hM : 1 ≤ M) (Y : Fin n → ℝ) (P : ClumpPartition n A)
    (hmax : HasMaxClumpSize P nstar) {d Δ : ℝ} (hd : 0 ≤ d) (hΔ : 0 ≤ Δ)
    (hscale : (M : ℝ) * Δ ≤ 1)
    (hcross : ∀ a a', a ≠ a' → ∀ u ∈ P.columnSubspace M Y a,
      ∀ v ∈ P.columnSubspace M Y a',
        ‖⟪u, v⟫_ℂ‖ ≤ (1 / (2 * (n : ℝ))) * ‖u‖ * ‖v‖)
    (hclump : ∀ a, d * Real.sqrt (M : ℝ) *
      ((M : ℝ) * Δ / (32 * Real.pi * Real.exp 1)) ^ (P.size a - 1) ≤
        matrixSingularValue (ClusteredVandermonde.vandermonde M (P.nodes Y a)) (P.size a - 1))
    (z : EuclideanSpace ℂ (Fin n)) :
    (d / 4 * ((M : ℝ) * Δ / (32 * Real.pi * Real.exp 1)) ^ (nstar - 1)) ^ 2 * ‖z‖ ^ 2 ≤
      ‖fullFourierSignal M Y z‖ ^ 2 := by
  let x : ℝ := (M : ℝ) * Δ / (32 * Real.pi * Real.exp 1)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hb1 : 1 ≤ 32 * Real.pi * Real.exp 1 := by
    have he : 1 ≤ Real.exp 1 := by simp
    nlinarith [Real.pi_gt_three]
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one (by positivity)).2 (hscale.trans hb1)
  have hlocal (a : Fin A) :
      (d / 2 * x ^ (nstar - 1)) ^ 2 * ‖P.coefficients a z‖ ^ 2 ≤
        ‖P.signal M Y z a‖ ^ 2 := by
    have ha := singleClump_normalized_energy_lower_of_minimumSingularValue
      (P.size_pos a) hM (P.nodes Y a) hd hΔ (hclump a) (P.coefficients a z)
    have hpow : x ^ (nstar - 1) ≤ x ^ (P.size a - 1) :=
      pow_le_pow_of_le_one hx0 hx1 (Nat.sub_le_sub_right (hmax.1 a) 1)
    have hco := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ d / 2)
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ d / 2 * x ^ (nstar - 1))
      (by positivity : 0 ≤ d / 2 * x ^ (P.size a - 1))).2 hco
    exact (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)).trans ha
  have hsum : (d / 2 * x ^ (nstar - 1)) ^ 2 * ‖z‖ ^ 2 ≤
      ∑ a, ‖P.signal M Y z a‖ ^ 2 := by
    rw [← P.sum_coefficients_norm_sq, Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => hlocal a
  have hhalf := (clump_sum_half_energy hn P.clump_count_le (P.signal M Y z)
    (fun a a' haa => hcross a a' haa _ (P.signal_mem_columnSubspace M Y z a)
      _ (P.signal_mem_columnSubspace M Y z a'))).1
  rw [P.sum_signals] at hhalf
  have hsumhalf := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hcoef : (d / 4 * x ^ (nstar - 1)) ^ 2 * ‖z‖ ^ 2 ≤
      (1 / 2 : ℝ) * ((d / 2 * x ^ (nstar - 1)) ^ 2 * ‖z‖ ^ 2) := by
    nlinarith [sq_nonneg (d * x ^ (nstar - 1) * ‖z‖)]
  exact hcoef.trans (hsumhalf.trans hhalf)

/-- The resulting lower bound for the smallest full normalized singular value.
The local interpolation hypotheses have already been converted before invoking
this purely finite-dimensional assembly lemma. -/
theorem multiClump_minimumSingularValue_lower_of_clump_singular_lower {n nstar A M : ℕ}
    (hn : 0 < n) (hM : 1 ≤ M) (Y : Fin n → ℝ) (P : ClumpPartition n A)
    (hmax : HasMaxClumpSize P nstar) {d Δ : ℝ} (hd : 0 ≤ d) (hΔ : 0 ≤ Δ)
    (hscale : (M : ℝ) * Δ ≤ 1)
    (hcross : ∀ a a', a ≠ a' → ∀ u ∈ P.columnSubspace M Y a,
      ∀ v ∈ P.columnSubspace M Y a',
        ‖⟪u, v⟫_ℂ‖ ≤ (1 / (2 * (n : ℝ))) * ‖u‖ * ‖v‖)
    (hclump : ∀ a, d * Real.sqrt (M : ℝ) *
      ((M : ℝ) * Δ / (32 * Real.pi * Real.exp 1)) ^ (P.size a - 1) ≤
        matrixSingularValue (ClusteredVandermonde.vandermonde M (P.nodes Y a)) (P.size a - 1)) :
    d / 4 * ((M : ℝ) * Δ / (32 * Real.pi * Real.exp 1)) ^ (nstar - 1) ≤
      matrixSingularValue (fullVandermonde M Y) (n - 1) := by
  obtain ⟨z, hz, he⟩ := exists_unit_vector_norm_sq_eq_singularValue_sq
    (fullVandermonde M Y) (i := n - 1) (by simpa using Nat.sub_lt hn Nat.zero_lt_one)
  have henergy := multiClump_energy_lower_of_clump_singular_lower hn hM Y P hmax hd hΔ
    hscale hcross hclump z
  rw [norm_fullFourierSignal_sq, ← fullVandermonde_energy, he, hz, one_pow, mul_one] at henergy
  exact (sq_le_sq₀ (by positivity)
    ((fullVandermonde M Y).toEuclideanLin.singularValues_nonneg _)).1 henergy

end
end LeanNumDetect.RandSamp
