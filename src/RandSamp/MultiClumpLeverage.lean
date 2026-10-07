import RandSamp.ClumpSignals
import RandSamp.MultiClumpAssembly
import RandSamp.SingleClumpLeverage

/-! The deterministic multiclump integer-row leverage estimate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Matrix WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect.RandSamp
noncomputable section

/-- Assembly at the actual normalized signal level, with no conversion of
the analytic hypotheses hidden in the conclusion. -/
theorem multiClump_leverage_of_signal_bounds {n A M : ℕ}
    (P : ClumpPartition n A) (Y : Fin n → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hlocal : ∀ a (k : Fin (M + 1)),
      ‖P.signal M Y z a k‖ ^ 2 ≤
        (512 * (P.size a : ℝ) ^ 2 / ((M + 1 : ℕ) : ℝ)) *
          ‖P.signal M Y z a‖ ^ 2)
    (henergy : (1 / 2 : ℝ) * (∑ a, ‖P.signal M Y z a‖ ^ 2) ≤
      ‖fullFourierSignal M Y z‖ ^ 2)
    (k : Fin (M + 1)) :
    fourierRowEnergy Y k.val (ofLp z) ≤
      (1024 * (P.sizeSquareSum : ℝ)) *
        FiniteMatrixSampling.quadratic (fullGram M Y) z := by
  let L : Fin A → ℝ := fun a =>
    512 * (P.size a : ℝ) ^ 2 / ((M + 1 : ℕ) : ℝ)
  have hs := row_bound_of_clump_bounds (P.signal M Y z) L
    (fun a => by dsimp [L]; positivity) hlocal
    (by simpa only [P.sum_signals] using henergy) k
  rw [P.sum_signals] at hs
  have hsum : (∑ a, L a) =
      512 * (P.sizeSquareSum : ℝ) / ((M + 1 : ℕ) : ℝ) := by
    dsimp [L]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    simp only [ClumpPartition.sizeSquareSum, Nat.cast_sum, Nat.cast_pow]
  rw [hsum] at hs
  have hN : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hs hN.le
  rw [fullFourierSignal_coordinate_energy] at hh
  rw [← norm_fullFourierSignal_sq]
  simp only [Nat.cast_add, Nat.cast_one] at hN hh
  convert hh using 1 <;> first | rfl | (field_simp [hN.ne'] <;> ring)

namespace ClumpPartition
variable {n A : ℕ} (P : ClumpPartition n A)

/-- Integer-row energies and normalized clump signal energy have exactly
the common normalization `M+1`. -/
theorem signal_integer_energy (M : ℕ) (Y : Fin n → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (a : Fin A) :
    (∑ l ∈ Finset.range (M + 1),
      fourierRowEnergy (P.nodes Y a) l (ofLp (P.coefficients a z))) =
      ((M + 1 : ℕ) : ℝ) * ‖P.signal M Y z a‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  change (∑ l ∈ Finset.range (M + 1),
    fourierRowEnergy (P.nodes Y a) l (ofLp (P.coefficients a z))) =
      ∑ k : Fin (M + 1), ((M + 1 : ℕ) : ℝ) *
        ‖fullFourierSignal M (P.nodes Y a) (P.coefficients a z) k‖ ^ 2
  simp_rw [fullFourierSignal_coordinate_energy]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

/-- The single-clump analytic theorem bounds evaluations of the actual
normalized clump signal. No geometric implication is left as an assumption. -/
theorem signal_local_row_bound {M : ℕ} (hM : 0 < M)
    (Y : Fin n → ℝ) (z : EuclideanSpace ℂ (Fin n)) (a : Fin A)
    {c0 C0 : ℝ} (hc0 : 0 ≤ c0) (hc0radius : c0 ≤ singleClumpRadius (P.size a))
    (hgeometry : MultiClumpGeometry M c0 C0 Y P)
    (hsize : singleClumpGridThreshold (P.size a) ≤ (M : ℝ))
    (k : Fin (M + 1)) :
    ‖P.signal M Y z a k‖ ^ 2 ≤
      (512 * (P.size a : ℝ) ^ 2 / ((M + 1 : ℕ) : ℝ)) *
        ‖P.signal M Y z a‖ ^ 2 := by
  have hraw := singleClump_circular_row_bound (P.size_pos a) hM (P.nodes Y a)
    (ofLp (P.coefficients a z)) hc0 hc0radius
    (fun i j => hgeometry.within _ _ (by
      rw [P.enumeration_label, P.enumeration_label])) hsize
    (show k.val ≤ M by omega)
  simp only [Nat.cast_add, Nat.cast_one] at hraw ⊢
  have hpoint : ((M : ℝ) + 1) * ‖P.signal M Y z a k‖ ^ 2 =
      fourierRowEnergy (P.nodes Y a) k.val (ofLp (P.coefficients a z)) := by
    simpa only [signal, Nat.cast_add, Nat.cast_one] using
      fullFourierSignal_coordinate_energy M (P.nodes Y a) (P.coefficients a z) k
  have hfull := P.signal_integer_energy M Y z a
  simp only [Nat.cast_add, Nat.cast_one] at hfull
  rw [hfull, ← hpoint] at hraw
  have hN : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  rw [← mul_assoc, div_mul_cancel₀ _ hN.ne'] at hraw
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hN).2
  simpa only [mul_comm] using hraw

end ClumpPartition

/-- The deterministic leverage conclusion under the fully interpreted
geometric and subspace hypotheses, with the absolute constant `1024`. -/
theorem multiClump_leverage_of_geometry {n A M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (P : ClumpPartition n A) (Y : Fin n → ℝ)
    {c0 C0 : ℝ} (hc0 : 0 ≤ c0) (_hc0one : c0 ≤ 1)
    (hgeometry : MultiClumpGeometry M c0 C0 Y P)
    (hsize : ∀ a, singleClumpGridThreshold (P.size a) ≤ (M : ℝ))
    (hRadius : ∀ a, c0 ≤ singleClumpRadius (P.size a))
    (hcross : ∀ a b, a ≠ b →
      ∀ u ∈ P.columnSubspace M Y a, ∀ v ∈ P.columnSubspace M Y b,
        ‖⟪u, v⟫_ℂ‖ ≤ (1 / (2 * (n : ℝ))) * ‖u‖ * ‖v‖)
    (k : Fin (M + 1)) (z : EuclideanSpace ℂ (Fin n)) :
    fourierRowEnergy Y k.val (ofLp z) ≤
      (1024 * (P.sizeSquareSum : ℝ)) *
        FiniteMatrixSampling.quadratic (fullGram M Y) z := by
  apply multiClump_leverage_of_signal_bounds P Y z
    (fun a k => P.signal_local_row_bound hM Y z a hc0 (hRadius a) hgeometry (hsize a) k)
  have henergy := (clump_sum_half_energy hn P.clump_count_le (P.signal M Y z)
    (fun a b hab => hcross a b hab _ (P.signal_mem_columnSubspace M Y z a)
      _ (P.signal_mem_columnSubspace M Y z b))).1
  simpa only [P.sum_signals] using henergy

/-- One choice of thresholds provides the leverage estimate while also
preserving arbitrary additional cardinality-dependent frequency and
shortness requirements. These extra requirements can be used for the
full-matrix singular-value estimates with the very same geometry constants. -/
theorem multiClump_leverage_thresholds (n nstar : ℕ) (hnstar : 2 ≤ nstar)
    (hn : nstar ≤ n) (B b : ℕ → ℝ)
    (hb : ∀ s, 1 ≤ s → s ≤ nstar → 0 < b s) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      (∀ s, 1 ≤ s → s ≤ nstar → B s ≤ C0 ∧ c0 ≤ b s) ∧
      ∀ (M A : ℕ), C0 ≤ (M : ℝ) →
        ∀ (Y : Fin n → ℝ) (P : ClumpPartition n A),
          HasMaxClumpSize P nstar → MultiClumpGeometry M c0 C0 Y P →
          ∀ (k : Fin (M + 1)) (z : EuclideanSpace ℂ (Fin n)),
            fourierRowEnergy Y k.val (ofLp z) ≤
              (1024 * (P.sizeSquareSum : ℝ)) *
                FiniteMatrixSampling.quadratic (fullGram M Y) z := by
  obtain ⟨c0, C0, hc0, hc0one, hC0, hlocal, hcross⟩ :=
    multiClump_subspace_thresholds n nstar hnstar hn
      (fun s => max (singleClumpGridThreshold s) (B s))
      (fun s => min (singleClumpRadius s) (b s))
      (fun s hs hsmax => lt_min (singleClumpRadius_pos s) (hb s hs hsmax))
  refine ⟨c0, C0, hc0, hc0one, hC0, ?_, ?_⟩
  · intro s hs hsmax
    have h := hlocal s hs hsmax
    exact ⟨(le_max_right _ _).trans h.1, h.2.trans (min_le_right _ _)⟩
  · intro M A hM Y P hmax hgeometry k z
    have hn0 : 0 < n := by omega
    have hMR : (0 : ℝ) < M := (by exact_mod_cast hn0 : (0 : ℝ) < n).trans_le (hC0.trans hM)
    have hM0 : 0 < M := by exact_mod_cast hMR
    apply multiClump_leverage_of_geometry hn0 hM0 P Y hc0.le hc0one.le hgeometry
    · intro a
      have h := (hlocal (P.size a) (P.size_pos a) (hmax.1 a)).1
      exact (le_max_left _ _).trans (h.trans hM)
    · intro a
      exact (hlocal (P.size a) (P.size_pos a) (hmax.1 a)).2.trans (min_le_left _ _)
    · exact hcross M A hM Y P hmax hgeometry

/-- Deterministic leverage form of the manuscript theorem, before random
rows are selected. The row constant is absolute; geometric thresholds
depend only on `n,nstar`. -/
theorem multiClump_integer_row_leverage (n nstar : ℕ) (hnstar : 2 ≤ nstar)
    (hn : nstar ≤ n) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      ∀ (M A : ℕ), C0 ≤ (M : ℝ) →
        ∀ (Y : Fin n → ℝ) (P : ClumpPartition n A),
          HasMaxClumpSize P nstar → MultiClumpGeometry M c0 C0 Y P →
          ∀ (k : Fin (M + 1)) (z : EuclideanSpace ℂ (Fin n)),
            fourierRowEnergy Y k.val (ofLp z) ≤
              (1024 * (P.sizeSquareSum : ℝ)) *
                FiniteMatrixSampling.quadratic (fullGram M Y) z := by
  obtain ⟨c0, C0, hc0, hc0one, hC0, _, hbound⟩ :=
    multiClump_leverage_thresholds n nstar hnstar hn (fun _ => 0) (fun _ => 1)
      (fun _ _ _ => zero_lt_one)
  exact ⟨c0, C0, hc0, hc0one, hC0, hbound⟩

end
end LeanNumDetect.RandSamp
