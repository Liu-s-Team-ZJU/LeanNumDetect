import MultiTuran.ConsecutiveWindow.WindowCounting
import MultiTuran.ConsecutiveWindow.Interpolation
import MultiTuran.Preliminaries.Energy
import General.Fourier.ExponentialSums
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Actual scalar block integrals from consecutive windows

The block estimate partitions the entire thickened block into its unit cells
and applies the complete `2*n-1` window-counting inequality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
noncomputable section

theorem scalar_exponentialSum_translate {n : ℕ} (Y : Fin n → ℝ)
    (c : Fin n → ℂ) (a t : ℝ) :
    ExponentialSumEstimates.exponentialSum Y
      (fun j => c j * Complex.exp (Complex.I * ((a * Y j : ℝ) : ℂ))) t =
        ExponentialSumEstimates.exponentialSum Y c (a + t) := by
  unfold ExponentialSumEstimates.exponentialSum
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Exact interpolation of the whole scalar sum, including repeated nodes. -/
theorem scalar_exponentialSum_interpolation {n : ℕ} (Y : Fin n → ℝ)
    (c : Fin n → ℂ) (a : Fin n → ℂ) (t : ℝ)
    (ha : ∀ j, Complex.exp (Complex.I * ((t * Y j : ℝ) : ℂ)) =
      ∑ k, a k * Complex.exp (Complex.I * (((k.val : ℝ) * Y j : ℝ) : ℂ))) :
    ExponentialSumEstimates.exponentialSum Y c t =
      ∑ k, a k * ExponentialSumEstimates.exponentialSum Y c k.val := by
  unfold ExponentialSumEstimates.exponentialSum
  simp_rw [ha, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The coefficient mass controls the squared sample energy. -/
theorem norm_combination_sq_le {n : ℕ} (a z : Fin n → ℂ) {A : ℝ}
    (hA : 0 ≤ A) (ha : (∑ k, ‖a k‖) ≤ A) :
    ‖∑ k, a k * z k‖ ^ 2 ≤ A ^ 2 * ∑ k, ‖z k‖ ^ 2 := by
  let E : ℝ := ∑ k, ‖z k‖ ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hz (k : Fin n) : ‖z k‖ ≤ Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    change ‖z k‖ ^ 2 ≤ ∑ i : Fin n, ‖z i‖ ^ 2
    exact Finset.single_le_sum (fun i _ => sq_nonneg ‖z i‖) (Finset.mem_univ k)
  have hnorm : ‖∑ k, a k * z k‖ ≤ A * Real.sqrt E := by
    calc
      _ ≤ ∑ k, ‖a k * z k‖ := norm_sum_le _ _
      _ = ∑ k, ‖a k‖ * ‖z k‖ := by simp only [norm_mul]
      _ ≤ ∑ k, ‖a k‖ * Real.sqrt E :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hz k) (norm_nonneg _)
      _ = (∑ k, ‖a k‖) * Real.sqrt E := (Finset.sum_mul _ _ _).symm
      _ ≤ A * Real.sqrt E := mul_le_mul_of_nonneg_right ha (Real.sqrt_nonneg _)
  have hsq := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hA (Real.sqrt_nonneg E))).mpr hnorm
  simpa only [mul_pow, Real.sq_sqrt hE, E] using hsq

/-- A cell estimate integrates and counts every cell of the block. This
transfer lemma has no exponential-sum or distinct-node assumption. -/
theorem block_integral_le_of_cell_bound {L n : ℕ} (hn : 0 < n) (hnL : n ≤ L)
    (a : ℝ) (f : ℝ → ℝ) (hf : Continuous f) (hpos : ∀ t, 0 ≤ f t)
    {A : ℝ} (hA : 0 ≤ A)
    (hcell : ∀ k : Fin L, ∀ t ∈ Icc (a + k.val) (a + k.val + 1),
      f t ≤ A * ∑ j : Fin n, f (a + (windowIndex hn hnL k j).val)) :
    (∫ t in Icc a (a + L), f t) ≤
      A * (2 * (n : ℝ) - 1) * ∑ k : Fin L, f (a + k.val) := by
  have hcellInt (k : Fin L) :
      (∫ t in (a + k.val)..(a + k.val + 1), f t) ≤
        A * ∑ j : Fin n, f (a + (windowIndex hn hnL k j).val) := by
    have hm := intervalIntegral.integral_mono_on (μ := volume)
      (by linarith : a + (k.val : ℝ) ≤ a + k.val + 1)
      (hf.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      (hcell k)
    simpa only [intervalIntegral.integral_const, smul_eq_mul,
      show a + (k.val : ℝ) + 1 - (a + k.val) = 1 by ring, one_mul] using hm
  let p : ℕ → ℝ := fun k => a + k
  have hpartition := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (a := p) (n := L) (fun k _ => hf.intervalIntegrable (p k) (p (k+1)))
  have hpartition' : (∫ t in Icc a (a + L), f t) =
      ∑ k : Fin L, ∫ t in (a + k.val)..(a + k.val + 1), f t := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
      (by linarith [Nat.cast_nonneg (α := ℝ) L] : a ≤ a + L)]
    simpa only [p, Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one,
      ← Fin.sum_univ_eq_sum_range, add_assoc] using hpartition.symm
  rw [hpartition']
  calc
    _ ≤ ∑ k : Fin L, A * ∑ j : Fin n, f (a + (windowIndex hn hnL k j).val) :=
      Finset.sum_le_sum fun k _ => hcellInt k
    _ = A * ∑ k : Fin L, ∑ j : Fin n, f (a + (windowIndex hn hnL k j).val) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ A * ((2 * (n : ℝ) - 1) * ∑ k : Fin L, f (a + k.val)) :=
      mul_le_mul_of_nonneg_left (window_weighted_sum_le hn hnL
        (fun k => f (a + k.val)) (fun k => hpos _)) hA
    _ = _ := by ring

/-- Conversion from the local `Fin L` enumeration to the original measured
integer block. -/
theorem sum_block_samples {L : ℕ} (hL : 0 < L) (a : ℕ) (f : ℕ → ℝ) :
    (∑ k : Fin L, f (a + k.val)) =
      ∑ k ∈ Finset.Icc a (a + (L - 1)), f k := by
  classical
  apply Finset.sum_bij (fun k _ => a + k.val)
  · intro k _
    simp only [Finset.mem_Icc]
    have hk := k.isLt
    omega
  · intro k _ l _ he
    exact Fin.ext (by omega)
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    refine ⟨⟨k - a, by omega⟩, Finset.mem_univ _, ?_⟩
    change a + (k - a) = k
    omega
  · intro k _
    rfl

/-- The local exponential-sum cell estimate follows from exact interpolation
and its coefficient mass, after shifting only the source coefficients. -/
theorem scalar_cell_energy_le_of_interpolation {L n : ℕ} (hn : 0 < n) (hnL : n ≤ L)
    (Y : Fin n → ℝ) (c : Fin n → ℂ)
    (hinterp : ∀ t : ℝ, 0 ≤ t → t ≤ n → ∃ α : Fin n → ℂ,
      (∑ j, ‖α j‖) ≤ 3 * (3 * (n : ℝ)) ^ n ∧
      ∀ j, Complex.exp (Complex.I * ((t * Y j : ℝ) : ℂ)) =
        ∑ k, α k * Complex.exp (Complex.I * (((k.val : ℝ) * Y j : ℝ) : ℂ)))
    (a : ℝ) (k : Fin L) {t : ℝ} (ht : t ∈ Icc (a + k.val) (a + k.val + 1)) :
    ‖ExponentialSumEstimates.exponentialSum Y c t‖ ^ 2 ≤
      9 * (3 * (n : ℝ)) ^ (2 * n) *
        ∑ j : Fin n, ‖ExponentialSumEstimates.exponentialSum Y c
          (a + (windowIndex hn hnL k j).val)‖ ^ 2 := by
  let b : ℝ := a + windowStart L n k.val
  have hoffset := cell_offset_mem_window hn hnL k
    (by linarith [ht.1] : 0 ≤ t - (a + k.val))
    (by linarith [ht.2] : t - (a + k.val) ≤ 1)
  have h0 : 0 ≤ t - b := by dsimp [b]; linarith [hoffset.1]
  have h1 : t - b ≤ n := by dsimp [b]; linarith [hoffset.2]
  obtain ⟨α, hα, hrepr⟩ := hinterp (t - b) h0 h1
  let z : Fin n → ℂ := fun j => c j * Complex.exp (Complex.I * ((b * Y j : ℝ) : ℂ))
  have htranslate (u : ℝ) : ExponentialSumEstimates.exponentialSum Y z u =
      ExponentialSumEstimates.exponentialSum Y c (b + u) := scalar_exponentialSum_translate Y c b u
  have hsum := scalar_exponentialSum_interpolation Y z α (t - b) hrepr
  rw [htranslate, show b + (t-b) = t by ring] at hsum
  simp_rw [htranslate] at hsum
  have hsquare := norm_combination_sq_le α
    (fun j => ExponentialSumEstimates.exponentialSum Y c (b + j.val))
    (by positivity : 0 ≤ 3 * (3 * (n : ℝ)) ^ n) hα
  rw [← hsum] at hsquare
  have hconstant : (3 * (3 * (n : ℝ)) ^ n) ^ 2 = 9 * (3 * (n : ℝ)) ^ (2*n) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm n 2]
    norm_num
  rw [hconstant] at hsquare
  have harg (j : Fin n) : a + ((windowIndex hn hnL k j).val : ℝ) = b + j.val := by
    dsimp [b, windowIndex]
    push_cast
    ring
  simpa only [harg] using hsquare

/-- The exact measured scalar block energy, with the manuscript's constant.
This transfer is used below with the proved analytic interpolation theorem. -/
theorem scalar_block_energy_le_of_interpolation {L n : ℕ} (hn : 0 < n) (hnL : n ≤ L)
    (Y : Fin n → ℝ) (c : Fin n → ℂ)
    (hinterp : ∀ t : ℝ, 0 ≤ t → t ≤ n → ∃ α : Fin n → ℂ,
      (∑ j, ‖α j‖) ≤ 3 * (3 * (n : ℝ)) ^ n ∧
      ∀ j, Complex.exp (Complex.I * ((t * Y j : ℝ) : ℂ)) =
        ∑ k, α k * Complex.exp (Complex.I * (((k.val : ℝ) * Y j : ℝ) : ℂ)))
    (a : ℕ) :
    (∫ t in Icc (a : ℝ) ((a + L : ℕ) : ℝ),
      ‖ExponentialSumEstimates.exponentialSum Y c t‖ ^ 2) ≤
      (18 * (n : ℝ) * (3 * (n : ℝ)) ^ (2*n)) *
        ∑ k ∈ Finset.Icc a (a + (L-1)),
          ‖ExponentialSumEstimates.exponentialSum Y c k‖ ^ 2 := by
  have hblock := block_integral_le_of_cell_bound hn hnL (a : ℝ)
    (fun t => ‖ExponentialSumEstimates.exponentialSum Y c t‖ ^ 2)
    ((ExponentialSumEstimates.continuous_exponentialSum Y c).norm.pow 2)
    (fun _ => sq_nonneg _) (by positivity : 0 ≤ 9 * (3 * (n : ℝ)) ^ (2*n))
    (fun k t ht => scalar_cell_energy_le_of_interpolation hn hnL Y c hinterp a k ht)
  have hsum : (∑ k : Fin L, ‖ExponentialSumEstimates.exponentialSum Y c ((a : ℝ) + k.val)‖ ^ 2) =
      ∑ k ∈ Finset.Icc a (a + (L-1)), ‖ExponentialSumEstimates.exponentialSum Y c k‖ ^ 2 := by
    simpa only [Nat.cast_add] using sum_block_samples (hn.trans_le hnL) a
      (fun k => ‖ExponentialSumEstimates.exponentialSum Y c k‖ ^ 2)
  rw [hsum] at hblock
  have hsumpos : 0 ≤ ∑ k ∈ Finset.Icc a (a + (L-1)),
      ‖ExponentialSumEstimates.exponentialSum Y c k‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hconstant : 9 * (3 * (n : ℝ)) ^ (2*n) * (2 * (n : ℝ) - 1) ≤
      18 * (n : ℝ) * (3 * (n : ℝ)) ^ (2*n) := by
    nlinarith [pow_nonneg (show 0 ≤ 3*(n : ℝ) by positivity) (2*n)]
  simpa only [Nat.cast_add] using hblock.trans
    (mul_le_mul_of_nonneg_right hconstant hsumpos)

/-- Summing all original block inequalities gives the actual coordinate
thickening and exactly the original coordinate row set. -/
theorem coordinate_integral_le_of_block_bound {d : ℕ} (G : SegmentedGrid d)
    (q : Fin d) (f : ℝ → ℝ) (hf : Continuous f) (hpos : ∀ t, 0 ≤ f t)
    {C : ℝ}
    (hblock : ∀ m : G.Block q,
      (∫ t in Icc (G.start q m : ℝ) ((G.start q m + G.thickLength q m : ℕ) : ℝ), f t) ≤
        C * ∑ k ∈ G.blockRows q m, f k) :
    (∫ t in G.coordinateThickening q, f t) ≤
      C * ∑ k : {k : ℕ // k ∈ G.coordinateRows q}, f k.val := by
  classical
  let S := fun m : G.Block q => Icc (G.start q m : ℝ)
    ((G.start q m + G.thickLength q m : ℕ) : ℝ)
  have hI : Integrable ((G.coordinateThickening q).indicator f) :=
    (integrable_indicator_iff (G.coordinateThickening_isCompact q).measurableSet).2
      (hf.continuousOn.integrableOn_compact (G.coordinateThickening_isCompact q))
  have hIS (m : G.Block q) : Integrable ((S m).indicator f) :=
    (integrable_indicator_iff measurableSet_Icc).2
      (hf.continuousOn.integrableOn_compact isCompact_Icc)
  have hsumI : Integrable (fun t => ∑ m : G.Block q, (S m).indicator f t) :=
    integrable_finsetSum _ fun m _ => hIS m
  have hcover : (∫ t in G.coordinateThickening q, f t) ≤
      ∑ m : G.Block q, ∫ t in S m, f t := by
    rw [← integral_indicator (G.coordinateThickening_isCompact q).measurableSet]
    calc
      _ ≤ ∫ t, ∑ m : G.Block q, (S m).indicator f t := by
        apply integral_mono hI hsumI
        intro t
        by_cases ht : t ∈ G.coordinateThickening q
        · obtain ⟨m, hm⟩ := Set.mem_iUnion.mp ht
          rw [Set.indicator_of_mem ht]
          calc
            f t = (S m).indicator f t := (Set.indicator_of_mem hm f).symm
            _ ≤ _ := Finset.single_le_sum
              (fun m _ => Set.indicator_nonneg (fun t _ => hpos t) t) (Finset.mem_univ m)
        · rw [Set.indicator_of_notMem ht]
          exact Finset.sum_nonneg fun m _ => Set.indicator_nonneg (fun t _ => hpos t) t
      _ = _ := by
        rw [integral_finsetSum _ (fun m _ => hIS m)]
        apply Finset.sum_congr rfl
        intro m _
        exact integral_indicator measurableSet_Icc
  have hrows : (∑ m : G.Block q, ∑ k ∈ G.blockRows q m, f k) =
      ∑ k : {k : ℕ // k ∈ G.coordinateRows q}, f k.val := by
    rw [← Finset.sum_biUnion (fun i _ j _ hij => G.blockRows_disjoint q hij)]
    change (∑ k ∈ G.coordinateRows q, f k) = _
    exact (Finset.sum_attach _ _).symm
  calc
    _ ≤ ∑ m : G.Block q, ∫ t in S m, f t := hcover
    _ ≤ ∑ m : G.Block q, C * ∑ k ∈ G.blockRows q m, f k :=
      Finset.sum_le_sum fun m _ => hblock m
    _ = _ := by rw [← Finset.mul_sum, hrows]

/-- The same scalar estimate on one original grid block. -/
theorem scalar_grid_block_energy_le_of_interpolation {d n : ℕ} (G : SegmentedGrid d)
    (hn : 0 < n) (Y : Fin n → ℝ) (c : Fin n → ℂ)
    (hinterp : ∀ t : ℝ, 0 ≤ t → t ≤ n → ∃ α : Fin n → ℂ,
      (∑ j, ‖α j‖) ≤ 3 * (3 * (n : ℝ)) ^ n ∧
      ∀ j, Complex.exp (Complex.I * ((t * Y j : ℝ) : ℂ)) =
        ∑ k, α k * Complex.exp (Complex.I * (((k.val : ℝ) * Y j : ℝ) : ℂ)))
    (q : Fin d) (m : G.Block q) (hnL : n ≤ G.thickLength q m) :
    (∫ t in Icc (G.start q m : ℝ) ((G.start q m + G.thickLength q m : ℕ) : ℝ),
      ‖ExponentialSumEstimates.exponentialSum Y c t‖ ^ 2) ≤
        (18 * (n : ℝ) * (3 * (n : ℝ)) ^ (2*n)) *
          ∑ k ∈ G.blockRows q m, ‖ExponentialSumEstimates.exponentialSum Y c k‖ ^ 2 := by
  simpa only [SegmentedGrid.blockRows, SegmentedGrid.thickLength, Nat.add_sub_cancel] using
    scalar_block_energy_le_of_interpolation hn hnL Y c hinterp (G.start q m)

/-- All coordinate blocks retain their original rows and their exact full
thickened intervals. -/
theorem scalar_coordinate_energy_le_of_interpolation {d n : ℕ} (G : SegmentedGrid d)
    (hn : 0 < n) (Y : Fin n → ℝ) (c : Fin n → ℂ)
    (hinterp : ∀ t : ℝ, 0 ≤ t → t ≤ n → ∃ α : Fin n → ℂ,
      (∑ j, ‖α j‖) ≤ 3 * (3 * (n : ℝ)) ^ n ∧
      ∀ j, Complex.exp (Complex.I * ((t * Y j : ℝ) : ℂ)) =
        ∑ k, α k * Complex.exp (Complex.I * (((k.val : ℝ) * Y j : ℝ) : ℂ)))
    (q : Fin d) (hblocks : ∀ m : G.Block q, n ≤ G.thickLength q m) :
    (∫ t in G.coordinateThickening q, ‖ExponentialSumEstimates.exponentialSum Y c t‖ ^ 2) ≤
      (18 * (n : ℝ) * (3 * (n : ℝ)) ^ (2*n)) *
        ∑ k : {k : ℕ // k ∈ G.coordinateRows q},
          ‖ExponentialSumEstimates.exponentialSum Y c k.val‖ ^ 2 := by
  apply coordinate_integral_le_of_block_bound G q
    (fun t => ‖ExponentialSumEstimates.exponentialSum Y c t‖ ^ 2)
    ((ExponentialSumEstimates.continuous_exponentialSum Y c).norm.pow 2)
    (fun _ => sq_nonneg _)
  intro m
  exact scalar_grid_block_energy_le_of_interpolation G hn Y c hinterp q m (hblocks m)

/-- Unconditional scalar block norming on the short angular chart. -/
theorem scalar_block_energy_le {L n : ℕ} (hn : 2 ≤ n) (hnL : n ≤ L)
    (Y : Fin n → ℝ) (c : Fin n → ℂ)
    (hY : ∀ j, |Y j| ≤ Real.pi-Real.pi/(n : ℝ)) (a : ℕ) :
    (∫ t in Icc (a : ℝ) ((a + L : ℕ) : ℝ),
      ‖ExponentialSumEstimates.exponentialSum Y c t‖ ^ 2) ≤
      (18 * (n : ℝ) * (3 * (n : ℝ)) ^ (2*n)) *
        ∑ k ∈ Finset.Icc a (a + (L-1)),
          ‖ExponentialSumEstimates.exponentialSum Y c k‖ ^ 2 := by
  exact scalar_block_energy_le_of_interpolation (by omega) hnL Y c
    (fun _ ht0 htn => exists_window_interpolation_coefficients hn Y hY ht0 htn) a

/-- The reusable actual local-block estimate, with no interpolation premise. -/
theorem scalar_grid_block_energy_le {d n : ℕ} (G : SegmentedGrid d)
    (hn : 2 ≤ n) (Y : Fin n → ℝ) (c : Fin n → ℂ)
    (hY : ∀ j, |Y j| ≤ Real.pi-Real.pi/(n : ℝ))
    (q : Fin d) (m : G.Block q) (hnL : n ≤ G.thickLength q m) :
    (∫ t in Icc (G.start q m : ℝ) ((G.start q m + G.thickLength q m : ℕ) : ℝ),
      ‖ExponentialSumEstimates.exponentialSum Y c t‖ ^ 2) ≤
        (18 * (n : ℝ) * (3 * (n : ℝ)) ^ (2*n)) *
          ∑ k ∈ G.blockRows q m, ‖ExponentialSumEstimates.exponentialSum Y c k‖ ^ 2 := by
  exact scalar_grid_block_energy_le_of_interpolation G (by omega) Y c
    (fun _ ht0 htn => exists_window_interpolation_coefficients hn Y hY ht0 htn) q m hnL

/-- Norming on the whole genuine coordinate thickening. -/
theorem scalar_coordinate_energy_le {d n : ℕ} (G : SegmentedGrid d)
    (hn : 2 ≤ n) (Y : Fin n → ℝ) (c : Fin n → ℂ)
    (hY : ∀ j, |Y j| ≤ Real.pi-Real.pi/(n : ℝ))
    (q : Fin d) (hblocks : ∀ m : G.Block q, n ≤ G.thickLength q m) :
    (∫ t in G.coordinateThickening q, ‖ExponentialSumEstimates.exponentialSum Y c t‖ ^ 2) ≤
      (18 * (n : ℝ) * (3 * (n : ℝ)) ^ (2*n)) *
        ∑ k : {k : ℕ // k ∈ G.coordinateRows q},
          ‖ExponentialSumEstimates.exponentialSum Y c k.val‖ ^ 2 := by
  exact scalar_coordinate_energy_le_of_interpolation G (by omega) Y c
    (fun _ ht0 htn => exists_window_interpolation_coefficients hn Y hY ht0 htn) q hblocks

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
