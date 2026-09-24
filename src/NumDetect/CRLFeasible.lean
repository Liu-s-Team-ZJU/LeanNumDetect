import NumDetect.Basic

/-! A finite feasible separation threshold for both number-detection CRLs. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect
namespace NumDetect

noncomputable section

private theorem abs_point_le_l1Norm {d : ℕ} (x : Point d) (k : Fin d) :
    |x k| ≤ l1Norm x := by
  unfold l1Norm
  exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ k)

/-- Any two nodes in the manuscript's source ball have coordinatewise
distance at most twice its radius. -/
theorem source_ball_coordinate_diameter {d n : ℕ} {Ω : ℝ}
    {x : Fin n → Point d}
    (hball : ∀ j, InOpenL1Ball (Real.pi * n / Ω) 0 (x j))
    (i j : Fin n) (k : Fin d) :
    |(x i - x j) k| ≤ 2 * (Real.pi * n / Ω) := by
  have hi : |x i k| ≤ Real.pi * n / Ω :=
    (abs_point_le_l1Norm (x i) k).trans (le_of_lt (by simpa [InOpenL1Ball] using hball i))
  have hj : |x j k| ≤ Real.pi * n / Ω :=
    (abs_point_le_l1Norm (x j) k).trans (le_of_lt (by simpa [InOpenL1Ball] using hball j))
  calc
    |(x i - x j) k| = |x i k - x j k| := rfl
    _ ≤ |x i k| + |x j k| := abs_sub _ _
    _ ≤ 2 * (Real.pi * n / Ω) := by linarith

/-- A finite uniform upper bound on `normAt p` for pairs of nodes in the
source ball. Its precise value is immaterial; adding one makes the separation
hypothesis impossible. -/
noncomputable def sourceBallSeparationBound (d n : ℕ) (p : LpIndex) (Ω : ℝ) : ℝ :=
  let B := 2 * (Real.pi * n / Ω)
  match p with
  | .finite q _ => ((d : ℝ) * B ^ q) ^ (1 / q) + 1
  | .infinity => B + 1

theorem sourceBallSeparationBound_pos {d n : ℕ} (p : LpIndex)
    {Ω : ℝ} (hΩ : 0 < Ω) (hn : 0 < n) :
    0 < sourceBallSeparationBound d n p Ω := by
  have hB : 0 ≤ 2 * (Real.pi * n / Ω) := by positivity
  cases p with
  | finite q hq =>
      unfold sourceBallSeparationBound
      dsimp
      have hpow : 0 ≤ ((d : ℝ) * (2 * (Real.pi * n / Ω)) ^ q) ^ (1 / q) :=
        Real.rpow_nonneg (by positivity) _
      linarith
  | infinity =>
      simp only [sourceBallSeparationBound]
      linarith

theorem normAt_source_ball_lt_bound {d n : ℕ} (p : LpIndex)
    {Ω : ℝ} (hΩ : 0 < Ω) (hn : 0 < n)
    {x : Fin n → Point d}
    (hball : ∀ j, InOpenL1Ball (Real.pi * n / Ω) 0 (x j))
    (i j : Fin n) :
    normAt p (x i - x j) < sourceBallSeparationBound d n p Ω := by
  have hB : 0 ≤ 2 * (Real.pi * n / Ω) := by positivity
  have hcoord (k : Fin d) := source_ball_coordinate_diameter hball i j k
  cases p with
  | finite q hq =>
      have hqpos : 0 < 1 / q := by positivity
      have hsum :
          (∑ k : Fin d, |(x i - x j) k| ^ q) ≤
            (d : ℝ) * (2 * (Real.pi * n / Ω)) ^ q := by
        calc
          _ ≤ ∑ _k : Fin d, (2 * (Real.pi * n / Ω)) ^ q := by
            apply Finset.sum_le_sum
            intro k _
            exact Real.rpow_le_rpow (abs_nonneg _) (hcoord k) (by linarith)
          _ = (d : ℝ) * (2 * (Real.pi * n / Ω)) ^ q := by simp
      have hpow := Real.rpow_le_rpow (Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (abs_nonneg _) _)) hsum (le_of_lt hqpos)
      simpa only [normAt, lpNorm, sourceBallSeparationBound] using lt_of_le_of_lt hpow (lt_add_one _)
  | infinity =>
      have hnorm : ‖x i - x j‖ ≤ 2 * (Real.pi * n / Ω) := by
        exact (pi_norm_le_iff_of_nonneg hB).2 (fun k => by simpa [Real.norm_eq_abs] using hcoord k)
      simpa only [normAt, linftyNorm, sourceBallSeparationBound] using
        lt_of_le_of_lt hnorm (lt_add_one _)

/-- The feasible set defining the general CRL is nonempty for every positive
bandwidth and every admissible dimension and source count. -/
theorem exists_numberDetectionGuarantee {d n : ℕ} (p : LpIndex)
    {Ω σ mMin : ℝ} (hΩ : 0 < Ω) (hn : 0 < n) (hn₂ : 2 ≤ n) :
    ∃ D : ℝ, 0 ≤ D ∧ NumberDetectionGuarantee d n p Ω σ mMin D hn := by
  refine ⟨sourceBallSeparationBound d n p Ω, le_of_lt (sourceBallSeparationBound_pos p hΩ hn), ?_⟩
  intro μ _ hball hsep Y hY k ν hν
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  have hge := hsep i j hij
  have hlt := normAt_source_ball_lt_bound p hΩ hn hball i j
  exfalso
  exact (not_le_of_gt hlt) hge

/-- The same finite feasible threshold works with positive amplitudes. -/
theorem exists_positiveNumberDetectionGuarantee {d n : ℕ} (p : LpIndex)
    {Ω σ mMin : ℝ} (hΩ : 0 < Ω) (hn : 0 < n) (hn₂ : 2 ≤ n) :
    ∃ D : ℝ, 0 ≤ D ∧ PositiveNumberDetectionGuarantee d n p Ω σ mMin D hn := by
  obtain ⟨D, hD, hgeneral⟩ :=
    exists_numberDetectionGuarantee p hΩ hn hn₂ (σ := σ) (mMin := mMin)
  refine ⟨D, hD, ?_⟩
  intro μ _ hmin hball hsep Y hY k ν hν
  exact hgeneral μ hmin hball hsep Y hY k ν hν.2

end
end NumDetect
end LeanNumDetect
