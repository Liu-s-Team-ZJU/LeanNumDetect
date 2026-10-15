import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Right endpoint Riemann sums on the unit interval, for arbitrary continuous
real functions. The proof uses only uniform continuity and interval integration. -/

set_option autoImplicit false
open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- The equally spaced right endpoint Riemann average, including `1`. -/
def rightRiemannSum (g : ℝ → ℝ) (M : ℕ) : ℝ :=
  (∑ k : Fin M, g (((k.val : ℝ) + 1) / (M : ℝ))) / M

/-- A uniform cell oscillation controls the entire Riemann-sum error. -/
theorem abs_rightRiemannSum_sub_integral_le {g : ℝ → ℝ} (hg : Continuous g)
    {M : ℕ} (hM : 0 < M) {ε : ℝ} (hε : 0 ≤ ε)
    (hmod : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |t-u| ≤ 1/(M : ℝ) → |g t-g u| ≤ ε) :
    |rightRiemannSum g M - ∫ t in (0 : ℝ)..1, g t| ≤ ε := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hM0 : (M : ℝ) ≠ 0 := hMR.ne'
  let a : ℕ → ℝ := fun k => (k : ℝ) / M
  have ha0 : a 0 = 0 := by simp [a]
  have haM : a M = 1 := by simp [a, hM0]
  have hstep (k : ℕ) : a (k+1) - a k = 1/(M : ℝ) := by
    dsimp [a]
    push_cast
    ring
  have hcell (k : ℕ) (hk : k < M) :
      (1/(M : ℝ)) * (g (a (k+1))-ε) ≤ (∫ t in a k..a (k+1), g t) ∧
      (∫ t in a k..a (k+1), g t) ≤ (1/(M : ℝ)) * (g (a (k+1))+ε) := by
    have hak : 0 ≤ a k := by dsimp [a]; positivity
    have hab : a k ≤ a (k+1) := by linarith [hstep k, one_div_pos.mpr hMR]
    have hab1 : a (k+1) ≤ 1 := by
      dsimp [a]
      rw [div_le_one hMR]
      exact_mod_cast (show k+1 ≤ M by omega)
    have hu : a (k+1) ∈ Icc (0 : ℝ) 1 := ⟨hak.trans hab, hab1⟩
    have hbound (t : ℝ) (ht : t ∈ Icc (a k) (a (k+1))) :
        g (a (k+1))-ε ≤ g t ∧ g t ≤ g (a (k+1))+ε := by
      have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨hak.trans ht.1, ht.2.trans hab1⟩
      have hd : |t-a (k+1)| ≤ 1/(M : ℝ) := by
        rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
        linarith [ht.1,hstep k]
      have hh := abs_le.mp (hmod (a (k+1)) hu t ht01 hd)
      constructor <;> linarith
    constructor
    · have hh := intervalIntegral.integral_mono_on (μ := volume) hab
        (continuous_const.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
        (f := fun _ => g (a (k+1))-ε) (fun t ht => (hbound t ht).1)
      simpa only [intervalIntegral.integral_const, smul_eq_mul, hstep] using hh
    · have hh := intervalIntegral.integral_mono_on (μ := volume) hab
        (hg.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
        (g := fun _ => g (a (k+1))+ε) (fun t ht => (hbound t ht).2)
      simpa only [intervalIntegral.integral_const, smul_eq_mul, hstep] using hh
  have hpartition := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (a := a) (n := M) (fun k _ => hg.intervalIntegrable (a k) (a (k+1)))
  rw [ha0,haM] at hpartition
  have hsumlow := Finset.sum_le_sum (s := Finset.range M)
    (fun k hk => (hcell k (Finset.mem_range.mp hk)).1)
  have hsumup := Finset.sum_le_sum (s := Finset.range M)
    (fun k hk => (hcell k (Finset.mem_range.mp hk)).2)
  rw [hpartition] at hsumlow hsumup
  have hsumid : (∑ k ∈ Finset.range M, g (a (k+1))) / M = rightRiemannSum g M := by
    unfold rightRiemannSum
    congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    simp only [a, Nat.cast_add, Nat.cast_one]
  have hlo : (∑ k ∈ Finset.range M, (1/(M : ℝ)) * (g (a (k+1))-ε)) =
      rightRiemannSum g M-ε := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    rw [show (1/(M : ℝ)) * ((∑ k ∈ Finset.range M, g (a (k+1))) - (M : ℝ)*ε) =
      (∑ k ∈ Finset.range M, g (a (k+1))) / M - ε by field_simp [hM0]]
    rw [hsumid]
  have hup : (∑ k ∈ Finset.range M, (1/(M : ℝ)) * (g (a (k+1))+ε)) =
      rightRiemannSum g M+ε := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    rw [show (1/(M : ℝ)) * ((∑ k ∈ Finset.range M, g (a (k+1))) + (M : ℝ)*ε) =
      (∑ k ∈ Finset.range M, g (a (k+1))) / M + ε by field_simp [hM0]]
    rw [hsumid]
  rw [hlo] at hsumlow
  rw [hup] at hsumup
  rw [abs_le]
  constructor <;> linarith

/-- Right Riemann averages converge to the genuine Bochner interval integral. -/
theorem tendsto_rightRiemannSum {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (rightRiemannSum g) atTop (𝓝 (∫ t in (0 : ℝ)..1, g t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hu := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).uniformContinuousOn_of_continuous hg.continuousOn
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuousOn_iff.mp hu (ε/2) (by positivity)
  have hmesh : ∀ᶠ M : ℕ in atTop, 1/(M : ℝ) < δ :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hδ)
  filter_upwards [hmesh, eventually_gt_atTop 0] with M hsmall hM
  have hh := abs_rightRiemannSum_sub_integral_le hg hM (by positivity : 0 ≤ ε/2)
    (fun u hu t ht hdist => by
      have hh := hmod t ht u hu (by simpa only [Real.dist_eq] using hdist.trans_lt hsmall)
      exact (by simpa only [Real.dist_eq] using hh.le))
  rw [Real.dist_eq]
  exact hh.trans_lt (by linarith)

/-- The same limit along an arbitrary fixed positive multiple of the mesh. -/
theorem tendsto_rightRiemannSum_mul {g : ℝ → ℝ} (hg : Continuous g)
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun m : ℕ => rightRiemannSum g (n*m)) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, g t)) := by
  apply (tendsto_rightRiemannSum hg).comp
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with m hm
  exact hm.trans (by simpa using Nat.mul_le_mul_right m (Nat.succ_le_of_lt hn))

end
end LeanNumDetect.MultiTuran
