import RandSamp.MultiClumpModel
import RandSamp.CubeRandomModel

/-! Angular multiclump geometry in arbitrary positive dimension. The partition
is shared with the one-dimensional model. The metric is the maximum of the
coordinate angular distances; its one-dimensional specialization is exact. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open Matrix WithLp

namespace LeanNumDetect.RandSamp

noncomputable section

/-- Angular infinity distance on the product torus `ℝ^d/(2πℤ)^d`. -/
def multidimensionalAngularTorusDistance {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  sSup (Set.range fun r => angularTorusDistance (x r) (y r))

theorem angularTorusDistance_le_multidimensional {d : ℕ} (x y : Fin d → ℝ) (r : Fin d) :
    angularTorusDistance (x r) (y r) ≤ multidimensionalAngularTorusDistance x y :=
  le_csSup (Set.finite_range _).bddAbove ⟨r, rfl⟩

theorem multidimensionalAngularTorusDistance_attained {d : ℕ} (hd : 1 ≤ d)
    (x y : Fin d → ℝ) :
    ∃ r : Fin d, angularTorusDistance (x r) (y r) = multidimensionalAngularTorusDistance x y := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  exact (Set.range_nonempty _).csSup_mem (Set.finite_range _)

theorem multidimensionalAngularTorusDistance_nonneg {d : ℕ} (hd : 1 ≤ d)
    (x y : Fin d → ℝ) : 0 ≤ multidimensionalAngularTorusDistance x y :=
  (angularTorusDistance_nonneg (x ⟨0, by omega⟩) (y ⟨0, by omega⟩)).trans
    (angularTorusDistance_le_multidimensional x y ⟨0, by omega⟩)

theorem multidimensionalAngularTorusDistance_le_iff {d : ℕ} (hd : 1 ≤ d)
    (x y : Fin d → ℝ) (w : ℝ) :
    multidimensionalAngularTorusDistance x y ≤ w ↔
      ∀ r, angularTorusDistance (x r) (y r) ≤ w := by
  constructor
  · intro h r
    exact (angularTorusDistance_le_multidimensional x y r).trans h
  · intro h
    letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨r, rfl⟩
    exact h r

theorem le_multidimensionalAngularTorusDistance_iff {d : ℕ} (hd : 1 ≤ d)
    (x y : Fin d → ℝ) (w : ℝ) :
    w ≤ multidimensionalAngularTorusDistance x y ↔
      ∃ r, w ≤ angularTorusDistance (x r) (y r) := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := multidimensionalAngularTorusDistance_attained hd x y
    exact ⟨r, hr ▸ h⟩
  · rintro ⟨r, hr⟩
    exact hr.trans (angularTorusDistance_le_multidimensional x y r)

theorem multidimensionalAngularTorusDistance_comm {d : ℕ} (x y : Fin d → ℝ) :
    multidimensionalAngularTorusDistance x y = multidimensionalAngularTorusDistance y x := by
  simp only [multidimensionalAngularTorusDistance, angularTorusDistance_comm]

theorem multidimensionalAngularTorusDistance_le_pi {d : ℕ} (hd : 1 ≤ d)
    (x y : Fin d → ℝ) : multidimensionalAngularTorusDistance x y ≤ Real.pi :=
  (multidimensionalAngularTorusDistance_le_iff hd x y Real.pi).2
    (fun r => angularTorusDistance_le_pi (x r) (y r))

@[simp] theorem multidimensionalAngularTorusDistance_one (x y : ℝ) :
    multidimensionalAngularTorusDistance (fun _ : Fin 1 => x) (fun _ => y) =
      angularTorusDistance x y := by
  simp [multidimensionalAngularTorusDistance, Set.range_const]

theorem multidimensionalAngularTorusDistance_add_winding_left {d : ℕ}
    (x y : Fin d → ℝ) (p : Fin d → ℤ) :
    multidimensionalAngularTorusDistance (fun r => x r + 2 * Real.pi * p r) y =
      multidimensionalAngularTorusDistance x y := by
  simp only [multidimensionalAngularTorusDistance, angularTorusDistance_add_winding_left]

theorem multidimensional_short_clump_lift {d s : ℕ} (_hd : 1 ≤ d) (hs : 0 < s)
    (Y : Fin s → Fin d → ℝ) {w : ℝ} (hw : 0 ≤ w) (hshort : 3 * w < 2 * Real.pi)
    (hpair : ∀ i j, multidimensionalAngularTorusDistance (Y i) (Y j) ≤ w) :
    ∃ p : Fin s → Fin d → ℤ,
      ∀ r, Metric.diam (Set.range fun j => Y j r - 2 * Real.pi * p j r) ≤ w := by
  have hcoordinate (r : Fin d) := angular_short_clump_lift hs (fun j => Y j r) hw hshort
    (fun i j => (angularTorusDistance_le_multidimensional (Y i) (Y j) r).trans (hpair i j))
  choose p hp using hcoordinate
  exact ⟨fun j r => p r j, hp⟩

/-- Periodic angular one-norm distance, used for the sharp lower spacing parameter. -/
def multidimensionalAngularTorusL1Distance {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  ∑ r, angularTorusDistance (x r) (y r)

theorem multidimensionalAngularTorusL1Distance_nonneg {d : ℕ} (x y : Fin d → ℝ) :
    0 ≤ multidimensionalAngularTorusL1Distance x y :=
  Finset.sum_nonneg fun r _ => angularTorusDistance_nonneg (x r) (y r)

theorem multidimensionalAngularTorusDistance_le_l1 {d : ℕ} (hd : 1 ≤ d)
    (x y : Fin d → ℝ) :
    multidimensionalAngularTorusDistance x y ≤ multidimensionalAngularTorusL1Distance x y := by
  obtain ⟨r, hr⟩ := multidimensionalAngularTorusDistance_attained hd x y
  rw [← hr]
  exact Finset.single_le_sum (fun a _ => angularTorusDistance_nonneg (x a) (y a))
    (Finset.mem_univ r)

theorem multidimensionalAngularTorusL1Distance_le_dimension_mul {d : ℕ}
    (x y : Fin d → ℝ) :
    multidimensionalAngularTorusL1Distance x y ≤
      (d : ℝ) * multidimensionalAngularTorusDistance x y := by
  calc
    _ ≤ ∑ _r : Fin d, multidimensionalAngularTorusDistance x y :=
      Finset.sum_le_sum fun r _ => angularTorusDistance_le_multidimensional x y r
    _ = _ := by simp

theorem div_dimension_le_multidimensionalAngularTorusDistance {d : ℕ} (hd : 1 ≤ d)
    (x y : Fin d → ℝ) {Δ : ℝ} (hΔ : Δ ≤ multidimensionalAngularTorusL1Distance x y) :
    Δ / (d : ℝ) ≤ multidimensionalAngularTorusDistance x y := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  apply (div_le_iff₀ hdr).2
  simpa only [mul_comm] using hΔ.trans (multidimensionalAngularTorusL1Distance_le_dimension_mul x y)

@[simp] theorem multidimensionalAngularTorusL1Distance_one (x y : ℝ) :
    multidimensionalAngularTorusL1Distance (fun _ : Fin 1 => x) (fun _ => y) =
      angularTorusDistance x y := by
  simp [multidimensionalAngularTorusL1Distance]

/-- Distinct points of the angular product torus, independently of their lifts. -/
def DistinctMultidimensionalAngularNodes {d n : ℕ} (Y : Fin n → Fin d → ℝ) : Prop :=
  ∀ i j, i ≠ j → 0 < multidimensionalAngularTorusDistance (Y i) (Y j)

/-- The exact within-clump and between-clump infinity-metric hypotheses. -/
structure MultidimensionalMultiClumpGeometry {d n A : ℕ} (M : ℕ) (c0 C0 : ℝ)
    (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A) : Prop where
  distinct : DistinctMultidimensionalAngularNodes Y
  within : ∀ i j, P.label i = P.label j →
    multidimensionalAngularTorusDistance (Y i) (Y j) ≤ c0 / (M : ℝ)
  between : ∀ i j, P.label i ≠ P.label j →
    C0 / (M : ℝ) ≤ multidimensionalAngularTorusDistance (Y i) (Y j)

/-- The strict separated-clump structure of NumDetect: short nonempty clumps
with attained maximum size and strictly larger cross-clump distances. -/
structure MultidimensionalClumpStructure {d n A : ℕ} (nstar : ℕ) (τ η : ℝ)
    (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A) : Prop where
  width_pos : 0 < τ
  width_le_separation : τ ≤ η
  maximum : HasMaxClumpSize P nstar
  distinct : DistinctMultidimensionalAngularNodes Y
  within : ∀ i j, P.label i = P.label j →
    multidimensionalAngularTorusDistance (Y i) (Y j) ≤ τ
  between : ∀ i j, P.label i ≠ P.label j →
    η < multidimensionalAngularTorusDistance (Y i) (Y j)

theorem MultidimensionalClumpStructure.toGeometry {d n A M nstar : ℕ}
    {τ η c0 C0 : ℝ} {Y : Fin n → Fin d → ℝ} {P : ClumpPartition n A}
    (h : MultidimensionalClumpStructure nstar τ η Y P)
    (hτ : τ ≤ c0 / (M : ℝ)) (hη : C0 / (M : ℝ) ≤ η) :
    MultidimensionalMultiClumpGeometry M c0 C0 Y P :=
  ⟨h.distinct, fun i j hij => (h.within i j hij).trans hτ,
    fun i j hij => hη.trans (h.between i j hij).le⟩

/-- A lower bound for every distinct intraclump periodic one-norm distance.
It makes no assumption on ratios of internal distances or node arrangements. -/
def MultidimensionalClumpL1SpacingLowerBound {d n A : ℕ} (P : ClumpPartition n A)
    (Y : Fin n → Fin d → ℝ) (Δ : ℝ) : Prop :=
  ∀ i j, i ≠ j → P.label i = P.label j →
    Δ ≤ multidimensionalAngularTorusL1Distance (Y i) (Y j)

/-- The corresponding infinity-norm lower spacing condition. -/
def MultidimensionalClumpSpacingLowerBound {d n A : ℕ} (P : ClumpPartition n A)
    (Y : Fin n → Fin d → ℝ) (Δ : ℝ) : Prop :=
  ∀ i j, i ≠ j → P.label i = P.label j →
    Δ ≤ multidimensionalAngularTorusDistance (Y i) (Y j)

theorem multidimensionalClumpSpacingLowerBound_of_l1 {d n A : ℕ} (hd : 1 ≤ d)
    (P : ClumpPartition n A) (Y : Fin n → Fin d → ℝ) {Δ : ℝ}
    (h : MultidimensionalClumpL1SpacingLowerBound P Y Δ) :
    MultidimensionalClumpSpacingLowerBound P Y (Δ / (d : ℝ)) :=
  fun i j hij hlabel => div_dimension_le_multidimensionalAngularTorusDistance hd
    (Y i) (Y j) (h i j hij hlabel)

/-- Internal distances comparable to one common scale, in the angular infinity metric. -/
def ComparableMultidimensionalClumpSpacing {d n A : ℕ} (P : ClumpPartition n A)
    (Y : Fin n → Fin d → ℝ) (Δ K : ℝ) : Prop :=
  ∀ i j, i ≠ j → P.label i = P.label j →
    Δ ≤ multidimensionalAngularTorusDistance (Y i) (Y j) ∧
      multidimensionalAngularTorusDistance (Y i) (Y j) ≤ K * Δ

/-- After removing a clump attaining the maximum, each remaining clump
contains at least one of the remaining sources. -/
theorem hasMaxClumpSize_clumpCount_sub_one_le {n A nstar : ℕ}
    {P : ClumpPartition n A} (hmax : HasMaxClumpSize P nstar) :
    A - 1 ≤ n - nstar := by
  obtain ⟨a, ha⟩ := hmax.2
  have hsum : (∑ b ∈ (Finset.univ : Finset (Fin A)).erase a, P.size b) + P.size a = n :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ a)).trans P.sum_sizes
  have hcount : A - 1 ≤ ∑ b ∈ (Finset.univ : Finset (Fin A)).erase a, P.size b := by
    calc
      A - 1 = ∑ _b ∈ (Finset.univ : Finset (Fin A)).erase a, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun b _ => P.size_pos b
  omega

/-- An attained maximal clump containing all sources is the only clump. -/
theorem hasMaxClumpSize_clumpCount_eq_one_of_total_eq_max {n A nstar : ℕ}
    {P : ClumpPartition n A} (hmax : HasMaxClumpSize P nstar) (hn : n = nstar) :
    A = 1 := by
  have hcount := hasMaxClumpSize_clumpCount_sub_one_le hmax
  obtain ⟨a, _⟩ := hmax.2
  have hA : 0 < A := Nat.zero_lt_of_lt a.isLt
  omega

namespace ClumpPartition

variable {n A : ℕ} (P : ClumpPartition n A)

/-- Size parameter for dimension `d`. -/
def sizePowerSum (d : ℕ) : ℕ := ∑ a : Fin A, P.size a ^ (2 * d)

@[simp] theorem sizePowerSum_one : P.sizePowerSum 1 = P.sizeSquareSum := by
  simp [sizePowerSum, sizeSquareSum]

theorem n_le_sizePowerSum {d : ℕ} (hd : 1 ≤ d) : n ≤ P.sizePowerSum d := by
  calc
    n = ∑ a : Fin A, P.size a := P.sum_sizes.symm
    _ ≤ _ := Finset.sum_le_sum fun a _ => Nat.le_self_pow (by omega) (P.size a)

theorem sizePowerSum_le {d nstar : ℕ} (hd : 1 ≤ d)
    (hsize : ∀ a, P.size a ≤ nstar) : P.sizePowerSum d ≤ n * nstar ^ (2 * d - 1) := by
  calc
    P.sizePowerSum d ≤ ∑ a : Fin A, P.size a * nstar ^ (2 * d - 1) := by
      apply Finset.sum_le_sum
      intro a _
      have heq : P.size a ^ (2 * d) = P.size a * P.size a ^ (2 * d - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [heq]
      exact Nat.mul_le_mul_left (P.size a) (Nat.pow_le_pow_left (hsize a) _)
    _ = n * nstar ^ (2 * d - 1) := by rw [← Finset.sum_mul, P.sum_sizes]

/-- Real representatives of the nodes in one clump, in arbitrary dimension. -/
def multidimensionalNodes {d : ℕ} (Y : Fin n → Fin d → ℝ) (a : Fin A) :
    Fin (P.size a) → Fin d → ℝ := fun j => Y (P.enumeration a j).val

/-- The actual cube-Fourier column span of one clump. -/
def cubeColumnSubspace {d : ℕ} (M : ℕ) (Y : Fin n → Fin d → ℝ) (a : Fin A) :
    Submodule ℂ (EuclideanSpace ℂ (CubeFrequency d M)) :=
  Submodule.span ℂ (Set.range fun j : Fin (P.size a) =>
    toLp 2 (fun k => cubeFourierRow (P.multidimensionalNodes Y a) k j))

end ClumpPartition

/-- The earlier fixed-loss section estimate remains available independently
of the sharp manuscript sampling interface. -/
def multidimensionalMultiClumpTightLeverageConstant (d : ℕ) : ℝ := 2 * 24 ^ d

/-- Sharp section evaluation and adjustable geometric losses give this
absolute leverage coefficient in every positive dimension. -/
def multidimensionalMultiClumpLowerLeverageConstant (_d : ℕ) : ℝ := 3 / 2

/-- Arbitrarily small coordinate losses and near-orthogonal clump energy
give an absolute sampling constant for the lower Chernoff tail. -/
def multidimensionalMultiClumpLowerSamplingConstant (_d : ℕ) : ℝ := 3

theorem multidimensionalMultiClumpLowerSamplingConstant_pos (d : ℕ) :
    0 < multidimensionalMultiClumpLowerSamplingConstant d := by
  unfold multidimensionalMultiClumpLowerSamplingConstant
  positivity

/-- A coordinate loss whose product stays bounded independently of the
ambient dimension. Its smallness is absorbed into the geometry thresholds. -/
def multidimensionalClumpEvaluationLoss (d : ℕ) : ℝ := 1 + 1 / (4 * (d : ℝ))

theorem multidimensionalClumpEvaluationLoss_gt_one {d : ℕ} (hd : 1 ≤ d) :
    1 < multidimensionalClumpEvaluationLoss d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  unfold multidimensionalClumpEvaluationLoss
  have : 0 < 1 / (4 * (d : ℝ)) := by positivity
  linarith

theorem multidimensionalClumpEvaluationLoss_pow_le {d : ℕ} (hd : 1 ≤ d) :
    (multidimensionalClumpEvaluationLoss d)^d ≤ (4 / 3 : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  let y : ℝ := 1 - 1 / (4 * (d : ℝ) + 1)
  have hden : 0 < 4 * (d : ℝ) + 1 := by positivity
  have hr : (d : ℝ) / (4 * (d : ℝ) + 1) ≤ 1 / 4 := by
    apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)).2
    linarith
  have hy : 0 ≤ y := by dsimp [y]; apply sub_nonneg.mpr; apply (div_le_one hden).2; linarith
  have hb := one_add_mul_le_pow (a := -(1 / (4 * (d : ℝ) + 1))) (by
    have : 1 / (4 * (d : ℝ) + 1) ≤ (1 : ℝ) := (div_le_one hden).2 (by linarith)
    linarith) d
  have hylower : (3 / 4 : ℝ) ≤ y^d := by
    dsimp [y]
    have he : (d : ℝ) * -(1 / (4 * (d : ℝ) + 1)) = -(d / (4 * (d : ℝ) + 1)) := by ring
    rw [he] at hb
    simp only [← sub_eq_add_neg] at hb
    linarith only [hb, hr]
  have hx : 0 ≤ multidimensionalClumpEvaluationLoss d :=
    le_trans (by norm_num) (multidimensionalClumpEvaluationLoss_gt_one hd).le
  have hxy : multidimensionalClumpEvaluationLoss d * y = 1 := by
    dsimp [multidimensionalClumpEvaluationLoss, y]
    field_simp
    <;> ring
  have hprod : (multidimensionalClumpEvaluationLoss d)^d * y^d = 1 := by
    rw [← mul_pow, hxy, one_pow]
  have h := mul_le_mul_of_nonneg_left hylower (pow_nonneg hx d)
  nlinarith only [h, hprod]

theorem multidimensionalClumpEvaluationLeverage_le {d : ℕ} (hd : 1 ≤ d)
    {K : ℝ} (hK : 0 ≤ K) :
    (K * multidimensionalClumpEvaluationLoss d)^d / (9 / 10 : ℝ) ≤
      (3 / 2 : ℝ) * K^d := by
  rw [mul_pow]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 9 / 10)).2
  have h := mul_le_mul_of_nonneg_left (multidimensionalClumpEvaluationLoss_pow_le hd)
    (pow_nonneg hK d)
  nlinarith only [h, pow_nonneg hK d]

/-- Tensor-box annihilation exponent for an `nstar`-point clump. -/
def multidimensionalClumpUpperExponent (d nstar : ℕ) : ℕ :=
  Nat.findGreatest (fun q => q ^ d < nstar) (nstar - 1)

@[simp] theorem multidimensionalClumpUpperExponent_one (nstar : ℕ) :
    multidimensionalClumpUpperExponent 1 nstar = nstar - 1 := by
  cases nstar with
  | zero => simp [multidimensionalClumpUpperExponent]
  | succ s =>
    unfold multidimensionalClumpUpperExponent
    exact Nat.findGreatest_eq (by simp)

theorem multidimensionalClumpUpperExponent_pos {d nstar : ℕ}
    (_hd : 1 ≤ d) (hnstar : 2 ≤ nstar) : 0 < multidimensionalClumpUpperExponent d nstar := by
  have h := Nat.le_findGreatest (P := fun q => q ^ d < nstar)
    (show 1 ≤ nstar - 1 by omega) (by simpa using (show 1 < nstar by omega))
  exact lt_of_lt_of_le (by norm_num) h

theorem multidimensionalClumpUpperExponent_power_lt {d nstar : ℕ}
    (_hd : 1 ≤ d) (hnstar : 2 ≤ nstar) :
    multidimensionalClumpUpperExponent d nstar ^ d < nstar := by
  exact Nat.findGreatest_spec (P := fun q => q ^ d < nstar)
    (show 1 ≤ nstar - 1 by omega) (by simpa using (show 1 < nstar by omega))

theorem le_multidimensionalClumpUpperExponent {d nstar q : ℕ}
    (hd : 1 ≤ d) (hq : q ^ d < nstar) : q ≤ multidimensionalClumpUpperExponent d nstar := by
  have hqbound : q ≤ nstar - 1 := by
    have h := Nat.le_self_pow (by omega : d ≠ 0) q
    omega
  exact Nat.le_findGreatest hqbound hq

@[simp] theorem multidimensionalMultiClumpGeometry_one {n A M : ℕ}
    (c0 C0 : ℝ) (Y : Fin n → ℝ) (P : ClumpPartition n A) :
    MultidimensionalMultiClumpGeometry M c0 C0 (fun j (_ : Fin 1) => Y j) P ↔
      MultiClumpGeometry M c0 C0 Y P := by
  constructor
  · intro h
    refine ⟨(distinctAngularNodes_iff_distance_pos Y).2 ?_, ?_, ?_⟩
    · simpa only [DistinctMultidimensionalAngularNodes, multidimensionalAngularTorusDistance_one]
        using h.distinct
    · simpa only [multidimensionalAngularTorusDistance_one] using h.within
    · simpa only [multidimensionalAngularTorusDistance_one] using h.between
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa only [DistinctMultidimensionalAngularNodes, multidimensionalAngularTorusDistance_one]
        using (distinctAngularNodes_iff_distance_pos Y).1 h.distinct
    · simpa only [multidimensionalAngularTorusDistance_one] using h.within
    · simpa only [multidimensionalAngularTorusDistance_one] using h.between

@[simp] theorem comparableMultidimensionalClumpSpacing_one {n A : ℕ}
    (P : ClumpPartition n A) (Y : Fin n → ℝ) (Δ K : ℝ) :
    ComparableMultidimensionalClumpSpacing P (fun j (_ : Fin 1) => Y j) Δ K ↔
      ComparableClumpSpacing P Y Δ K := by
  simp only [ComparableMultidimensionalClumpSpacing, ComparableClumpSpacing,
    multidimensionalAngularTorusDistance_one]

end
end LeanNumDetect.RandSamp
