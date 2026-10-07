import General.Probability.ClippedQuadraticProcesses
import General.Probability.FiniteBernoulliChaining
import General.Probability.FiniteCubeProcessMaxima

/-!
# Normalized clipped mask processes

Each mask is normalized by the square root of its cardinality. Its expected
Bernoulli supremum is consequently independent of the mask size, as is its
bounded-differences variance budget. A finite family of masks then incurs
only a logarithmic cardinality cost in the squared expected maximum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

/-- A coordinate envelope gives the precise single-sign oscillation of an
absolute Bernoulli supremum over an arbitrary bounded class. -/
theorem bernoulliAbsoluteSupremum_coordinateOscillation
    {T : Type*} [Nonempty T] {m : ℕ}
    (z : T → Fin m → ℝ) (B : Fin m → ℝ)
    (hbound : ∀ t i, |z t i| ≤ B i) :
    CoordinateOscillationBound (bernoulliAbsoluteSupremum z) (fun i => 2 * B i) := by
  classical
  have hz : ∀ i, BddAbove (Set.range fun t => |z t i|) := fun i =>
    ⟨B i, by rintro _ ⟨t, rfl⟩; exact hbound t i⟩
  have hd (i : Fin m) (σ τ : Fin m → Bool) (heq : ∀ j, j ≠ i → σ j = τ j) (t : T) :
      |∑ j, finiteBernoulliSign (σ j) * z t j -
        ∑ j, finiteBernoulliSign (τ j) * z t j| ≤ 2 * B i := by
    rw [← Finset.sum_sub_distrib]
    have hid : (∑ j, (finiteBernoulliSign (σ j) * z t j -
        finiteBernoulliSign (τ j) * z t j)) =
          (finiteBernoulliSign (σ i) - finiteBernoulliSign (τ i)) * z t i := by
      rw [Finset.sum_eq_single i]
      · ring
      · intro j _ hji
        rw [heq j hji]
        ring
      · simp
    rw [hid, abs_mul]
    have hs : |finiteBernoulliSign (σ i) - finiteBernoulliSign (τ i)| ≤ 2 := by
      cases σ i <;> cases τ i <;> norm_num [finiteBernoulliSign]
    exact mul_le_mul hs (hbound t i) (abs_nonneg _) (by norm_num)
  have hup (i : Fin m) (σ τ : Fin m → Bool) (heq : ∀ j, j ≠ i → σ j = τ j) :
      bernoulliAbsoluteSupremum z σ ≤ bernoulliAbsoluteSupremum z τ + 2 * B i := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨t, rfl⟩
    dsimp only
    have hdiff := (abs_abs_sub_abs_le_abs_sub
      (∑ j, finiteBernoulliSign (σ j) * z t j)
      (∑ j, finiteBernoulliSign (τ j) * z t j)).trans (hd i σ τ heq t)
    have hτ := le_csSup (bddAbove_range_abs_linear_combination z
      (fun j => finiteBernoulliSign (τ j)) hz) (Set.mem_range_self t)
    change _ ≤ bernoulliAbsoluteSupremum z τ at hτ
    linarith [(abs_le.mp hdiff).2]
  intro i σ τ heq
  apply abs_le.mpr
  constructor
  · have h := hup i τ σ (fun j hj => (heq j hj).symm)
    linarith
  · have h := hup i σ τ heq
    linarith

theorem bernoulliAbsoluteSupremum_nonneg
    {T : Type*} [Nonempty T] {m : ℕ} (z : T → Fin m → ℝ)
    (hbound : ∀ i, BddAbove (Set.range fun t => |z t i|))
    (σ : Fin m → Bool) : 0 ≤ bernoulliAbsoluteSupremum z σ := by
  obtain ⟨t⟩ := ‹Nonempty T›
  exact (abs_nonneg _).trans (le_csSup
    (bddAbove_range_abs_linear_combination z (fun i => finiteBernoulliSign (σ i)) hbound)
    (Set.mem_range_self t))

end LeanNumDetect.FiniteMatrixSampling

namespace LeanNumDetect.BoundedRieszConcentration

open LeanNumDetect.FiniteMatrixSampling

/-- The normalized absolute clipped process associated with one coordinate
mask. The empty mask has value zero. -/
noncomputable def normalizedClippedMaskProcess
    {N m : ℕ} {T : Type*} (f : T → ComplexVector N)
    (rows : Fin m → ComplexVector N) (E : Finset (Fin m)) (R : ℝ)
    (σ : Fin m → Bool) : ℝ :=
  (Real.sqrt (E.card : ℝ))⁻¹ * bernoulliAbsoluteSupremum
    (fun t i => clippedComplexEnergy R
      (rowPairing (f t) (if i ∈ E then rows i else 0))) σ

theorem normalizedClippedMaskProcess_nonneg
    {N m : ℕ} {T : Type*} [Nonempty T] (f : T → ComplexVector N)
    (rows : Fin m → ComplexVector N) (E : Finset (Fin m)) (R : ℝ)
    (σ : Fin m → Bool) : 0 ≤ normalizedClippedMaskProcess f rows E R σ := by
  apply mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply bernoulliAbsoluteSupremum_nonneg
  intro i
  refine ⟨2 * R ^ 2, ?_⟩
  rintro _ ⟨t, rfl⟩
  dsimp only
  rw [abs_of_nonneg (clippedComplexEnergy_nonneg _ _)]
  exact clippedComplexEnergy_le_radius _ _

/-- After cardinality normalization the oscillation square sum is bounded
by `16R⁴`, uniformly over all masks, including the empty one. -/
theorem normalizedClippedMaskProcess_oscillation
    {N m : ℕ} {T : Type*} [Nonempty T] (f : T → ComplexVector N)
    (rows : Fin m → ComplexVector N) (E : Finset (Fin m)) (R : ℝ) :
    ∃ b : Fin m → ℝ, (∀ i, 0 ≤ b i) ∧
      CoordinateOscillationBound (normalizedClippedMaskProcess f rows E R) b ∧
      ∑ i, b i ^ 2 ≤ 16 * R ^ 4 := by
  classical
  let u := (Real.sqrt (E.card : ℝ))⁻¹
  let z := fun t (i : Fin m) => clippedComplexEnergy R
    (rowPairing (f t) (if i ∈ E then rows i else 0))
  let B := fun i : Fin m => if i ∈ E then 2 * R ^ 2 else 0
  let b := fun i : Fin m => u * (2 * B i)
  have hu : 0 ≤ u := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hB : ∀ i, 0 ≤ B i := by intro i; dsimp [B]; split_ifs <;> positivity
  have hb : ∀ i, 0 ≤ b i := fun i => mul_nonneg hu
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hB i))
  have henv : ∀ t i, |z t i| ≤ B i := by
    intro t i
    dsimp [z, B]
    split_ifs with hi
    · rw [abs_of_nonneg (clippedComplexEnergy_nonneg _ _)]
      exact clippedComplexEnergy_le_radius _ _
    · simp [rowPairing]
  have hosc := bernoulliAbsoluteSupremum_coordinateOscillation z B henv
  refine ⟨b, hb, ?_, ?_⟩
  · intro i σ τ heq
    change |u * bernoulliAbsoluteSupremum z σ - u * bernoulliAbsoluteSupremum z τ| ≤ _
    rw [← mul_sub, abs_mul, abs_of_nonneg hu]
    exact mul_le_mul_of_nonneg_left (hosc i σ τ heq) hu
  · have hsum : (∑ i, b i ^ 2) = u ^ 2 * 16 * R ^ 4 * (E.card : ℝ) := by
      calc
        _ = ∑ i : Fin m, if i ∈ E then u ^ 2 * 16 * R ^ 4 else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp [b, B]
          split_ifs <;> ring
        _ = _ := by simp; ring
    rw [hsum]
    by_cases hc : E.card = 0
    · simp only [u, hc, Nat.cast_zero, Real.sqrt_zero, inv_zero, zero_pow (by decide : 2 ≠ 0),
        zero_mul]
      positivity
    · have hcard : (0 : ℝ) < E.card := by exact_mod_cast Nat.pos_of_ne_zero hc
      have hu2 : u ^ 2 * (E.card : ℝ) = 1 := by
        dsimp [u]
        rw [inv_pow, Real.sq_sqrt hcard.le]
        exact inv_mul_cancel₀ hcard.ne'
      have heq : u ^ 2 * 16 * R ^ 4 * (E.card : ℝ) = 16 * R ^ 4 := by
        calc
          _ = (u ^ 2 * (E.card : ℝ)) * (16 * R ^ 4) := by ring
          _ = _ := by rw [hu2, one_mul]
      exact heq.le

/-- Cardinality normalization removes the mask size from the expected
clipped-process bound, including the empty-mask case. -/
theorem normalizedClippedMaskProcess_expectation_le
    {N m : ℕ} (hN : 0 < N) {T : Type*} [Nonempty T]
    (f : T → ComplexVector N) (rows : Fin m → ComplexVector N)
    (E : Finset (Fin m)) {s K R : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hf : ∀ t, coefficientL1Norm (f t) ≤ Real.sqrt s)
    (hrows : ∀ i j, ‖rows i j‖ ≤ K)
    (t₀ : T) (hfzero : f t₀ = 0) :
    finiteAverage (normalizedClippedMaskProcess f rows E R) ≤
      16 * R * Real.sqrt s * Real.sqrt (2 * K ^ 2 * Real.log (2 * (N : ℝ))) := by
  let u := (Real.sqrt (E.card : ℝ))⁻¹
  have hu : 0 ≤ u := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hraw := masked_clipped_energy_expectation_le hN f rows E hK hR hf hrows t₀ hfzero
  have hmean : finiteAverage (normalizedClippedMaskProcess f rows E R) =
      u * finiteAverage (fun σ : Fin m → Bool => sSup (Set.range fun t =>
        |∑ i, finiteBernoulliSign (σ i) * clippedComplexEnergy R
          (rowPairing (f t) (if i ∈ E then rows i else 0))|)) := by
    change finiteAverage (fun σ : Fin m → Bool => u • sSup (Set.range fun t =>
      |∑ i, finiteBernoulliSign (σ i) * clippedComplexEnergy R
        (rowPairing (f t) (if i ∈ E then rows i else 0))|)) = _
    rw [finiteAverage_smul]
    rfl
  rw [hmean]
  by_cases hc : E.card = 0
  · simp only [u, hc, Nat.cast_zero, Real.sqrt_zero, inv_zero, zero_mul]
    positivity
  · have hcard : (0 : ℝ) < E.card := by exact_mod_cast Nat.pos_of_ne_zero hc
    apply (mul_le_mul_of_nonneg_left hraw hu).trans
    have hsqrt : Real.sqrt (2 * ((E.card : ℝ) * K ^ 2) * Real.log (2 * (N : ℝ))) =
        Real.sqrt (E.card : ℝ) * Real.sqrt (2 * K ^ 2 * Real.log (2 * (N : ℝ))) := by
      rw [show 2 * ((E.card : ℝ) * K ^ 2) * Real.log (2 * (N : ℝ)) =
        (E.card : ℝ) * (2 * K ^ 2 * Real.log (2 * (N : ℝ))) by ring,
          Real.sqrt_mul hcard.le]
    rw [hsqrt]
    have hu_cancel : u * Real.sqrt (E.card : ℝ) = 1 :=
      inv_mul_cancel₀ (Real.sqrt_pos.mpr hcard).ne'
    have heq : u * (16 * R * Real.sqrt s *
        (Real.sqrt (E.card : ℝ) * Real.sqrt (2 * K ^ 2 * Real.log (2 * (N : ℝ))))) =
          16 * R * Real.sqrt s * Real.sqrt (2 * K ^ 2 * Real.log (2 * (N : ℝ))) := by
      calc
        _ = (u * Real.sqrt (E.card : ℝ)) *
          (16 * R * Real.sqrt s * Real.sqrt (2 * K ^ 2 * Real.log (2 * (N : ℝ)))) := by ring
        _ = _ := by rw [hu_cancel, one_mul]
    exact heq.le

/-- A finite family of normalized masks has a squared-maximum bound with
one entropy logarithm. The coefficient class remains arbitrary and infinite.
This estimate is used with masks determined by coarse approximation prefixes. -/
theorem normalizedClippedMask_family_square_expectation_le
    {N m : ℕ} (hN : 0 < N) {T J : Type*} [Nonempty T] [Fintype J] [Nonempty J]
    (f : T → ComplexVector N) (rows : Fin m → ComplexVector N)
    (E : J → Finset (Fin m)) {s K R : ℝ} (hK : 0 ≤ K) (hR : 0 < R)
    (hf : ∀ t, coefficientL1Norm (f t) ≤ Real.sqrt s)
    (hrows : ∀ i j, ‖rows i j‖ ≤ K)
    (t₀ : T) (hfzero : f t₀ = 0) :
    finiteAverage (fun σ : Fin m → Bool => finiteProcessAbsoluteMaximum
      (fun j => normalizedClippedMaskProcess f rows (E j) R) σ ^ 2) ≤
      2 * (16 * R * Real.sqrt s * Real.sqrt (2 * K ^ 2 * Real.log (2 * (N : ℝ)))) ^ 2 +
        160 * R ^ 4 * Real.log (2 * (Fintype.card J : ℝ)) := by
  classical
  choose b hb hosc hvariance using fun j => normalizedClippedMaskProcess_oscillation f rows (E j) R
  have hmean (j : J) : |finiteAverage (normalizedClippedMaskProcess f rows (E j) R)| ≤
      16 * R * Real.sqrt s * Real.sqrt (2 * K ^ 2 * Real.log (2 * (N : ℝ))) := by
    have hn : 0 ≤ finiteAverage (normalizedClippedMaskProcess f rows (E j) R) := by
      have h := finiteAverage_mono (fun σ : Fin m → Bool =>
        normalizedClippedMaskProcess_nonneg f rows (E j) R σ)
      simpa only [finiteAverage_const] using h
    rw [abs_of_nonneg hn]
    exact normalizedClippedMaskProcess_expectation_le hN f rows (E j) hK hR.le hf hrows t₀ hfzero
  have hv : ∀ j, ∑ i, b j i ^ 2 ≤ 4 * (4 * R ^ 4) := by
    intro j
    convert hvariance j using 1
    ring
  have h := finiteCube_absoluteMaximum_square_expectation_le
    (fun j => normalizedClippedMaskProcess f rows (E j) R) b hb hosc
    (show 0 < 4 * R ^ 4 by positivity) hmean hv
  convert h using 1
  ring

end LeanNumDetect.BoundedRieszConcentration
