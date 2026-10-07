import General.Probability.CausalShellProcesses
import General.Probability.CausalShellParameters

/-!
# Constructing causal weak atomic shells

Atomic words are selected at each dyadic scale by the proved weak-net
estimate. Their first-crossing masks are members of the canonical prefix
families. The common exceptional set is kept explicitly in the shell error
and mass budgets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace LeanNumDetect.BoundedRieszConcentration

open LeanNumDetect.FiniteMatrixSampling LeanNumDetect.WeakShellDecomposition

/-- Embedding the prefix through level `k` into the full scale family. -/
def prefixLevelEmbedding {ℓ : ℕ} (k : Fin ℓ) (j : Fin (k.val + 1)) : Fin ℓ :=
  ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩

@[simp] theorem prefixLevelEmbedding_val {ℓ : ℕ} (k : Fin ℓ) (j : Fin (k.val + 1)) :
    (prefixLevelEmbedding k j).val = j.val := rfl

@[simp] theorem prefixLevelEmbedding_last {ℓ : ℕ} (k : Fin ℓ) :
    prefixLevelEmbedding k (Fin.last k.val) = k := Fin.ext rfl

/-- Weak-net atomic words can be selected simultaneously at all scales,
with the same exceptional-row count at every dyadic scale. -/
theorem exists_dyadic_weakAtomicWords
    {N m ℓ : ℕ} {T : Type*} (f : T → ComplexVector N)
    (rows : Fin m → ComplexVector N) {s K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hf : ∀ t, coefficientL1Norm (f t) ≤ Real.sqrt s)
    (hrows : ∀ i j, ‖rows i j‖ ≤ K) {L₀ : ℕ} (hL₀ : 0 < L₀)
    (r : Fin ℓ → ℝ) (hr : ∀ k, 0 < r k)
    (hscale : ∀ k, r k ^ 2 * (4 : ℝ) ^ k.val = s * K ^ 2) :
    ∃ w : ∀ _ : T, ∀ k : Fin ℓ, ComplexAtomicWord N (L₀ * 4 ^ k.val),
      ∀ t k, ((Finset.univ.filter fun i => r k / 4 <
        ‖rowPairing (complexAtomicAverage (2 * Real.sqrt s) (w t k)) (rows i) -
          rowPairing (f t) (rows i)‖).card : ℝ) ≤
          4 * (m : ℝ) * Real.exp (-(L₀ : ℝ) / 512) := by
  classical
  have hex (t : T) (k : Fin ℓ) : ∃ w : ComplexAtomicWord N (L₀ * 4 ^ k.val),
      ((Finset.univ.filter fun i => r k / 4 <
        ‖rowPairing (complexAtomicAverage (2 * Real.sqrt s) w) (rows i) -
          rowPairing (f t) (rows i)‖).card : ℝ) ≤
          4 * (m : ℝ) * Real.exp (-(L₀ : ℝ) / 512) := by
    obtain ⟨w, hw⟩ := complexL1Ball_weakAtomicWord (s := s) (K := K) (r := r k / 4) rows hs hK
      (by have h := hr k; positivity) hrows
      (Nat.mul_pos hL₀ (pow_pos (by norm_num : 0 < (4 : ℕ)) _)) (f t) (hf t)
    refine ⟨w, ?_⟩
    have hnorm (i : Fin m) : ‖rowPairing (f t - complexAtomicAverage (2 * Real.sqrt s) w)
        (rows i)‖ = ‖rowPairing (complexAtomicAverage (2 * Real.sqrt s) w) (rows i) -
          rowPairing (f t) (rows i)‖ := by rw [rowPairing_sub_left, norm_sub_rev]
    have heq : ((L₀ * 4 ^ k.val : ℕ) : ℝ) * (r k / 4) ^ 2 / (32 * s * K ^ 2) =
        (L₀ : ℝ) / 512 := by
      rw [Nat.cast_mul, Nat.cast_pow]
      norm_num only [Nat.cast_ofNat]
      calc
        _ = ((L₀ : ℝ) / 16) * (r k ^ 2 * (4 : ℝ) ^ k.val) / (32 * s * K ^ 2) := by ring
        _ = ((L₀ : ℝ) / 16) * (s * K ^ 2) / (32 * s * K ^ 2) := by rw [hscale]
        _ = _ := by field_simp; ring
    simp_rw [hnorm] at hw
    simpa only [heq, Fintype.card_fin, neg_div] using hw
  choose w hw using hex
  exact ⟨w, hw⟩

/-- A canonical prefix determines the full first-crossing mask at its final
level. No approximant beyond that level occurs in this identity. -/
theorem atomicPrefixMask_eq_crossingMask
    {N m ℓ L₀ : ℕ} (rows : Fin m → ComplexVector N) (R : ℝ) (r : Fin ℓ → ℝ)
    (w : ∀ k : Fin ℓ, ComplexAtomicWord N (L₀ * 4 ^ k.val))
    (level : Fin m → Option (Fin ℓ))
    (hspec : ∀ i, CrossingSpec r
      (fun k => rowPairing (complexAtomicAverage R (w k)) (rows i)) (level i))
    (k : Fin ℓ) :
    prefixFirstCrossingMask (fun j : Fin (k.val + 1) => L₀ * 4 ^ j.val)
      (fun j => r (prefixLevelEmbedding k j))
      (fun _ word i => rowPairing (complexAtomicAverage R word) (rows i))
      (fun j => w (prefixLevelEmbedding k j)) =
        Finset.univ.filter (fun i => level i = some k) := by
  classical
  ext i
  simp only [prefixFirstCrossingMask, Finset.mem_filter, Finset.mem_univ, true_and,
    prefixLevelEmbedding_last]
  rw [CrossingSpec_eq_some_iff r _ (hspec i) k]
  constructor
  · rintro ⟨hcross, hbefore⟩
    refine ⟨hcross, ?_⟩
    intro j hj
    let j' : Fin (k.val + 1) := ⟨j.val, by have h := hj; change j.val < k.val at h; omega⟩
    have heq : prefixLevelEmbedding k j' = j := Fin.ext rfl
    have hbefore' := hbefore j' (by change j'.val < k.val; exact hj)
    have havg := congrArg (fun k => complexAtomicAverage R (w k)) heq
    rw [havg, heq] at hbefore'
    exact hbefore'
  · rintro ⟨hcross, hbefore⟩
    refine ⟨hcross, ?_⟩
    intro j hj
    exact hbefore (prefixLevelEmbedding k j) (by exact hj)

/-- The exact normalized-mask budget at one scale is controlled by the
causal-prefix entropy at that scale. -/
theorem dyadic_mask_level_budget_le {N L₀ k : ℕ} (hN : 0 < N)
    {s K q : ℝ} (hs : 0 ≤ s) (hq : 0 < q)
    (hscale : q ^ 2 * (4 : ℝ) ^ k = s * K ^ 2) :
    (2 * (16 * (4 * q) * Real.sqrt s *
        Real.sqrt (2 * K ^ 2 * Real.log (2 * (N : ℝ)))) ^ 2 +
      160 * (4 * q) ^ 4 * Real.log (2 * (Fintype.card
        (ComplexAtomicPrefix N (fun j : Fin (k + 1) => L₀ * 4 ^ j.val)) : ℝ))) / q ^ 2 ≤
      (s * K ^ 2) * (16384 * Real.log (2 * (N : ℝ)) + 40960 * Real.log 2 +
        81920 * (L₀ : ℝ) * Real.log (4 * (N : ℝ) + 1)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by linarith)
  have ht : 0 ≤ 2 * K ^ 2 * Real.log (2 * (N : ℝ)) := by positivity
  have hsqrt := Real.sq_sqrt hs
  have hsqrt' := Real.sq_sqrt ht
  have hid : (2 * (16 * (4 * q) * Real.sqrt s *
      Real.sqrt (2 * K ^ 2 * Real.log (2 * (N : ℝ)))) ^ 2 +
        160 * (4 * q) ^ 4 * Real.log (2 * (Fintype.card
          (ComplexAtomicPrefix N (fun j : Fin (k + 1) => L₀ * 4 ^ j.val)) : ℝ))) / q ^ 2 =
      16384 * (s * K ^ 2) * Real.log (2 * (N : ℝ)) +
        40960 * q ^ 2 * Real.log (2 * (Fintype.card
          (ComplexAtomicPrefix N (fun j : Fin (k + 1) => L₀ * 4 ^ j.val)) : ℝ)) := by
    simp only [mul_pow, hsqrt, hsqrt']
    field_simp
    ring
  have hpw : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have hqbound : q ^ 2 ≤ s * K ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hpw)]
  have hprefix := geometricPrefix_log_card_le N L₀ k
  have he : q ^ 2 * Real.log (2 * (Fintype.card
      (ComplexAtomicPrefix N (fun j : Fin (k + 1) => L₀ * 4 ^ j.val)) : ℝ)) ≤
        (s * K ^ 2) * Real.log 2 +
          2 * (L₀ : ℝ) * (s * K ^ 2) * Real.log (4 * (N : ℝ) + 1) := by
    calc
      _ ≤ q ^ 2 * (Real.log 2 + 2 * (L₀ : ℝ) * 4 ^ k * Real.log (4 * (N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hprefix (sq_nonneg q)
      _ = q ^ 2 * Real.log 2 +
          2 * (L₀ : ℝ) * (q ^ 2 * 4 ^ k) * Real.log (4 * (N : ℝ) + 1) := by ring
      _ = q ^ 2 * Real.log 2 +
          2 * (L₀ : ℝ) * (s * K ^ 2) * Real.log (4 * (N : ℝ) + 1) := by rw [hscale]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hqbound
        (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))) le_rfl
  rw [hid]
  nlinarith [mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 40960)]

/-- Fully constructed weak atomic shells give the sharp deterministic
Bernoulli expectation estimate. All approximation choices, exceptional
sets, and causal prefix masks are constructed in the proof. The scale
parameters are explicit, permitting separate numerical optimization. -/
theorem dyadic_weakShell_energy_expectation_le
    {N m ℓ L₀ : ℕ} (hN : 0 < N) (hℓ : 0 < ℓ) (hL₀ : 0 < L₀)
    {T : Type*} [Nonempty T] (f : T → ComplexVector N)
    (rows : Fin m → ComplexVector N) {s K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hf : ∀ t, coefficientL1Norm (f t) ≤ Real.sqrt s)
    (hrows : ∀ i j, ‖rows i j‖ ≤ K) (t₀ : T) (hfzero : f t₀ = 0)
    (r : Fin ℓ → ℝ) (hr : ∀ k, 0 < r k)
    (hscale : ∀ k, r k ^ 2 * (4 : ℝ) ^ k.val = s * K ^ 2)
    (hstep : ∀ k : Fin ℓ, ∀ hk : 0 < k.val,
      r ⟨k.val - 1, by omega⟩ = 2 * r k) :
    let p := s * K ^ 2
    let B := 4 * p * (m : ℝ) * (ℓ : ℝ) * Real.exp (-(L₀ : ℝ) / 512)
    let Q := sSup (Set.range fun t => ∑ i, rowEnergy (f t) (rows i))
    finiteAverage (bernoulliAbsoluteSupremum (fun t i => rowEnergy (f t) (rows i))) ≤
      B + 2 * (m : ℝ) * r ⟨ℓ - 1, by omega⟩ ^ 2 +
        Real.sqrt ((16 / 9 : ℝ) * Q + B) * Real.sqrt ((ℓ : ℝ) * p *
          (16384 * Real.log (2 * (N : ℝ)) + 40960 * Real.log 2 +
            81920 * (L₀ : ℝ) * Real.log (4 * (N : ℝ) + 1))) := by
  classical
  let p := s * K ^ 2
  let β := 4 * p * (m : ℝ) * (ℓ : ℝ) * Real.exp (-(L₀ : ℝ) / 512)
  let Q := sSup (Set.range fun t => ∑ i, rowEnergy (f t) (rows i))
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have henergy (t : T) (i : Fin m) : ‖rowPairing (f t) (rows i)‖ ^ 2 ≤ p :=
    rowEnergy_le_radius (f t) (rows i) hs.le hK.le (hf t) (hrows i)
  have hQbdd : BddAbove (Set.range fun t => ∑ i, rowEnergy (f t) (rows i)) := by
    refine ⟨(m : ℝ) * p, ?_⟩
    rintro _ ⟨t, rfl⟩
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => henergy t i)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, rowEnergy] using h
  have hQ (t : T) : ∑ i, rowEnergy (f t) (rows i) ≤ Q :=
    le_csSup hQbdd (Set.mem_range_self t)
  obtain ⟨w, hw⟩ := exists_dyadic_weakAtomicWords f rows hs hK hf hrows hL₀ r hr hscale
  let a := fun t i k => rowPairing (complexAtomicAverage (2 * Real.sqrt s) (w t k)) (rows i)
  let z := fun t i => rowPairing (f t) (rows i)
  choose level hspec using fun t i => exists_first_crossing r (a t i)
  let B := fun t => Finset.univ.biUnion fun k =>
    Finset.univ.filter (fun i => r k / 4 < ‖a t i k - z t i‖)
  have hBcard (t : T) : ((B t).card : ℝ) ≤
      (ℓ : ℝ) * (4 * (m : ℝ) * Real.exp (-(L₀ : ℝ) / 512)) := by
    have hnat := Finset.card_biUnion_le (s := Finset.univ)
      (t := fun k => Finset.univ.filter (fun i => r k / 4 < ‖a t i k - z t i‖))
    calc
      _ ≤ ∑ k, ((Finset.univ.filter (fun i => r k / 4 < ‖a t i k - z t i‖)).card : ℝ) := by
        exact_mod_cast hnat
      _ ≤ ∑ _ : Fin ℓ, 4 * (m : ℝ) * Real.exp (-(L₀ : ℝ) / 512) :=
        Finset.sum_le_sum fun k _ => hw t k
      _ = _ := by simp
  have hbad (t : T) : p * ((B t).card : ℝ) ≤ β := by
    apply (mul_le_mul_of_nonneg_left (hBcard t) hp).trans_eq
    dsimp [β]
    ring
  have hgood (t : T) (i : Fin m) (hi : i ∉ B t) (k : Fin ℓ) :
      ‖a t i k - z t i‖ ≤ r k / 4 := by
    apply le_of_not_gt
    intro h
    apply hi
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  have hrweight (k : Fin ℓ) : r k ^ 2 ≤ p := by
    have hpw : (1 : ℝ) ≤ 4 ^ k.val := one_le_pow₀ (by norm_num)
    nlinarith [hscale k, mul_nonneg (sq_nonneg (r k)) (sub_nonneg.mpr hpw)]
  have hfirst (t : T) (i : Fin m) : ‖z t i‖ ≤ r ⟨0, hℓ⟩ := by
    have hsq := hscale ⟨0, hℓ⟩
    simp only [pow_zero, mul_one] at hsq
    have hn := henergy t i
    have hr0 := hr ⟨0, hℓ⟩
    nlinarith [norm_nonneg (z t i)]
  have hshell (t : T) := shell_residual_and_weight_bounds hℓ r (fun k => (hr k).le) hstep
    (a t) (z t) (level t) (hspec t) (B t) hp (henergy t) hrweight (hfirst t) (hgood t)
  let J := fun k : Fin ℓ => ComplexAtomicPrefix N (fun j : Fin (k.val + 1) => L₀ * 4 ^ j.val)
  letI : ∀ k, Fintype (J k) := fun k => by dsimp [J]; infer_instance
  letI : ∀ k, Nonempty (J k) := fun k => by dsimp [J]; infer_instance
  let E := fun k : Fin ℓ => prefixFirstCrossingMask
    (fun j : Fin (k.val + 1) => L₀ * 4 ^ j.val) (fun j => r (prefixLevelEmbedding k j))
    (fun _ word i => rowPairing (complexAtomicAverage (2 * Real.sqrt s) word) (rows i))
  let choose := fun k t j => w t (prefixLevelEmbedding k j)
  have hmask (k : Fin ℓ) (t : T) : E k (choose k t) =
      Finset.univ.filter (fun i => level t i = some k) :=
    atomicPrefixMask_eq_crossingMask rows (2 * Real.sqrt s) r (w t) (level t) (hspec t) k
  have hresidual (t : T) : ∑ i, (rowEnergy (f t) (rows i) -
      shellEnergy r (z t i) (level t i)) ≤ β + 2 * (m : ℝ) * r ⟨ℓ - 1, by omega⟩ ^ 2 := by
    apply (hshell t).1.trans
    simpa only [Fintype.card_fin] using add_le_add (hbad t) le_rfl
  have hweight (t : T) : ∑ i, shellWeight r (level t i) ≤ (16 / 9 : ℝ) * Q + β := by
    apply (hshell t).2.trans
    exact add_le_add (mul_le_mul_of_nonneg_left (hQ t) (by norm_num)) (hbad t)
  have h := causal_shell_energy_expectation_le (J := J) hN f rows E choose r hr level hmask
    hK.le hf hrows t₀ hfzero hresidual hweight
  apply h.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  have hb := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) =>
    dyadic_mask_level_budget_le (N := N) (L₀ := L₀) (k := k.val) hN hs.le (hr k) (hscale k))
  simpa only [J, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc] using hb

/-- Positive dyadic amplitude radii used by the causal shell construction. -/
noncomputable def causalShellRadius (p : ℝ) {ℓ : ℕ} (k : Fin ℓ) : ℝ :=
  Real.sqrt p / (2 : ℝ) ^ k.val

theorem causalShellRadius_pos {p : ℝ} (hp : 0 < p) {ℓ : ℕ} (k : Fin ℓ) :
    0 < causalShellRadius p k := by unfold causalShellRadius; positivity

theorem causalShellRadius_scale {p : ℝ} (hp : 0 ≤ p) {ℓ : ℕ} (k : Fin ℓ) :
    causalShellRadius p k ^ 2 * (4 : ℝ) ^ k.val = p := by
  unfold causalShellRadius
  have heq : ((2 : ℝ) ^ k.val) ^ 2 = (4 : ℝ) ^ k.val := by
    rw [pow_two, ← mul_pow]
    norm_num
  rw [div_pow, Real.sq_sqrt hp, heq, div_mul_cancel₀ _ (by positivity)]

theorem causalShellRadius_square {p : ℝ} (hp : 0 ≤ p) {ℓ : ℕ} (k : Fin ℓ) :
    causalShellRadius p k ^ 2 = p / (4 : ℝ) ^ k.val := by
  exact (eq_div_iff (by positivity : (4 : ℝ) ^ k.val ≠ 0)).mpr (causalShellRadius_scale hp k)

theorem causalShellRadius_step (p : ℝ) {ℓ : ℕ} (k : Fin ℓ) (hk : 0 < k.val) :
    causalShellRadius p (ℓ := ℓ) ⟨k.val - 1, by omega⟩ = 2 * causalShellRadius p k := by
  have hpw : (2 : ℝ) ^ k.val = (2 : ℝ) ^ (k.val - 1) * 2 := by
    conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ k.val by omega)]
    rw [pow_succ]
  unfold causalShellRadius
  simp only [hpw]
  field_simp

/-- With explicit logarithmic shell parameters, the constructed Bernoulli
process bound retains exactly the source's squared logarithmic rate. -/
theorem boundedRows_bernoulli_expectation_le
    {N m : ℕ} (hN : 0 < N) {T : Type*} [Nonempty T]
    (f : T → ComplexVector N) (rows : Fin m → ComplexVector N)
    {s K δ : ℝ} (hs : 0 < s) (hK : 0 < K) (hδ : 0 < δ)
    (hpδ : 4 * δ ≤ s * K ^ 2)
    (hf : ∀ t, coefficientL1Norm (f t) ≤ Real.sqrt s)
    (hrows : ∀ i j, ‖rows i j‖ ≤ K) (t₀ : T) (hfzero : f t₀ = 0) :
    let p := s * K ^ 2
    let Q := sSup (Set.range fun t => ∑ i, rowEnergy (f t) (rows i))
    finiteAverage (bernoulliAbsoluteSupremum (fun t i => rowEnergy (f t) (rows i))) ≤
      3 * δ * (m : ℝ) + Real.sqrt ((16 / 9 : ℝ) * Q + δ * (m : ℝ)) *
        Real.sqrt (10000000000 * p * Real.log (Real.exp 1 * (N : ℝ)) * Real.log (p / δ) ^ 2) := by
  let p := s * K ^ 2
  have hp : 0 < p := by dsimp [p]; positivity
  let ℓ := shellLevelCount p δ
  let L₀ := shellWordBaseLength p δ
  let r := causalShellRadius p (ℓ := ℓ)
  have hℓ : 0 < ℓ := shellLevelCount_pos p δ
  have hL₀ : 0 < L₀ := shellWordBaseLength_pos hδ hpδ
  have hr : ∀ k, 0 < r k := causalShellRadius_pos hp
  have hscale : ∀ k, r k ^ 2 * (4 : ℝ) ^ k.val = s * K ^ 2 := causalShellRadius_scale hp.le
  have h := dyadic_weakShell_energy_expectation_le hN hℓ hL₀ f rows hs hK hf hrows
    t₀ hfzero r hr hscale (causalShellRadius_step p)
  apply h.trans
  have hbad := shell_bad_budget_le hδ hpδ (Nat.cast_nonneg (α := ℝ) m)
  have hlast : r ⟨ℓ - 1, by omega⟩ ^ 2 ≤ δ := by
    rw [causalShellRadius_square hp.le]
    exact shell_last_radius_sq_le hδ hpδ
  have hε : 4 * p * (m : ℝ) * (ℓ : ℝ) * Real.exp (-(L₀ : ℝ) / 512) +
      2 * (m : ℝ) * r ⟨ℓ - 1, by omega⟩ ^ 2 ≤ 3 * δ * (m : ℝ) := by
    have hlast' := mul_le_mul_of_nonneg_left hlast (show 0 ≤ 2 * (m : ℝ) by positivity)
    nlinarith
  apply add_le_add hε
  apply mul_le_mul
  · exact Real.sqrt_le_sqrt (add_le_add le_rfl hbad)
  · exact Real.sqrt_le_sqrt (shell_total_budget_le hN hδ hpδ)
  · exact Real.sqrt_nonneg _
  · exact Real.sqrt_nonneg _

end LeanNumDetect.BoundedRieszConcentration
