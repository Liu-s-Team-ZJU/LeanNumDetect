import General.Probability.FiniteBernoulliProcess
import Mathlib.Data.Finset.Max

/-!
# Causal weak-shell energy decomposition

The shell of a row is its first coarse threshold crossing. Only approximants
up to that crossing enter its label. On the common good set, dyadic coarse
errors control the true amplitude; separable clipping then preserves the
true energy exactly. Exceptional rows retain an explicit additive error.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace LeanNumDetect.WeakShellDecomposition

/-- First-crossing specification; `none` means no coarse threshold crossed. -/
def CrossingSpec {ℓ : ℕ} (r : Fin ℓ → ℝ) (a : Fin ℓ → ℂ)
    (level : Option (Fin ℓ)) : Prop := match level with
  | none => ∀ k, ‖a k‖ < r k
  | some k => r k ≤ ‖a k‖ ∧ ∀ j, j < k → ‖a j‖ < r j

theorem exists_first_crossing {ℓ : ℕ} (r : Fin ℓ → ℝ) (a : Fin ℓ → ℂ) :
    ∃ level, CrossingSpec r a level := by
  classical
  let S := Finset.univ.filter (fun k => r k ≤ ‖a k‖)
  by_cases hS : S.Nonempty
  · let k := S.min' hS
    refine ⟨some k, ?_⟩
    constructor
    · exact (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
    · intro j hj
      by_contra h
      have hmem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt h⟩
      have hmin := Finset.min'_le S j hmem
      exact (not_le_of_gt hj) hmin
  · refine ⟨none, ?_⟩
    intro k
    by_contra h
    exact hS ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt h⟩⟩

/-- Separable clipping permits scalar Bernoulli contraction twice. -/
def clippedEnergy (B : ℝ) (z : ℂ) : ℝ :=
  min (z.re ^ 2) B + min (z.im ^ 2) B

theorem clippedEnergy_nonneg {B : ℝ} (hB : 0 ≤ B) (z : ℂ) :
    0 ≤ clippedEnergy B z := add_nonneg
      (le_min (sq_nonneg _) hB) (le_min (sq_nonneg _) hB)

theorem clippedEnergy_le (B : ℝ) (z : ℂ) : clippedEnergy B z ≤ ‖z‖ ^ 2 := by
  have hz := Complex.sq_norm z
  rw [Complex.normSq_apply] at hz
  simp only [← pow_two] at hz
  exact (add_le_add (min_le_left _ _) (min_le_left _ _)).trans_eq hz.symm

theorem clippedEnergy_eq {B : ℝ} (z : ℂ) (h : ‖z‖ ^ 2 ≤ B) :
    clippedEnergy B z = ‖z‖ ^ 2 := by
  have hz := Complex.sq_norm z
  rw [Complex.normSq_apply] at hz
  simp only [← pow_two] at hz
  have hr : z.re ^ 2 ≤ B := by nlinarith [sq_nonneg z.im]
  have hi : z.im ^ 2 ≤ B := by nlinarith [sq_nonneg z.re]
  simp only [clippedEnergy, min_eq_left hr, min_eq_left hi]
  exact hz.symm

/-- Only the selected shell contributes an energy or a radius weight. -/
def shellEnergy {ℓ : ℕ} (r : Fin ℓ → ℝ) (z : ℂ) : Option (Fin ℓ) → ℝ
  | none => 0
  | some k => clippedEnergy (16 * r k ^ 2) z

def shellWeight {ℓ : ℕ} (r : Fin ℓ → ℝ) : Option (Fin ℓ) → ℝ
  | none => 0
  | some k => r k ^ 2

theorem shellEnergy_nonneg {ℓ : ℕ} (r : Fin ℓ → ℝ) (z : ℂ) (level) :
    0 ≤ shellEnergy r z level := by
  cases level with
  | none => exact le_refl _
  | some k => exact clippedEnergy_nonneg (by positivity) z

theorem shellEnergy_le {ℓ : ℕ} (r : Fin ℓ → ℝ) (z : ℂ) (level) :
    shellEnergy r z level ≤ ‖z‖ ^ 2 := by
  cases level with
  | none => exact sq_nonneg _
  | some k => exact clippedEnergy_le _ z

/-- Dyadic first-crossing amplitudes lie between `3r/4` and `5r/2`. -/
theorem crossing_amplitude_bounds {ℓ : ℕ} (hℓ : 0 < ℓ)
    (r : Fin ℓ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hstep : ∀ k : Fin ℓ, ∀ hk : 0 < k.val,
      r ⟨k.val - 1, by omega⟩ = 2 * r k)
    (a : Fin ℓ → ℂ) (z : ℂ) (hz : ‖z‖ ≤ r ⟨0, hℓ⟩)
    (hgood : ∀ j, ‖a j - z‖ ≤ r j / 4) (k : Fin ℓ)
    (hcross : CrossingSpec r a (some k)) :
    3 * r k / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 5 * r k / 2 := by
  have hlow := norm_le_norm_add_norm_sub z (a k)
  rw [norm_sub_rev z (a k)] at hlow
  constructor
  · nlinarith [hcross.1, hgood k]
  · by_cases hk : k.val = 0
    · have heq : k = ⟨0, hℓ⟩ := Fin.ext hk
      rw [heq]
      nlinarith [hr ⟨0, hℓ⟩]
    · have hk0 : 0 < k.val := by omega
      let j : Fin ℓ := ⟨k.val - 1, by omega⟩
      have hj : j < k := by show j.val < k.val; dsimp [j]; omega
      have ha := hcross.2 j hj
      have hg := hgood j
      have hn := norm_le_norm_add_norm_sub (a j) z
      have heq : r j = 2 * r k := hstep k hk0
      nlinarith

theorem selected_shell_exact {ℓ : ℕ} (hℓ : 0 < ℓ)
    (r : Fin ℓ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hstep : ∀ k : Fin ℓ, ∀ hk : 0 < k.val,
      r ⟨k.val - 1, by omega⟩ = 2 * r k)
    (a : Fin ℓ → ℂ) (z : ℂ) (hz : ‖z‖ ≤ r ⟨0, hℓ⟩)
    (hgood : ∀ j, ‖a j - z‖ ≤ r j / 4) (k : Fin ℓ)
    (hcross : CrossingSpec r a (some k)) :
    shellEnergy r z (some k) = ‖z‖ ^ 2 ∧
      shellWeight r (some k) ≤ (16 / 9 : ℝ) * ‖z‖ ^ 2 := by
  obtain ⟨hlow, hhigh⟩ := crossing_amplitude_bounds hℓ r hr hstep a z hz hgood k hcross
  have hrk := hr k
  have hsquared := pow_le_pow_left₀ (norm_nonneg z) hhigh 2
  have hloSquared := pow_le_pow_left₀ (by positivity : 0 ≤ 3 * r k / 4) hlow 2
  constructor
  · apply clippedEnergy_eq
    nlinarith [sq_nonneg (r k)]
  · dsimp [shellWeight]
    nlinarith

theorem unselected_shell_error {ℓ : ℕ} (hℓ : 0 < ℓ)
    (r : Fin ℓ → ℝ) (_hr : ∀ k, 0 ≤ r k)
    (a : Fin ℓ → ℂ) (z : ℂ)
    (hgood : ∀ j, ‖a j - z‖ ≤ r j / 4)
    (hcross : CrossingSpec r a none) :
    ‖z‖ ^ 2 - shellEnergy r z none ≤ 2 * r ⟨ℓ - 1, by omega⟩ ^ 2 := by
  let j : Fin ℓ := ⟨ℓ - 1, by omega⟩
  have ha := hcross j
  have hg := hgood j
  have hn := norm_le_norm_add_norm_sub (a j) z
  have hle : ‖z‖ ≤ 5 * r j / 4 := by nlinarith
  have hsq := pow_le_pow_left₀ (norm_nonneg z) hle 2
  dsimp [shellEnergy]
  nlinarith [sq_nonneg (r j)]

/-- Exceptional rows are accounted for explicitly; no good-set restriction
is dropped in the residual or shell-energy comparison. -/
theorem shell_residual_and_weight_bounds {κ : Type*} [Fintype κ]
    {ℓ : ℕ} (hℓ : 0 < ℓ) (r : Fin ℓ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hstep : ∀ k : Fin ℓ, ∀ hk : 0 < k.val,
      r ⟨k.val - 1, by omega⟩ = 2 * r k)
    (a : κ → Fin ℓ → ℂ) (z : κ → ℂ) (level : κ → Option (Fin ℓ))
    (hspec : ∀ i, CrossingSpec r (a i) (level i))
    (B : Finset κ) {p : ℝ} (hp : 0 ≤ p) (henergy : ∀ i, ‖z i‖ ^ 2 ≤ p)
    (hweight : ∀ k, r k ^ 2 ≤ p) (hfirst : ∀ i, ‖z i‖ ≤ r ⟨0, hℓ⟩)
    (hgood : ∀ i, i ∉ B → ∀ k, ‖a i k - z i‖ ≤ r k / 4) :
    (∑ i, (‖z i‖ ^ 2 - shellEnergy r (z i) (level i))) ≤
        p * (B.card : ℝ) + 2 * (Fintype.card κ : ℝ) * r ⟨ℓ - 1, by omega⟩ ^ 2 ∧
    (∑ i, shellWeight r (level i)) ≤
        (16 / 9 : ℝ) * (∑ i, ‖z i‖ ^ 2) + p * (B.card : ℝ) := by
  classical
  have hsum : (∑ i : κ, if i ∈ B then p else 0) = p * (B.card : ℝ) := by
    simp [Finset.sum_ite_mem, mul_comm]
  have hres (i : κ) : ‖z i‖ ^ 2 - shellEnergy r (z i) (level i) ≤
      (if i ∈ B then p else 0) + 2 * r ⟨ℓ - 1, by omega⟩ ^ 2 := by
    by_cases hi : i ∈ B
    · simp only [if_pos hi]
      have h0 := shellEnergy_nonneg r (z i) (level i)
      nlinarith [henergy i, sq_nonneg (r ⟨ℓ - 1, by omega⟩)]
    · simp only [if_neg hi, zero_add]
      cases hli : level i with
      | none =>
          exact unselected_shell_error hℓ r hr (a i) (z i) (hgood i hi)
            (by simpa [hli] using hspec i)
      | some k =>
        have h := selected_shell_exact hℓ r hr hstep (a i) (z i) (hfirst i) (hgood i hi) k
          (by simpa [hli] using hspec i)
        simpa only [h.1, sub_self] using
          (show 0 ≤ 2 * r ⟨ℓ - 1, by omega⟩ ^ 2 by positivity)
  have hw (i : κ) : shellWeight r (level i) ≤
      (16 / 9 : ℝ) * ‖z i‖ ^ 2 + (if i ∈ B then p else 0) := by
    by_cases hi : i ∈ B
    · simp only [if_pos hi]
      cases hli : level i with
      | none => dsimp [shellWeight]; positivity
      | some k => exact (hweight k).trans (le_add_of_nonneg_left (by positivity))
    · simp only [if_neg hi, add_zero]
      cases hli : level i with
      | none => dsimp [shellWeight]; positivity
      | some k => exact (selected_shell_exact hℓ r hr hstep (a i) (z i)
          (hfirst i) (hgood i hi) k (by simpa [hli] using hspec i)).2
  constructor
  · have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hres i)
    simp only [Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at h
    convert h using 1 <;> first | rfl | ring
  · have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hw i)
    simpa only [Finset.sum_add_distrib, hsum, ← Finset.mul_sum] using h

end LeanNumDetect.WeakShellDecomposition
