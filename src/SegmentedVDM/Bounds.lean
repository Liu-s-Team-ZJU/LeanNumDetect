import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Finite products and bandwidth arithmetic for the segmented VDM proof.
The products stay inside one clump; no cardinality assertion about a global
distance-threshold neighborhood is used. -/

set_option autoImplicit false
open scoped BigOperators

namespace SegmentedVDM

/-- Replace each close-neighbor factor by the minimum separation, then enlarge
the exponent to the clump size bound. The empty product is included. -/
theorem local_product_lower {ι : Type*} (J : Finset ι) {s : ℕ}
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hcard : J.card ≤ s - 1)
    (f : ι → ℝ) (hf : ∀ j ∈ J, a ≤ f j) :
    a ^ (s - 1) ≤ ∏ j ∈ J, f j := by
  calc
    a ^ (s - 1) ≤ a ^ J.card := pow_le_pow_of_le_one ha ha1 hcard
    _ = ∏ _j ∈ J, a := (Finset.prod_const _).symm
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => ha) hf

/-- A thresholded reciprocal product has at most one factor for each other
node of the clump. No nodes outside that clump are inserted. -/
theorem local_reciprocal_product_upper {ι : Type*} (J : Finset ι) {s : ℕ}
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hcard : J.card ≤ s - 1)
    (f : ι → ℝ) (hf : ∀ j ∈ J, a ≤ f j) :
    (∏ j ∈ J, (f j)⁻¹) ≤ (a⁻¹) ^ (s - 1) := by
  rw [Finset.prod_inv_distrib, inv_pow]
  exact inv_anti₀ (pow_pos ha _) (local_product_lower J ha.le ha1 hcard f hf)

theorem half_bandwidth_split (m : ℕ) : (m + 1) / 2 + m / 2 = m := by omega

theorem local_bandwidth_budget (m s : ℕ) : ((m + 1) / 2 / s) * s ≤ (m + 1) / 2 :=
  Nat.div_mul_le_self _ _

/-- Convert the Two-Scale separation condition into the localization bandwidth
condition of NumDetect, with its auxiliary parameter equal to one. -/
theorem localization_bandwidth {m s : ℕ} (hm : 0 < m) (hs : 0 < s)
    {β : ℝ} (hβ : 4 * (s : ℝ) / m < β) :
    4 * Real.pi / (((m + 1) / 2 / s : ℕ) + 1 : ℝ) < 2 * Real.pi * β := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hb := (div_lt_iff₀ hmR).mp hβ
  have hβpos : 0 < β := lt_trans (by positivity) hβ
  have hfloor : (m + 1) / 2 < (((m + 1) / 2 / s) + 1) * s :=
    by simpa only [Nat.mul_comm s] using Nat.lt_mul_div_succ ((m + 1) / 2) hs
  have hhalf : m ≤ 2 * ((m + 1) / 2) := by omega
  have hlt : m < 2 * ((((m + 1) / 2 / s) + 1) * s) := by omega
  have hltR : (m : ℝ) < 2 * ((((m + 1) / 2 / s : ℕ) + 1 : ℝ) * s) := by
    exact_mod_cast hlt
  have hden : (0 : ℝ) < ((m + 1) / 2 / s : ℕ) + 1 := by positivity
  apply (div_lt_iff₀ hden).mpr
  have hh := mul_lt_mul_of_pos_left hltR hβpos
  have hmul : 2 < β * (((m + 1) / 2 / s : ℕ) + 1 : ℝ) := by nlinarith
  nlinarith [Real.pi_pos]

end SegmentedVDM
