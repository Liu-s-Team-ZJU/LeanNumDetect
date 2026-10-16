import MultiTuran.Turan.RecurrenceBounds
import MultiTuran.Nikolskii.NikolskiiAffine
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Frequency-independent Turán extrapolation between real intervals

The proof samples a genuine exponential sum on a mesh and applies the
degree-sharp unit-root recurrence. No separation of frequencies is needed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Set

namespace LeanNumDetect.MultiTuran
open ExponentialSumEstimates TuranRecurrence
noncomputable section

/-- An extrapolation mesh whose first `r+1` points lie in the measured
interval and whose index has the required relative bound. -/
theorem exists_turan_extrapolation_mesh {r : ℕ} (hr : 0 < r)
    {length T : ℝ} (hlength : 0 < length) (hT : length ≤ T) :
    ∃ M : ℕ, r ≤ M ∧ 0 < M ∧
      (r : ℝ)*(T/M) ≤ length ∧ (M : ℝ)/r ≤ 2*T/length := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hT0 : 0 < T := hlength.trans_le hT
  let y : ℝ := (r : ℝ)*T/length
  let M : ℕ := Nat.ceil y
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hry : (r : ℝ) ≤ y := by
    dsimp [y]
    apply (le_div_iff₀ hlength).mpr
    exact mul_le_mul_of_nonneg_left hT hrR.le
  have hyM : y ≤ (M : ℝ) := Nat.le_ceil y
  have hMr : r ≤ M := by exact_mod_cast hry.trans hyM
  have hMpos : 0 < M := hr.trans_le hMr
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hy1 : 1 ≤ y := by
    have h : (1 : ℝ) ≤ r := by exact_mod_cast hr
    exact h.trans hry
  have hMupper : (M : ℝ) ≤ 2*y := by
    have h := (Nat.ceil_lt_add_one hy0).le
    dsimp [M]
    linarith
  refine ⟨M,hMr,hMpos,?_,?_⟩
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hMR).mpr
    simpa [mul_comm] using (div_le_iff₀ hlength).mp hyM
  · apply (div_le_iff₀ hrR).mpr
    calc
      _ ≤ 2*y := hMupper
      _ = _ := by dsimp [y]; ring

theorem exponentialSum_on_mesh {n : ℕ} (frequency : Fin n → ℝ)
    (c : Fin n → ℂ) (a step : ℝ) (M : ℕ) :
    powerSum (fun j => Complex.exp (Complex.I * ((step * frequency j : ℝ) : ℂ)))
      (fun j => c j * Complex.exp (Complex.I * ((a * frequency j : ℝ) : ℂ))) M =
      ExponentialSumEstimates.exponentialSum frequency c (a + (M : ℝ)*step) := by
  unfold powerSum ExponentialSumEstimates.exponentialSum
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Exact degree `n - 1` extrapolation from `n` consecutive mesh samples. -/
theorem exponentialSum_mesh_norm_le {n : ℕ} (hn : 2 ≤ n)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) (a step : ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hinitial : ∀ k < n,
      ‖ExponentialSumEstimates.exponentialSum frequency c (a+(k : ℝ)*step)‖ ≤ B)
    {M : ℕ} (hM : n-1 ≤ M) :
    ‖ExponentialSumEstimates.exponentialSum frequency c (a+(M : ℝ)*step)‖ ≤
      B * (2*Real.exp 1*M/(n-1 : ℕ))^(n-1) := by
  have h := unit_powerSum_norm_le_degree hn
    (fun j => Complex.exp (Complex.I * ((step * frequency j : ℝ) : ℂ)))
    (fun j => c j * Complex.exp (Complex.I * ((a * frequency j : ℝ) : ℂ)))
    (fun j => by rw [Complex.norm_exp_I_mul_ofReal]) hB
    (fun k hk => by rw [exponentialSum_on_mesh]; exact hinitial k hk) hM
  rwa [exponentialSum_on_mesh] at h

/-- A real interval controls extrapolation to its right, with an absolute
base constant and the exact number-of-terms exponent. -/
theorem exponentialSum_extrapolate_right {n : ℕ} (hn : 2 ≤ n)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ)
    {a length T B : ℝ} (hlength : 0 < length) (hT : length ≤ T)
    (hbound : ∀ t ∈ Icc a (a+length),
      ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ≤ B) :
    ‖ExponentialSumEstimates.exponentialSum frequency c (a+T)‖ ≤
      B * (4*Real.exp 1*T/length)^(n-1) := by
  have hr : 0 < n-1 := by omega
  have hrR : (0 : ℝ) < (n-1 : ℕ) := by exact_mod_cast hr
  have hT0 : 0 < T := hlength.trans_le hT
  have hB : 0 ≤ B := (norm_nonneg _).trans (hbound a ⟨le_rfl, by linarith⟩)
  let y : ℝ := (n-1 : ℕ)*T/length
  let M : ℕ := Nat.ceil y
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hry : (n-1 : ℕ) ≤ y := by
    dsimp [y]
    apply (le_div_iff₀ hlength).mpr
    exact mul_le_mul_of_nonneg_left hT hrR.le
  have hyM : y ≤ (M : ℝ) := Nat.le_ceil y
  have hMr : n-1 ≤ M := by exact_mod_cast hry.trans hyM
  have hMpos : 0 < M := hr.trans_le hMr
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hy1 : 1 ≤ y := by
    have h : (1 : ℝ) ≤ (n-1 : ℕ) := by exact_mod_cast hr
    exact h.trans hry
  have hMupper : (M : ℝ) ≤ 2*y := by
    have h := (Nat.ceil_lt_add_one hy0).le
    dsimp [M]
    linarith
  let step : ℝ := T/M
  have hstep : 0 ≤ step := by dsimp [step]; positivity
  have hsample : ∀ k < n,
      ‖ExponentialSumEstimates.exponentialSum frequency c (a+(k : ℝ)*step)‖ ≤ B := by
    intro k hk
    apply hbound
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hstep)
    · have hkr : (k : ℝ) ≤ (n-1 : ℕ) := by exact_mod_cast (show k ≤ n-1 by omega)
      have hle : (n-1 : ℕ)*T ≤ (M : ℝ)*length :=
        (div_le_iff₀ hlength).mp hyM
      have hkle : (k : ℝ)*T ≤ (M : ℝ)*length :=
        (mul_le_mul_of_nonneg_right hkr hT0.le).trans hle
      have hfrac : (k : ℝ)*step ≤ length := by
        dsimp [step]
        rw [← mul_div_assoc]
        exact (div_le_iff₀ hMR).mpr (by simpa [mul_comm] using hkle)
      linarith
  have hmesh := exponentialSum_mesh_norm_le hn frequency c a step hB hsample hMr
  have heval : a+(M : ℝ)*step = a+T := by dsimp [step]; field_simp
  rw [heval] at hmesh
  have hratio : (M : ℝ)/(n-1 : ℕ) ≤ 2*T/length := by
    apply (div_le_iff₀ hrR).mpr
    calc
      _ ≤ 2*y := hMupper
      _ = _ := by dsimp [y]; ring
  have hbase : 2*Real.exp 1*M/(n-1 : ℕ) ≤ 4*Real.exp 1*T/length := by
    calc
      _ = (2*Real.exp 1)*((M : ℝ)/(n-1 : ℕ)) := by ring
      _ ≤ (2*Real.exp 1)*(2*T/length) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  exact hmesh.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hbase _) hB)

/-- A literal subinterval controls the whole interval with a universal
constant and the sharp exponent `n - 1`. Frequencies are arbitrary real
numbers and may coincide. -/
theorem exponentialSum_interval_norm_le_of_subinterval_bound {n : ℕ} (hn : 0 < n)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) {a b u v B : ℝ}
    (hau : a ≤ u) (huv : u < v) (hvb : v ≤ b)
    (hbound : ∀ t ∈ Icc u v,
      ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ≤ B)
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖ExponentialSumEstimates.exponentialSum frequency c x‖ ≤
      B * (4*Real.exp 1*(b-a)/(v-u))^(n-1) := by
  by_cases hn2 : 2 ≤ n
  · have hlength : 0 < v-u := sub_pos.mpr huv
    have hB : 0 ≤ B := (norm_nonneg _).trans (hbound u ⟨le_rfl,huv.le⟩)
    have hbase_nonneg : 0 ≤ 4*Real.exp 1*(b-a)/(v-u) := by
      have hab : a ≤ b := hau.trans (huv.le.trans hvb)
      positivity
    have henlarge {T : ℝ} (hT : 0 ≤ T) (hTle : T ≤ b-a) :
        B*(4*Real.exp 1*T/(v-u))^(n-1) ≤
          B*(4*Real.exp 1*(b-a)/(v-u))^(n-1) := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply pow_le_pow_left₀ (by positivity)
      apply div_le_div_of_nonneg_right _ hlength.le
      exact mul_le_mul_of_nonneg_left hTle (by positivity)
    by_cases hux : u ≤ x
    · by_cases hxv : x ≤ v
      · have hratio : 1 ≤ (b-a)/(v-u) := by
          apply (one_le_div hlength).mpr
          linarith
        have hexp : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
        have hbase : 1 ≤ 4*Real.exp 1*(b-a)/(v-u) := by
          calc
            _ ≤ 4*Real.exp (1 : ℝ) := by linarith
            _ = (4*Real.exp 1)*1 := by ring
            _ ≤ (4*Real.exp 1)*((b-a)/(v-u)) :=
              mul_le_mul_of_nonneg_left hratio (by positivity)
            _ = _ := by ring
        exact (hbound x ⟨hux,hxv⟩).trans (by
          simpa using mul_le_mul_of_nonneg_left (one_le_pow₀ hbase) hB)
      · have hT : v-u ≤ x-u := by linarith
        have h := exponentialSum_extrapolate_right hn2 frequency c (a := u) hlength hT
          (by simpa only [show u+(v-u) = v by ring] using hbound)
        rw [show u+(x-u) = x by ring] at h
        exact h.trans (henlarge (by linarith) (by linarith [hx.2]))
    · let reflectedFrequency : Fin n → ℝ := fun j => -frequency j
      let reflectedCoeff : Fin n → ℂ := fun j =>
        c j * Complex.exp (Complex.I * ((v*frequency j : ℝ) : ℂ))
      have hreflect (t : ℝ) :
          ExponentialSumEstimates.exponentialSum reflectedFrequency reflectedCoeff t =
            ExponentialSumEstimates.exponentialSum frequency c (v-t) := by
        simpa [reflectedFrequency, reflectedCoeff, sub_eq_add_neg, add_comm] using
          exponentialSum_affine frequency c v (-1) t
      have hreflectBound : ∀ t ∈ Icc (0 : ℝ) (0+(v-u)),
          ‖ExponentialSumEstimates.exponentialSum reflectedFrequency reflectedCoeff t‖ ≤ B := by
        intro t ht
        rw [hreflect]
        apply hbound
        constructor <;> linarith [ht.1,ht.2]
      have hT : v-u ≤ v-x := by linarith
      have h := exponentialSum_extrapolate_right hn2 reflectedFrequency reflectedCoeff
        hlength hT hreflectBound
      rw [zero_add, hreflect, sub_sub_cancel] at h
      exact h.trans (henlarge (by linarith) (by linarith [hx.1]))
  · have hn1 : n = 1 := by omega
    subst n
    have hnorm (t : ℝ) :
        ‖ExponentialSumEstimates.exponentialSum frequency c t‖ = ‖c 0‖ := by
      simp only [ExponentialSumEstimates.exponentialSum, Fin.sum_univ_one,
        norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
    simpa [hnorm] using hbound u ⟨le_rfl,huv.le⟩

end
end LeanNumDetect.MultiTuran
