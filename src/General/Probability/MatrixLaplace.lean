import General.Probability.SamplingConvexOrder
import General.MatrixAnalysis.TraceExponential
import Mathlib.Data.Fin.Tuple.Basic

/-!
Iteration of a one-step finite Laplace bound, followed by the proved
sampling-without-replacement convex comparison. The one-step estimate is an
explicit hypothesis: the iteration itself applies to any real-valued function
on a real vector space, including the trace exponential on Hermitian matrices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

/-- Split a uniformly distributed tuple into its first coordinate and its tail. -/
theorem finiteAverage_fin_succ {κ E : Type*} [Fintype κ]
    [AddCommGroup E] [Module ℝ E] {m : ℕ} (g : (Fin (m + 1) → κ) → E) :
    finiteAverage g = finiteAverage (fun k =>
      finiteAverage (fun ω : Fin m → κ => g (Fin.cons k ω))) := by
  rw [← finiteAverage_comp_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => κ)) g]
  exact finiteAverage_prod (fun k (ω : Fin m → κ) => g (Fin.cons k ω))

/-- A uniform one-step bound iterates for independent finite samples, with any
initial value. No sign condition on the function is needed. -/
theorem finiteAverage_iid_add_sum_le {κ E : Type*} [Fintype κ] [Nonempty κ]
    [AddCommGroup E] [Module ℝ E] (Y : κ → E) {f : E → ℝ} {c : ℝ}
    (hc : 0 ≤ c)
    (hstep : ∀ H, finiteAverage (fun k => f (H + Y k)) ≤ c * f H)
    (m : ℕ) (H : E) :
    finiteAverage (fun ω : Fin m → κ => f (H + ∑ i, Y (ω i))) ≤
      c ^ m * f H := by
  induction m generalizing H with
  | zero => simp
  | succ m ih =>
      rw [finiteAverage_fin_succ]
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← add_assoc]
      calc
        finiteAverage (fun k => finiteAverage (fun ω : Fin m → κ =>
            f (H + Y k + ∑ i, Y (ω i)))) ≤
            finiteAverage (fun k => c ^ m * f (H + Y k)) :=
          finiteAverage_mono fun k => ih (H + Y k)
        _ = c ^ m * finiteAverage (fun k => f (H + Y k)) := by
          exact finiteAverage_smul (c ^ m) _
        _ ≤ c ^ m * (c * f H) :=
          mul_le_mul_of_nonneg_left (hstep H) (pow_nonneg hc _)
        _ = c ^ (m + 1) * f H := by rw [pow_succ]; ring

/-- A finite iid Laplace bound obtained by iteration of its one-step estimate. -/
theorem finiteAverage_iid_sum_le {κ E : Type*} [Fintype κ] [Nonempty κ]
    [AddCommGroup E] [Module ℝ E] (Y : κ → E) {f : E → ℝ} {c : ℝ}
    (hc : 0 ≤ c)
    (hstep : ∀ H, finiteAverage (fun k => f (H + Y k)) ≤ c * f H)
    (m : ℕ) :
    finiteAverage (fun ω : Fin m → κ => f (∑ i, Y (ω i))) ≤
      c ^ m * f 0 := by
  simpa only [zero_add] using finiteAverage_iid_add_sum_le Y hc hstep m 0

/-- Convex comparison transfers the iterated iid estimate to a uniform subset
of a finite population. -/
theorem finiteAverage_subset_sum_le {N m : ℕ} (hN : 0 < N) (hmN : m ≤ N)
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Y : Fin N → E) {f : E → ℝ} {c : ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hc : 0 ≤ c)
    (hstep : ∀ H, finiteAverage (fun k => f (H + Y k)) ≤ c * f H) :
    finiteAverage (fun Ω : Sample N m => f (∑ k ∈ Ω.val, Y k)) ≤
      c ^ m * f 0 := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact (sampling_withoutReplacement_convex_le hmN Y hf).trans
    (finiteAverage_iid_sum_le Y hc hstep m)

end LeanNumDetect.FiniteMatrixSampling

namespace LeanNumDetect.TraceExponential

open FiniteMatrixSampling

/-- The iid trace-exponential moment bound from a one-step estimate. -/
theorem traceExp_iid_sum_le {κ : Type*} [Fintype κ] [Nonempty κ] {d : ℕ}
    (Y : κ → selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) {c : ℝ} (hc : 0 ≤ c)
    (hstep : ∀ H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ),
      finiteAverage (fun k => traceExp (H + Y k).val) ≤ c * traceExp H.val)
    (m : ℕ) :
    finiteAverage (fun ω : Fin m → κ => traceExp (∑ i, Y (ω i)).val) ≤
      c ^ m * d := by
  have h := finiteAverage_iid_sum_le (f := fun A => traceExp A.val) Y hc hstep m
  change _ ≤ c ^ m * traceExp (0 : Matrix (Fin d) (Fin d) ℂ) at h
  simpa only [traceExp_zero] using h

/-- The corresponding moment bound for uniformly sampled fixed-size subsets.
The convex comparison used here is fully proved in `SamplingConvexOrder`. -/
theorem traceExp_subset_sum_le {N m d : ℕ} (hN : 0 < N) (hmN : m ≤ N)
    (Y : Fin N → selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) {c : ℝ} (hc : 0 ≤ c)
    (hstep : ∀ H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ),
      finiteAverage (fun k => traceExp (H + Y k).val) ≤ c * traceExp H.val) :
    finiteAverage (fun Ω : Sample N m => traceExp (∑ k ∈ Ω.val, Y k).val) ≤
      c ^ m * d := by
  have h := finiteAverage_subset_sum_le hN hmN Y convexOn_traceExp hc hstep
  change _ ≤ c ^ m * traceExp (0 : Matrix (Fin d) (Fin d) ℂ) at h
  simpa only [traceExp_zero] using h

end LeanNumDetect.TraceExponential
