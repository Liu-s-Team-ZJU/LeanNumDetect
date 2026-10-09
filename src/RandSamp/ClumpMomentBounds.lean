import RandSamp.MultidimensionalMultiClumpModel

/-! Explicit second and fourth clump-size moments and their joint bound. -/
set_option autoImplicit false
open scoped BigOperators
namespace LeanNumDetect.RandSamp
noncomputable section

theorem hasMaxClumpSize_clumpCount_le_sub_add_one {n A nstar : ℕ}
    {P : ClumpPartition n A} (hmax : HasMaxClumpSize P nstar) :
    A ≤ n - nstar + 1 := by
  have h := hasMaxClumpSize_clumpCount_sub_one_le hmax
  obtain ⟨a, _⟩ := hmax.2
  have hA : 0<A := Nat.zero_lt_of_lt a.isLt
  omega

theorem hasMaxClumpSize_clumpCount_le_sub_add_one_real {n A nstar : ℕ}
    {P : ClumpPartition n A} (hmax : HasMaxClumpSize P nstar) :
    (A : ℝ) ≤ (n : ℝ) - (nstar : ℝ) + 1 := by
  have h := Nat.cast_le (α := ℝ).mpr (hasMaxClumpSize_clumpCount_le_sub_add_one hmax)
  simpa only [Nat.cast_add, Nat.cast_sub (hasMaxClumpSize_le_n hmax), Nat.cast_one] using h

namespace ClumpPartition
variable {n A : ℕ} (P : ClumpPartition n A)

theorem real_sizeSquareSum_le {nstar : ℕ} (hsize : ∀ a, P.size a≤nstar) :
    (∑ a : Fin A, (P.size a : ℝ)^2) ≤ (n : ℝ)*(nstar : ℝ) := by
  have h := P.sizeSquareSum_le hsize
  unfold sizeSquareSum at h
  exact_mod_cast h

theorem real_sizeFourthSum_le {nstar : ℕ} (hsize : ∀ a, P.size a≤nstar) :
    (∑ a : Fin A, (P.size a : ℝ)^4) ≤ (n : ℝ)*(nstar : ℝ)^3 := by
  have h := P.sizePowerSum_le (d := 2) (by omega) hsize
  simp only [sizePowerSum, show 2*2=4 by omega, show 2*2-1=3 by omega] at h
  exact_mod_cast h

theorem sqrt_clumpCount_mul_real_sizeFourthSum_le {nstar : ℕ}
    (hmax : HasMaxClumpSize P nstar) :
    Real.sqrt ((A : ℝ)*∑ a : Fin A, (P.size a : ℝ)^4) ≤
      Real.sqrt (((n : ℝ)-(nstar : ℝ)+1)*(n : ℝ)*(nstar : ℝ)^3) := by
  have hcount := hasMaxClumpSize_clumpCount_le_sub_add_one_real hmax
  have hfour := P.real_sizeFourthSum_le hmax.1
  have hcount0 : 0≤(n : ℝ)-(nstar : ℝ)+1 :=
    (Nat.cast_nonneg A).trans hcount
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ ((n : ℝ)-(nstar : ℝ)+1)*((n : ℝ)*(nstar : ℝ)^3) :=
      mul_le_mul hcount hfour (Finset.sum_nonneg (fun _ _ => by positivity)) hcount0
    _ = _ := by ring

theorem real_globalMomentCoefficient_le {nstar : ℕ}
    (hmax : HasMaxClumpSize P nstar) :
    (∑ a : Fin A, (P.size a : ℝ)^2) +
        Real.sqrt ((A : ℝ)*∑ a : Fin A, (P.size a : ℝ)^4) ≤
      (n : ℝ)*(nstar : ℝ) +
        Real.sqrt (((n : ℝ)-(nstar : ℝ)+1)*(n : ℝ)*(nstar : ℝ)^3) :=
  add_le_add (P.real_sizeSquareSum_le hmax.1)
    (P.sqrt_clumpCount_mul_real_sizeFourthSum_le hmax)

end ClumpPartition
end
end LeanNumDetect.RandSamp
