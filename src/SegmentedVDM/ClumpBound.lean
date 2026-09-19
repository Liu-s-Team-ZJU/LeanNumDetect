import SegmentedVDM.Construction
import SegmentedVDM.SingularBound
import SegmentedVDM.Constants

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SegmentedVDM

/-- Geometric one-dimensional segmented-VDM estimate. All interpolation and
frame hypotheses have been discharged; only clump geometry remains. -/
theorem clump_singularValue_bound_of_split {n s : ℕ} (C : Clumps n s)
    (hn : 0 < n) (hs : 1 ≤ s) (m₁ b M : ℕ) (hM : 2*s ≤ M)
    (D Δ : ℝ) (hD : 0 < D) (hΔ : 0 < Δ)
    (x : Fin n → ℝ) {a : ℝ} (ha : 0 < a) (haHalf : a ≤ 1/2)
    (hscale : ((M : ℝ)/s)*D*Δ ≤ Real.pi)
    (hsep : ∀ i j, i ≠ j → Δ ≤ |x i-x j|)
    (hdiam : ∀ i j, C.label i = C.label j → |x i-x j| ≤ Real.pi/(2*D))
    (hcross : ∀ i j, C.label i ≠ C.label j → ∀ p : ℤ,
      4*Real.pi/((m₁/s : ℕ)+1) ≤ |x i-x j-2*Real.pi*p|) :
    a^((s : ℝ)/2) * Real.sqrt ((M : ℝ)*(b+1 : ℕ)/(n*s)) *
      ((M : ℝ)*D*Δ/(Real.sqrt 2*Real.pi*s))^(s-1) ≤
      LeanNumDetect.matrixSingularValue (vandermonde (m₁+b) M D x) (n-1) := by
  classical
  choose P hPi hPm using clump_packets C hs m₁ M hM D Δ hD hΔ x
    ha haHalf hscale hsep hdiam hcross
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let H := (1/Real.sqrt a)^s * (Real.sqrt 2/(((M : ℝ)/s)*D*Δ/Real.pi))^(s-1)
  have hH : 0 < H := by dsimp [H]; positivity
  have hh := singularValue_ge_of_packets hn P b (M/s) D x hH hPm hPi
  rw [Nat.sub_add_cancel (Nat.div_le_self M s)] at hh
  apply le_trans _ hh
  have hz : (M : ℝ)/s ≤ (M/s : ℕ)+1 := by
    have hf := Nat.lt_mul_div_succ M (show 0 < s from hs)
    have hfR : (M : ℝ) < s*((M/s : ℕ)+1) := by exact_mod_cast hf
    exact (div_le_iff₀ hsR).2 (by nlinarith)
  have hnum : Real.sqrt ((M : ℝ)/s*((b : ℕ)+1)) ≤
      Real.sqrt (((M/s+1)*(b+1) : ℕ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    push_cast
    exact mul_le_mul_of_nonneg_right hz (by positivity)
  have h := div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ Real.sqrt n*H)
  rw [bound_normalization hn hs (show 0 < M by omega) ha hD hΔ] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The usual half-bandwidth allocation is a specialization of the independent
localization and averaging degrees. -/
theorem clump_singularValue_bound {n s : ℕ} (C : Clumps n s)
    (hn : 0 < n) (hs : 1 ≤ s) (m M : ℕ) (hM : 2*s ≤ M)
    (D Δ : ℝ) (hD : 0 < D) (hΔ : 0 < Δ)
    (x : Fin n → ℝ) {a : ℝ} (ha : 0 < a) (haHalf : a ≤ 1/2)
    (hscale : ((M : ℝ)/s)*D*Δ ≤ Real.pi)
    (hsep : ∀ i j, i ≠ j → Δ ≤ |x i-x j|)
    (hdiam : ∀ i j, C.label i = C.label j → |x i-x j| ≤ Real.pi/(2*D))
    (hcross : ∀ i j, C.label i ≠ C.label j → ∀ p : ℤ,
      4*Real.pi/(((m+1)/2/s : ℕ)+1) ≤ |x i-x j-2*Real.pi*p|) :
    a^((s : ℝ)/2) * Real.sqrt ((M : ℝ)*(m/2+1 : ℕ)/(n*s)) *
      ((M : ℝ)*D*Δ/(Real.sqrt 2*Real.pi*s))^(s-1) ≤
      LeanNumDetect.matrixSingularValue (vandermonde m M D x) (n-1) := by
  have hsplit : (m+1)/2+m/2 = m := by omega
  have h :=
    clump_singularValue_bound_of_split C hn hs ((m+1)/2) (m/2) M hM
      D Δ hD hΔ x ha haHalf hscale hsep hdiam hcross
  rw [hsplit] at h
  exact h

end SegmentedVDM
