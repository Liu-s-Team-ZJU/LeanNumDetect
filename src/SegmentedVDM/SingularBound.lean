import SegmentedVDM.Smoothing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open WithLp Matrix LeanNumDetect
namespace SegmentedVDM

/-- The physical angular-frequency VDM, with one row per block/sample pair. -/
noncomputable def vandermonde {n : ℕ} (m r : ℕ) (D : ℝ) (x : Fin n → ℝ) :
    Matrix (Fin (r+1) × Fin (m+1)) (Fin n) ℂ := fun t j => steering m r D (x j) t

/-- The complete averaging and Lagrange-duality step. Its packet hypotheses
record the remaining constructive part of the main theorem explicitly. -/
theorem singularValue_ge_of_packets {n m r : ℕ} (hn : 0 < n)
    (P : Fin n → Packet m r) (b z : ℕ) (D : ℝ) (x : Fin n → ℝ)
    {H : ℝ} (hH : 0 < H) (hP : ∀ k, (P k).mass ≤ H)
    (hinterp : ∀ k j, (P k).value D (x j-x k) = if k = j then 1 else 0) :
    Real.sqrt (((z+1)*(b+1) : ℕ) : ℝ) / (Real.sqrt n * H) ≤
      matrixSingularValue (vandermonde (m+b) (r+z) D x) (n-1) := by
  classical
  let N : ℝ := ((z+1)*(b+1) : ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  let C : Matrix (Fin n) (Fin (r+z+1) × Fin (m+b+1)) ℂ :=
    fun k => modulation (ofLp (smoothedVector (P k) b z)) D (x k)
  have hCV : C * vandermonde (m+b) (r+z) D x = 1 := by
    ext k j
    change modulation (ofLp (smoothedVector (P k) b z)) D (x k) ⬝ᵥ
      steering (m+b) (r+z) D (x j) = _
    rw [modulation_evaluation, smoothedVector_evaluation, hinterp]
    by_cases h : k = j
    · subst j; simp
    · simp [h]
  have hC (k : Fin n) : energy (C k) ≤ (H / Real.sqrt N)^2 := by
    change energy (modulation (ofLp (smoothedVector (P k) b z)) D (x k)) ≤ _
    rw [energy_modulation]
    change (∑ i, ‖(smoothedVector (P k) b z) i‖^2) ≤ _
    rw [← EuclideanSpace.norm_sq_eq]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).2
    exact (smoothedVector_norm_le (P k) b z).trans
      (div_le_div_of_nonneg_right (hP k) (Real.sqrt_nonneg _))
  have hh := singularValue_ge_of_interpolation (vandermonde (m+b) (r+z) D x)
    C hCV hn (by positivity : 0 < H / Real.sqrt N) hC
  convert! hh using 1
  dsimp [N]
  field_simp

end SegmentedVDM
