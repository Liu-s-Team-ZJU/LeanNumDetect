import MultiTuran.Nikolskii.ProductNikolskii

/-! # Uniform constants for product sampling errors

The exact product Nikolskii coefficient is bounded here in terms of the
single minimum thickened block length. These are elementary consequences
of the proved product estimate and the actual block geometry.
-/

set_option autoImplicit false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran
noncomputable section

theorem minThickLength_le_coordinateMinLength {d : ℕ} (G : SegmentedGrid d) (q : Fin d) :
    G.minThickLength ≤ G.coordinateMinLength q := Finset.inf'_le _ (Finset.mem_univ q)

theorem minThickLength_pos {d : ℕ} (G : SegmentedGrid d) : 0 < G.minThickLength := by
  have h := G.minLength_add_one_le_minThickLength
  omega

theorem minThickLength_pow_le_product {d : ℕ} (G : SegmentedGrid d) :
    (G.minThickLength : ℝ) ^ d ≤ ∏ q, (G.coordinateMinLength q : ℝ) := by
  calc
    _ = ∏ _q : Fin d, (G.minThickLength : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun q _ => by
      exact_mod_cast minThickLength_le_coordinateMinLength G q)

/-- Exact square of the product coefficient; no estimate is lost here. -/
theorem productNikolskiiCoefficient_sq {d n : ℕ} (G : SegmentedGrid d) :
    (∏ q, Real.pi * n / (2 * Real.sqrt (G.coordinateMinLength q : ℝ))) ^ 2 =
      (Real.pi * n / 2) ^ (2*d) / (∏ q, (G.coordinateMinLength q : ℝ)) := by
  rw [← Finset.prod_pow]
  calc
    _ = ∏ q, (Real.pi * n / 2) ^ 2 / (G.coordinateMinLength q : ℝ) := by
      apply Finset.prod_congr rfl
      intro q _
      rw [← div_div, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    _ = _ := by
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

/-- The explicit uniform coefficient used in the derivative sampling error. -/
theorem productNikolskiiCoefficient_sq_le {d n : ℕ} (G : SegmentedGrid d) :
    (∏ q, Real.pi * n / (2 * Real.sqrt (G.coordinateMinLength q : ℝ))) ^ 2 ≤
      (4 : ℝ)^d * (n : ℝ)^(2*d) / (G.minThickLength : ℝ)^d := by
  rw [productNikolskiiCoefficient_sq]
  have hL : (0 : ℝ) < G.minThickLength := by exact_mod_cast minThickLength_pos G
  have hbase : Real.pi * n / 2 ≤ 2 * (n : ℝ) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith [Real.pi_lt_four]
  have hnum : (Real.pi * n / 2) ^ (2*d) ≤ (4 : ℝ)^d * (n : ℝ)^(2*d) := by
    calc
      _ ≤ (2 * (n : ℝ))^(2*d) := pow_le_pow_left₀ (by positivity) hbase _
      _ = _ := by rw [mul_pow, pow_mul]; norm_num
  calc
    _ ≤ (Real.pi * n / 2) ^ (2*d) / (G.minThickLength : ℝ)^d :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hL _)
        (minThickLength_pow_le_product G)
    _ ≤ _ := div_le_div_of_nonneg_right hnum (pow_pos hL _).le

/-- A uniform pointwise energy bound, with all quantities from the actual
segmented grid and its actual continuous integral. -/
theorem exponentialSum_product_norm_sq_le_uniform {d n : ℕ} (G : SegmentedGrid d)
    (hn : 0 < n) (Y : Fin n → Point d) (c : Fin n → ℂ) {t : Point d}
    (ht : t ∈ G.thickening) :
    ‖exponentialSum Y c t‖ ^ 2 ≤
      ((4 : ℝ)^d * (n : ℝ)^(2*d) / (G.minThickLength : ℝ)^d) *
        continuousEnergy G Y c := by
  have h := exponentialSum_product_norm_le G hn Y c ht
  have hsq := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
      (Real.sqrt_nonneg _))).mpr h
  rw [mul_pow, Real.sq_sqrt (continuousEnergy_nonneg G Y c)] at hsq
  exact hsq.trans (mul_le_mul_of_nonneg_right (productNikolskiiCoefficient_sq_le G)
    (continuousEnergy_nonneg G Y c))

end
end LeanNumDetect.MultiTuran
