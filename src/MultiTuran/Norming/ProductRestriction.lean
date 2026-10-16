import MultiTuran.Nikolskii.ProductNikolskii

/-! # Continuous restriction transfer on the actual product sets

This module proves the elementary norm-transfer step after a supremum
comparison is supplied. It does not assume or assert a Turán theorem: the
needed supremum comparison remains an explicit premise.
-/

set_option autoImplicit false
open scoped BigOperators ENNReal
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran
noncomputable section

theorem setSupNorm_nonneg {α : Type*} (f : α → ℂ) (S : Set α) :
    0 ≤ setSupNorm f S := by
  apply Real.sSup_nonneg
  rintro z ⟨x,hx,rfl⟩
  exact norm_nonneg _

theorem norm_le_setSupNorm_on_compact {α : Type*} [TopologicalSpace α]
    (f : α → ℂ) (hf : Continuous f) {S : Set α} (hS : IsCompact S)
    {x : α} (hx : x ∈ S) : ‖f x‖ ≤ setSupNorm f S :=
  le_csSup (hS.image hf.norm).bddAbove ⟨x,hx,rfl⟩

/-- Actual aperture energy is dominated by its actual supremum and volume. -/
theorem apertureEnergy_le_boxVolume_mul_supNorm_sq {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (c : Fin n → ℂ) :
    setEnergy Y c G.apertureBox ≤
      G.boxVolume * setSupNorm (exponentialSum Y c) G.apertureBox ^ 2 := by
  have hint := exponentialSum_energy_integrableOn Y c G.apertureBox_isCompact
  have hfinite : volume G.apertureBox ≠ ∞ := by
    rw [G.apertureBox_volume]
    exact ENNReal.ofReal_ne_top
  have hc : IntegrableOn
      (fun _ : Point d => setSupNorm (exponentialSum Y c) G.apertureBox ^ 2)
      G.apertureBox := integrableOn_const hfinite
  have h := setIntegral_mono_on hint hc G.apertureBox_measurableSet
    (fun t ht => pow_le_pow_left₀ (norm_nonneg _)
      (norm_le_setSupNorm_on_compact _ (continuous_exponentialSum Y c)
        G.apertureBox_isCompact ht) 2)
  simpa only [setIntegral_const, smul_eq_mul, measureReal_def,
    G.apertureBox_volume_toReal, setEnergy] using h

/-- The literal square-root volume factor in the continuous restriction step. -/
theorem apertureL2_le_sqrt_boxVolume_mul_supNorm {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (c : Fin n → ℂ) :
    Real.sqrt (setEnergy Y c G.apertureBox) ≤
      Real.sqrt G.boxVolume * setSupNorm (exponentialSum Y c) G.apertureBox := by
  have h := Real.sqrt_le_sqrt (apertureEnergy_le_boxVolume_mul_supNorm_sq G Y c)
  rwa [Real.sqrt_mul G.boxVolume_pos.le,
    Real.sqrt_sq (setSupNorm_nonneg _ _)] at h

/-- The product Nikolskii estimate and a stated supremum comparison yield
the continuous restriction transfer, with its exact coordinate constants. -/
theorem apertureL2_le_of_supNorm_restriction {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (c : Fin n → ℂ) (hn : 0 < n)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hrestriction : setSupNorm (exponentialSum Y c) G.apertureBox ≤
      τ * setSupNorm (exponentialSum Y c) G.thickening) :
    Real.sqrt (setEnergy Y c G.apertureBox) ≤
      (Real.sqrt G.boxVolume * τ *
        (∏ q, Real.pi * n / (2 * Real.sqrt (G.coordinateMinLength q : ℝ)))) *
          continuousL2Norm G Y c := by
  calc
    _ ≤ Real.sqrt G.boxVolume * setSupNorm (exponentialSum Y c) G.apertureBox :=
      apertureL2_le_sqrt_boxVolume_mul_supNorm G Y c
    _ ≤ Real.sqrt G.boxVolume *
        (τ * setSupNorm (exponentialSum Y c) G.thickening) :=
      mul_le_mul_of_nonneg_left hrestriction (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt G.boxVolume * (τ *
        ((∏ q, Real.pi * n / (2 * Real.sqrt (G.coordinateMinLength q : ℝ))) *
          continuousL2Norm G Y c)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (exponentialSum_product_supNorm_le G hn Y c) hτ) (Real.sqrt_nonneg _)
    _ = _ := by ring

end
end LeanNumDetect.MultiTuran
