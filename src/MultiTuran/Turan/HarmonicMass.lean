import MultiTuran.Turan.HalfPlane

/-! A nonnegative upper-half-plane harmonic function with inverse-height
centre decay has finite real-line logarithmic mass. Tangent circle averages
and Fatou's lemma give the actual integral estimate. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Topology ENNReal
open Set Filter MeasureTheory Complex Metric InnerProductSpace Real

namespace LeanNumDetect.MultiTuran
noncomputable section

private theorem lintegral_limit_le_uniform_bound {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    (hg : ∀ n, Measurable (g n))
    (hlim : ∀ᵐ x : ℝ, Tendsto (fun n => g n x) atTop (𝓝 (f x)))
    {C : ℝ≥0∞} (hbound : ∀ n, (∫⁻ x : ℝ, ENNReal.ofReal (g n x)) ≤ C) :
    (∫⁻ x : ℝ, ENNReal.ofReal (f x)) ≤ C := by
  calc
    _ = ∫⁻ x : ℝ, liminf (fun n => ENNReal.ofReal (g n x)) atTop := by
      apply lintegral_congr_ae
      filter_upwards [hlim] with x hx
      exact (ENNReal.tendsto_ofReal hx).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x : ℝ, ENNReal.ofReal (g n x)) atTop :=
      lintegral_liminf_le (fun n => (hg n).ennreal_ofReal)
    _ ≤ C := liminf_le_of_frequently_le' (Filter.Eventually.frequently (Filter.Eventually.of_forall hbound))

private theorem continuous_harmonic_on_flatteningCircle {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u {z : ℂ | 0 < z.im}) {ε R : ℝ}
    (hε : 0 < ε) (hR : 0 ≤ R) : Continuous (fun t => u (flatteningCircle ε R t)) := by
  apply continuous_iff_continuousAt.2
  intro t
  exact (hu _ (flatteningCircle_im_pos hε hR t)).1.continuousAt.comp
    (continuous_flatteningCircle ε R).continuousAt

private theorem continuous_harmonic_on_horizontalLine {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u {z : ℂ | 0 < z.im}) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun x : ℝ => u ((x : ℂ)+Complex.I*(ε : ℂ))) := by
  apply continuous_iff_continuousAt.2
  intro x
  have hx : 0 < ((x : ℂ)+Complex.I*(ε : ℂ)).im := by simpa using hε
  have hline : Continuous (fun t : ℝ => (t : ℂ)+Complex.I*(ε : ℂ)) := by fun_prop
  exact ContinuousAt.comp (f := fun t : ℝ => (t : ℂ)+Complex.I*(ε : ℂ))
    (x := x) (hu _ hx).1.continuousAt hline.continuousAt

/-- Uniform inverse-height control of the harmonic centre values bounds the
actual logarithmic mass on every horizontal line in the upper half plane. -/
theorem harmonic_upperHalfPlane_lintegral_horizontal_le {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u {z : ℂ | 0 < z.im})
    (hnonneg : ∀ z : ℂ, 0 < z.im → 0 ≤ u z)
    {A : ℝ} (hA : 0 ≤ A)
    (hcentre : ∀ R : ℝ, 0 < R → u (Complex.I*(R : ℂ)) ≤ A/R)
    {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ x : ℝ, ENNReal.ofReal (u ((x : ℂ)+Complex.I*(ε : ℂ)))) ≤
      ENNReal.ofReal (2*Real.pi*A) := by
  let R : ℕ → ℝ := fun n => (n : ℝ)+1
  let g : ℕ → ℝ → ℝ := fun n =>
    (Icc (-Real.pi*R n) (Real.pi*R n)).indicator (fun t => u (flatteningCircle ε (R n) t))
  have hR (n : ℕ) : 0 < R n := by dsimp [R]; positivity
  apply lintegral_limit_le_uniform_bound (g := g)
  · intro n
    exact (continuous_harmonic_on_flatteningCircle hu hε (hR n).le).measurable.indicator measurableSet_Icc
  · apply Filter.Eventually.of_forall
    intro x
    have hgrowth : Tendsto (fun n : ℕ => Real.pi*R n) atTop atTop :=
      Tendsto.const_mul_atTop Real.pi_pos
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    have hmem : ∀ᶠ n in atTop, x ∈ Icc (-Real.pi*R n) (Real.pi*R n) := by
      filter_upwards [hgrowth.eventually (eventually_ge_atTop |x|)] with n hn
      exact ⟨by linarith [neg_le_abs x], (le_abs_self x).trans hn⟩
    have hcont := (hu ((x : ℂ)+Complex.I*(ε : ℂ)) (by simpa using hε)).1.continuousAt
    apply (hcont.tendsto.comp (tendsto_flatteningCircle ε x)).congr'
    filter_upwards [hmem] with n hn
    exact (Set.indicator_of_mem hn (fun t => u (flatteningCircle ε (R n) t))).symm
  · intro n
    have hc := continuous_harmonic_on_flatteningCircle hu hε (hR n).le
    have hint : IntegrableOn (fun t => u (flatteningCircle ε (R n) t))
        (Icc (-Real.pi*R n) (Real.pi*R n)) := hc.continuousOn.integrableOn_compact isCompact_Icc
    have hgi : Integrable (g n) := hint.integrable_indicator measurableSet_Icc
    have hgn : ∀ᵐ t : ℝ, 0 ≤ g n t := Filter.Eventually.of_forall (fun t => by
      apply Set.indicator_nonneg
      intro _ _
      exact hnonneg _ (flatteningCircle_im_pos hε (hR n).le _))
    rw [← ofReal_integral_eq_lintegral_ofReal hgi hgn]
    apply ENNReal.ofReal_le_ofReal
    change (∫ t : ℝ, (Icc (-Real.pi*R n) (Real.pi*R n)).indicator
      (fun t => u (flatteningCircle ε (R n) t)) t) ≤ _
    rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by nlinarith [Real.pi_pos,hR n]),
      harmonic_integral_flatteningCircle hu hε (hR n)]
    have h := hcentre (R n+ε) (by positivity)
    have hmul := mul_le_mul_of_nonneg_left h (hR n).le
    have hfrac : R n*(A/(R n+ε)) ≤ A := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < R n+ε)).mpr
      nlinarith
    have hfinal := mul_le_mul_of_nonneg_left (hmul.trans hfrac) (by positivity : (0:ℝ) ≤ 2*Real.pi)
    nlinarith

/-- Passing to the boundary only requires continuity outside a null set.
The conclusion is an actual whole-line Lebesgue integral bound. -/
theorem harmonic_upperHalfPlane_lintegral_boundary_le {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u {z : ℂ | 0 < z.im})
    (hnonneg : ∀ z : ℂ, 0 < z.im → 0 ≤ u z)
    {A : ℝ} (hA : 0 ≤ A)
    (hcentre : ∀ R : ℝ, 0 < R → u (Complex.I*(R : ℂ)) ≤ A/R)
    (hboundary : ∀ᵐ x : ℝ, ContinuousAt u (x : ℂ)) :
    (∫⁻ x : ℝ, ENNReal.ofReal (u (x : ℂ))) ≤ ENNReal.ofReal (2*Real.pi*A) := by
  let ε : ℕ → ℝ := fun n => ((n : ℝ)+1)⁻¹
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  apply lintegral_limit_le_uniform_bound
    (g := fun n x => u ((x : ℂ)+Complex.I*((ε n : ℝ) : ℂ)))
  · intro n
    exact (continuous_harmonic_on_horizontalLine hu (hε n)).measurable
  · filter_upwards [hboundary] with x hx
    have he := tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
    have hh := (tendsto_const_nhds (x := (x : ℂ))).add (he.ofReal.const_mul Complex.I)
    have harg : Tendsto (fun n : ℕ => (x : ℂ)+Complex.I*((ε n : ℝ) : ℂ)) atTop (𝓝 (x : ℂ)) := by
      simpa only [ε,Function.comp_def,Complex.ofReal_zero,mul_zero,add_zero] using hh
    exact hx.tendsto.comp harg
  · intro n
    exact harmonic_upperHalfPlane_lintegral_horizontal_le hu hnonneg hA hcentre (hε n)

end
end LeanNumDetect.MultiTuran
