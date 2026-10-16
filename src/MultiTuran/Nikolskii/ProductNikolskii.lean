import MultiTuran.Preliminaries.Volume
import MultiTuran.Preliminaries.Energy
import MultiTuran.Nikolskii.NikolskiiIntervals
import Mathlib.MeasureTheory.Integral.Prod

/-! # Tensorization of scalar exponential-sum evaluation estimates

All product estimates below are obtained by successive scalar evaluation
and Tonelli's theorem on the actual product measure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ENNReal
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran
noncomputable section

private theorem measurable_fin_cons (d : ℕ) :
    Measurable (fun p : ℝ × Point d => (Fin.cons p.1 p.2 : Point (d+1))) := by
  apply measurable_pi_iff.2
  intro q
  refine Fin.cases ?_ (fun r => ?_) q
  · simpa using (measurable_fst : Measurable (fun p : ℝ × Point d => p.1))
  · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply r).comp
      (measurable_snd : Measurable (fun p : ℝ × Point d => p.2))

/-- Tonelli's decomposition of a product set into one coordinate and its tail. -/
theorem setLIntegral_pi_fin_succ {d : ℕ} (S : Fin (d+1) → Set ℝ)
    (F : Point (d+1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x in Set.pi Set.univ S, F x) =
      ∫⁻ u in S 0, ∫⁻ v in Set.pi Set.univ (fun q => S q.succ), F (Fin.cons u v) := by
  let μ : Fin (d+1) → Measure ℝ := fun q => volume.restrict (S q)
  change (∫⁻ x, F x ∂(Measure.pi (fun _ : Fin (d+1) => (volume : Measure ℝ))).restrict
    (Set.pi Set.univ S)) = _
  rw [Measure.restrict_pi_pi]
  have he := (measurePreserving_piFinSuccAbove μ 0).symm
  rw [← he.lintegral_comp hF]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_zero, Fin.zero_succAbove, cast_eq]
  change (∫⁻ p : ℝ × Point d, F (Fin.cons p.1 p.2)
    ∂(μ 0).prod (Measure.pi (fun q : Fin d => μ q.succ))) = _
  have hprod : Measurable (fun p : ℝ × Point d => F (Fin.cons p.1 p.2)) := by
    simpa only [Function.comp_def] using hF.comp (measurable_fin_cons d)
  rw [lintegral_prod _ hprod.aemeasurable]
  change (∫⁻ u in S 0, ∫⁻ v, F (Fin.cons u v)
    ∂Measure.pi (fun q : Fin d => volume.restrict (S q.succ))) = _
  congr 1
  funext u
  change _ = ∫⁻ v, F (Fin.cons u v)
    ∂(Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (Set.pi Set.univ (fun q => S q.succ))
  rw [Measure.restrict_pi_pi]

private theorem update_cons_zero {d : ℕ} (u v : ℝ) (x : Point d) :
    Function.update (Fin.cons u x : Point (d+1)) 0 v = Fin.cons v x := by
  ext q
  refine Fin.cases ?_ (fun r => ?_) q <;> simp

private theorem update_cons_succ {d : ℕ} (u v : ℝ) (x : Point d) (q : Fin d) :
    Function.update (Fin.cons u x : Point (d+1)) q.succ v =
      Fin.cons u (Function.update x q v) := by
  ext r
  refine Fin.cases ?_ (fun r => ?_) r
  · rw [Function.update_of_ne (Fin.succ_ne_zero q).symm]
    rfl
  · by_cases hr : r = q
    · subst r; simp
    · simp [hr, Fin.succ_inj]

/-- Scalar coordinate inequalities tensorize without changing their constants.
No product analytic estimate is assumed in this theorem. -/
theorem pi_coordinate_evaluation_bound (d : ℕ) (S : Fin d → Set ℝ)
    (C : Fin d → ℝ≥0∞) (F : Point d → ℝ≥0∞) (hF : Measurable F)
    (hsection : ∀ q (x : Point d), x q ∈ S q →
      F x ≤ C q * ∫⁻ u in S q, F (Function.update x q u))
    (t : Point d) (ht : ∀ q, t q ∈ S q) :
    F t ≤ (∏ q, C q) * ∫⁻ x in Set.pi Set.univ S, F x := by
  induction d with
  | zero =>
    have hconst : F = fun _ => F t := funext fun x => congrArg F (Subsingleton.elim x t)
    have hS : Set.pi Set.univ S = Set.univ := by ext x; simp
    rw [hconst, hS]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, lintegral_const,
      Measure.restrict_apply_univ]
    change F t ≤ F t * (Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ))) Set.univ
    rw [Measure.pi_empty_univ, mul_one]
  | succ d ih =>
    let Stail := fun q : Fin d => S q.succ
    let Ctail := fun q : Fin d => C q.succ
    let ttail := fun q : Fin d => t q.succ
    have hcons_t : Fin.cons (t 0) ttail = t := by ext q; refine Fin.cases ?_ (fun r => ?_) q <;> rfl
    have htail (u : ℝ) : F (Fin.cons u ttail) ≤
        (∏ q, Ctail q) * ∫⁻ v in Set.pi Set.univ Stail, F (Fin.cons u v) := by
      apply ih Stail Ctail (fun v => F (Fin.cons u v))
      · exact hF.comp ((measurable_fin_cons d).comp (measurable_const.prodMk measurable_id))
      · intro q x hx
        simpa only [update_cons_succ, Fin.cons_succ] using
          hsection q.succ (Fin.cons u x) hx
      · intro q
        exact ht q.succ
    have hfirst := hsection 0 t (ht 0)
    rw [← hcons_t] at hfirst
    simp only [update_cons_zero] at hfirst
    rw [hcons_t] at hfirst
    have hprod : Measurable (fun p : ℝ × Point d => F (Fin.cons p.1 p.2)) := by
      simpa only [Function.comp_def] using hF.comp (measurable_fin_cons d)
    have hinnerMeas : Measurable (fun u =>
        ∫⁻ v in Set.pi Set.univ Stail, F (Fin.cons u v)) :=
      hprod.lintegral_prod_right'
    calc
      F t ≤ C 0 * ∫⁻ u in S 0, F (Fin.cons u ttail) := hfirst
      _ ≤ C 0 * ∫⁻ u in S 0,
          (∏ q, Ctail q) * ∫⁻ v in Set.pi Set.univ Stail, F (Fin.cons u v) :=
        mul_le_mul_right (lintegral_mono htail) _
      _ = C 0 * ((∏ q, Ctail q) * ∫⁻ u in S 0,
          ∫⁻ v in Set.pi Set.univ Stail, F (Fin.cons u v)) := by
        rw [lintegral_const_mul _ hinnerMeas]
      _ = (∏ q, C q) * ∫⁻ x in Set.pi Set.univ S, F x := by
        rw [Fin.prod_univ_succ, setLIntegral_pi_fin_succ S F hF]
        simp only [Ctail, Stail, mul_assoc]

/-- Freezing all but one variable gives a genuine scalar `n`-term sum. -/
theorem exponentialSum_coordinate_section {d n : ℕ} (Y : Fin n → Point d)
    (c : Fin n → ℂ) (x : Point d) (q : Fin d) (u : ℝ) :
    exponentialSum Y c (Function.update x q u) =
      ExponentialSumEstimates.exponentialSum (fun j => Y j q)
        (fun j => c j * Complex.exp (Complex.I *
          ((∑ r ∈ Finset.univ.erase q, x r * Y j r : ℝ) : ℂ))) u := by
  classical
  unfold exponentialSum ExponentialSumEstimates.exponentialSum
  apply Finset.sum_congr rfl
  intro j _
  have hdot : (∑ r, Function.update x q u r * Y j r) =
      (∑ r ∈ Finset.univ.erase q, x r * Y j r) + u * Y j q := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ q), Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [Function.update_of_ne (Finset.mem_erase.mp hr).1]
  rw [hdot, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Exact squared product Nikolskii bound on the actual segmented thickening. -/
theorem exponentialSum_product_norm_sq_le {d n : ℕ} (G : SegmentedGrid d)
    (hn : 0 < n) (Y : Fin n → Point d) (c : Fin n → ℂ) {t : Point d}
    (ht : t ∈ G.thickening) :
    ‖exponentialSum Y c t‖ ^ 2 ≤
      (Real.pi * n / 2) ^ (2 * d) /
        (∏ q, (G.coordinateMinLength q : ℝ)) * continuousEnergy G Y c := by
  classical
  let C : Fin d → ℝ := fun q => (Real.pi * n / 2) ^ 2 / (G.coordinateMinLength q : ℝ)
  let F : Point d → ℝ≥0∞ := fun x => ENNReal.ofReal (‖exponentialSum Y c x‖ ^ 2)
  have hP : Continuous (fun x => exponentialSum Y c x) := by
    unfold exponentialSum
    fun_prop
  have hC (q : Fin d) : 0 ≤ C q := by dsimp [C]; positivity
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hsection (q : Fin d) (x : Point d) (hx : x q ∈ G.coordinateThickening q) :
      F x ≤ ENNReal.ofReal (C q) * ∫⁻ u in G.coordinateThickening q,
        F (Function.update x q u) := by
    let a := fun m : G.Block q => (G.start q m : ℝ)
    let b := fun m : G.Block q => ((G.start q m + G.thickLength q m : ℕ) : ℝ)
    let z := fun j => c j * Complex.exp (Complex.I *
      ((∑ r ∈ Finset.univ.erase q, x r * Y j r : ℝ) : ℂ))
    have hL : (0 : ℝ) < G.coordinateMinLength q := by exact_mod_cast G.coordinateMinLength_pos q
    have hlength (m : G.Block q) : (G.coordinateMinLength q : ℝ) ≤ b m - a m := by
      have hnat : (G.coordinateMinLength q : ℝ) ≤ G.thickLength q m := by
        exact_mod_cast G.coordinateMinLength_le q m
      simpa [a,b,Nat.cast_add] using hnat
    have hscalar := exponentialSum_intervalUnion_norm_sq_le_div hn (fun j => Y j q) z
      a b hL hlength hx
    have hrepr (u : ℝ) : ExponentialSumEstimates.exponentialSum (fun j => Y j q) z u =
        exponentialSum Y c (Function.update x q u) :=
      (exponentialSum_coordinate_section Y c x q u).symm
    simp_rw [hrepr] at hscalar
    simp only [Function.update_eq_self] at hscalar
    change ‖exponentialSum Y c x‖ ^ 2 ≤ C q *
      (∫ u in G.coordinateThickening q, ‖exponentialSum Y c (Function.update x q u)‖ ^ 2)
      at hscalar
    have hInt : IntegrableOn (fun u => ‖exponentialSum Y c (Function.update x q u)‖ ^ 2)
        (G.coordinateThickening q) := by
      have hc : Continuous (fun u => ‖exponentialSum Y c (Function.update x q u)‖ ^ 2) := by
        convert (ExponentialSumEstimates.continuous_exponentialSum (fun j => Y j q) z).norm.pow 2
          using 1
        funext u
        change ‖exponentialSum Y c (Function.update x q u)‖ ^ 2 =
          ‖ExponentialSumEstimates.exponentialSum (fun j => Y j q) z u‖ ^ 2
        exact congrArg (fun v : ℂ => ‖v‖ ^ 2) (hrepr u).symm
      exact hc.continuousOn.integrableOn_compact (G.coordinateThickening_isCompact q)
    have h := ENNReal.ofReal_le_ofReal hscalar
    rw [ENNReal.ofReal_mul (hC q), ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))] at h
    exact h
  have hpi := pi_coordinate_evaluation_bound d G.coordinateThickening
    (fun q => ENNReal.ofReal (C q)) F hF hsection t (fun q => ht q (Set.mem_univ q))
  change F t ≤ (∏ q, ENNReal.ofReal (C q)) * ∫⁻ x in G.thickening, F x at hpi
  have hInt : IntegrableOn (fun x => ‖exponentialSum Y c x‖ ^ 2) G.thickening :=
    (hP.norm.pow 2).continuousOn.integrableOn_compact G.thickening_isCompact
  have henergy : ENNReal.ofReal (continuousEnergy G Y c) = ∫⁻ x in G.thickening, F x :=
    ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  rw [← ENNReal.ofReal_prod_of_nonneg (fun q _ => hC q), ← henergy,
    ← ENNReal.ofReal_mul (Finset.prod_nonneg (fun q _ => hC q))] at hpi
  have hreal : ‖exponentialSum Y c t‖ ^ 2 ≤ (∏ q, C q) * continuousEnergy G Y c :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Finset.prod_nonneg (fun q _ => hC q))
      (continuousEnergy_nonneg G Y c))).mp hpi
  have hconstant : (∏ q, C q) = (Real.pi * n / 2) ^ (2 * d) /
      (∏ q, (G.coordinateMinLength q : ℝ)) := by
    dsimp [C]
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [hconstant] at hreal
  exact hreal

/-- The exact pointwise product coefficient of `lem:nikolskii-product`. -/
theorem exponentialSum_product_norm_le {d n : ℕ} (G : SegmentedGrid d)
    (hn : 0 < n) (Y : Fin n → Point d) (c : Fin n → ℂ) {t : Point d}
    (ht : t ∈ G.thickening) :
    ‖exponentialSum Y c t‖ ≤
      (∏ q, Real.pi * n / (2 * Real.sqrt (G.coordinateMinLength q : ℝ))) *
        continuousL2Norm G Y c := by
  have hcoef : 0 ≤ ∏ q, Real.pi * n / (2 * Real.sqrt (G.coordinateMinLength q : ℝ)) :=
    Finset.prod_nonneg (fun _ _ => by positivity)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hcoef (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (continuousEnergy_nonneg G Y c)]
  have hconstant :
      (∏ q, Real.pi * n / (2 * Real.sqrt (G.coordinateMinLength q : ℝ))) ^ 2 =
        (Real.pi * n / 2) ^ (2 * d) / (∏ q, (G.coordinateMinLength q : ℝ)) := by
    rw [← Finset.prod_pow]
    calc
      _ = ∏ q, (Real.pi * n / 2) ^ 2 / (G.coordinateMinLength q : ℝ) := by
        apply Finset.prod_congr rfl
        intro q _
        rw [← div_div, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      _ = _ := by
        rw [Finset.prod_div_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [hconstant]
  exact exponentialSum_product_norm_sq_le G hn Y c ht

/-- The article's product `L²`--`L∞` inequality, using the actual supremum and
the actual continuous energy on the segmented product. -/
theorem exponentialSum_product_supNorm_le {d n : ℕ} (G : SegmentedGrid d)
    (hn : 0 < n) (Y : Fin n → Point d) (c : Fin n → ℂ) :
    setSupNorm (exponentialSum Y c) G.thickening ≤
      (∏ q, Real.pi * n / (2 * Real.sqrt (G.coordinateMinLength q : ℝ))) *
        continuousL2Norm G Y c := by
  apply Real.sSup_le
  · rintro z ⟨t,ht,rfl⟩
    exact exponentialSum_product_norm_le G hn Y c ht
  · apply mul_nonneg
    · exact Finset.prod_nonneg (fun _ _ => by positivity)
    · exact Real.sqrt_nonneg _

end
end LeanNumDetect.MultiTuran
