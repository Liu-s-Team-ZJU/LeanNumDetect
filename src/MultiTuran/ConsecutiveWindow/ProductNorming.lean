import MultiTuran.Nikolskii.ProductNikolskii
import MultiTuran.ConsecutiveWindow.BlockNorming

/-! # Tensorization of consecutive-window norming

Tonelli and finite summation tensorize scalar integral-to-sample inequalities
on the actual Cartesian product of measured rows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators ENNReal
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
noncomputable section

def windowNormingLoss (d n : ℕ) : ℝ :=
  (18 * (n : ℝ) * (3 * (n : ℝ)) ^ (2 * n)) ^ d

def windowNormingConstant (d n : ℕ) : ℝ := (windowNormingLoss d n)⁻¹

theorem windowNormingLoss_pos {d n : ℕ} (hn : 0 < n) :
    0 < windowNormingLoss d n := by unfold windowNormingLoss; positivity

theorem windowNormingConstant_pos {d n : ℕ} (hn : 0 < n) :
    0 < windowNormingConstant d n := inv_pos.mpr (windowNormingLoss_pos hn)

private theorem measurable_fin_cons (d : ℕ) :
    Measurable (fun p : ℝ × Point d => (Fin.cons p.1 p.2 : Point (d+1))) := by
  apply measurable_pi_iff.2
  intro q
  refine Fin.cases ?_ (fun r => ?_) q
  · simpa using (measurable_fst : Measurable (fun p : ℝ × Point d => p.1))
  · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply r).comp
      (measurable_snd : Measurable (fun p : ℝ × Point d => p.2))

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

/-- Finite sampling in each coordinate tensorizes, with no integrability
premise and without changing any scalar constant. -/
theorem pi_coordinate_integral_bound (d : ℕ) (S : Fin d → Set ℝ)
    (R : Fin d → Finset ℕ) (C : ℝ≥0∞) (F : Point d → ℝ≥0∞)
    (hF : Measurable F)
    (hsection : ∀ q (x : Point d), (∫⁻ u in S q, F (Function.update x q u)) ≤
      C * ∑ k : {k : ℕ // k ∈ R q}, F (Function.update x q k.val)) :
    (∫⁻ x in Set.pi Set.univ S, F x) ≤
      C ^ d * ∑ k : ((q : Fin d) → {k : ℕ // k ∈ R q}), F (fun q => (k q).val) := by
  classical
  induction d with
  | zero =>
    let z : Point 0 := fun q => Fin.elim0 q
    have hconst : F = fun _ => F z := funext fun x => congrArg F (Subsingleton.elim x z)
    have hS : Set.pi Set.univ S = Set.univ := by ext x; simp
    rw [hconst, hS]
    simp only [lintegral_const, Measure.restrict_apply_univ, pow_zero, one_mul]
    change F z * (Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ))) Set.univ ≤ _
    rw [Measure.pi_empty_univ, mul_one]
    simp
  | succ d ih =>
    let Stail := fun q : Fin d => S q.succ
    let Rtail := fun q : Fin d => R q.succ
    let T := (q : Fin d) → {k : ℕ // k ∈ Rtail q}
    have htail (u : ℝ) : (∫⁻ v in Set.pi Set.univ Stail, F (Fin.cons u v)) ≤
        C ^ d * ∑ k : T, F (Fin.cons u (fun q => (k q).val)) := by
      apply ih Stail Rtail (fun v => F (Fin.cons u v))
      · exact hF.comp ((measurable_fin_cons d).comp (measurable_const.prodMk measurable_id))
      · intro q x
        simpa only [update_cons_succ, Fin.cons_succ] using
          hsection q.succ (Fin.cons u x)
    have hmeas (k : T) : Measurable (fun u => F (Fin.cons u (fun q => (k q).val))) :=
      hF.comp ((measurable_fin_cons d).comp (measurable_id.prodMk measurable_const))
    have hfirst (k : T) :
        (∫⁻ u in S 0, F (Fin.cons u (fun q => (k q).val))) ≤
          C * ∑ r : {r : ℕ // r ∈ R 0}, F (Fin.cons r.val (fun q => (k q).val)) := by
      simpa only [update_cons_zero] using hsection 0 (Fin.cons 0 (fun q => (k q).val))
    calc
      _ = ∫⁻ u in S 0, ∫⁻ v in Set.pi Set.univ Stail, F (Fin.cons u v) :=
        setLIntegral_pi_fin_succ S F hF
      _ ≤ ∫⁻ u in S 0, C ^ d * ∑ k : T, F (Fin.cons u (fun q => (k q).val)) :=
        lintegral_mono htail
      _ = C ^ d * ∑ k : T, ∫⁻ u in S 0, F (Fin.cons u (fun q => (k q).val)) := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ (fun k _ => hmeas k)),
          lintegral_finsetSum _ (fun k _ => hmeas k)]
      _ ≤ C ^ d * ∑ k : T, C * ∑ r : {r : ℕ // r ∈ R 0},
          F (Fin.cons r.val (fun q => (k q).val)) :=
        mul_le_mul_right (Finset.sum_le_sum fun k _ => hfirst k) _
      _ = C ^ (d+1) * ∑ r : {r : ℕ // r ∈ R 0}, ∑ k : T,
          F (Fin.cons r.val (fun q => (k q).val)) := by
        rw [← Finset.mul_sum, Finset.sum_comm, pow_succ]
        simp only [mul_assoc]
      _ = _ := by
        congr 1
        let e : ({r : ℕ // r ∈ R 0} × T) ≃
            ((q : Fin (d+1)) → {k : ℕ // k ∈ R q}) := by
          simpa only [Fin.zero_succAbove] using
            (Fin.insertNthEquiv (fun q => {k : ℕ // k ∈ R q}) (0 : Fin (d+1)))
        rw [← Fintype.sum_prod_type']
        exact Fintype.sum_equiv e _ _ (fun p => by
          congr 1
          ext q
          refine Fin.cases ?_ (fun r => ?_) q <;> rfl)

/-- Genuine continuous energy and measured digital energy tensorize from
scalar coefficient-uniform inequalities. -/
theorem continuousEnergy_le_of_coordinate_norming {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) {C : ℝ} (hC : 0 ≤ C)
    (hscalar : ∀ q (z : Fin n → ℂ),
      (∫ u in G.coordinateThickening q,
        ‖ExponentialSumEstimates.exponentialSum (fun j => Y j q) z u‖ ^ 2) ≤
          C * ∑ k : {k : ℕ // k ∈ G.coordinateRows q},
            ‖ExponentialSumEstimates.exponentialSum (fun j => Y j q) z k.val‖ ^ 2)
    (c : Fin n → ℂ) :
    continuousEnergy G Y c ≤ C ^ d * discreteEnergy G Y c := by
  classical
  let F : Point d → ℝ≥0∞ := fun x => ENNReal.ofReal (‖exponentialSum Y c x‖ ^ 2)
  have hF : Measurable F := by dsimp [F]; unfold exponentialSum; fun_prop
  have hsection (q : Fin d) (x : Point d) :
      (∫⁻ u in G.coordinateThickening q, F (Function.update x q u)) ≤
        ENNReal.ofReal C * ∑ k : {k : ℕ // k ∈ G.coordinateRows q},
          F (Function.update x q k.val) := by
    let z := fun j => c j * Complex.exp (Complex.I *
      ((∑ r ∈ Finset.univ.erase q, x r * Y j r : ℝ) : ℂ))
    have hrepr (u : ℝ) : ExponentialSumEstimates.exponentialSum (fun j => Y j q) z u =
        exponentialSum Y c (Function.update x q u) :=
      (exponentialSum_coordinate_section Y c x q u).symm
    have hscalar' := hscalar q z
    simp_rw [hrepr] at hscalar'
    have hInt : IntegrableOn (fun u => ‖exponentialSum Y c (Function.update x q u)‖ ^ 2)
        (G.coordinateThickening q) := by
      have hcont : Continuous (fun u => ‖exponentialSum Y c (Function.update x q u)‖ ^ 2) := by
        convert (ExponentialSumEstimates.continuous_exponentialSum (fun j => Y j q) z).norm.pow 2
          using 1
        funext u
        exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hrepr u).symm
      exact hcont.continuousOn.integrableOn_compact (G.coordinateThickening_isCompact q)
    have h := ENNReal.ofReal_le_ofReal hscalar'
    rw [ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)), ENNReal.ofReal_mul hC,
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)] at h
    exact h
  have hpi := pi_coordinate_integral_bound d G.coordinateThickening G.coordinateRows
    (ENNReal.ofReal C) F hF hsection
  have hInt := exponentialSum_energy_integrableOn Y c G.thickening_isCompact
  have hcont : ENNReal.ofReal (continuousEnergy G Y c) = ∫⁻ x in G.thickening, F x :=
    ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  have hdisc : ENNReal.ofReal (discreteEnergy G Y c) =
      ∑ k : G.Row, F (fun q => (G.rowVector k q : ℝ)) := by
    unfold discreteEnergy
    exact ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)
  change (∫⁻ x in G.thickening, F x) ≤
    ENNReal.ofReal C ^ d * ∑ k : G.Row, F (fun q => (G.rowVector k q : ℝ)) at hpi
  rw [← hcont, ← hdisc, ← ENNReal.ofReal_pow hC, ← ENNReal.ofReal_mul (pow_nonneg hC d)] at hpi
  have hdiscnonneg : 0 ≤ discreteEnergy G Y c := by unfold discreteEnergy; positivity
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (pow_nonneg hC d) hdiscnonneg)).mp hpi

/-- The corresponding reciprocal constant in the article's norming
normalization. -/
theorem continuousNorming_of_coordinate_norming {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) {C : ℝ} (hC : 0 < C)
    (hscalar : ∀ q (z : Fin n → ℂ),
      (∫ u in G.coordinateThickening q,
        ‖ExponentialSumEstimates.exponentialSum (fun j => Y j q) z u‖ ^ 2) ≤
          C * ∑ k : {k : ℕ // k ∈ G.coordinateRows q},
            ‖ExponentialSumEstimates.exponentialSum (fun j => Y j q) z k.val‖ ^ 2) :
    ContinuousNorming G Y ((C ^ d)⁻¹) := by
  intro c
  exact (inv_mul_le_iff₀ (pow_pos hC d)).mpr
    (continuousEnergy_le_of_coordinate_norming G Y hC.le hscalar c)

/-- The full product energy inequality with the explicit loss of the
consecutive-window argument. No clump or separation input is used. -/
theorem continuousEnergy_le_windowNormingLoss {d n : ℕ}
    (G : SegmentedGrid d) (hn : 2 ≤ n) (Y : Fin n → Point d)
    (hchart : ∀ j q, |Y j q| ≤ Real.pi-Real.pi/(n : ℝ))
    (hblocks : ∀ q (m : G.Block q), n ≤ G.thickLength q m)
    (c : Fin n → ℂ) :
    continuousEnergy G Y c ≤ windowNormingLoss d n * discreteEnergy G Y c := by
  apply continuousEnergy_le_of_coordinate_norming G Y
    (by positivity : 0 ≤ 18*(n : ℝ)*(3*(n : ℝ))^(2*n))
  intro q z
  exact scalar_coordinate_energy_le G hn (fun j => Y j q) z
    (fun j => hchart j q) q (hblocks q)

/-- Literal `prop:norming`: the coefficient-uniform actual continuous
norming constant is `[18*n*(3*n)^(2*n)]^(-d)`. -/
theorem continuousNorming_of_long_consecutive_blocks {d n : ℕ}
    (G : SegmentedGrid d) (hn : 2 ≤ n) (Y : Fin n → Point d)
    (hchart : ∀ j q, |Y j q| ≤ Real.pi-Real.pi/(n : ℝ))
    (hblocks : ∀ q (m : G.Block q), n ≤ G.thickLength q m) :
    ContinuousNorming G Y (windowNormingConstant d n) := by
  intro c
  exact (inv_mul_le_iff₀ (windowNormingLoss_pos (by omega : 0 < n))).mpr
    (continuousEnergy_le_windowNormingLoss G hn Y hchart hblocks c)

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
