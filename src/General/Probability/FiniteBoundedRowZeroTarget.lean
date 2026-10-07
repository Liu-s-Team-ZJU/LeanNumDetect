import General.Probability.FiniteBoundedRowConcentration

/-! Adding the zero coefficient vector leaves every nonnegative energy
maximum and absolute deviation maximum unchanged. This discharges the
zero-test hypothesis of the clipped-process contraction proof. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.BoundedRieszConcentration

/-- The original finite class preceded by the zero coefficient vector. -/
def zeroExtendedTarget {N J : ℕ} (f : Fin J → ComplexVector N) :
    Fin (J + 1) → ComplexVector N := Fin.cons 0 f

theorem sSup_fin_cons_zero {J : ℕ} (hJ : 0 < J) (g : Fin J → ℝ)
    (hg : ∀ j, 0 ≤ g j) :
    sSup (Set.range (Fin.cons 0 g)) = sSup (Set.range g) := by
  letI : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨j, rfl⟩
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [Fin.cons_zero]
      exact (hg ⟨0, hJ⟩).trans
        (le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self (f := g) (⟨0, hJ⟩ : Fin J)))
    · simp only [Fin.cons_succ]
      exact le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self k)
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨j, rfl⟩
    apply le_csSup (Set.finite_range _).bddAbove
    exact ⟨j.succ, Fin.cons_succ _ _ _⟩

theorem finiteRowPopulationSup_cons_zero {N L J : ℕ} (hJ : 0 < J)
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ)
    (hq : ∀ a, 0 ≤ q a) :
    finiteRowPopulationSup X (zeroExtendedTarget f) q = finiteRowPopulationSup X f q := by
  have he : (fun j : Fin (J + 1) => FiniteEntropy.weightedMean q
      (fun a => rowEnergy (zeroExtendedTarget f j) (X a))) =
      Fin.cons 0 (fun j => FiniteEntropy.weightedMean q
        (fun a => rowEnergy (f j) (X a))) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;>
      simp [zeroExtendedTarget, FiniteEntropy.weightedMean]
  unfold finiteRowPopulationSup
  rw [he]
  exact sSup_fin_cons_zero hJ _ (fun j => Finset.sum_nonneg
    (fun a _ => mul_nonneg (hq a) (rowEnergy_nonneg _ _)))

theorem finiteRowDeviation_cons_zero {N L J m : ℕ} (hJ : 0 < J)
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ)
    (x : Fin m → Fin L) :
    finiteRowDeviation X (zeroExtendedTarget f) q x = finiteRowDeviation X f q x := by
  have he : (fun j : Fin (J + 1) => |(m : ℝ)⁻¹ *
      (∑ i, rowEnergy (zeroExtendedTarget f j) (X (x i))) -
      FiniteEntropy.weightedMean q (fun a => rowEnergy (zeroExtendedTarget f j) (X a))|) =
      Fin.cons 0 (fun j => |(m : ℝ)⁻¹ * (∑ i, rowEnergy (f j) (X (x i))) -
        FiniteEntropy.weightedMean q (fun a => rowEnergy (f j) (X a))|) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;>
      simp [zeroExtendedTarget, FiniteEntropy.weightedMean]
  unfold finiteRowDeviation
  rw [he]
  exact sSup_fin_cons_zero hJ _ (fun _ => abs_nonneg _)

theorem finiteRowEnergySumSup_cons_zero {N J m : ℕ} (hJ : 0 < J)
    (rows : Fin m → ComplexVector N) (f : Fin J → ComplexVector N) :
    sSup (Set.range (fun j => ∑ i, rowEnergy (zeroExtendedTarget f j) (rows i))) =
      sSup (Set.range (fun j => ∑ i, rowEnergy (f j) (rows i))) := by
  have he : (fun j : Fin (J + 1) => ∑ i, rowEnergy (zeroExtendedTarget f j) (rows i)) =
      Fin.cons 0 (fun j => ∑ i, rowEnergy (f j) (rows i)) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp [zeroExtendedTarget]
  rw [he]
  exact sSup_fin_cons_zero hJ _ (fun j => Finset.sum_nonneg fun i _ => rowEnergy_nonneg _ _)

theorem coefficientL1Norm_cons_zero_bound {N J : ℕ} (f : Fin J → ComplexVector N)
    {s : ℝ} (hs : 0 ≤ s) (hf : ∀ j, coefficientL1Norm (f j) ≤ Real.sqrt s) :
    ∀ j, coefficientL1Norm (zeroExtendedTarget f j) ≤ Real.sqrt s := by
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [zeroExtendedTarget, Fin.cons_zero, coefficientL1Norm_zero]
    exact Real.sqrt_nonneg _
  · simpa only [zeroExtendedTarget, Fin.cons_succ] using hf k

end LeanNumDetect.BoundedRieszConcentration
