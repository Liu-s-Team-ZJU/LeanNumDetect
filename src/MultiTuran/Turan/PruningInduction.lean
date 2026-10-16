import MultiTuran.Turan.GeometricMean

/-! # The geometric-mean pruning induction

This internal assembly theorem states its two analytic inputs explicitly:
a bounded-spectrum geometric estimate and the weak distribution estimate for
actual first-order prunings. Neither input is asserted in this module.
The induction retains the original measurable set at every step and permits
repeated frequencies, zero coefficients and identically zero prunings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LeanNumDetect.MultiTuran
noncomputable section

open ExponentialSumEstimates

/-- A real finite frequency family has actual minimum and maximum members. -/
theorem exists_frequency_extremal_pair {n : ℕ} (hn : 0 < n) (frequency : Fin n → ℝ) :
    ∃ a b : Fin n, ∀ j, frequency a ≤ frequency j ∧ frequency j ≤ frequency b := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  obtain ⟨a,ha,hea⟩ := Finset.exists_mem_eq_inf' hne frequency
  obtain ⟨b,hb,heb⟩ := Finset.exists_mem_eq_sup' hne frequency
  refine ⟨a,b,?_⟩
  intro j
  rw [← hea, ← heb]
  exact ⟨Finset.inf'_le _ (Finset.mem_univ j), Finset.le_sup' _ (Finset.mem_univ j)⟩

/-- Once the explicitly stated analytic inputs hold, actual exponential sums
obey the full geometric-mean estimate with algebraic exponent `n-1`. -/
theorem exponentialSum_geometric_bound_of_pruning
    {E I : Set ℝ} (hE : MeasurableSet E) (hEfin : volume E < ∞) (hEpos : 0 < volume E)
    {A₀ C K : ℝ} (hA₀ : 0 ≤ A₀) (hC : 0 < C)
    (hαK : (volume E).toReal ≤ K) (hCK : 2*Real.exp 1*K ≤ C)
    (hregular : ∀ (m : ℕ), 0 < m → ∀ (frequency : Fin m → ℝ) (c : Fin m → ℂ),
      ExponentialSumEstimates.exponentialSum frequency c ≠ 0 →
        LogRegular (volume.restrict E) (ExponentialSumEstimates.exponentialSum frequency c))
    (hsmall : ∀ (m : ℕ), 0 < m → ∀ (frequency : Fin m → ℝ) (c : Fin m → ℂ),
      (∀ a b, |frequency b-frequency a| ≤ A₀*(m : ℝ)) → ∀ t ∈ I,
        ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ≤
          (C/(volume E).toReal)^(m-1)*
            geometricMean E (ExponentialSumEstimates.exponentialSum frequency c))
    (hweak : ∀ (m : ℕ), 2 ≤ m → ∀ (frequency : Fin m → ℝ) (c : Fin m → ℂ),
      ExponentialSumEstimates.exponentialSum frequency c ≠ 0 → ∀ (a : Fin m) (ρ : ℝ),
      A₀*(m : ℝ) < ρ → (∀ i j, |frequency j-frequency i| ≤ ρ) →
      ∀ u > 0, volume {t | t ∈ E ∧ ExponentialSumEstimates.exponentialSum frequency c t ≠ 0 ∧
        u*‖ExponentialSumEstimates.exponentialSum frequency c t‖ <
          ‖prunedExponentialSum frequency c a ρ t‖} ≤ ENNReal.ofReal (K/u)) :
    ∀ (n : ℕ), 0 < n → ∀ (frequency : Fin n → ℝ) (c : Fin n → ℂ), ∀ t ∈ I,
      ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ≤
        (C/(volume E).toReal)^(n-1)*
          geometricMean E (ExponentialSumEstimates.exponentialSum frequency c) := by
  have hα : 0 < (volume E).toReal := ENNReal.toReal_pos (ne_of_gt hEpos) hEfin.ne
  have hratio : 0 ≤ C/(volume E).toReal := (div_pos hC hα).le
  have hloss : Real.exp 1*K/(volume E).toReal ≤ (C/(volume E).toReal)/2 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).2
    calc
      _ = (2*Real.exp 1*K)/(volume E).toReal := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hCK hα.le
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn frequency c t ht
    cases n with
    | zero => omega
    | succ m =>
      by_cases hzero : ExponentialSumEstimates.exponentialSum frequency c = 0
      · simp only [hzero,Pi.zero_apply,norm_zero,geometricMean_zero,mul_zero,le_refl]
      by_cases hmzero : m = 0
      · subst m
        apply hsmall 1 (by norm_num) frequency c _ t ht
        intro a b
        have hab : a = b := Subsingleton.elim _ _
        rw [hab,sub_self,abs_zero]
        positivity
      have hm : 0 < m := Nat.pos_of_ne_zero hmzero
      have htwo : 2 ≤ m+1 := by omega
      by_cases hbounded : ∀ a b, |frequency b-frequency a| ≤ A₀*((m+1 : ℕ) : ℝ)
      · exact hsmall (m+1) hn frequency c hbounded t ht
      push Not at hbounded
      obtain ⟨i,j,hlargePair⟩ := hbounded
      obtain ⟨a,b,hext⟩ := exists_frequency_extremal_pair hn frequency
      let ρ := frequency b-frequency a
      have hab : frequency a ≤ frequency b := (hext b).1
      have hρall : ∀ i j, |frequency j-frequency i| ≤ ρ := by
        intro i j
        apply abs_le.mpr
        constructor <;> dsimp [ρ] <;> linarith [(hext i).1,(hext i).2,(hext j).1,(hext j).2]
      have hlarge : A₀*((m+1 : ℕ) : ℝ) < ρ := hlargePair.trans_le (hρall i j)
      have hρpos : 0 < ρ := lt_of_le_of_lt (by positivity) hlarge
      have hgap : |frequency b-frequency a| = ρ := abs_of_nonneg (sub_nonneg.mpr hab)
      have hrepr (z : Fin (m+1)) : prunedExponentialSum frequency c z ρ =
          ExponentialSumEstimates.exponentialSum (fun j => frequency (z.succAbove j))
            (prunedCoefficients frequency c z ρ) :=
        funext (fun s => prunedExponentialSum_eq_sum frequency c z ρ s)
      have hgeom (z : Fin (m+1)) :
          geometricMean E (prunedExponentialSum frequency c z ρ) ≤
            ((C/(volume E).toReal)/2)*
              geometricMean E (ExponentialSumEstimates.exponentialSum frequency c) := by
        have hQmeas : Measurable (prunedExponentialSum frequency c z ρ) := by
          rw [hrepr z]
          exact (ExponentialSumEstimates.continuous_exponentialSum _ _).measurable
        have hQreg : prunedExponentialSum frequency c z ρ ≠ 0 →
            LogRegular (volume.restrict E) (prunedExponentialSum frequency c z ρ) := by
          intro hne
          rw [hrepr z]
          exact hregular m hm _ _ (by rwa [← hrepr z])
        have hq := geometricMean_le_of_weak_quotient hE hEfin hEpos
          (ExponentialSumEstimates.continuous_exponentialSum frequency c).measurable hQmeas
          hzero (hregular (m+1) hn frequency c hzero) hQreg hαK
          (hweak (m+1) htwo frequency c hzero z ρ hlarge hρall)
        exact hq.trans (mul_le_mul_of_nonneg_right hloss (geometricMean_nonneg _ _))
      have hind (z : Fin (m+1)) : ‖prunedExponentialSum frequency c z ρ t‖ ≤
          (C/(volume E).toReal)^(m-1)*geometricMean E (prunedExponentialSum frequency c z ρ) := by
        rw [hrepr z]
        exact ih m (Nat.lt_succ_self m) hm _ _ t ht
      have hstep := geometric_pruning_step hratio
        (geometricMean_nonneg E (ExponentialSumEstimates.exponentialSum frequency c))
        (norm_exponentialSum_le_pruned_pair frequency c a b hρpos hgap t)
        (hind a) (hind b) (hgeom a) (hgeom b)
      simpa only [Nat.add_sub_cancel, Nat.sub_add_cancel hm] using hstep

end
end LeanNumDetect.MultiTuran
