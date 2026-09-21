import General.Fourier.DisjointParseval
set_option autoImplicit false
open scoped BigOperators
namespace LeanNumDetect

theorem norm_sum_sq_real {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    ‖∑ i, z i‖^2 = ∑ i, ∑ j, (star (z i) * z j).re := by
  have hh : ((‖∑ i, z i‖^2 : ℝ) : ℂ) = ∑ i, ∑ j, star (z i) * z j := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul]
    simp only [Finset.mul_sum, Complex.star_def]
  have he := congrArg Complex.re hh
  simpa only [Complex.ofReal_re, Complex.re_sum] using he

/-- Weighted orthogonality decouples the full series, even for signed weights. -/
theorem weighted_sum_energy_hasSum {ι κ : Type*} [Fintype ι]
    (w : κ → ℝ) (v : ι → κ → ℂ) (E : ι → ℝ)
    (hdiag : ∀ i, HasSum (fun k => w k * ‖v i k‖^2) (E i))
    (hcross : ∀ i j, i ≠ j → HasSum (fun k => w k * (star (v i k) * v j k).re) 0) :
    HasSum (fun k => w k * ‖∑ i, v i k‖^2) (∑ i, E i) := by
  classical
  have hp (i j : ι) : HasSum (fun k => w k * (star (v i k)*v j k).re)
      (if j = i then E i else 0) := by
    by_cases he : j = i
    · subst j
      simpa only [if_pos rfl, if_true, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
        Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hdiag i
    · rw [if_neg he]
      exact hcross i j (Ne.symm he)
  have hh := hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_sum (s := Finset.univ) (fun j _ => hp i j))
  simpa only [norm_sum_sq_real, Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hh
/-- A signed weight bounded by one on a finite block and nonpositive outside gives
an upper bound by the unweighted block energy. -/
theorem weighted_series_le_block {κ : Type*} (S : Finset κ) (w E : κ → ℝ) (W : ℝ)
    (hE : ∀ k, 0 ≤ E k) (hin : ∀ k ∈ S, w k ≤ 1)
    (hout : ∀ k ∉ S, w k ≤ 0) (hsum : HasSum (fun k => w k*E k) W) :
    W ≤ ∑ k ∈ S, E k := by
  have hh := hsum.neg.summable.sum_le_tsum S (fun k hk =>
    neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (hout k hk) (hE k)))
  rw [hsum.neg.tsum_eq, Finset.sum_neg_distrib] at hh
  have he : W ≤ ∑ k ∈ S, w k*E k := by linarith
  exact he.trans (Finset.sum_le_sum (fun k hk => mul_le_of_le_one_left (hE k) (hin k hk)))

/-- A nonnegative full-lattice majorant which is at least one on a finite
block gives an upper bound for the unweighted block energy. -/
theorem block_le_weighted_series {κ : Type*} (S : Finset κ)
    (w E : κ → ℝ) (W : ℝ)
    (hE : ∀ k, 0 ≤ E k) (hin : ∀ k ∈ S, 1 ≤ w k)
    (hw : ∀ k, 0 ≤ w k) (hsum : HasSum (fun k => w k * E k) W) :
    ∑ k ∈ S, E k ≤ W := by
  have hfinite : ∑ k ∈ S, E k ≤ ∑ k ∈ S, w k * E k :=
    Finset.sum_le_sum fun k hk =>
      le_mul_of_one_le_left (hE k) (hin k hk)
  have htail := hsum.summable.sum_le_tsum S fun k _ =>
    mul_nonneg (hw k) (hE k)
  rw [hsum.tsum_eq] at htail
  exact hfinite.trans htail
end LeanNumDetect
