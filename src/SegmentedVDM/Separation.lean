import General.Finite.FiniteSorting
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SegmentedVDM

/-- The actual minimum separation is attained after taking the nearest integer
for each of the finitely many pairs. -/
theorem exists_minimum_separation {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    {γ : ℝ} (hγ : 0 < γ)
    (hsep : ∀ i j, i ≠ j → ∀ p : ℤ, γ ≤ |x i-x j-p|) :
    ∃ δ : ℝ, γ ≤ δ ∧ 0 < δ ∧
      (∀ i j, i ≠ j → ∀ p : ℤ, δ ≤ |x i-x j-p|) ∧
      ∃ i j, i ≠ j ∧ ∃ p : ℤ, δ = |x i-x j-p| := by
  classical
  let S := (Finset.univ : Finset (Fin n)).offDiag
  have hS : S.Nonempty := by
    refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
    simp [S, Finset.mem_offDiag]
  let f (ij : Fin n × Fin n) := |x ij.1-x ij.2-round (x ij.1-x ij.2)|
  obtain ⟨ij, hij, hmin⟩ := Finset.exists_min_image S f hS
  have hne : ij.1 ≠ ij.2 := (Finset.mem_offDiag.mp hij).2.2
  have hlow := hsep ij.1 ij.2 hne (round (x ij.1-x ij.2))
  refine ⟨f ij, hlow, hγ.trans_le hlow, ?_, ij.1, ij.2, hne, _, rfl⟩
  intro i j h p
  exact (hmin (i,j) (by simp [S, h])).trans (round_le (x i-x j) p)

/-- Separation by `2/N` in the unit interval implies fewer than `N` nodes.
This verifies the rectangularity assumption in the original large-sieve result. -/
theorem separated_card_lt_samples {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hsep : ∀ i j, i ≠ j → 2/(N : ℝ) ≤ |x i-x j|) : n < N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hinj : Function.Injective x := by
    intro i j h
    by_contra hh
    have hs := hsep i j hh
    rw [h, sub_self, abs_zero] at hs
    have hp : 0 < 2/(N : ℝ) := by positivity
    linarith
  obtain ⟨e, he⟩ := LeanNumDetect.exists_strictMono_reordering x hinj
  have hstep (j : ℕ) (hj : j < n) : (j : ℝ)*(2/(N : ℝ)) ≤ x (e ⟨j,hj⟩) := by
    induction j with
    | zero => simpa using (hx (e ⟨0,hj⟩)).1
    | succ j ih =>
      have hj' : j < n := by omega
      have hprev := ih hj'
      have hlt : (⟨j,hj'⟩ : Fin n) < ⟨j+1,hj⟩ := by simp
      have horder := he hlt
      have hne : e ⟨j+1,hj⟩ ≠ e ⟨j,hj'⟩ :=
        fun h => (ne_of_gt hlt) (e.injective h)
      have hs := hsep (e ⟨j+1,hj⟩) (e ⟨j,hj'⟩) hne
      rw [abs_of_pos (sub_pos.mpr horder)] at hs
      push_cast
      linarith
  have hlast := (hstep (n-1) (by omega)).trans_lt (hx (e ⟨n-1,by omega⟩)).2
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at hlast
  have hreal : (n : ℝ) < N := by
    have hh : ((n : ℝ)-1)*2 < N := by
      have h := (div_lt_iff₀ hNp).mp (show ((n : ℝ)-1)*2/(N : ℝ) < 1 by
        simpa only [mul_div_assoc] using hlast)
      simpa only [one_mul] using h
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact_mod_cast hreal

end SegmentedVDM
