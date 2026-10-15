import MultiTuran.TuranBlaschkeZeroCount
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.List.OfFn

/-! # Finite enumeration of analytic zeros with their actual multiplicities -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Topology
open Set Metric Filter

namespace LeanNumDetect.MultiTuran
noncomputable section

theorem zeroMultiplicity_eq_sum {N : ℕ} (roots : Fin N → ℂ) (z : ℂ) :
    zeroMultiplicity roots z = ∑ i, if roots i=z then 1 else 0 := by
  classical
  simp [zeroMultiplicity]

theorem zeroMultiplicity_get (l : List ℂ) (z : ℂ) :
    zeroMultiplicity l.get z = l.count z := by
  classical
  rw [zeroMultiplicity_eq_sum]
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, Fin.sum_univ_succ, List.get_cons_zero,
      List.get_cons_succ]
    change (if a=z then 1 else 0) +
      (∑ i : Fin l.length, if l.get i=z then 1 else 0) = (a::l).count z
    rw [ih]
    by_cases ha : a=z <;> simp [ha,add_comm]

theorem exists_roots_of_finite_multiplicity (m : ℂ → ℕ) (hm : (Function.support m).Finite) :
    ∃ N : ℕ, ∃ roots : Fin N → ℂ, ∀ z, zeroMultiplicity roots z = m z := by
  classical
  let S : Multiset ℂ := (Finsupp.ofSupportFinite m hm).toMultiset
  let l : List ℂ := S.toList
  refine ⟨l.length,l.get,?_⟩
  intro z
  rw [zeroMultiplicity_get]
  change S.toList.count z = m z
  rw [← Multiset.coe_count,Multiset.coe_toList]
  exact Finsupp.count_toMultiset _ _

theorem zeroMultiplicity_pos_at_root {N : ℕ} (roots : Fin N → ℂ) (i : Fin N) :
    0 < zeroMultiplicity roots (roots i) := by
  classical
  unfold zeroMultiplicity
  exact Finset.card_pos.mpr ⟨i,by simp⟩

end
end LeanNumDetect.MultiTuran
