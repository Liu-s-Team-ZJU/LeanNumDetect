import MultiTuran.Turan.EffectiveProduct
import MultiTuran.Turan.EffectiveRoots
import Mathlib.Data.Fin.Tuple.Sort

/-! Effective-degree cancellation for actual finite complex root families. -/

set_option autoImplicit false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran
noncomputable section

theorem exp_neg_effectiveLogPotential_le_injective_product {N m : ℕ}
    (d : ℕ) (z : Fin N → ℂ) (e : Fin m → Fin N)
    (he : Function.Injective e) (hm : m ≤ d) (x : ℝ)
    (hroot : ∀ j, (x : ℂ) ≠ z j) :
    Real.exp (-effectiveLogPotential d z x) ≤
      ∏ j, min 1 ‖(x : ℂ)-z (e j)‖ := by
  let s := Finset.univ.map ⟨e,he⟩
  have hs : s.card ≤ d := by simpa [s] using hm
  have h := exp_neg_effectiveLogPotential_le_product d z s hs x (fun j _ => hroot j)
  simpa only [s,Finset.prod_map,Function.Embedding.coeFn_mk] using h

/-- No ordering of roots is part of the hypotheses: sorting is performed
inside the proof and only a finite selection of `d` roots is retained. -/
theorem rootProduct_lower_of_scale_growth {N : ℕ} (d : ℕ) (z : Fin N → ℂ)
    (x H : ℝ) (hH : 0 ≤ H) (hroot : ∀ j, (x : ℂ) ≠ z j)
    (hgrowth : ∀ r : ℝ, 0 < r → r ≤ 1 →
      Real.exp (-H)*r^d ≤ ∏ j, (r+min 1 ‖(x : ℂ)-z j‖)) :
    (Real.exp (-H)/(2 : ℝ)^N)*Real.exp (-effectiveLogPotential d z x) ≤
      ∏ j, min 1 ‖(x : ℂ)-z j‖ := by
  have hfactor : Real.exp (-H)/(2 : ℝ)^N ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hH)).trans (one_le_pow₀ (by norm_num))
  by_cases hNd : N ≤ d
  · have hselected := exp_neg_effectiveLogPotential_le_product d z Finset.univ
      (by simpa using hNd) x (fun j _ => hroot j)
    exact (mul_le_of_le_one_left (Real.exp_nonneg _) hfactor).trans hselected
  · obtain ⟨k,hN⟩ : ∃ k, N=d+(k+1) := ⟨N-d-1,by omega⟩
    subst N
    let a : Fin (d+(k+1)) → ℝ := fun j => min 1 ‖(x : ℂ)-z j‖
    let σ := Tuple.sort a
    have ha : ∀ j, 0 < a j := fun j => lt_min (by norm_num)
      (norm_pos_iff.mpr (sub_ne_zero.mpr (hroot j)))
    have hsorted : Monotone (a ∘ σ) := Tuple.monotone_sort a
    have hprod : ∀ r : ℝ, (∏ j, (r+a (σ j)))=∏ j, (r+a j) :=
      fun r => Equiv.prod_comp σ (fun j => r+a j)
    have hgrowth' : ∀ r : ℝ, 0 < r → r ≤ 1 →
        Real.exp (-H)*r^d ≤ ∏ j, (r+(a ∘ σ) j) := by
      intro r hr hr1
      simpa only [Function.comp_apply,hprod] using hgrowth r hr hr1
    let e : Fin d → Fin (d+(k+1)) := fun j => σ (j.castAdd (k+1))
    have he : Function.Injective e := σ.injective.comp (Fin.castAdd_injective d (k+1))
    have hb := exp_neg_effectiveLogPotential_le_injective_product d z e he le_rfl x hroot
    have h := zeroProduct_lower_of_scale_growth d k (a ∘ σ) (fun j => ha (σ j))
      hsorted (fun j => min_le_left _ _) H hgrowth' hb
    simpa only [Function.comp_apply,Equiv.prod_comp] using h

end
end LeanNumDetect.MultiTuran
