import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic
import General.Finite.AlmostOrthogonalEnergy

/-! A weighted quadratic cross estimate which keeps the clump sizes in the
global coefficient, instead of replacing every size by its maximum. -/

set_option autoImplicit false
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect.WeightedClumpCrossBounds
noncomputable section

theorem nonnegative_cross_quadratic_bound {A : ℕ} (s x : Fin A → ℝ)
    (_hs : ∀ a, 0≤s a) (hx : ∀ a, 0≤x a) :
    (∑ a : Fin A, ∑ b : Fin A,
      (s a*s b+((s a)^2+(s b)^2)/2)*x a*x b) ≤
      ((∑ a : Fin A, (s a)^2)+Real.sqrt ((A : ℝ)*(∑ a : Fin A, (s a)^4)))*
        (∑ a : Fin A, (x a)^2) := by
  let U := ∑ a : Fin A, s a*x a
  let R := ∑ a : Fin A, (s a)^2*x a
  let T := ∑ a : Fin A, x a
  let S2 := ∑ a : Fin A, (s a)^2
  let S4 := ∑ a : Fin A, (s a)^4
  let X2 := ∑ a : Fin A, (x a)^2
  have hS4 : 0≤S4 := Finset.sum_nonneg (fun a _ => by positivity)
  have hX2 : 0≤X2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hR : 0≤R := Finset.sum_nonneg (fun a _ => mul_nonneg (sq_nonneg _) (hx a))
  have hT : 0≤T := Finset.sum_nonneg (fun a _ => hx a)
  have hU : U^2≤S2*X2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ s x
  have hR2 : R^2≤S4*X2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => (s a)^2) x
    simpa only [← pow_mul, Nat.mul_comm 2 2] using h
  have hT2 : T^2≤(A : ℝ)*X2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin A => (1 : ℝ)) x
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] using h
  have hRT : R*T≤Real.sqrt ((A : ℝ)*S4)*X2 := by
    apply (sq_le_sq₀ (mul_nonneg hR hT) (by positivity)).1
    calc
      (R*T)^2 = R^2*T^2 := mul_pow _ _ _
      _ ≤ (S4*X2)*((A : ℝ)*X2) :=
        mul_le_mul hR2 hT2 (sq_nonneg _) (mul_nonneg hS4 hX2)
      _ = (Real.sqrt ((A : ℝ)*S4)*X2)^2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        ring
  have he : (∑ a : Fin A, ∑ b : Fin A,
      (s a*s b+((s a)^2+(s b)^2)/2)*x a*x b)=U^2+R*T := by
    have hinner (a : Fin A) : (∑ b : Fin A,
        (s a*s b+((s a)^2+(s b)^2)/2)*x a*x b)=
        (s a*x a)*U+((s a)^2*x a*T)/2+(x a*R)/2 := by
      calc
        _ = ∑ b : Fin A, ((s a*x a)*(s b*x b)+
            ((s a)^2*x a)*x b/2+x a*((s b)^2*x b)/2) := by
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
          rfl
    simp_rw [hinner]
    simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    change U*U+(R*T)/2+(T*R)/2=U^2+R*T
    ring
  rw [he]
  change U^2+R*T≤(S2+Real.sqrt ((A : ℝ)*S4))*X2
  nlinarith only [hU, hRT]

theorem nonnegative_offDiagonal_product_bound {A : ℕ} (x : Fin A → ℝ) :
    (∑ a : Fin A, ∑ b : Fin A, if b=a then 0 else x a*x b) ≤
      ((A : ℝ)-1)*(∑ a : Fin A, (x a)^2) := by
  classical
  have he (a b : Fin A) : (if b=a then 0 else x a*x b)=
      x a*x b-(if b=a then (x a)^2 else 0) := by
    by_cases h : b=a
    · simp [h]
      ring
    · simp [h]
  simp_rw [he]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    ← Finset.mul_sum, ← Finset.sum_mul]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin A => (1 : ℝ)) x
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hc
  nlinarith only [hc]

/-- Size-dependent pair bounds assemble globally; the constant perturbation
part pays only for the other clumps, while the size part uses two weighted
Cauchy--Schwarz estimates. -/
theorem sizeWeighted_clump_sum_energy_lower {A : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : Fin A → E) (s : Fin A → ℝ) (hs : ∀ a, 0≤s a)
    {α β : ℝ} (hα : 0≤α) (hβ : 0≤β)
    (hcross : ∀ a b, a≠b → ‖⟪v a,v b⟫_ℂ‖ ≤
      (α*(s a*s b+((s a)^2+(s b)^2)/2)+β)*‖v a‖*‖v b‖) :
    (1-α*((∑ a : Fin A, (s a)^2)+
        Real.sqrt ((A : ℝ)*(∑ a : Fin A, (s a)^4)))-β*((A : ℝ)-1))*
      (∑ a : Fin A, ‖v a‖^2) ≤ ‖∑ a : Fin A, v a‖^2 := by
  classical
  let x : Fin A → ℝ := fun a => ‖v a‖
  let w : Fin A → Fin A → ℝ := fun a b => s a*s b+((s a)^2+(s b)^2)/2
  let C := (∑ a : Fin A, (s a)^2)+Real.sqrt ((A : ℝ)*(∑ a : Fin A, (s a)^4))
  let X2 := ∑ a : Fin A, (x a)^2
  have hx (a : Fin A) : 0≤x a := norm_nonneg _
  have hw (a b : Fin A) : 0≤w a b :=
    add_nonneg (mul_nonneg (hs a) (hs b))
      (div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num))
  have hp (a b : Fin A) :
      |(⟪v a,v b⟫_ℂ).re-(if b=a then (x a)^2 else 0)| ≤
        if b=a then 0 else (α*w a b+β)*x a*x b := by
    by_cases hab : b=a
    · subst b
      have hd : (⟪v a,v a⟫_ℂ).re=(x a)^2 :=
        (norm_sq_eq_re_inner (𝕜 := ℂ) (v a)).symm
      simp only [ite_true, hd, sub_self, abs_zero, le_refl]
    · rw [if_neg hab, if_neg hab, sub_zero]
      exact (Complex.abs_re_le_norm _).trans (hcross a b (Ne.symm hab))
  have hall := nonnegative_cross_quadratic_bound s x hs hx
  change (∑ a : Fin A, ∑ b : Fin A, w a b*x a*x b)≤C*X2 at hall
  have hsumw : (∑ a : Fin A, ∑ b : Fin A,
      if b=a then 0 else w a b*x a*x b)≤C*X2 := by
    apply LE.le.trans _ hall
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    by_cases hab : b=a
    · simp only [if_pos hab]
      exact mul_nonneg (mul_nonneg (hw a b) (hx a)) (hx b)
    · simp only [if_neg hab, le_refl]
  have hsumx := nonnegative_offDiagonal_product_bound x
  have hb : (∑ a : Fin A, ∑ b : Fin A,
      if b=a then 0 else (α*w a b+β)*x a*x b) ≤
      (α*C+β*((A : ℝ)-1))*X2 := by
    have he (a b : Fin A) : (if b=a then 0 else (α*w a b+β)*x a*x b)=
        α*(if b=a then 0 else w a b*x a*x b)+
          β*(if b=a then 0 else x a*x b) := by
      by_cases hab : b=a <;> simp only [hab, if_true, if_false] <;> ring
    simp_rw [he]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left hsumw hα
    have h2 := mul_le_mul_of_nonneg_left hsumx hβ
    dsimp [X2]
    nlinarith only [h1, h2]
  have habs : |‖∑ a : Fin A, v a‖^2-X2|≤(α*C+β*((A : ℝ)-1))*X2 := by
    have he : (∑ a : Fin A, ∑ b : Fin A,
        ((⟪v a,v b⟫_ℂ).re-(if b=a then (x a)^2 else 0)))=
        ‖∑ a : Fin A, v a‖^2-X2 := by
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [AlmostOrthogonalEnergy.clump_sum_norm_sq]
    rw [← he]
    exact ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun a _ => (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun b _ => hp a b))))).trans hb
  have hlo := (abs_le.mp habs).1
  change (1-α*C-β*((A : ℝ)-1))*X2≤‖∑ a : Fin A, v a‖^2
  nlinarith only [hlo]

end
end LeanNumDetect.WeightedClumpCrossBounds
