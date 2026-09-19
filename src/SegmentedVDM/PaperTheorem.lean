import SegmentedVDM.ClumpBound

/-! The angular-frequency statement of `lem:minsvd_small_clumps` in Two-Scale.
The clump size may be any upper bound. The scalar `dmin` need only be a lower
bound for all periodic pair distances; taking the actual minimum recovers the
paper. The zero-separation boundary is included. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SegmentedVDM

/-- Lemma `lem:minsvd_small_clumps`, with the exact constant and physical
sampling rows `(j D+h)`, `0 ≤ j ≤ M`, `0 ≤ h ≤ m`. -/
theorem small_clumps_singularValue {n s : ℕ} (C : Clumps n s)
    (hn : 0 < n) (hs : 2 ≤ s) (m M D : ℕ) (hm : 0 < m) (hD : m < D)
    (hM : 2*s ≤ M) (δ β τ dmin : ℝ) (hτ : 1 ≤ τ)
    (hβ : 4*(s : ℝ)/m < β) (hphase : τ*D*δ ≤ 1/4)
    (hδmin : 2*Real.pi*δ ≤ dmin) (hminupper : dmin ≤ Real.pi*s/((M : ℝ)*D))
    (x : Fin n → ℝ)
    (hmin : ∀ i j, i ≠ j → ∀ p : ℤ, dmin ≤ |x i-x j-2*Real.pi*p|)
    (hdiam : ∀ i j, C.label i = C.label j → |x i-x j| ≤ 2*Real.pi*τ*δ)
    (hcross : ∀ i j, C.label i ≠ C.label j → ∀ p : ℤ,
      2*Real.pi*β < |x i-x j-2*Real.pi*p|) :
    (2-Real.sqrt (Real.exp 1))^((s : ℝ)/2) *
      Real.sqrt ((M : ℝ)*(m/2+1 : ℕ)/(n*s)) *
      (Real.sqrt 2*M*D*δ/s)^(s-1) ≤
      LeanNumDetect.matrixSingularValue (vandermonde m M D x) (n-1) := by
  have hspos : 0 < s := by omega
  have hsR : (0 : ℝ) < s := by exact_mod_cast hspos
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hτpos : 0 < τ := by linarith
  have hδnonneg : 0 ≤ δ := by
    have hh := hdiam ⟨0,hn⟩ ⟨0,hn⟩ rfl
    simp only [sub_self, abs_zero] at hh
    exact nonneg_of_mul_nonneg_right hh (by positivity : 0 < 2*Real.pi*τ)
  by_cases hδ : 0 < δ
  · have hscale : ((M : ℝ)/s)*D*(2*Real.pi*δ) ≤ Real.pi := by
      have hh := (le_div_iff₀ (by positivity : 0 < (M : ℝ)*D)).mp
        (hδmin.trans hminupper)
      have he : ((M : ℝ)/s)*D*(2*Real.pi*δ) = (2*Real.pi*δ*((M : ℝ)*D))/s := by ring
      rw [he]
      exact (div_le_iff₀ hsR).2 hh
    have hdiam' (i j : Fin n) (hij : C.label i = C.label j) :
        |x i-x j| ≤ Real.pi/(2*D) := by
      apply (hdiam i j hij).trans
      apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ)*D)).2
      nlinarith [mul_le_mul_of_nonneg_left hphase Real.pi_pos.le]
    have hcross' (i j : Fin n) (hij : C.label i ≠ C.label j) (p : ℤ) :=
      (localization_bandwidth hm hspos hβ).le.trans (hcross i j hij p).le
    have hh := clump_singularValue_bound C hn (by omega) m M hM (D : ℝ)
      (2*Real.pi*δ) hDR (by positivity) x clumpBase_pos clumpBase_le_half hscale
      (fun i j hij => by simpa using hδmin.trans (hmin i j hij 0)) hdiam' hcross'
    have he : (M : ℝ)*D*(2*Real.pi*δ)/(Real.sqrt 2*Real.pi*s) =
        Real.sqrt 2*M*D*δ/s := by
      have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      field_simp
      nlinarith
    simpa only [clumpBase, he] using hh
  · have he : δ = 0 := le_antisymm (le_of_not_gt hδ) hδnonneg
    subst δ
    have hsne : s-1 ≠ 0 := by omega
    simp only [mul_zero, zero_div, zero_pow hsne, mul_zero]
    exact LinearMap.singularValues_nonneg _ _

end SegmentedVDM
