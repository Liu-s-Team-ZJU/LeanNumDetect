import MultiTuran.Turan.Unit
import MultiTuran.Turan.AffineTransfer
import MultiTuran.Turan.EssentialTransfer

/-! # The unconditional multidimensional Turán theorem

This is the purely oscillatory convex-body estimate `lem:multidim-turan`
of the manuscript, including the literal essential `L∞` formulation. The
absolute constant is defined explicitly. The scalar measurable-set theorem
and the geometric ray reduction are proved in the imported modules.
-/

set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- One absolute constant works in every dimension and for every finite
purely oscillatory spectrum. No separation assumption occurs. -/
def multidimensionalTuranConstant : ℝ := 2*oneDimensionalTuranConstant

theorem multidimensionalTuranConstant_pos : 0 < multidimensionalTuranConstant :=
  mul_pos (by norm_num) oneDimensionalTuranConstant_pos

/-- The full arbitrary-measurable-set scalar Turán–Nazarov comparison. -/
theorem oneDimensional_turan_comparison :
    OneDimensionalTuranComparison oneDimensionalTuranConstant := by
  apply oneDimensionalTuranComparison_of_unit_norm_bound
  intro n hn frequency c E hE hEsub hEpos M hM hbound t ht
  exact exponentialSum_unit_norm_le_of_bound hn frequency c E hE hEsub hEpos hM hbound t ht

/-- The actual supremum formulation of manuscript `lem:multidim-turan`. -/
theorem exponentialSum_convexBody_supNorm_le {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {B Z : Set (Point d)} (hcompact : IsCompact B) (hconvex : Convex ℝ B)
    (hZ : MeasurableSet Z) (hZB : Z ⊆ B) (hZpos : 0 < volume Z)
    (Y : Fin n → Point d) (c : Fin n → ℂ) :
    setSupNorm (exponentialSum Y c) B ≤
      (multidimensionalTuranConstant*(d : ℝ)*(volume B).toReal/(volume Z).toReal)^(n-1)*
        setSupNorm (exponentialSum Y c) Z :=
  multidim_supNorm_le_of_oneDimensional_comparison oneDimensionalTuranConstant_pos
    oneDimensional_turan_comparison hd hn hcompact hconvex hZ hZB hZpos Y c

/-- Literal essential `L∞` norms, so null exceptional subsets of `Z` do not
change the statement. This is also valid for repeated frequencies. -/
theorem exponentialSum_convexBody_eLpNorm_top_le {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {B Z : Set (Point d)} (hcompact : IsCompact B) (hconvex : Convex ℝ B)
    (hZ : MeasurableSet Z) (hZB : Z ⊆ B) (hZpos : 0 < volume Z)
    (Y : Fin n → Point d) (c : Fin n → ℂ) :
    eLpNorm (exponentialSum Y c) ∞ (volume.restrict B) ≤
      ENNReal.ofReal ((multidimensionalTuranConstant*(d : ℝ)*(volume B).toReal/
        (volume Z).toReal)^(n-1))*eLpNorm (exponentialSum Y c) ∞ (volume.restrict Z) :=
  multidim_eLpNorm_top_le_of_oneDimensional_comparison oneDimensionalTuranConstant_pos
    oneDimensional_turan_comparison hd hn hcompact hconvex hZ hZB hZpos Y c

/-- The filling-ratio specialization used by the segmented-array theorem. -/
theorem aperture_supNorm_turan {d n : ℕ} (G : SegmentedGrid d) (hn : 0 < n)
    (Y : Fin n → Point d) (c : Fin n → ℂ) :
    setSupNorm (exponentialSum Y c) G.apertureBox ≤
      (multidimensionalTuranConstant*(d : ℝ)/G.fillingRatio)^(n-1)*
        setSupNorm (exponentialSum Y c) G.thickening :=
  aperture_supNorm_le_of_oneDimensional_comparison oneDimensionalTuranConstant_pos
    oneDimensional_turan_comparison G hn Y c

/-- The absolute-constant quantifier in the article, with no scalar
comparison or analytic estimate left as an assumption. -/
theorem exists_multidimensionalTuranConstant :
    ∃ C_T : ℝ, 0 < C_T ∧ ∀ (d n : ℕ), 0 < d → 0 < n →
      ∀ (B Z : Set (Point d)), IsCompact B → Convex ℝ B → MeasurableSet Z → Z ⊆ B →
        0 < volume Z → ∀ (Y : Fin n → Point d) (c : Fin n → ℂ),
          setSupNorm (exponentialSum Y c) B ≤
            (C_T*(d : ℝ)*(volume B).toReal/(volume Z).toReal)^(n-1)*
              setSupNorm (exponentialSum Y c) Z := by
  exact ⟨multidimensionalTuranConstant,multidimensionalTuranConstant_pos,
    fun _ _ hd hn _ _ hcompact hconvex hZ hZB hZpos Y c =>
      exponentialSum_convexBody_supNorm_le hd hn hcompact hconvex hZ hZB hZpos Y c⟩

end
end LeanNumDetect.MultiTuran
