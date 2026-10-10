import General.Fourier.ConnectedCubeBasis
import General.Fourier.TranslatedBasisThickness

/-! Subspace thickness from a connected quantitative cube basis. -/

set_option autoImplicit false

open scoped BigOperators

namespace LeanNumDetect.ConnectedBasisBounds
open TranslatedBasisThickness

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Concrete translated-basis thickness from the connected prefix certificate. -/
theorem CubeBasisPrefix.thick_card
    {d L Q n : ℕ} (hn : 1 ≤ n) (hbudget : 2 * n * Q ≤ L)
    {f : CubePoint d L → E} {c K θ : ℝ}
    (basis : CubeBasisPrefix d L Q n f c) (hK : 0 < K) (hθ : θ < c / K)
    (T : CubeTranslations d L basis.width → E →L[ℂ] E)
    (htrans : ∀ t j, f (translatedPoint basis.point basis.width basis.point_le_width t j) =
      T t (f (basis.point j)))
    (hconorm : ∀ t v, ‖v‖ ≤ K * ‖T t v‖)
    (U : Submodule ℂ E) [FiniteDimensional ℂ U]
    [DecidablePred (fun p => FarFromSubspace (f p) U θ)] :
    (n + 1) * (n - Module.finrank ℂ U) * Fintype.card (CubePoint d L) ≤
      2 * n ^ 2 * Fintype.card {p : CubePoint d L // FarFromSubspace (f p) U θ} := by
  classical
  have hw : 2 * n * (∑ l, basis.width l) ≤ (n - 1) * L := by
    calc
      2 * n * (∑ l, basis.width l) ≤ 2 * n * ((n - 1) * Q) :=
        Nat.mul_le_mul_left _ basis.total_width
      _ = (n - 1) * (2 * n * Q) := by ring
      _ ≤ (n - 1) * L := Nat.mul_le_mul_left _ hbudget
  have hnQ : n * Q ≤ L := by
    have hh : n * Q ≤ 2 * n * Q := Nat.mul_le_mul_right Q (by omega)
    exact hh.trans hbudget
  have hg : ∀ l, basis.width l ≤ L := by
    intro l
    have hh : basis.width l ≤ ∑ k, basis.width k :=
      Finset.single_le_sum (fun k hk => Nat.zero_le _) (Finset.mem_univ _)
    have hN : (n - 1) * Q ≤ n * Q := Nat.mul_le_mul_right _ (by omega)
    exact hh.trans (basis.total_width.trans (hN.trans hnQ))
  apply cube_thick_card hn f basis.point basis.width basis.point_le_width hg hw U hθ
  intro t
  have h := basis.lower.map_lower (T t) hK (hconorm t)
  simpa only [htrans t] using h

end Normed

end LeanNumDetect.ConnectedBasisBounds

namespace LeanNumDetect.TranslatedBasisThickness
export ConnectedBasisBounds
  (CubeBasisPrefix CubeBasisPrefix.initial CubeBasisPrefix.append
   CubeBasisPrefix.thick_card exists_connected_cube_basis)
end LeanNumDetect.TranslatedBasisThickness
