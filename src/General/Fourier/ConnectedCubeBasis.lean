import General.Fourier.TranslatedBasisThickness
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false

open scoped BigOperators

namespace LeanNumDetect.TranslatedBasisThickness

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A quantitative cube basis with controlled total coordinate width. -/
structure CubeBasisPrefix (d L Q r : ℕ) (f : CubePoint d L → E) (c : ℝ) where
  point : Fin r → CubePoint d L
  width : Fin d → ℕ
  point_le_width : ∀ j l, (point j l).val ≤ width l
  total_width : (∑ l, width l) ≤ (r - 1) * Q
  zero_mem : ∃ j, point j = fun _ => 0
  lower : L1LowerBound (fun j => f (point j)) c

/-- The initial connected prefix consists of the zero row. -/
def CubeBasisPrefix.initial {d L Q : ℕ} (f : CubePoint d L → E) (c : ℝ)
    (hc : c ≤ ‖f (fun _ => 0)‖) : CubeBasisPrefix d L Q 1 f c where
  point := fun _ _ => 0
  width := fun _ => 0
  point_le_width := by simp
  total_width := by simp
  zero_mem := ⟨0, rfl⟩
  lower := by
    intro a
    simp only [Fin.sum_univ_one, norm_smul]
    exact mul_le_mul_of_nonneg_right hc (norm_nonneg (a 0)) |>.trans_eq (mul_comm _ _)

/-- Appending a coarse border point increases total width by at most `Q`. -/
def CubeBasisPrefix.append {d L Q r : ℕ} {f : CubePoint d L → E} {c c' : ℝ}
    (basis : CubeBasisPrefix d L Q r f c) (hr : 1 ≤ r)
    (j : Fin r) (l : Fin d) (q : ℕ) (hq : q ≤ Q)
    (hadd : (basis.point j l).val + q ≤ L)
    (hlower : L1LowerBound
      (fun i : Fin (r + 1) => f (Fin.cons (α := fun _ => CubePoint d L) (addCubeCoordinate (basis.point j) l q hadd) basis.point i)) c') :
    CubeBasisPrefix d L Q (r + 1) f c' where
  point := Fin.cons (α := fun _ => CubePoint d L) (addCubeCoordinate (basis.point j) l q hadd) basis.point
  width := Function.update basis.width l (basis.width l + q)
  point_le_width := by
    intro i k
    cases i using Fin.cases with
    | zero =>
      simpa using addCubeCoordinate_le_updated_width (basis.point j) basis.width
        (basis.point_le_width j) l q hadd k
    | succ i =>
      exact (basis.point_le_width i k).trans (le_updated_width basis.width l q k)
  total_width := by
    rw [sum_updated_width]
    have hs := basis.total_width
    have he : (r - 1) * Q + Q = r * Q := by
      calc
        (r - 1) * Q + Q = (r - 1 + 1) * Q := by ring
        _ = r * Q := by rw [Nat.sub_add_cancel hr]
    simpa only [Nat.add_sub_cancel] using (show (∑ k, basis.width k) + q ≤ r * Q by omega)
  zero_mem := by
    obtain ⟨i, hi⟩ := basis.zero_mem
    exact ⟨i.succ, by simpa using hi⟩
  lower := hlower


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


section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]

/-- Connected cube-basis extraction from isotropy and bounded coarse shifts. -/
theorem exists_connected_cube_basis
    {d L Q n : ℕ} [NeZero d] (hn : 1 ≤ n) (hbudget : n * Q ≤ L)
    (f : CubePoint d L → E) (hdim : Module.finrank ℂ E = n)
    {c₀ M H B : ℝ} (hc₀ : 0 < c₀) (hM : 0 < M) (hH : 1 ≤ H)
    (hc₀M : c₀ ≤ M) (hB : 2 ≤ B)
    (hzero : c₀ ≤ ‖f (fun _ => 0)‖) (hrow : ∀ p, ‖f p‖ ≤ M)
    (hiso : ∀ u : E, (∑ p, ‖inner ℂ u (f p)‖ ^ 2) =
      (Fintype.card (CubePoint d L) : ℝ) * ‖u‖ ^ 2)
    (A : (Fin d × Fin (Q + 1)) → E →L[ℂ] E)
    (hA : ∀ s x, ‖A s x‖ ≤ B * ‖x‖)
    (hshift : ∀ (p : CubePoint d L) (l : Fin d) (q : Fin (Q + 1))
      (hadd : (p l).val + q.val ≤ L),
      f (addCubeCoordinate p l q.val hadd) = A (l, q) (f p))
    (e : ℕ)
    (hreach : ∀ p, ∃ path : BoundedShiftPath A (f (fun _ => 0)) (f p) M,
      path.length ≤ e)
    (hsize : B ^ e * M ≤ H) :
    Nonempty (CubeBasisPrefix d L Q n f (basisCoefficient c₀ M H (n - 1))) := by
  classical
  have aux : ∀ r < n,
      Nonempty (CubeBasisPrefix d L Q (r + 1) f (basisCoefficient c₀ M H r)) := by
    intro r
    induction r with
    | zero =>
      intro hr
      exact ⟨CubeBasisPrefix.initial f c₀ hzero⟩
    | succ r ih =>
      intro hr
      obtain ⟨basis⟩ := ih (by omega)
      let c := basisCoefficient c₀ M H r
      have hc : 0 < c := basisCoefficient_pos hc₀ hM (show 0 < H by linarith) r
      have hcM : c ≤ M := (basisCoefficient_le_initial hc₀ hM hH hc₀M r).trans hc₀M
      let U : Submodule ℂ E := Submodule.span ℂ (Set.range (fun j => f (basis.point j)))
      have hproper : U ≠ ⊤ := by
        intro htop
        have hh : Module.finrank ℂ E ≤ Fintype.card (Fin (r + 1)) :=
          finrank_le_of_span_eq_top htop
        rw [hdim, Fintype.card_fin] at hh
        omega
      have hz : f (fun _ => 0) ∈ U := by
        obtain ⟨j, hj⟩ := basis.zero_mem
        apply Submodule.subset_span
        exact ⟨j, congrArg f hj⟩
      have hvalid : ∀ (s : Fin d × Fin (Q + 1)) (j : Fin (r + 1)),
          (basis.point j s.1).val + s.2.val ≤ L := by
        intro s j
        have hq : s.2.val ≤ Q := by omega
        have hg := basis.point_le_width j s.1
        have hgs : basis.width s.1 ≤ ∑ l, basis.width l :=
          Finset.single_le_sum (fun l hl => Nat.zero_le _) (Finset.mem_univ _)
        have hsum := basis.total_width
        have hmul : (r + 1) * Q ≤ n * Q := Nat.mul_le_mul_right Q (by omega)
        simp only [Nat.add_sub_cancel] at hsum
        nlinarith
      obtain ⟨s, j, hres⟩ := exists_large_basis_border
        (fun j => f (basis.point j)) f (f (fun _ => 0)) hc hB hM.le
        (show 0 < H by linarith) basis.lower A hA U rfl hproper hz hiso e hreach hsize
      let p := addCubeCoordinate (basis.point j) s.1 s.2.val (hvalid s j)
      have hp : f p = A s (f (basis.point j)) := hshift _ _ _ _
      have ht : 0 ≤ c / H := by positivity
      have htM : c / H ≤ M := by
        apply (div_le_iff₀ (by linarith : 0 < H)).mpr
        nlinarith
      have hmem : ∀ j, f (basis.point j) ∈ U := by
        intro j
        exact Submodule.subset_span ⟨j, rfl⟩
      have hres' : c / H ≤ ‖Uᗮ.starProjection (f p)‖ := by rw [hp]; exact hres
      have hnew := basis.lower.cons_of_subspace (f p) U hc.le ht hM hcM htM
        (hrow p) hmem hres'
      have hcoef : c * (c / H) / (3 * M) = basisCoefficient c₀ M H (r + 1) := by
        simp only [basisCoefficient]
        change c * (c / H) / (3 * M) = c ^ 2 / (3 * M * H)
        field_simp
      rw [hcoef] at hnew
      have hnew' : L1LowerBound (fun i : Fin (r + 2) => f (Fin.cons (α := fun _ => CubePoint d L) p basis.point i))
          (basisCoefficient c₀ M H (r + 1)) := by
        convert hnew using 1
        funext i
        cases i using Fin.cases <;> simp
      exact ⟨basis.append (by omega) j s.1 s.2.val (by omega) (hvalid s j) hnew'⟩
  have h := aux (n - 1) (by omega)
  simpa only [Nat.sub_add_cancel hn] using h

end InnerProduct

end LeanNumDetect.TranslatedBasisThickness
