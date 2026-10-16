import MultiTuran.MultiClump.ClumpDerivative
import MultiTuran.Norming.NormingConstants
import MultiTuran.Norming.ProductDiscretization
import MultiTuran.Norming.ProductRestriction
import MultiTuran.Preliminaries.Translation

/-! # Riemann norming for one clump of arbitrary spectral radius

The actual coordinate derivatives and exact product Nikolskii coefficient
bound the oscillation on every measured unit cell. There is no aperture
localization hypothesis. The final norming theorem and its translated
version use only the explicit two-term sampling threshold.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

/-- Retaining the exact `π/2` coefficient instead of replacing it by `2`. -/
theorem productNikolskiiCoefficient_sq_le_exact {d n : ℕ} (G : SegmentedGrid d) :
    (∏ q, Real.pi * n / (2 * Real.sqrt (G.coordinateMinLength q : ℝ))) ^ 2 ≤
      (Real.pi / 2)^(2*d) * (n : ℝ)^(2*d) / (G.minThickLength : ℝ)^d := by
  rw [productNikolskiiCoefficient_sq]
  have hL : (0 : ℝ) < G.minThickLength := by exact_mod_cast minThickLength_pos G
  calc
    _ ≤ (Real.pi * n / 2)^(2*d) / (G.minThickLength : ℝ)^d :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hL _)
        (minThickLength_pow_le_product G)
    _ = _ := by rw [show Real.pi * (n : ℝ) / 2 = (Real.pi / 2) * n by ring, mul_pow]

/-- Genuine coordinate oscillation on an actual measured unit cell, for
frequencies bounded by an arbitrary nonnegative clump radius. -/
theorem exponentialSum_cell_coordinate_lipschitz_of_frequency_bound {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (hd : 2 ≤ d) (hn : 0 < n)
    {τ : ℝ} (hτ : 0 ≤ τ) (hY : ∀ j q, |Y j q| ≤ τ)
    (c : Fin n → ℂ) (k : G.Row) (q : Fin d) (z : Point d)
    (hz : z ∈ G.unitCell k) {u : ℝ}
    (hu : u ∈ Icc (G.rowPoint k q) (G.rowPoint k q + 1)) :
    |‖exponentialSum Y c (Function.update z q u)‖^2 - ‖exponentialSum Y c z‖^2| ≤
      (24 * (Real.pi / 2)^(2*d) *
        ((n : ℝ)^(4*d+5) / (G.minThickLength : ℝ)^(d+1) +
          (n : ℝ)^(4*d+1)*τ / (G.minThickLength : ℝ)^d) *
        continuousEnergy G Y c) * |u-z q| := by
  classical
  obtain ⟨m,hm⟩ := (G.mem_coordinateRows q _).1 (k q).property
  obtain ⟨hklo,hkhi⟩ := (G.mem_blockRows q m _).1 hm
  let a : ℝ := G.start q m
  let b : ℝ := (G.start q m + G.thickLength q m : ℕ)
  let L : ℝ := G.minThickLength
  let A : ℝ := (Real.pi / 2)^(2*d)
  let B : ℝ := (∏ r, Real.pi * n / (2 * Real.sqrt (G.coordinateMinLength r : ℝ))) *
    continuousL2Norm G Y c
  let v : Fin n → ℂ := fun j => c j * Complex.exp (Complex.I *
    ((∑ r ∈ Finset.univ.erase q, z r * Y j r : ℝ) : ℂ))
  let f : ℝ → ℂ := ExponentialSumEstimates.exponentialSum (fun j => Y j q) v
  have hrepr (t : ℝ) : f t = exponentialSum Y c (Function.update z q t) :=
    (exponentialSum_coordinate_section Y c z q t).symm
  have hL : 0 < L := by dsimp [L]; exact_mod_cast minThickLength_pos G
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B, continuousL2Norm]; positivity
  have hlen : b-a = (G.thickLength q m : ℝ) := by dsimp [a,b]; push_cast; ring
  have hab : a < b := by
    rw [← sub_pos, hlen]
    exact_mod_cast (show 0 < G.thickLength q m by unfold SegmentedGrid.thickLength; omega)
  have hLlen : L ≤ b-a := by
    rw [hlen]
    change (G.minThickLength : ℝ) ≤ (G.thickLength q m : ℝ)
    exact_mod_cast (minThickLength_le_coordinateMinLength G q).trans
      (G.coordinateMinLength_le q m)
  have hcell (t : ℝ) (ht : t ∈ Icc (G.rowPoint k q) (G.rowPoint k q+1)) :
      t ∈ Icc a b := by
    have hlo : a ≤ G.rowPoint k q := by
      change (G.start q m : ℝ) ≤ ((k q).val : ℝ)
      exact_mod_cast hklo
    have hhi : G.rowPoint k q + 1 ≤ b := by
      dsimp [b,SegmentedGrid.thickLength]
      push_cast
      have h : G.rowPoint k q ≤ (G.start q m : ℝ) + G.length q m := by
        change ((k q).val : ℝ) ≤ (G.start q m : ℝ) + G.length q m
        exact_mod_cast hkhi
      linarith
    exact ⟨hlo.trans ht.1, ht.2.trans hhi⟩
  have hupdate (t : ℝ) (ht : t ∈ Icc a b) : Function.update z q t ∈ G.thickening := by
    intro r hr
    by_cases he : r = q
    · subst r
      rw [Function.update_self]
      exact Set.mem_iUnion.2 ⟨m,ht⟩
    · rw [Function.update_of_ne he]
      exact G.unitCell_subset_thickening k hz r hr
  have hval : ∀ t ∈ Icc a b, ‖f t‖ ≤ B := by
    intro t ht
    rw [hrepr]
    exact exponentialSum_product_norm_le G hn Y c (hupdate t ht)
  have hsup : setSupNorm f (Icc a b) ≤ B := by
    apply Real.sSup_le
    · rintro w ⟨t,ht,rfl⟩
      exact hval t ht
    · exact hB
  have hderiv : ∀ t ∈ Icc a b,
      ‖deriv f t‖ ≤ (2*(n : ℝ)^2*τ + 12*(n : ℝ)^3/L)*B := by
    intro t ht
    have h := exponentialSum_interval_derivative_frequency_bound hn (fun j => Y j q) v
      hab hτ (fun j => hY j q) ht
    change ‖deriv f t‖ ≤ (2*(n : ℝ)^2*τ + 12*(n : ℝ)^3/(b-a))*
      setSupNorm f (Icc a b) at h
    apply h.trans
    apply mul_le_mul
    · exact add_le_add le_rfl (div_le_div_of_nonneg_left
        (by positivity : 0 ≤ 12*(n : ℝ)^3) hL hLlen)
    · exact hsup
    · exact setSupNorm_nonneg _ _
    · positivity
  have hvariation := norm_sq_variation_of_derivative_bound hB
    (fun t _ => ExponentialSumEstimates.differentiable_exponentialSum (fun j => Y j q) v t)
    hval hderiv (hcell _ (hz q (Set.mem_univ q))) (hcell u hu)
  change |‖f u‖^2 - ‖f (z q)‖^2| ≤
    (2*B*((2*(n : ℝ)^2*τ+12*(n : ℝ)^3/L)*B))*|u-z q| at hvariation
  rw [hrepr u, hrepr (z q), Function.update_eq_self] at hvariation
  have hBsq : B^2 ≤ (A*(n : ℝ)^(2*d)/L^d)*continuousEnergy G Y c := by
    dsimp [B]
    rw [mul_pow, continuousL2Norm_sq]
    exact mul_le_mul_of_nonneg_right (productNikolskiiCoefficient_sq_le_exact G)
      (continuousEnergy_nonneg G Y c)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow₁ : (n : ℝ)^(2*d+3) ≤ (n : ℝ)^(4*d+5) :=
    pow_le_pow_right₀ hnR (by omega)
  have hpow₂ : (n : ℝ)^(2*d+2) ≤ (n : ℝ)^(4*d+1) :=
    pow_le_pow_right₀ hnR (by omega)
  have hcoef : 2*B*((2*(n : ℝ)^2*τ+12*(n : ℝ)^3/L)*B) ≤
      (24*A*((n : ℝ)^(4*d+5)/L^(d+1)+(n : ℝ)^(4*d+1)*τ/L^d))*
        continuousEnergy G Y c := by
    calc
      _ = (4*(n : ℝ)^2*τ+24*(n : ℝ)^3/L)*B^2 := by ring
      _ ≤ (4*(n : ℝ)^2*τ+24*(n : ℝ)^3/L)*
          ((A*(n : ℝ)^(2*d)/L^d)*continuousEnergy G Y c) :=
        mul_le_mul_of_nonneg_left hBsq (by positivity)
      _ = (A*(24*(n : ℝ)^(2*d+3)/L^(d+1)+4*(n : ℝ)^(2*d+2)*τ/L^d))*
          continuousEnergy G Y c := by
        simp only [pow_add, pow_one]
        field_simp
        <;> ring
      _ ≤ (A*(24*(n : ℝ)^(4*d+5)/L^(d+1)+4*(n : ℝ)^(4*d+1)*τ/L^d))*
          continuousEnergy G Y c := by
        apply mul_le_mul_of_nonneg_right _ (continuousEnergy_nonneg G Y c)
        apply mul_le_mul_of_nonneg_left _ hA
        apply add_le_add
        · exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow₁ (by positivity)) (by positivity)
        · exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow₂ (by positivity)) hτ) (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (continuousEnergy_nonneg G Y c)
        have hterm : 0 ≤ (n : ℝ)^(4*d+1)*τ/L^d := by positivity
        have hsmall : 4*((n : ℝ)^(4*d+1)*τ/L^d) ≤
            24*((n : ℝ)^(4*d+1)*τ/L^d) :=
          mul_le_mul_of_nonneg_right (by norm_num) hterm
        calc
          _ = A*(24*((n : ℝ)^(4*d+5)/L^(d+1))+
              4*((n : ℝ)^(4*d+1)*τ/L^d)) := by ring
          _ ≤ A*(24*((n : ℝ)^(4*d+5)/L^(d+1))+
              24*((n : ℝ)^(4*d+1)*τ/L^d)) :=
            mul_le_mul_of_nonneg_left (add_le_add le_rfl hsmall) hA
          _ = _ := by ring
  exact hvariation.trans (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _))

/-- The explicit two-term Riemann condition proves norming on any segmented
product grid. No upper bound on the aperture times the radius is required. -/
theorem continuousNorming_half_of_frequency_bound {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (hd : 2 ≤ d) (hn : 0 < n)
    {τ : ℝ} (hτ : 0 ≤ τ) (hY : ∀ j q, |Y j q| ≤ τ)
    (hcondition : 48*(d : ℝ)*(Real.pi/2)^(2*d)*(G.rowCount : ℝ)*
      ((n : ℝ)^(4*d+5)/(G.minThickLength : ℝ)^(d+1)+
        (n : ℝ)^(4*d+1)*τ/(G.minThickLength : ℝ)^d) ≤ 1) :
    ContinuousNorming G Y (1/2) := by
  let A : ℝ := 24*(Real.pi/2)^(2*d)*
    ((n : ℝ)^(4*d+5)/(G.minThickLength : ℝ)^(d+1)+
      (n : ℝ)^(4*d+1)*τ/(G.minThickLength : ℝ)^d)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  apply continuousNorming_half_of_coordinate_lipschitz G Y
    (fun c _ => A*continuousEnergy G Y c)
    (fun c _ => mul_nonneg hA (continuousEnergy_nonneg G Y c))
  · intro c k q z hz u hu
    exact exponentialSum_cell_coordinate_lipschitz_of_frequency_bound G Y hd hn hτ hY
      c k q z hz hu
  · intro c
    have hhalf : (G.rowCount : ℝ)*d*A ≤ 1/2 := by dsimp [A]; nlinarith only [hcondition]
    calc
      _ = ((G.rowCount : ℝ)*d*A)*continuousEnergy G Y c := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ (1/2 : ℝ)*continuousEnergy G Y c :=
        mul_le_mul_of_nonneg_right hhalf (continuousEnergy_nonneg G Y c)

/-- A common center can be removed by the proved translation invariance of
both the actual continuous integral and the actual measured energy. -/
theorem continuousNorming_half_of_centered_frequency_bound {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (center : Point d)
    (hd : 2 ≤ d) (hn : 0 < n) {τ : ℝ} (hτ : 0 ≤ τ)
    (hY : ∀ j q, |Y j q-center q| ≤ τ)
    (hcondition : 48*(d : ℝ)*(Real.pi/2)^(2*d)*(G.rowCount : ℝ)*
      ((n : ℝ)^(4*d+5)/(G.minThickLength : ℝ)^(d+1)+
        (n : ℝ)^(4*d+1)*τ/(G.minThickLength : ℝ)^d) ≤ 1) :
    ContinuousNorming G Y (1/2) := by
  apply (continuousNorming_translateNodes_iff G Y center (1/2)).mp
  exact continuousNorming_half_of_frequency_bound G (translateNodes Y center) hd hn hτ hY
    hcondition

end
end LeanNumDetect.MultiTuran.MultiClump
