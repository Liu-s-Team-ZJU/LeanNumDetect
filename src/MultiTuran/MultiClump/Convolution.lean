import MultiTuran.Energy
import MultiTuran.MultiClump.ShortenedGrid
import NumDetect.Segmented.Polynomial

/-!
Finite shift operators used to isolate a source clump. The coefficient mass
bound available for the constructive selectors proves the same operator bound
as the torus multiplier argument, without any factor for support cardinality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
open WithLp

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

private theorem energy_comp_le {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (e : κ → ρ) (he : Function.Injective e) (f : ρ → ℂ) :
    (∑ k, ‖f (e k)‖ ^ 2) ≤ ∑ r, ‖f r‖ ^ 2 := by
  classical
  calc
    _ = ∑ r ∈ Finset.univ.image e, ‖f r‖ ^ 2 := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact he hab
    _ ≤ ∑ r, ‖f r‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)

/-- Finite Young inequality for a family of injective shifts. There is no
support-cardinality loss: only the actual coefficient mass appears. -/
theorem finite_shift_energy_le {σ κ ρ : Type*}
    [Fintype σ] [Fintype κ] [Fintype ρ]
    (shift : σ → κ → ρ) (hshift : ∀ s, Function.Injective (shift s))
    (a : σ → ℂ) (f : ρ → ℂ) :
    (∑ k, ‖∑ s, a s * f (shift s k)‖ ^ 2) ≤
      (∑ s, ‖a s‖) ^ 2 * (∑ r, ‖f r‖ ^ 2) := by
  classical
  let u (s : σ) : EuclideanSpace ℂ κ := toLp 2 (fun k => f (shift s k))
  have hu (s : σ) : ‖u s‖ ≤ Real.sqrt (∑ r, ‖f r‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    exact Real.sqrt_le_sqrt (energy_comp_le (shift s) (hshift s) f)
  have hvec : (toLp 2 (fun k => ∑ s, a s * f (shift s k)) : EuclideanSpace ℂ κ) =
      ∑ s, a s • u s := by
    apply WithLp.ofLp_injective 2
    funext k
    simp [u, ofLp_sum, ofLp_smul]
  have hnorm : ‖(toLp 2 (fun k => ∑ s, a s * f (shift s k)) : EuclideanSpace ℂ κ)‖ ≤
      (∑ s, ‖a s‖) * Real.sqrt (∑ r, ‖f r‖ ^ 2) := by
    rw [hvec]
    calc
      _ ≤ ∑ s, ‖a s • u s‖ := norm_sum_le _ _
      _ = ∑ s, ‖a s‖ * ‖u s‖ := by simp only [norm_smul]
      _ ≤ ∑ s, ‖a s‖ * Real.sqrt (∑ r, ‖f r‖ ^ 2) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hu s) (norm_nonneg _)
      _ = _ := (Finset.sum_mul ..).symm
  have hsquare := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (Real.sqrt_nonneg _))).2 hnorm
  rw [EuclideanSpace.norm_sq_eq, mul_pow,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hsquare
  exact hsquare


/-- The actual selector action on the retained rows. Every frequency stays
inside the original block by `selectorRowShift`. -/
def selectorAction {d W D : ℕ} (G : SegmentedGrid d)
    (hW : 2 * W < G.minThickLength)
    (P : NumDetect.SegmentedPolynomial d W 0 D) (f : G.Row → ℂ)
    (k : (shortenedGrid G W).Row) : ℂ :=
  ∑ i, P.coeff i * f (selectorRowShift G W hW (fun q => (i q).2) k)

/-- The selector action has the same coefficient-mass bound on the actual
shortened and full grids, with no dependence on the number of blocks. -/
theorem selectorAction_energy_le {d W D : ℕ} (G : SegmentedGrid d)
    (hW : 2 * W < G.minThickLength)
    (P : NumDetect.SegmentedPolynomial d W 0 D) (f : G.Row → ℂ) :
    (∑ k, ‖selectorAction G hW P f k‖ ^ 2) ≤
      P.mass ^ 2 * ∑ r, ‖f r‖ ^ 2 := by
  simpa only [selectorAction, NumDetect.SegmentedPolynomial.mass] using
    finite_shift_energy_le (σ := NumDetect.SegmentedIndex d W 0)
      (κ := (shortenedGrid G W).Row) (ρ := G.Row)
      (fun i => selectorRowShift G W hW (fun q => (i q).2))
      (fun i => selectorRowShift_injective G W hW (fun q => (i q).2)) P.coeff f

private theorem angularValue_one_block {d W D : ℕ}
    (P : NumDetect.SegmentedPolynomial d W 0 D) (y : Point d) :
    P.angularValue y = ∑ i, P.coeff i * Complex.exp
      (Complex.I * ((∑ q, ((i q).2 : ℝ) * y q : ℝ) : ℂ)) := by
  rw [NumDetect.SegmentedPolynomial.angularValue_eq_angularTrigPolynomial]
  unfold angularTrigPolynomial NumDetect.segmentedPolynomialFrequency
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  apply congrArg (fun t : ℝ => Complex.I * (t : ℂ))
  apply Finset.sum_congr rfl
  intro q _
  simp

/-- The finite shift action is exactly multiplication by the selector at each
source node. Its sign is positive because shifts use `k+s`. -/
theorem selectorAction_exponentialSum {d n W D : ℕ} (G : SegmentedGrid d)
    (hW : 2 * W < G.minThickLength)
    (P : NumDetect.SegmentedPolynomial d W 0 D)
    (Y : Fin n → Point d) (c : Fin n → ℂ)
    (k : (shortenedGrid G W).Row) :
    selectorAction G hW P (fun r => exponentialSum Y c (G.rowPoint r)) k =
      exponentialSum Y (fun j => c j * P.angularValue (Y j))
        ((shortenedGrid G W).rowPoint k) := by
  classical
  have hphase (i : NumDetect.SegmentedIndex d W 0) (j : Fin n) :
      Complex.exp (Complex.I * ((∑ q,
        G.rowPoint (selectorRowShift G W hW (fun q => (i q).2) k) q * Y j q : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((∑ q, ((i q).2 : ℝ) * Y j q : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((∑ q,
          (shortenedGrid G W).rowPoint k q * Y j q : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    simp_rw [selectorRowShift_rowPoint, add_mul]
    rw [Finset.sum_add_distrib]
    push_cast
    ring
  unfold selectorAction exponentialSum
  simp_rw [hphase, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [angularValue_one_block]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact clump extraction on every retained row, from the selector's proved
interpolation identities. -/
theorem selectorAction_clump {d n A W D : ℕ} (G : SegmentedGrid d)
    (hW : 2 * W < G.minThickLength)
    (P : NumDetect.SegmentedPolynomial d W 0 D)
    (Y : Fin n → Point d) (label : Fin n → Fin A) (a : Fin A)
    (hP : ∀ j, P.angularValue (Y j) = if label j = a then 1 else 0)
    (c : Fin n → ℂ) (k : (shortenedGrid G W).Row) :
    selectorAction G hW P (fun r => exponentialSum Y c (G.rowPoint r)) k =
      exponentialSum Y (fun j => if label j = a then c j else 0)
        ((shortenedGrid G W).rowPoint k) := by
  rw [selectorAction_exponentialSum]
  congr 1
  funext j
  rw [hP]
  split_ifs <;> simp

/-- Cancellation between clumps costs only the uniform selector constant on
all original sampled blocks. This is the discrete input to multi-clump norming. -/
theorem clump_discreteEnergy_le_of_selector {d n A W D : ℕ} (G : SegmentedGrid d)
    (hW : 2 * W < G.minThickLength)
    (P : NumDetect.SegmentedPolynomial d W 0 D)
    (Y : Fin n → Point d) (label : Fin n → Fin A) (a : Fin A)
    (hP : ∀ j, P.angularValue (Y j) = if label j = a then 1 else 0)
    (c : Fin n → ℂ) :
    discreteEnergy (shortenedGrid G W) Y (fun j => if label j = a then c j else 0) ≤
      P.mass ^ 2 * discreteEnergy G Y c := by
  have h := selectorAction_energy_le G hW P
    (fun r => exponentialSum Y c (G.rowPoint r))
  simp_rw [selectorAction_clump G hW P Y label a hP c] at h
  exact h

end
end LeanNumDetect.MultiTuran.MultiClump
