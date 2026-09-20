import NumDetectMain.Matrices
import NumDetectMain.UniformProofSupport
import SegmentedVDM.Interpolation
import SegmentedVDM.UniformFrame
import SegmentedVDM.UniformInterpolation
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
Proved support for the multidimensional segmented Vandermonde argument.

The definitions here keep the two frequency budgets separate: `fine` records
the consecutive offset and `coarse` records the multiple of `D`.  Repeated
frequencies are allowed until coefficients are collected into a matrix row.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- A finite presentation of a multivariate segmented trigonometric polynomial. -/
structure SegmentedPacket (d m r : ℕ) where
  Index : Type
  finite : Fintype Index
  coarse : Index → Fin d → ℕ
  fine : Index → Fin d → ℕ
  coarse_le : ∀ i k, coarse i k ≤ r
  fine_le : ∀ i k, fine i k ≤ m
  coeff : Index → ℂ

attribute [instance] SegmentedPacket.finite

namespace SegmentedPacket

/-- Evaluation in the manuscript's angular normalization. -/
noncomputable def value {d m r : ℕ} (P : SegmentedPacket d m r)
    (D : ℕ) (x : Point d) : ℂ :=
  ∑ i, P.coeff i * Complex.exp
    (Complex.I * ((∑ k, ((D * P.coarse i k + P.fine i k : ℕ) : ℝ) * x k : ℝ) : ℂ))

/-- Coefficient `ℓ¹` mass of a finite presentation. -/
noncomputable def mass {d m r : ℕ} (P : SegmentedPacket d m r) : ℝ :=
  ∑ i, ‖P.coeff i‖

theorem mass_nonneg {d m r : ℕ} (P : SegmentedPacket d m r) :
    0 ≤ P.mass :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- The constant polynomial. -/
noncomputable def one (d : ℕ) : SegmentedPacket d 0 0 where
  Index := Unit
  finite := inferInstance
  coarse _ _ := 0
  fine _ _ := 0
  coarse_le _ _ := le_rfl
  fine_le _ _ := le_rfl
  coeff _ := 1

@[simp] theorem value_one (d D : ℕ) (x : Point d) :
    (one d).value D x = 1 := by
  simp [value, one]

@[simp] theorem mass_one (d : ℕ) : (one d).mass = 1 := by
  simp [mass, one]

/-- Enlarge either support budget without changing the polynomial. -/
def widen {d m r m' r' : ℕ} (P : SegmentedPacket d m r)
    (hm : m ≤ m') (hr : r ≤ r') : SegmentedPacket d m' r' where
  Index := P.Index
  finite := P.finite
  coarse := P.coarse
  fine := P.fine
  coarse_le i k := (P.coarse_le i k).trans hr
  fine_le i k := (P.fine_le i k).trans hm
  coeff := P.coeff

@[simp] theorem value_widen {d m r m' r' : ℕ} (P : SegmentedPacket d m r)
    (hm : m ≤ m') (hr : r ≤ r') (D : ℕ) (x : Point d) :
    (P.widen hm hr).value D x = P.value D x := rfl

@[simp] theorem mass_widen {d m r m' r' : ℕ} (P : SegmentedPacket d m r)
    (hm : m ≤ m') (hr : r ≤ r') :
    (P.widen hm hr).mass = P.mass := rfl

/-- Product of two segmented packets. -/
noncomputable def mul {d m₁ m₂ r₁ r₂ : ℕ}
    (P : SegmentedPacket d m₁ r₁) (Q : SegmentedPacket d m₂ r₂) :
    SegmentedPacket d (m₁ + m₂) (r₁ + r₂) where
  Index := P.Index × Q.Index
  finite := inferInstance
  coarse i k := P.coarse i.1 k + Q.coarse i.2 k
  fine i k := P.fine i.1 k + Q.fine i.2 k
  coarse_le i k := Nat.add_le_add (P.coarse_le _ k) (Q.coarse_le _ k)
  fine_le i k := Nat.add_le_add (P.fine_le _ k) (Q.fine_le _ k)
  coeff i := P.coeff i.1 * Q.coeff i.2

theorem value_mul {d m₁ m₂ r₁ r₂ : ℕ}
    (P : SegmentedPacket d m₁ r₁) (Q : SegmentedPacket d m₂ r₂)
    (D : ℕ) (x : Point d) :
    (P.mul Q).value D x = P.value D x * Q.value D x := by
  classical
  unfold value mul
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change
    (P.coeff i * Q.coeff j) * Complex.exp
        (Complex.I * ((∑ k,
          (((D * (P.coarse i k + Q.coarse j k) +
            (P.fine i k + Q.fine j k) : ℕ) : ℝ) * x k) : ℝ) : ℂ)) =
      (P.coeff i * Complex.exp
        (Complex.I * ((∑ k,
          (((D * P.coarse i k + P.fine i k : ℕ) : ℝ) * x k) : ℝ) : ℂ))) *
      (Q.coeff j * Complex.exp
        (Complex.I * ((∑ k,
          (((D * Q.coarse j k + Q.fine j k : ℕ) : ℝ) * x k) : ℝ) : ℂ)))
  rw [show Complex.I * ((∑ k,
      (((D * (P.coarse i k + Q.coarse j k) +
        (P.fine i k + Q.fine j k) : ℕ) : ℝ) * x k) : ℝ) : ℂ) =
      Complex.I * ((∑ k,
        (((D * P.coarse i k + P.fine i k : ℕ) : ℝ) * x k) : ℝ) : ℂ) +
      Complex.I * ((∑ k,
        (((D * Q.coarse j k + Q.fine j k : ℕ) : ℝ) * x k) : ℝ) : ℂ) by
        push_cast
        rw [← mul_add, ← Finset.sum_add_distrib]
        apply congrArg
        apply Finset.sum_congr rfl
        intro k _
        ring,
    Complex.exp_add]
  ring

theorem mass_mul {d m₁ m₂ r₁ r₂ : ℕ}
    (P : SegmentedPacket d m₁ r₁) (Q : SegmentedPacket d m₂ r₂) :
    (P.mul Q).mass = P.mass * Q.mass := by
  change (∑ i : P.Index × Q.Index, ‖P.coeff i.1 * Q.coeff i.2‖) = _
  simp only [mass, norm_mul, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Spatial translation changes coefficient phases but not their moduli. -/
noncomputable def translate {d m r : ℕ} (P : SegmentedPacket d m r)
    (D : ℕ) (y : Point d) : SegmentedPacket d m r :=
  { P with
    coeff := fun i => P.coeff i * Complex.exp
      (-Complex.I *
        ((∑ k, ((D * P.coarse i k + P.fine i k : ℕ) : ℝ) * y k : ℝ) : ℂ)) }

theorem value_translate {d m r : ℕ} (P : SegmentedPacket d m r)
    (D : ℕ) (y x : Point d) :
    (P.translate D y).value D x = P.value D (x - y) := by
  classical
  unfold value translate
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  have hsum :
      (∑ k, ((D * P.coarse i k + P.fine i k : ℕ) : ℝ) * (x - y) k) =
        (∑ k, ((D * P.coarse i k + P.fine i k : ℕ) : ℝ) * x k) -
        ∑ k, ((D * P.coarse i k + P.fine i k : ℕ) : ℝ) * y k := by
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hsum]
  push_cast
  ring

theorem mass_translate {d m r : ℕ} (P : SegmentedPacket d m r)
    (D : ℕ) (y : Point d) :
    (P.translate D y).mass = P.mass := by
  apply Finset.sum_congr rfl
  intro i _
  simp [translate, norm_mul, Complex.norm_exp]

/-- Product of a finite family, with coordinatewise support budgets added. -/
noncomputable def prod {d m r q : ℕ}
    (P : Fin q → SegmentedPacket d m r) :
    SegmentedPacket d (q * m) (q * r) where
  Index := (i : Fin q) → (P i).Index
  finite := inferInstance
  coarse a k := ∑ i, (P i).coarse (a i) k
  fine a k := ∑ i, (P i).fine (a i) k
  coarse_le a k := by
    calc
      _ ≤ ∑ _i : Fin q, r :=
        Finset.sum_le_sum fun i _ => (P i).coarse_le (a i) k
      _ = q * r := by simp
  fine_le a k := by
    calc
      _ ≤ ∑ _i : Fin q, m :=
        Finset.sum_le_sum fun i _ => (P i).fine_le (a i) k
      _ = q * m := by simp
  coeff a := ∏ i, (P i).coeff (a i)

theorem value_prod {d m r q : ℕ}
    (P : Fin q → SegmentedPacket d m r) (D : ℕ) (x : Point d) :
    (prod P).value D x = ∏ i, (P i).value D x := by
  classical
  simp only [value, prod]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hphase :
      (∑ k, ((D * (∑ i, (P i).coarse (a i) k) +
          ∑ i, (P i).fine (a i) k : ℕ) : ℝ) * x k) =
        ∑ i, ∑ k,
          ((D * (P i).coarse (a i) k + (P i).fine (a i) k : ℕ) : ℝ) *
            x k := by
    push_cast
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    calc
      ((D : ℝ) * ∑ i, ((P i).coarse (a i) k : ℝ) +
          ∑ i, ((P i).fine (a i) k : ℝ)) * x k =
          ((D : ℝ) * x k) * ∑ i, ((P i).coarse (a i) k : ℝ) +
            x k * ∑ i, ((P i).fine (a i) k : ℝ) := by ring
      _ = ∑ i, ((D : ℝ) * x k) * ((P i).coarse (a i) k : ℝ) +
            ∑ i, x k * ((P i).fine (a i) k : ℝ) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ = ∑ i, ((D : ℝ) * ((P i).coarse (a i) k : ℝ) +
            ((P i).fine (a i) k : ℝ)) * x k := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
  rw [hphase, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum,
    ← Finset.prod_mul_distrib]

theorem mass_prod {d m r q : ℕ}
    (P : Fin q → SegmentedPacket d m r) :
    (prod P).mass = ∏ i, (P i).mass := by
  simp only [mass, prod, norm_prod]
  exact (Fintype.prod_sum (fun i a => ‖(P i).coeff a‖)).symm

/-- The actual segmented row occupied by one term of a packet. -/
def frequencyIndex {d m r : ℕ} (P : SegmentedPacket d m r)
    (i : P.Index) : SegmentedIndex d m r :=
  fun k =>
    (⟨P.coarse i k, Nat.lt_succ_of_le (P.coarse_le i k)⟩,
      ⟨P.fine i k, Nat.lt_succ_of_le (P.fine_le i k)⟩)

/-- Collect a presentation, summing coefficients that occupy the same row. -/
noncomputable def coefficientVector {d m r : ℕ}
    (P : SegmentedPacket d m r) : SegmentedIndex d m r → ℂ :=
  fun α => ∑ i, if P.frequencyIndex i = α then P.coeff i else 0

/-- Collecting repeated frequencies does not change packet evaluation. -/
theorem coefficientVector_dot_vandermonde
    {d n m r : ℕ} (P : SegmentedPacket d m r) (D : ℕ)
    (x : Fin n → Point d) (j : Fin n) :
    P.coefficientVector ⬝ᵥ
        (fun α => segmentedVandermonde m r D x α j) =
      P.value D (x j) := by
  classical
  simp only [coefficientVector, dotProduct, segmentedVandermonde,
    generalizedVandermonde, steeringVector]
  unfold value
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (P.frequencyIndex i)]
  · simp only [if_true]
    congr 2
  · intro α _ hα
    simp [hα.symm]
  · simp

/-- A collected coefficient vector has no more `ℓ¹` mass than its presentation. -/
theorem coefficientVector_norm_sum_le_mass
    {d m r : ℕ} (P : SegmentedPacket d m r) :
    (∑ α, ‖P.coefficientVector α‖) ≤ P.mass := by
  classical
  calc
    (∑ α, ‖P.coefficientVector α‖)
        ≤ ∑ α, ∑ i, ‖if P.frequencyIndex i = α then P.coeff i else 0‖ :=
      Finset.sum_le_sum fun α _ => norm_sum_le _ _
    _ = ∑ i, ∑ α, ‖if P.frequencyIndex i = α then P.coeff i else 0‖ := by
      rw [Finset.sum_comm]
    _ = P.mass := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single (P.frequencyIndex i)]
      · simp [mass]
      · intro α _ hα
        simp [hα.symm]
      · simp

/-- The coefficient energy of a collected packet is bounded by squared mass. -/
theorem coefficientVector_energy_le_mass_sq
    {d m r : ℕ} (P : SegmentedPacket d m r) :
    SegmentedVDM.energy P.coefficientVector ≤ P.mass ^ 2 := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun α => ‖P.coefficientVector α‖)
    (fun _ _ => norm_nonneg _)
  exact hs.trans
    ((sq_le_sq₀
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      P.mass_nonneg).2 P.coefficientVector_norm_sum_le_mass)

/-- Lagrange packets with a common coefficient-energy bound give the final
minimum-singular-value estimate. -/
theorem singularValue_ge_of_segmentedPackets
    {d n m r D : ℕ} (hn : 0 < n) (x : Fin n → Point d)
    (P : Fin n → SegmentedPacket d m r)
    (hinterp : ∀ k j, (P k).value D (x j) =
      if k = j then 1 else 0)
    {B : ℝ} (hB : 0 < B)
    (henergy : ∀ k,
      SegmentedVDM.energy (P k).coefficientVector ≤ B ^ 2) :
    1 / (Real.sqrt n * B) ≤
      matrixSingularValue (segmentedVandermonde m r D x) (n - 1) := by
  classical
  let C : Matrix (Fin n) (SegmentedIndex d m r) ℂ :=
    fun k => (P k).coefficientVector
  have hCV : C * segmentedVandermonde m r D x = 1 := by
    ext k j
    change (P k).coefficientVector ⬝ᵥ
      (fun α => segmentedVandermonde m r D x α j) = _
    rw [coefficientVector_dot_vandermonde]
    simpa only [Matrix.one_apply] using hinterp k j
  exact SegmentedVDM.singularValue_ge_of_interpolation
    (segmentedVandermonde m r D x) C hCV hn hB henergy

/-- A cube of extra segmented frequencies used to average packet coefficients. -/
abbrev SmoothingIndex (d b z : ℕ) :=
  SegmentedIndex d b z

/-- Add one smoothing frequency to a row occupied by a packet term. -/
def shiftedSegmentedRow {d m r : ℕ} (P : SegmentedPacket d m r)
    (b z : ℕ) (i : P.Index) (q : SmoothingIndex d b z) :
    SegmentedIndex d (m + b) (r + z) :=
  fun k =>
    (⟨P.coarse i k + (q k).1, by
        have hp := P.coarse_le i k
        have hq := (q k).1.isLt
        omega⟩,
      ⟨P.fine i k + (q k).2, by
        have hp := P.fine_le i k
        have hq := (q k).2.isLt
        omega⟩)

theorem shiftedSegmentedRow_injective
    {d m r : ℕ} (P : SegmentedPacket d m r)
    (b z : ℕ) (i : P.Index) :
    Function.Injective (shiftedSegmentedRow P b z i) := by
  intro q q' h
  funext k
  have hk := congrFun h k
  apply Prod.ext
  · apply Fin.ext
    have := congrArg (fun a => a.1.val) hk
    simpa only [shiftedSegmentedRow] using
      Nat.add_left_cancel this
  · apply Fin.ext
    have := congrArg (fun a => a.2.val) hk
    simpa only [shiftedSegmentedRow] using
      Nat.add_left_cancel this

/-- The normalized frequency cube, phased so that it equals one at `y`. -/
noncomputable def segmentedAveragingVector
    {d m r : ℕ} (P : SegmentedPacket d m r)
    (b z D : ℕ) (y : Point d) (i : P.Index) :
    EuclideanSpace ℂ (SegmentedIndex d (m + b) (r + z)) :=
  SegmentedVDM.spread (shiftedSegmentedRow P b z i) fun q =>
    Complex.exp
        (-Complex.I *
          ((∑ k, (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) *
            y k) : ℝ) : ℂ)) /
      (((z + 1) * (b + 1)) ^ d : ℕ)

theorem segmentedAveragingVector_norm
    {d m r : ℕ} (P : SegmentedPacket d m r)
    (b z D : ℕ) (y : Point d) (i : P.Index) :
    ‖segmentedAveragingVector P b z D y i‖ =
      1 / Real.sqrt ((((z + 1) * (b + 1)) ^ d : ℕ) : ℝ) := by
  have hN : (0 : ℝ) < (((z + 1) * (b + 1)) ^ d : ℕ) := by positivity
  have hh := SegmentedVDM.norm_spread_sq
    (shiftedSegmentedRow P b z i)
    (shiftedSegmentedRow_injective P b z i)
    (fun q : SmoothingIndex d b z =>
      Complex.exp
          (-Complex.I *
            ((∑ k, (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) *
              y k) : ℝ) : ℂ)) /
        (((z + 1) * (b + 1)) ^ d : ℕ))
  change ‖segmentedAveragingVector P b z D y i‖ ^ 2 = _ at hh
  have hcard :
      Fintype.card (SmoothingIndex d b z) =
        ((z + 1) * (b + 1)) ^ d := by
    simp [SmoothingIndex, SegmentedIndex, SegmentedCoordinateIndex]
  have he : SegmentedVDM.energy
      (fun q : SmoothingIndex d b z =>
        Complex.exp
            (-Complex.I *
              ((∑ k, (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) *
                y k) : ℝ) : ℂ)) /
          (((z + 1) * (b + 1)) ^ d : ℕ)) =
      1 / ((((z + 1) * (b + 1)) ^ d : ℕ) : ℝ) := by
    have hexp (q : SmoothingIndex d b z) :
        ‖Complex.exp
          (-Complex.I *
            ((∑ k, (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) *
              y k) : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    simp only [SegmentedVDM.energy, norm_div, hexp, Complex.norm_natCast,
      one_div, inv_pow, one_pow, Finset.sum_const, Finset.card_univ,
      hcard, nsmul_eq_mul]
    field_simp
  rw [he] at hh
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hh, div_pow, one_pow, Real.sq_sqrt hN.le]

/-- Average every term of a packet over the same translated frequency cube. -/
noncomputable def smoothedSegmentedVector
    {d m r : ℕ} (P : SegmentedPacket d m r)
    (b z D : ℕ) (y : Point d) :
    EuclideanSpace ℂ (SegmentedIndex d (m + b) (r + z)) :=
  ∑ i, P.coeff i • segmentedAveragingVector P b z D y i

theorem smoothedSegmentedVector_norm_le
    {d m r : ℕ} (P : SegmentedPacket d m r)
    (b z D : ℕ) (y : Point d) :
    ‖smoothedSegmentedVector P b z D y‖ ≤
      P.mass /
        Real.sqrt ((((z + 1) * (b + 1)) ^ d : ℕ) : ℝ) := by
  calc
    _ ≤ ∑ i, ‖P.coeff i • segmentedAveragingVector P b z D y i‖ :=
      norm_sum_le _ _
    _ = _ := by
      simp only [norm_smul, segmentedAveragingVector_norm, mul_one_div,
        ← Finset.sum_div, SegmentedPacket.mass]

/-- The translated averaging cube used in the evaluation identity. -/
noncomputable def segmentedMeanKernel
    (d b z D : ℕ) (u : Point d) : ℂ :=
  ∑ q : SmoothingIndex d b z,
    (1 / ((((z + 1) * (b + 1)) ^ d : ℕ) : ℂ)) *
      Complex.exp
        (Complex.I *
          ((∑ k, (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) *
            u k) : ℝ) : ℂ))

@[simp] theorem segmentedMeanKernel_zero (d b z D : ℕ) :
    segmentedMeanKernel d b z D 0 = 1 := by
  have hcard :
      Fintype.card (SmoothingIndex d b z) =
        ((z + 1) * (b + 1)) ^ d := by
    simp [SmoothingIndex, SegmentedIndex, SegmentedCoordinateIndex]
  simp [segmentedMeanKernel, hcard]
  exact div_self (by
    exact_mod_cast
      (show ((z + 1) * (b + 1)) ^ d ≠ 0 by positivity))

/-- Steering vector for one segmented-frequency cube. -/
noncomputable def segmentedSteering
    (d m r D : ℕ) (x : Point d) :
    SegmentedIndex d m r → ℂ :=
  fun α => Complex.exp
    (Complex.I *
      ((∑ k, (((D * (α k).1.val + (α k).2.val : ℕ) : ℝ) *
        x k) : ℝ) : ℂ))

theorem segmentedSteering_eq_vandermonde
    {d n m r D : ℕ} (x : Fin n → Point d) (j : Fin n) :
    segmentedSteering d m r D (x j) =
      fun α => segmentedVandermonde m r D x α j := by
  rfl

theorem segmentedAveragingVector_evaluation
    {d m r : ℕ} (P : SegmentedPacket d m r)
    (b z D : ℕ) (y x : Point d) (i : P.Index) :
    ofLp (segmentedAveragingVector P b z D y i) ⬝ᵥ
        segmentedSteering d (m + b) (r + z) D x =
      Complex.exp
          (Complex.I *
            ((∑ k, (((D * P.coarse i k + P.fine i k : ℕ) : ℝ) *
              x k) : ℝ) : ℂ)) *
        segmentedMeanKernel d b z D (x - y) := by
  rw [segmentedAveragingVector, SegmentedVDM.spread_dotProduct]
  unfold segmentedMeanKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  change
    Complex.exp
          (-Complex.I *
            ((∑ k, (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) *
              y k) : ℝ) : ℂ)) /
        (((z + 1) * (b + 1)) ^ d : ℕ) *
      Complex.exp
        (Complex.I *
          ((∑ k,
            (((D * (P.coarse i k + (q k).1.val) +
              (P.fine i k + (q k).2.val) : ℕ) : ℝ) * x k) : ℝ) : ℂ)) =
      Complex.exp
          (Complex.I *
            ((∑ k, (((D * P.coarse i k + P.fine i k : ℕ) : ℝ) *
              x k) : ℝ) : ℂ)) *
        (1 / ((((z + 1) * (b + 1)) ^ d : ℕ) : ℂ) *
          Complex.exp
            (Complex.I *
              ((∑ k, (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) *
                (x - y) k) : ℝ) : ℂ)))
  rw [div_mul_eq_mul_div]
  have hphase :
      -Complex.I *
          ((∑ k, (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) *
            y k) : ℝ) : ℂ) +
        Complex.I *
          ((∑ k,
            (((D * (P.coarse i k + (q k).1.val) +
              (P.fine i k + (q k).2.val) : ℕ) : ℝ) * x k) : ℝ) : ℂ) =
      Complex.I *
          ((∑ k, (((D * P.coarse i k + P.fine i k : ℕ) : ℝ) *
            x k) : ℝ) : ℂ) +
        Complex.I *
          ((∑ k, (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) *
            (x - y) k) : ℝ) : ℂ) := by
    have hadd :
        (∑ k,
            (((D * (P.coarse i k + (q k).1.val) +
              (P.fine i k + (q k).2.val) : ℕ) : ℝ) * x k)) =
          (∑ k, (((D * P.coarse i k + P.fine i k : ℕ) : ℝ) * x k)) +
          ∑ k, (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) * x k) := by
      push_cast
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hsub :
        (∑ k, (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) *
            (x - y) k)) =
          (∑ k, (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) * x k)) -
          ∑ k, (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) * y k) := by
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [hadd, hsub]
    push_cast
    ring
  rw [← Complex.exp_add, hphase, Complex.exp_add]
  ring

theorem smoothedSegmentedVector_evaluation
    {d m r : ℕ} (P : SegmentedPacket d m r)
    (b z D : ℕ) (y x : Point d) :
    ofLp (smoothedSegmentedVector P b z D y) ⬝ᵥ
        segmentedSteering d (m + b) (r + z) D x =
      P.value D x * segmentedMeanKernel d b z D (x - y) := by
  simp only [smoothedSegmentedVector, WithLp.ofLp_sum, sum_dotProduct,
    WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul,
    segmentedAveragingVector_evaluation]
  unfold SegmentedPacket.value
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Frequency-cube smoothing and Lagrange duality for segmented packets. -/
theorem singularValue_ge_of_smoothedSegmentedPackets
    {d n m r b z D : ℕ} (hn : 0 < n) (x : Fin n → Point d)
    (P : Fin n → SegmentedPacket d m r)
    (hinterp : ∀ k j, (P k).value D (x j) =
      if k = j then 1 else 0)
    {H : ℝ} (hH : 0 < H) (hP : ∀ k, (P k).mass ≤ H) :
    Real.sqrt ((((z + 1) * (b + 1)) ^ d : ℕ) : ℝ) /
        (Real.sqrt n * H) ≤
      matrixSingularValue
        (segmentedVandermonde (m + b) (r + z) D x) (n - 1) := by
  classical
  let C : Matrix (Fin n) (SegmentedIndex d (m + b) (r + z)) ℂ :=
    fun k => ofLp (smoothedSegmentedVector (P k) b z D (x k))
  have hCV : C * segmentedVandermonde (m + b) (r + z) D x = 1 := by
    ext k j
    change
      ofLp (smoothedSegmentedVector (P k) b z D (x k)) ⬝ᵥ
          (fun α => segmentedVandermonde (m + b) (r + z) D x α j) =
        (1 : Matrix (Fin n) (Fin n) ℂ) k j
    rw [← segmentedSteering_eq_vandermonde,
      smoothedSegmentedVector_evaluation, hinterp]
    by_cases hkj : k = j
    · subst j
      simp
    · simp [hkj]
  have hC (k : Fin n) :
      SegmentedVDM.energy (C k) ≤
        (H /
          Real.sqrt ((((z + 1) * (b + 1)) ^ d : ℕ) : ℝ)) ^ 2 := by
    change (∑ i, ‖(smoothedSegmentedVector (P k) b z D (x k)) i‖ ^ 2) ≤ _
    rw [← EuclideanSpace.norm_sq_eq]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).2
    exact (smoothedSegmentedVector_norm_le (P k) b z D (x k)).trans
      (div_le_div_of_nonneg_right (hP k) (Real.sqrt_nonneg _))
  have hh := SegmentedVDM.singularValue_ge_of_interpolation
    (segmentedVandermonde (m + b) (r + z) D x)
    C hCV hn (by positivity :
      0 < H / Real.sqrt ((((z + 1) * (b + 1)) ^ d : ℕ) : ℝ)) hC
  convert! hh using 1
  field_simp

end SegmentedPacket

/-- The coordinatewise shortest representative of an angular difference. -/
def wrappedCoordinateDifference (u v : ℝ) : ℝ :=
  if Real.pi < u - v then u - v - 2 * Real.pi
  else if u - v ≤ -Real.pi then u - v + 2 * Real.pi
  else u - v

/-- The integer number of periods removed by `wrappedCoordinateDifference`. -/
def wrappedCoordinateTurns (u v : ℝ) : ℤ :=
  if Real.pi < u - v then 1
  else if u - v ≤ -Real.pi then -1
  else 0

theorem sub_eq_wrappedCoordinateDifference_add
    (u v : ℝ) :
    u - v =
      wrappedCoordinateDifference u v +
        2 * Real.pi * wrappedCoordinateTurns u v := by
  unfold wrappedCoordinateDifference wrappedCoordinateTurns
  split_ifs <;> push_cast <;> ring

/-- Coordinatewise shortest representative of a torus difference. -/
def wrappedDifference {d : ℕ} (u v : Point d) : Point d :=
  fun k => wrappedCoordinateDifference (u k) (v k)

theorem sub_eq_wrappedDifference_add
    {d : ℕ} (u v : Point d) (k : Fin d) :
    u k - v k =
      wrappedDifference u v k +
        2 * Real.pi * wrappedCoordinateTurns (u k) (v k) :=
  sub_eq_wrappedCoordinateDifference_add _ _

theorem abs_wrappedCoordinateDifference
    {u v : ℝ}
    (hu : -Real.pi < u ∧ u ≤ Real.pi)
    (hv : -Real.pi < v ∧ v ≤ Real.pi) :
    |wrappedCoordinateDifference u v| =
      periodicCoordinateDistance u v := by
  unfold wrappedCoordinateDifference periodicCoordinateDistance
  have hdiffLower : -2 * Real.pi < u - v := by linarith
  have hdiffUpper : u - v < 2 * Real.pi := by linarith
  by_cases hupper : Real.pi < u - v
  · rw [if_pos hupper]
    have hpos : 0 < u - v := hupper.trans' Real.pi_pos
    have hwrap : u - v - 2 * Real.pi < 0 := by linarith
    rw [abs_of_pos hpos, abs_of_nonpos hwrap.le, min_eq_right]
    · ring
    · linarith
  · rw [if_neg hupper]
    by_cases hlower : u - v ≤ -Real.pi
    · rw [if_pos hlower]
      have hneg : u - v ≤ 0 := hlower.trans (neg_nonpos.mpr Real.pi_pos.le)
      have hwrap : 0 < u - v + 2 * Real.pi := by linarith
      rw [abs_of_nonpos hneg, abs_of_pos hwrap, min_eq_right]
      · ring
      · linarith
    · rw [if_neg hlower]
      have hlow : -Real.pi < u - v := lt_of_not_ge hlower
      have habs : |u - v| ≤ Real.pi := (abs_le).2 ⟨by linarith, by linarith⟩
      rw [min_eq_left (by linarith)]

theorem l1Norm_wrappedDifference
    {d : ℕ} {u v : Point d}
    (hu : InAngularCube u) (hv : InAngularCube v) :
    l1Norm (wrappedDifference u v) = periodicL1Distance u v := by
  unfold l1Norm periodicL1Distance
  apply Finset.sum_congr rfl
  intro k _
  exact abs_wrappedCoordinateDifference (hu k) (hv k)

theorem l1Norm_wrappedDifference_le
    {d : ℕ} {u v : Point d}
    (hu : InAngularCube u) (hv : InAngularCube v) :
    l1Norm (wrappedDifference u v) ≤
      d * periodicLInfDistance u v := by
  rw [l1Norm_wrappedDifference hu hv]
  unfold periodicL1Distance periodicLInfDistance
  calc
    (∑ k, periodicCoordinateDistance (u k) (v k))
        ≤ ∑ _k : Fin d, ‖fun k => periodicCoordinateDistance (u k) (v k)‖ :=
      Finset.sum_le_sum fun k _ =>
        (le_abs_self _).trans (by
          simpa only [Real.norm_eq_abs] using
            norm_le_pi_norm
              (fun k => periodicCoordinateDistance (u k) (v k)) k)
    _ = d * ‖fun k => periodicCoordinateDistance (u k) (v k)‖ := by simp

/-- Recenter a scalar coarse-frequency packet coordinatewise according to the
signs of `u`.  Its frequencies lie in the nonnegative cube and its value is a
unimodular multiple of the scalar packet evaluated at `‖u‖₁`. -/
def SegmentedPacket.liftScalarRecentered
    {d K : ℕ} (u : Point d) (P : SegmentedVDM.Packet 0 K) :
    SegmentedPacket d 0 K where
  Index := P.Index
  finite := P.finite
  coarse i k := if 0 ≤ u k then P.coarse i else K - P.coarse i
  fine _ _ := 0
  coarse_le i k := by
    split_ifs
    · exact P.coarse_le i
    · exact Nat.sub_le _ _
  fine_le _ _ := le_rfl
  coeff := P.coeff

theorem SegmentedPacket.mass_liftScalarRecentered
    {d K : ℕ} (u : Point d) (P : SegmentedVDM.Packet 0 K) :
    (SegmentedPacket.liftScalarRecentered u P).mass = P.mass :=
  rfl

theorem SegmentedPacket.value_liftScalarRecentered
    {d K : ℕ} (u : Point d) (P : SegmentedVDM.Packet 0 K)
    (D : ℕ) :
    (SegmentedPacket.liftScalarRecentered u P).value D u =
      Complex.exp
          (Complex.I *
            (((D * K : ℕ) : ℝ) *
              ∑ k, if 0 ≤ u k then 0 else u k : ℝ)) *
        P.value D (l1Norm u) := by
  classical
  unfold SegmentedPacket.value SegmentedPacket.liftScalarRecentered
    SegmentedVDM.Packet.value l1Norm
  change
    (∑ i, P.coeff i * Complex.exp
      (Complex.I * ((∑ k,
        (((D * (if 0 ≤ u k then P.coarse i else K - P.coarse i) +
          0 : ℕ) : ℝ) * u k) : ℝ) : ℂ))) =
      Complex.exp
          (Complex.I *
            (((D * K : ℕ) : ℝ) *
              ∑ k, if 0 ≤ u k then 0 else u k : ℝ)) *
        ∑ i, P.coeff i * Complex.exp
          (Complex.I *
            ((((P.coarse i : ℝ) * D + P.fine i) *
              ∑ k, |u k| : ℝ) : ℂ))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show
      Complex.exp
          (Complex.I *
            (((D * K : ℕ) : ℝ) *
              ∑ k, if 0 ≤ u k then 0 else u k : ℝ)) *
          (P.coeff i * Complex.exp
            (Complex.I *
              ((((P.coarse i : ℝ) * D + P.fine i) *
                ∑ k, |u k| : ℝ) : ℂ))) =
        P.coeff i *
          (Complex.exp
            (Complex.I *
              (((D * K : ℕ) : ℝ) *
                ∑ k, if 0 ≤ u k then 0 else u k : ℝ)) *
            Complex.exp
              (Complex.I *
                ((((P.coarse i : ℝ) * D + P.fine i) *
                  ∑ k, |u k| : ℝ) : ℂ))) by ring,
    ← Complex.exp_add]
  congr 2
  have hf : P.fine i = 0 := Nat.le_zero.mp (P.fine_le i)
  push_cast
  rw [hf]
  simp only [Nat.cast_zero, add_zero, Nat.cast_mul, Nat.cast_sub (P.coarse_le i)]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hk
  · rw [abs_of_nonneg hk]
    norm_num
    push_cast
    ring <;> simp [hk]
  · rw [abs_of_nonpos (le_of_not_ge hk)]
    norm_num
    push_cast
    ring <;> simp [hk]

@[simp] theorem SegmentedPacket.value_liftScalarRecentered_zero
    {d K : ℕ} (u : Point d) (P : SegmentedVDM.Packet 0 K)
    (D : ℕ) :
    (SegmentedPacket.liftScalarRecentered u P).value D 0 =
      P.value D 0 := by
  classical
  simp [SegmentedPacket.value, SegmentedPacket.liftScalarRecentered,
    SegmentedVDM.Packet.value]

/-- Integer-frequency packets have the same value on an angular difference
and on its coordinatewise shortest representative. -/
theorem SegmentedPacket.value_sub_eq_wrappedDifference
    {d m r : ℕ} (P : SegmentedPacket d m r) (D : ℕ)
    (u v : Point d) :
    P.value D (u - v) = P.value D (wrappedDifference u v) := by
  classical
  unfold SegmentedPacket.value
  apply Finset.sum_congr rfl
  intro i _
  let z : ℤ :=
    ∑ k, ((D * P.coarse i k + P.fine i k : ℕ) : ℤ) *
      wrappedCoordinateTurns (u k) (v k)
  have hphase :
      (∑ k, ((D * P.coarse i k + P.fine i k : ℕ) : ℝ) *
          (u - v) k) =
        (∑ k, ((D * P.coarse i k + P.fine i k : ℕ) : ℝ) *
          wrappedDifference u v k) +
        2 * Real.pi * (z : ℝ) := by
    simp only [Pi.sub_apply, sub_eq_wrappedDifference_add]
    dsimp [z]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  congr 1
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨z, ?_⟩
  rw [hphase]
  push_cast
  ring

/-- Product of recentered two-point factors annihilating a finite family of
short wrapped differences. -/
theorem segmentedNeighborProduct
    {d q D : ℕ} {T Δ : ℝ}
    (hT : 2 ≤ T) (hD : 0 < D) (hΔ : 0 < Δ)
    (u : Fin q → Point d)
    (hΔu : ∀ i, Δ ≤ l1Norm (u i))
    (hu : ∀ i, l1Norm (u i) ≤ Real.pi / (2 * D))
    (hscale : T * D * Δ ≤ Real.pi) :
    ∃ P : SegmentedPacket d 0 (q * ⌊T⌋₊),
      P.value D 0 = 1 ∧
      (∀ i, P.value D (u i) = 0) ∧
      P.mass ≤
        (Real.sqrt 2 / (T * D * Δ / Real.pi)) ^ q := by
  classical
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have huNonneg (i : Fin q) : 0 ≤ l1Norm (u i) := by
    unfold l1Norm
    positivity
  choose F hF using fun i =>
    SegmentedVDM.neighbor_factor (u := l1Norm (u i)) hT hDR hΔ
      (by simpa only [abs_of_nonneg (huNonneg i)] using hΔu i)
      (by simpa only [abs_of_nonneg (huNonneg i)] using hu i)
      hscale
  let Q (i : Fin q) : SegmentedPacket d 0 ⌊T⌋₊ :=
    SegmentedPacket.liftScalarRecentered (u i) (F i)
  let P : SegmentedPacket d 0 (q * ⌊T⌋₊) :=
    (SegmentedPacket.prod Q).widen (by simp) le_rfl
  refine ⟨P, ?_, ?_, ?_⟩
  · simp only [P, SegmentedPacket.value_widen, SegmentedPacket.value_prod]
    apply Finset.prod_eq_one
    intro i _
    simpa only [Q, SegmentedPacket.value_liftScalarRecentered_zero] using
      (hF i).1
  · intro j
    simp only [P, SegmentedPacket.value_widen, SegmentedPacket.value_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    change
      (SegmentedPacket.liftScalarRecentered (u j) (F j)).value D (u j) = 0
    rw [SegmentedPacket.value_liftScalarRecentered]
    rw [(hF j).2.1, mul_zero]
  · simp only [P, SegmentedPacket.mass_widen, SegmentedPacket.mass_prod,
      Q, SegmentedPacket.mass_liftScalarRecentered]
    calc
      _ ≤ ∏ _i : Fin q,
          Real.sqrt 2 / (T * D * Δ / Real.pi) :=
        Finset.prod_le_prod
          (fun i _ => (F i).mass_nonneg)
          (fun i _ => (hF i).2.2)
      _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem periodicMinimumL1Separation_le
    {d n : ℕ} {x : Fin n → Point d} (hn : 2 ≤ n)
    {i j : Fin n} (hij : i ≠ j) :
    periodicMinimumL1Separation x hn ≤ periodicL1Distance (x i) (x j) := by
  unfold periodicMinimumL1Separation minimumOverDistinctPairs
  exact Finset.inf'_le
    (fun ij : Fin n × Fin n => periodicL1Distance (x ij.1) (x ij.2))
    (by
      change (i, j) ∈ distinctPairs n
      rw [distinctPairs, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hij⟩)

theorem segmented_periodicMinimumL1Separation_pos
    {d n : ℕ} (μ : AtomicMeasure d n) (hn : 2 ≤ n)
    (hcube : ∀ j, InAngularCube (μ.node j)) :
    0 < periodicMinimumL1Separation μ.node hn := by
  rw [periodicMinimumL1Separation, minimumOverDistinctPairs,
    Finset.lt_inf'_iff]
  intro ij hij
  have hne : ij.1 ≠ ij.2 := by
    simpa [distinctPairs] using hij
  obtain ⟨k, hk⟩ : ∃ k, μ.node ij.1 k ≠ μ.node ij.2 k := by
    by_contra h
    apply hne
    apply μ.node_injective
    funext k
    exact not_ne_iff.mp (not_exists.mp h k)
  unfold periodicL1Distance
  apply Finset.sum_pos'
  · intro k _
    rw [← abs_wrappedCoordinateDifference (hcube ij.1 k) (hcube ij.2 k)]
    exact abs_nonneg _
  · refine ⟨k, Finset.mem_univ k, ?_⟩
    unfold periodicCoordinateDistance
    rw [lt_min_iff]
    constructor
    · exact abs_pos.mpr (sub_ne_zero.mpr hk)
    · rw [sub_pos, abs_lt]
      constructor <;>
        linarith [(hcube ij.1 k).1, (hcube ij.1 k).2,
          (hcube ij.2 k).1, (hcube ij.2 k).2, Real.pi_pos]

/-- Slot data used to color each clump with at most `nStar` colors. -/
structure ClumpSlots {d n A nStar : ℕ} (x : Fin n → Point d) where
  label : Fin n → Fin A
  slot : Fin n → Fin nStar
  injective : Function.Injective (fun j => (label j, slot j))

/-- Other nodes in the anchor's clump. -/
def ClumpSlots.neighbors
    {d n A nStar : ℕ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x)
    (anchor : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j =>
    j ≠ anchor ∧ C.label j = C.label anchor

@[simp] theorem ClumpSlots.mem_neighbors
    {d n A nStar : ℕ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x)
    (anchor j : Fin n) :
    j ∈ C.neighbors anchor ↔
      j ≠ anchor ∧ C.label j = C.label anchor := by
  simp [ClumpSlots.neighbors]

theorem ClumpSlots.neighbors_card
    {d n A nStar : ℕ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x)
    (anchor : Fin n) :
    (C.neighbors anchor).card ≤ nStar - 1 := by
  have h :
      (C.neighbors anchor).card ≤
        (Finset.univ.erase (C.slot anchor)).card := by
    apply Finset.card_le_card_of_injOn C.slot
    · intro j hj
      have hj' := (C.mem_neighbors anchor j).mp hj
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      intro hslot
      exact hj'.1 (C.injective (Prod.ext hj'.2 hslot))
    · intro i hi j hj hslot
      have hi' := (C.mem_neighbors anchor i).mp hi
      have hj' := (C.mem_neighbors anchor j).mp hj
      exact C.injective (Prod.ext (hi'.2.trans hj'.2.symm) hslot)
  simpa using h

/-- The quantized coarse-frequency factor that interpolates within one clump. -/
theorem withinClumpPacket
    {d n A nStar r D : ℕ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x)
    (anchor : Fin n) (hd : 1 ≤ d) (hnStar : 1 ≤ nStar)
    (hr : 2 * nStar ≤ r)
    {τ Δ : ℝ} (hD : 0 < D) (hΔ : 0 < Δ)
    (hcube : ∀ j, InAngularCube (x j))
    (hsame : ∀ i j, C.label i = C.label j →
      periodicLInfDistance (x i) (x j) ≤ τ)
    (hτ : τ ≤ Real.pi / (2 * D * d))
    (hmin : ∀ i j, i ≠ j →
      Δ ≤ periodicL1Distance (x i) (x j))
    (hscale : Δ ≤ Real.pi * nStar / (r * D)) :
    ∃ P : SegmentedPacket d 0 (r - r / nStar),
      (∀ j, C.label j = C.label anchor →
        P.value D (x j) = if anchor = j then 1 else 0) ∧
      P.mass ≤
        (Real.sqrt 2 /
          (((r : ℝ) / nStar) * D * Δ / Real.pi)) ^ (nStar - 1) := by
  classical
  let S := C.neighbors anchor
  let q := S.card
  let e : Fin q ≃ S := (Fintype.equivFinOfCardEq (by simp [q])).symm
  let u : Fin q → Point d :=
    fun i => wrappedDifference (x (e i)) (x anchor)
  have hq : q ≤ nStar - 1 := C.neighbors_card anchor
  have hnStarR : (0 : ℝ) < nStar := by exact_mod_cast hnStar
  have hT : 2 ≤ (r : ℝ) / nStar := by
    apply (le_div_iff₀ hnStarR).2
    exact_mod_cast hr
  have hΔu (i : Fin q) : Δ ≤ l1Norm (u i) := by
    change Δ ≤ l1Norm (wrappedDifference (x (e i)) (x anchor))
    rw [l1Norm_wrappedDifference (hcube (e i)) (hcube anchor)]
    apply hmin
    exact ((C.mem_neighbors anchor (e i)).mp (e i).property).1
  have hu (i : Fin q) : l1Norm (u i) ≤ Real.pi / (2 * D) := by
    calc
      l1Norm (u i)
          ≤ d * periodicLInfDistance (x (e i)) (x anchor) := by
        exact l1Norm_wrappedDifference_le (hcube (e i)) (hcube anchor)
      _ ≤ d * τ := by
        gcongr
        exact hsame _ _
          ((C.mem_neighbors anchor (e i)).mp (e i).property).2
      _ ≤ Real.pi / (2 * D) := by
        have hDR : (0 : ℝ) < D := by exact_mod_cast hD
        have hdR : (0 : ℝ) < d := by exact_mod_cast hd
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * D)).2
        have hh := mul_le_mul_of_nonneg_left hτ (show (0 : ℝ) ≤ d by positivity)
        field_simp at hh ⊢
        nlinarith [Real.pi_pos]
  have hscale' : ((r : ℝ) / nStar) * D * Δ ≤ Real.pi := by
    have hrD : (0 : ℝ) < r * D := by
      have : 0 < r := by omega
      positivity
    have hh := (le_div_iff₀ hrD).1 hscale
    field_simp
    field_simp at hh
    nlinarith
  obtain ⟨B, hB0, hBzero, hBmass⟩ :=
    segmentedNeighborProduct hT hD hΔ u hΔu hu hscale'
  have hfloor : ⌊(r : ℝ) / nStar⌋₊ = r / nStar := by
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have hcoarse : q * ⌊(r : ℝ) / nStar⌋₊ ≤ r - r / nStar := by
    rw [hfloor]
    have hdiv := Nat.div_mul_le_self r nStar
    have hqsucc : q + 1 ≤ nStar := by omega
    have hmul := Nat.mul_le_mul_right (r / nStar) hqsucc
    have : q * (r / nStar) + r / nStar ≤ r := by
      calc
        _ = (q + 1) * (r / nStar) := by ring
        _ ≤ nStar * (r / nStar) := hmul
        _ ≤ r := by simpa [Nat.mul_comm] using hdiv
    omega
  let P : SegmentedPacket d 0 (r - r / nStar) :=
    (B.translate D (x anchor)).widen le_rfl hcoarse
  have hfactor :
      1 ≤ Real.sqrt 2 /
        (((r : ℝ) / nStar) * D * Δ / Real.pi) := by
    have hden : 0 < ((r : ℝ) / nStar) * D * Δ / Real.pi := by positivity
    have hdenOne :
        ((r : ℝ) / nStar) * D * Δ / Real.pi ≤ 1 :=
      (div_le_one Real.pi_pos).2 hscale'
    have hsqrt : 1 ≤ Real.sqrt 2 := (Real.one_le_sqrt).2 (by norm_num)
    exact (le_div_iff₀ hden).2 (by nlinarith)
  refine ⟨P, ?_, ?_⟩
  · intro j hj
    simp only [P, SegmentedPacket.value_widen,
      SegmentedPacket.value_translate]
    by_cases hja : anchor = j
    · subst j
      simp [hB0]
    · rw [if_neg hja]
      have hjS : j ∈ S := by
        simp [S, Ne.symm hja, hj]
      let j' : S := ⟨j, hjS⟩
      have he : (e (e.symm j')).val = j :=
        congrArg Subtype.val (e.apply_symm_apply j')
      have hz := hBzero (e.symm j')
      change
        B.value D
          (wrappedDifference (x (e (e.symm j'))) (x anchor)) = 0 at hz
      rw [he] at hz
      rw [SegmentedPacket.value_sub_eq_wrappedDifference, hz]
  · simp only [P, SegmentedPacket.mass_widen,
      SegmentedPacket.mass_translate]
    exact hBmass.trans (pow_le_pow_right₀ hfactor hq)

/-- A partition whose fibers have size at most `nStar` admits injective slots. -/
theorem exists_clumpSlots
    {d n A nStar : ℕ} {x : Fin n → Point d}
    (label : Fin n → Fin A)
    (hsize : ∀ a, (Finset.univ.filter fun j => label j = a).card ≤ nStar) :
    ∃ C : ClumpSlots (A := A) (nStar := nStar) x, C.label = label := by
  classical
  let S (a : Fin A) := {j : Fin n // label j = a}
  have hc (a : Fin A) : Fintype.card (S a) ≤ Fintype.card (Fin nStar) := by
    simpa [S, Fintype.card_subtype] using hsize a
  let e (a : Fin A) : S a ↪ Fin nStar :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (hc a))
  let slot (j : Fin n) := e (label j) ⟨j, rfl⟩
  refine ⟨{ label := label, slot := slot, injective := ?_ }, rfl⟩
  intro i j hij
  have hl := congrArg Prod.fst hij
  have hs := congrArg Prod.snd hij
  change label i = label j at hl
  change e (label i) ⟨i, rfl⟩ = e (label j) ⟨j, rfl⟩ at hs
  have transport (a b : Fin A) (hab : a = b) (u : Fin n)
      (hu : label u = a) :
      e a ⟨u, hu⟩ = e b ⟨u, hu.trans hab⟩ := by
    subst b
    rfl
  have hs' : e (label j) ⟨i, hl⟩ = e (label j) ⟨j, rfl⟩ :=
    (transport (label i) (label j) hl i rfl).symm.trans hs
  exact congrArg Subtype.val ((e (label j)).injective hs')

/-- One separated color class, with the anchor inserted in every class. -/
def clumpColorClass
    {d n A nStar : ℕ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x)
    (anchor : Fin n) (color : Fin nStar) :
    Finset (Fin n) :=
  Finset.univ.filter fun j =>
    j = anchor ∨ (C.label j ≠ C.label anchor ∧ C.slot j = color)

@[simp] theorem mem_clumpColorClass
    {d n A nStar : ℕ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x)
    (anchor j : Fin n) (color : Fin nStar) :
    j ∈ clumpColorClass C anchor color ↔
      j = anchor ∨ (C.label j ≠ C.label anchor ∧ C.slot j = color) := by
  simp [clumpColorClass]

theorem anchor_mem_clumpColorClass
    {d n A nStar : ℕ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x)
    (anchor : Fin n) (color : Fin nStar) :
    anchor ∈ clumpColorClass C anchor color := by
  simp

/-- Distinct nodes in one color class belong to different original clumps. -/
theorem clumpColorClass_labels_ne
    {d n A nStar : ℕ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x)
    (anchor : Fin n) (color : Fin nStar)
    (i j : ↥(clumpColorClass C anchor color)) (hij : i ≠ j) :
    C.label i ≠ C.label j := by
  intro hlabel
  have hi := (mem_clumpColorClass C anchor i color).mp i.property
  have hj := (mem_clumpColorClass C anchor j color).mp j.property
  apply hij
  apply Subtype.ext
  rcases hi with hi | ⟨hi, hsi⟩ <;>
      rcases hj with hj | ⟨hj, hsj⟩
  · exact hi.trans hj.symm
  · exact False.elim (hj (by simpa [hi] using hlabel.symm))
  · exact False.elim (hi (by simpa [hj] using hlabel))
  · exact C.injective (Prod.ext hlabel (hsi.trans hsj.symm))

/-- Evaluation matrix on the nonnegative integer cube `{0,...,K}^d`. -/
noncomputable def fineCubeEvaluation
    {d : ℕ} {ι : Type*} (K : ℕ) (x : ι → Point d) :
    Matrix (UniformIndex d K) ι ℂ :=
  fun α j => Complex.exp
    (Complex.I * ((∑ k, (α k : ℝ) * x j k : ℝ) : ℂ))

/-- The exact one-sided fine-cube frame input needed by localization. Nodes
are restricted to the manuscript's angular fundamental domain because the
coordinate formula for `periodicLInfDistance` is valid only there. -/
def HasFineCubeFrame (d K : ℕ) (η a : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x : ι → Point d),
    (∀ j, InAngularCube (x j)) →
    (∀ i j, i ≠ j → η < periodicLInfDistance (x i) (x j)) →
    ∀ v,
      a * (((K + 1) ^ d : ℕ) : ℝ) * SegmentedVDM.energy v ≤
        SegmentedVDM.energy (fineCubeEvaluation K x *ᵥ v)

theorem periodicCoordinateDistance_le_pi
    {u v : ℝ}
    (hu : -Real.pi < u ∧ u ≤ Real.pi)
    (hv : -Real.pi < v ∧ v ≤ Real.pi) :
    periodicCoordinateDistance u v ≤ Real.pi := by
  unfold periodicCoordinateDistance
  by_cases h : |u - v| ≤ Real.pi
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

theorem periodicLInfDistance_le_pi
    {d : ℕ} {u v : Point d}
    (hu : InAngularCube u) (hv : InAngularCube v) :
    periodicLInfDistance u v ≤ Real.pi := by
  unfold periodicLInfDistance
  rw [pi_norm_le_iff_of_nonneg Real.pi_pos.le]
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact periodicCoordinateDistance_le_pi (hu k) (hv k)
  · unfold periodicCoordinateDistance
    have habs : |u k - v k| ≤ 2 * Real.pi := by
      rw [abs_le]
      constructor <;> linarith [(hu k).1, (hu k).2, (hv k).1, (hv k).2]
    exact le_min (abs_nonneg _) (sub_nonneg.2 habs)

/-- A zero-width fine cube has a valid frame on a subsingleton node family. -/
theorem fineCube_frame_zero_of_subsingleton
    {ι : Type*} [Fintype ι] [Subsingleton ι]
    {d : ℕ} (x : ι → Point d) {a : ℝ} (ha : a ≤ 1) :
    ∀ v,
      a * ((((0 + 1) ^ d : ℕ) : ℝ)) * SegmentedVDM.energy v ≤
        SegmentedVDM.energy (fineCubeEvaluation 0 x *ᵥ v) := by
  classical
  intro v
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      letI := hempty
      simp [SegmentedVDM.energy, fineCubeEvaluation, Matrix.mulVec, dotProduct]
  | inr hnonempty =>
      letI := hnonempty
      letI : Unique ι :=
        { default := Classical.arbitrary ι
          uniq := fun _ => Subsingleton.elim _ _ }
      have he :
          SegmentedVDM.energy (fineCubeEvaluation 0 x *ᵥ v) =
            SegmentedVDM.energy v := by
        simp [SegmentedVDM.energy, fineCubeEvaluation, Matrix.mulVec,
          dotProduct, Fintype.sum_unique]
      simpa [he] using
        mul_le_of_le_one_left (SegmentedVDM.energy_nonneg v) ha

/-- At separation scale at least `π`, an angular-cube family satisfying the
strict separation premise is a subsingleton, so the zero-width frame is exact. -/
theorem hasFineCubeFrame_zero_of_pi_le
    (d : ℕ) {η a : ℝ} (hη : Real.pi ≤ η) (ha : a ≤ 1) :
    HasFineCubeFrame d 0 η a := by
  unfold HasFineCubeFrame
  intro ι _ _ x hx hsep v
  letI : Subsingleton ι :=
    ⟨fun i j => by
      apply Classical.byContradiction
      intro hij
      have hdist := periodicLInfDistance_le_pi (hx i) (hx j)
      exact (not_lt_of_ge hdist) (hη.trans_lt (hsep i j hij))⟩
  exact fineCube_frame_zero_of_subsingleton x ha v

/-- The manuscript's separation scale automatically discharges the zero-order
fine-cube case in every positive dimension. -/
theorem hasFineCubeFrame_zero_of_sourceRange
    (d : ℕ) (hd : 1 ≤ d) (β η : ℝ)
    (hβ : 1 / (2 * Real.log 2) < β)
    (hη : 4 * Real.pi * β * d ≤ η) :
    HasFineCubeFrame d 0 η (2 - Real.exp (1 / (2 * β))) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hquarter : (1 : ℝ) / 4 < 1 / (2 * Real.log 2) := by
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [Real.log_two_lt_d9]
  have hβquarter : (1 : ℝ) / 4 < β := hquarter.trans hβ
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hfactor : (1 : ℝ) ≤ 4 * β * d := by
    calc
      (1 : ℝ) = 4 * ((1 : ℝ) / 4) * 1 := by ring
      _ ≤ 4 * β * d := by gcongr
  have hpi : Real.pi ≤ 4 * Real.pi * β * d := by
    calc
      Real.pi = Real.pi * 1 := by ring
      _ ≤ Real.pi * (4 * β * d) :=
        mul_le_mul_of_nonneg_left hfactor Real.pi_pos.le
      _ = 4 * Real.pi * β * d := by ring
  apply hasFineCubeFrame_zero_of_pi_le d (hpi.trans hη)
  have hβpos : 0 < β := by linarith
  have hexp : 1 ≤ Real.exp (1 / (2 * β)) :=
    Real.one_le_exp (by positivity)
  linarith

theorem periodicCoordinateDistance_le_integerTranslate
    {u v : ℝ}
    (hu : -Real.pi < u ∧ u ≤ Real.pi)
    (hv : -Real.pi < v ∧ v ≤ Real.pi)
    (p : ℤ) :
    periodicCoordinateDistance u v ≤
      |u - v - 2 * Real.pi * p| := by
  have hdiffLower : -2 * Real.pi < u - v := by linarith
  have hdiffUpper : u - v < 2 * Real.pi := by linarith
  by_cases hp0 : p = 0
  · subst p
    simp only [Int.cast_zero, mul_zero, sub_zero]
    exact min_le_left _ _
  by_cases hp : 1 ≤ p
  · have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hnonpos : u - v - 2 * Real.pi * p ≤ 0 := by
      nlinarith [Real.pi_pos]
    rw [abs_of_nonpos hnonpos]
    exact (min_le_right _ _).trans (by
      have hle := le_abs_self (u - v)
      nlinarith [Real.pi_pos])
  · have hp : p ≤ -1 := by omega
    have hpR : (p : ℝ) ≤ -1 := by exact_mod_cast hp
    have hnonneg : 0 ≤ u - v - 2 * Real.pi * p := by
      nlinarith [Real.pi_pos]
    rw [abs_of_nonneg hnonneg]
    exact (min_le_right _ _).trans (by
      have hle := neg_le_abs (u - v)
      nlinarith [Real.pi_pos])

/-- The proved one-dimensional consecutive-sampling theorem supplies a
fine-cube lower frame constant of `1/2`. -/
theorem fineCube_frame_half_oneDimensional
    {K : ℕ} {ι : Type} [Fintype ι]
    (hK : 1 ≤ K) (x : ι → Point 1)
    (hx : ∀ j, InAngularCube (x j))
    (hsep : ∀ i j, i ≠ j →
      4 * Real.pi / (K + 1) ≤ periodicLInfDistance (x i) (x j)) :
    ∀ v,
      (((K + 1 : ℕ) : ℝ) / 2) * SegmentedVDM.energy v ≤
        SegmentedVDM.energy (fineCubeEvaluation K x *ᵥ v) := by
  intro v
  have hsep' : ∀ i j, i ≠ j → ∀ p : ℤ,
      4 * Real.pi / (K + 1) ≤
        |x i 0 - x j 0 - 2 * Real.pi * p| := by
    intro i j hij p
    have hcoord :
        4 * Real.pi / (K + 1) ≤
          periodicCoordinateDistance (x i 0) (x j 0) := by
      have hnonneg :
          0 ≤ periodicCoordinateDistance (x i 0) (x j 0) := by
        unfold periodicCoordinateDistance
        have habs : |x i 0 - x j 0| ≤ 2 * Real.pi := by
          rw [abs_le]
          constructor <;>
            linarith [(hx i 0).1, (hx i 0).2, (hx j 0).1, (hx j 0).2]
        exact le_min (abs_nonneg _) (sub_nonneg.2 habs)
      have hfun :
          (fun k : Fin 1 =>
              periodicCoordinateDistance (x i k) (x j k)) =
            fun _ => periodicCoordinateDistance (x i 0) (x j 0) := by
        funext k
        exact congrArg
          (fun k => periodicCoordinateDistance (x i k) (x j k))
          (Fin.eq_zero k)
      simpa [periodicLInfDistance, hfun, Real.norm_eq_abs,
        abs_of_nonneg hnonneg] using hsep i j hij
    exact hcoord.trans
      (periodicCoordinateDistance_le_integerTranslate
        (hx i 0) (hx j 0) p)
  have h :=
    SegmentedVDM.uniform_frame_half K (fun j => x j 0) hsep' v
  have henergy :
      SegmentedVDM.energy (fineCubeEvaluation K x *ᵥ v) =
        SegmentedVDM.energy
          (SegmentedVDM.uniformEvaluation K (fun j => x j 0) *ᵥ v) := by
    let e := Equiv.funUnique (Fin 1) (Fin (K + 1))
    unfold SegmentedVDM.energy fineCubeEvaluation Matrix.mulVec dotProduct
      SegmentedVDM.uniformEvaluation
    apply Fintype.sum_equiv e
    intro α
    congr 1
    apply congrArg norm
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    simp [e]
  rw [henergy]
  simpa only [Nat.cast_add, Nat.cast_one] using h

theorem fineCube_frame_oneDimensional_of_halfConstant
    {K : ℕ} {ι : Type} [Fintype ι]
    (hK : 1 ≤ K) (x : ι → Point 1)
    (hx : ∀ j, InAngularCube (x j)) {a : ℝ} (ha : a ≤ 1 / 2)
    (hsep : ∀ i j, i ≠ j →
      4 * Real.pi / (K + 1) ≤ periodicLInfDistance (x i) (x j)) :
    ∀ v,
      a * (((K + 1) ^ 1 : ℕ) : ℝ) * SegmentedVDM.energy v ≤
        SegmentedVDM.energy (fineCubeEvaluation K x *ᵥ v) := by
  intro v
  apply (show
      a * (((K + 1) ^ 1 : ℕ) : ℝ) * SegmentedVDM.energy v ≤
        (((K + 1 : ℕ) : ℝ) / 2) * SegmentedVDM.energy v by
      simp only [pow_one, Nat.cast_add, Nat.cast_one]
      calc
        a * (K + 1) * SegmentedVDM.energy v ≤
            (1 / 2) * (K + 1) * SegmentedVDM.energy v :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right ha (by positivity))
            (SegmentedVDM.energy_nonneg v)
        _ = (K + 1) / 2 * SegmentedVDM.energy v := by ring).trans
  exact fineCube_frame_half_oneDimensional hK x hx hsep v

/-- Automatic one-dimensional fine-cube frame in the parameter range covered
by the proved `1/2` consecutive-sampling constant. -/
theorem fineCube_frame_oneDimensional_of_sourceRange
    {K : ℕ} {ι : Type} [Fintype ι]
    (β η : ℝ) (hβone : 1 ≤ β)
    (ha : 2 - Real.exp (1 / (2 * β)) ≤ 1 / 2)
    (hη : 4 * Real.pi * β / (K + 1) ≤ η)
    (x : ι → Point 1) (hx : ∀ j, InAngularCube (x j))
    (hsep : ∀ i j, i ≠ j →
      η < periodicLInfDistance (x i) (x j)) :
    ∀ v,
      (2 - Real.exp (1 / (2 * β))) *
          (((K + 1) ^ 1 : ℕ) : ℝ) *
          SegmentedVDM.energy v ≤
        SegmentedVDM.energy (fineCubeEvaluation K x *ᵥ v) := by
  have hβpos : 0 < β := zero_lt_one.trans_le hβone
  by_cases hKzero : K = 0
  · subst K
    norm_num at hη
    have hlarge : Real.pi < 4 * Real.pi * β := by
      nlinarith [Real.pi_pos]
    have hsub : Subsingleton ι := ⟨fun i j => by
        apply Classical.byContradiction
        intro hij
        have hu := periodicLInfDistance_le_pi (hx i) (hx j)
        have hs := (lt_of_lt_of_le hlarge hη).trans (hsep i j hij)
        exact (not_lt_of_ge hu) hs⟩
    letI := hsub
    apply fineCube_frame_zero_of_subsingleton x
    linarith
  · apply fineCube_frame_oneDimensional_of_halfConstant
      (Nat.one_le_iff_ne_zero.2 hKzero) x hx ha
    intro i j hij
    calc
      4 * Real.pi / (K + 1)
          ≤ 4 * Real.pi * β / (K + 1) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            nlinarith [Real.pi_pos]
      _ ≤ η := hη
      _ ≤ periodicLInfDistance (x i) (x j) := (hsep i j hij).le

/-- A lower frame bound produces one cardinal polynomial on the fine cube. -/
theorem fineCube_cardinalPacket
    {d K : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Point d) (j : ι) {a : ℝ} (ha : 0 < a)
    (hframe : ∀ v,
      a * (((K + 1) ^ d : ℕ) : ℝ) * SegmentedVDM.energy v ≤
        SegmentedVDM.energy (fineCubeEvaluation K x *ᵥ v)) :
    ∃ P : SegmentedPacket d K 0,
      (∀ D k, P.value D (x k) = if j = k then 1 else 0) ∧
      P.mass ≤ 1 / Real.sqrt a := by
  obtain ⟨c, hc, hcnorm⟩ :=
    SegmentedVDM.cardinal_coefficients_of_frame (fineCubeEvaluation K x)
      (show 0 < a * (((K + 1) ^ d : ℕ) : ℝ) by positivity)
      (by
        intro v
        simpa only [mul_assoc] using hframe v)
      j
  let P : SegmentedPacket d K 0 := {
    Index := UniformIndex d K
    finite := inferInstance
    coarse := fun _ _ => 0
    fine := fun α k => α k
    coarse_le := fun _ _ => le_rfl
    fine_le := fun α k => Nat.le_of_lt_succ (α k).isLt
    coeff := c }
  refine ⟨P, ?_, ?_⟩
  · intro D k
    convert! hc k using 1
    simp [P, SegmentedPacket.value, fineCubeEvaluation, dotProduct]
  · have hs := sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun i => ‖c i‖)
    have hcard : Fintype.card (UniformIndex d K) = (K + 1) ^ d := by
      simp [UniformIndex]
    rw [Finset.card_univ, hcard] at hs
    have hscale : (0 : ℝ) < (((K + 1) ^ d : ℕ) : ℝ) := by positivity
    have hsq : P.mass ^ 2 ≤ 1 / a := by
      have h := mul_le_mul_of_nonneg_left hcnorm hscale.le
      have he :
          (((K + 1) ^ d : ℕ) : ℝ) *
              (1 / (a * (((K + 1) ^ d : ℕ) : ℝ))) =
            1 / a := by
        field_simp
      rw [he] at h
      exact hs.trans h
    have he : (1 / Real.sqrt a) ^ 2 = 1 / a := by
      rw [div_pow, one_pow, Real.sq_sqrt ha.le]
    exact (sq_le_sq₀ P.mass_nonneg (by positivity)).mp (by rwa [he])

/-- Product of one cardinal factor per color eliminates every node outside the
anchor's clump. -/
theorem localizationPacket_of_colorFrames
    {d n A nStar K : ℕ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x) (anchor : Fin n)
    {a : ℝ} (ha : 0 < a)
    (hframe : ∀ color (v : ↥(clumpColorClass C anchor color) → ℂ),
      a * (((K + 1) ^ d : ℕ) : ℝ) * SegmentedVDM.energy v ≤
        SegmentedVDM.energy
          (fineCubeEvaluation K
            (fun j : ↥(clumpColorClass C anchor color) => x j) *ᵥ v)) :
    ∃ P : SegmentedPacket d (nStar * K) 0,
      (∀ D, P.value D (x anchor) = 1) ∧
      (∀ D j, C.label j ≠ C.label anchor → P.value D (x j) = 0) ∧
      P.mass ≤ (1 / Real.sqrt a) ^ nStar := by
  classical
  choose F hF using fun color =>
    fineCube_cardinalPacket
      (fun j : ↥(clumpColorClass C anchor color) => x j)
      ⟨anchor, anchor_mem_clumpColorClass C anchor color⟩ ha
      (hframe color)
  let P : SegmentedPacket d (nStar * K) 0 :=
    (SegmentedPacket.prod F).widen (by simp) (by simp)
  refine ⟨P, ?_, ?_, ?_⟩
  · intro D
    simp only [P, SegmentedPacket.value_widen, SegmentedPacket.value_prod]
    have hone (color : Fin nStar) : (F color).value D (x anchor) = 1 := by
      simpa using (hF color).1 D
        ⟨anchor, anchor_mem_clumpColorClass C anchor color⟩
    simp [hone]
  · intro D j hj
    simp only [P, SegmentedPacket.value_widen, SegmentedPacket.value_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ (C.slot j))
    have hmem : j ∈ clumpColorClass C anchor (C.slot j) := by
      simp [hj]
    have hzero := (hF (C.slot j)).1 D ⟨j, hmem⟩
    have hne : anchor ≠ j := by
      intro he
      exact hj (congrArg C.label he.symm)
    simpa [Subtype.ext_iff, hne] using hzero
  · simp only [P, SegmentedPacket.mass_widen, SegmentedPacket.mass_prod]
    calc
      _ ≤ ∏ _color : Fin nStar, 1 / Real.sqrt a :=
        Finset.prod_le_prod
          (fun color _ => (F color).mass_nonneg)
          (fun color _ => (hF color).2)
      _ = _ := by simp

/-- Combine localization outside the anchor's clump with quantized
interpolation inside that clump. -/
theorem segmentedInterpolationPacket_of_colorFrames
    {d n A nStar K m₁ r D : ℕ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x) (anchor : Fin n)
    (hd : 1 ≤ d) (hnStar : 1 ≤ nStar) (hr : 2 * nStar ≤ r)
    (hD : 0 < D) {τ Δ a : ℝ} (hΔ : 0 < Δ)
    (hcube : ∀ j, InAngularCube (x j))
    (hsame : ∀ i j, C.label i = C.label j →
      periodicLInfDistance (x i) (x j) ≤ τ)
    (hτ : τ ≤ Real.pi / (2 * D * d))
    (hmin : ∀ i j, i ≠ j →
      Δ ≤ periodicL1Distance (x i) (x j))
    (hscale : Δ ≤ Real.pi * nStar / (r * D))
    (ha : 0 < a) (hK : nStar * K ≤ m₁)
    (hframe : ∀ color (v : ↥(clumpColorClass C anchor color) → ℂ),
      a * (((K + 1) ^ d : ℕ) : ℝ) * SegmentedVDM.energy v ≤
        SegmentedVDM.energy
          (fineCubeEvaluation K
            (fun j : ↥(clumpColorClass C anchor color) => x j) *ᵥ v)) :
    ∃ P : SegmentedPacket d m₁ (r - r / nStar),
      (∀ j, P.value D (x j) = if anchor = j then 1 else 0) ∧
      P.mass ≤
        (1 / Real.sqrt a) ^ nStar *
        (Real.sqrt 2 /
          (((r : ℝ) / nStar) * D * Δ / Real.pi)) ^ (nStar - 1) := by
  classical
  obtain ⟨G₀, hGanchor, hGzero, hGmass⟩ :=
    localizationPacket_of_colorFrames C anchor ha hframe
  let G : SegmentedPacket d m₁ 0 :=
    G₀.widen hK le_rfl
  obtain ⟨B, hBvalue, hBmass⟩ :=
    withinClumpPacket C anchor hd hnStar hr hD hΔ hcube hsame hτ hmin hscale
  let P : SegmentedPacket d m₁ (r - r / nStar) :=
    (G.mul B).widen (by simp) (by simp)
  refine ⟨P, ?_, ?_⟩
  · intro j
    simp only [P, SegmentedPacket.value_widen, SegmentedPacket.value_mul,
      G, SegmentedPacket.value_widen]
    by_cases hj : C.label j = C.label anchor
    · rw [hBvalue j hj]
      by_cases haj : anchor = j
      · subst j
        simp [hGanchor]
      · simp [haj]
    · rw [hGzero D j hj, zero_mul]
      have haj : anchor ≠ j := by
        intro h
        exact hj (congrArg C.label h.symm)
      simp [haj]
  · simp only [P, SegmentedPacket.mass_widen, SegmentedPacket.mass_mul,
      G, SegmentedPacket.mass_widen]
    exact mul_le_mul hGmass hBmass B.mass_nonneg (by positivity)

/-- The support assumptions expose slot data for the manuscript decomposition. -/
theorem clumpStructure_has_slots
    {d n A nStar : ℕ} {x : Fin n → Point d} {τ η : ℝ}
    (h : IsAngularClumpStructure x A nStar τ η) :
    ∃ C : ClumpSlots (A := A) (nStar := nStar) x,
      (∀ i j, C.label i = C.label j →
        periodicLInfDistance (x i) (x j) ≤ τ) ∧
      ∀ i j, C.label i ≠ C.label j →
        η < periodicLInfDistance (x i) (x j) := by
  rcases h with ⟨_, _, _, _, label, _, hsize, _, hsame, hcross⟩
  obtain ⟨C, hC⟩ := exists_clumpSlots label hsize
  refine ⟨C, ?_, ?_⟩
  · intro i j hij
    exact hsame i j (by simpa only [hC] using hij)
  · intro i j hij
    exact hcross i j (by simpa only [hC] using hij)

/-- Complete segmented packet construction from fine-cube frame bounds.  This
is the algebraic and geometric core of the manuscript theorem; the remaining
analytic input is exactly `hframe`. -/
theorem segmentedVandermonde_ge_of_colorFrames
    {d n A nStar m₁ b m r D K : ℕ} {τ η Δ a : ℝ}
    (μ : AtomicMeasure d n) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hsplit : m₁ + b = m) (hK : nStar * K ≤ m₁)
    (hD : 0 < D) (hτ : τ ≤ Real.pi / (2 * D * d))
    (hr : 2 * nStar ≤ r) (hΔ : 0 < Δ)
    (hmin : ∀ i j, i ≠ j →
      Δ ≤ periodicL1Distance (μ.node i) (μ.node j))
    (hscale : Δ ≤ Real.pi * nStar / (r * D))
    (ha : 0 < a)
    (hframe :
      ∀ (C : ClumpSlots (A := A) (nStar := nStar) μ.node)
        (anchor : Fin n),
        (∀ i j, C.label i = C.label j →
          periodicLInfDistance (μ.node i) (μ.node j) ≤ τ) →
        (∀ i j, C.label i ≠ C.label j →
          η < periodicLInfDistance (μ.node i) (μ.node j)) →
        ∀ color (v : ↥(clumpColorClass C anchor color) → ℂ),
          a * (((K + 1) ^ d : ℕ) : ℝ) * SegmentedVDM.energy v ≤
            SegmentedVDM.energy
              (fineCubeEvaluation K
                (fun j : ↥(clumpColorClass C anchor color) => μ.node j) *ᵥ v)) :
    let H :=
      (1 / Real.sqrt a) ^ nStar *
        (Real.sqrt 2 /
          (((r : ℝ) / nStar) * D * Δ / Real.pi)) ^ (nStar - 1)
    Real.sqrt
          (((((r / nStar) + 1) * (b + 1)) ^ d : ℕ) : ℝ) /
        (Real.sqrt n * H) ≤
      matrixSingularValue
        (segmentedVandermonde m r D μ.node) (n - 1) := by
  classical
  dsimp only
  have hnStar : 1 ≤ nStar := (hclumps.1).trans' (by omega)
  have hcube : ∀ j, InAngularCube (μ.node j) := hclumps.2.2.2.1
  obtain ⟨C, hsame, hcross⟩ := clumpStructure_has_slots hclumps
  choose P hPvalue hPmass using fun anchor =>
    segmentedInterpolationPacket_of_colorFrames C anchor hd hnStar hr hD hΔ
      hcube hsame hτ hmin hscale ha hK
      (hframe C anchor hsame hcross)
  let H :=
    (1 / Real.sqrt a) ^ nStar *
      (Real.sqrt 2 /
        (((r : ℝ) / nStar) * D * Δ / Real.pi)) ^ (nStar - 1)
  have hH : 0 < H := by
    dsimp [H]
    have hrPos : 0 < r := by omega
    have hnStarR : (0 : ℝ) < nStar := by exact_mod_cast hnStar
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD
    have hrR : (0 : ℝ) < r := by exact_mod_cast hrPos
    have hden :
        0 < ((r : ℝ) / nStar) * D * Δ / Real.pi := by
      positivity
    exact mul_pos (pow_pos (by positivity) _) (pow_pos (by positivity) _)
  have hh :=
    SegmentedPacket.singularValue_ge_of_smoothedSegmentedPackets
      (Nat.zero_lt_of_lt hn) μ.node P hPvalue hH hPmass
      (b := b) (z := r / nStar)
  rw [hsplit] at hh
  have hdiv : r / nStar ≤ r := Nat.div_le_self r nStar
  rw [Nat.sub_add_cancel hdiv] at hh
  exact hh

/-- Rewrite the packet-mass ratio into the explicit manuscript constant. -/
theorem segmentedLowerBound_le_smoothedRatio
    {d n nStar b r D : ℕ} {a Δ : ℝ}
    (hn : 0 < n) (hnStar : 0 < nStar) (hr : 0 < r) (hD : 0 < D)
    (ha : 0 < a) (hΔ : 0 < Δ) :
    1 / Real.sqrt n *
          a ^ ((nStar : ℝ) / 2) *
          Real.sqrt
            (((r : ℝ) / nStar) ^ d *
              (((b + 1 : ℕ) : ℝ) ^ d)) /
          (Real.sqrt 2) ^ (nStar - 1) *
          ((((r * D : ℕ) : ℝ) / (Real.pi * nStar) * Δ) ^
            (nStar - 1)) ≤
      Real.sqrt
          (((((r / nStar) + 1) * (b + 1)) ^ d : ℕ) : ℝ) /
        (Real.sqrt n *
          ((1 / Real.sqrt a) ^ nStar *
            (Real.sqrt 2 /
              (((r : ℝ) / nStar) * D * Δ / Real.pi)) ^
                (nStar - 1))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnStarR : (0 : ℝ) < nStar := by exact_mod_cast hnStar
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hz :
      (r : ℝ) / nStar ≤ ((r / nStar : ℕ) : ℝ) + 1 := by
    have hlt := Nat.lt_mul_div_succ r hnStar
    have hltR :
        (r : ℝ) < nStar * ((r / nStar : ℕ) + 1) := by
      exact_mod_cast hlt
    exact (div_le_iff₀ hnStarR).2 (by
      simpa only [mul_comm] using hltR.le)
  have hbase :
      (r : ℝ) / nStar * (b + 1) ≤
        (((r / nStar : ℕ) : ℝ) + 1) * (b + 1) := by
    gcongr
  have hpow :
      ((r : ℝ) / nStar * (b + 1)) ^ d ≤
        ((((r / nStar : ℕ) : ℝ) + 1) * (b + 1)) ^ d :=
    pow_le_pow_left₀ (by positivity) hbase d
  have hvolume :
      Real.sqrt
          (((r : ℝ) / nStar) ^ d *
            (((b + 1 : ℕ) : ℝ) ^ d)) ≤
        Real.sqrt
          (((((r / nStar) + 1) * (b + 1)) ^ d : ℕ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    push_cast
    simpa only [mul_pow] using hpow
  have hsqrtpow :
      (Real.sqrt a) ^ nStar = a ^ ((nStar : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ha.le]
    congr 1
    ring
  have ht :
      ((r : ℝ) / nStar) * D * Δ / Real.pi =
        ((r * D : ℕ) : ℝ) / (Real.pi * nStar) * Δ := by
    push_cast
    field_simp
  let H :=
    (1 / Real.sqrt a) ^ nStar *
      (Real.sqrt 2 /
        (((r : ℝ) / nStar) * D * Δ / Real.pi)) ^ (nStar - 1)
  have hH : 0 < H := by
    dsimp [H]
    positivity
  calc
    1 / Real.sqrt n *
          a ^ ((nStar : ℝ) / 2) *
          Real.sqrt
            (((r : ℝ) / nStar) ^ d *
              (((b + 1 : ℕ) : ℝ) ^ d)) /
          (Real.sqrt 2) ^ (nStar - 1) *
          ((((r * D : ℕ) : ℝ) / (Real.pi * nStar) * Δ) ^
            (nStar - 1)) =
        Real.sqrt
            (((r : ℝ) / nStar) ^ d *
              (((b + 1 : ℕ) : ℝ) ^ d)) /
          (Real.sqrt n * H) := by
      dsimp [H]
      rw [← hsqrtpow, ← ht]
      ring_nf
      field_simp [ne_of_gt hnStarR, ne_of_gt hrR, ne_of_gt hDR,
        ne_of_gt hΔ, ne_of_gt (Real.sqrt_pos.2 ha), Real.pi_ne_zero]
    _ ≤
        Real.sqrt
            (((((r / nStar) + 1) * (b + 1)) ^ d : ℕ) : ℝ) /
          (Real.sqrt n * H) :=
      div_le_div_of_nonneg_right hvolume (by positivity)

/-- Manuscript-shaped segmented Vandermonde bound from the exact one-sided
fine-cube frame input. -/
theorem segmentedVandermonde_minimumSingularValue_of_colorFrames
    {d n A nStar m₁ b m r D K : ℕ} {τ η Δ β : ℝ}
    (μ : AtomicMeasure d n) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hsplit : m₁ + b = m) (hK : nStar * K ≤ m₁)
    (hD : 0 < D) (hτ : τ ≤ Real.pi / (2 * D * d))
    (hβ : 1 / (2 * Real.log 2) < β)
    (hr : 2 * nStar ≤ r) (hΔ : 0 < Δ)
    (hmin : ∀ i j, i ≠ j →
      Δ ≤ periodicL1Distance (μ.node i) (μ.node j))
    (hscale : Δ ≤ Real.pi * nStar / (r * D))
    (hframe :
      ∀ (C : ClumpSlots (A := A) (nStar := nStar) μ.node)
        (anchor : Fin n),
        (∀ i j, C.label i = C.label j →
          periodicLInfDistance (μ.node i) (μ.node j) ≤ τ) →
        (∀ i j, C.label i ≠ C.label j →
          η < periodicLInfDistance (μ.node i) (μ.node j)) →
        ∀ color (v : ↥(clumpColorClass C anchor color) → ℂ),
          (2 - Real.exp (1 / (2 * β))) *
                (((K + 1) ^ d : ℕ) : ℝ) *
                SegmentedVDM.energy v ≤
            SegmentedVDM.energy
              (fineCubeEvaluation K
                (fun j : ↥(clumpColorClass C anchor color) => μ.node j) *ᵥ v)) :
    1 / Real.sqrt n *
          (2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2) *
          Real.sqrt
            (((r : ℝ) / nStar) ^ d *
              (((b + 1 : ℕ) : ℝ) ^ d)) /
          (Real.sqrt 2) ^ (nStar - 1) *
          ((((r * D : ℕ) : ℝ) / (Real.pi * nStar) * Δ) ^
            (nStar - 1)) ≤
      matrixSingularValue
        (segmentedVandermonde m r D μ.node) (n - 1) := by
  let a := 2 - Real.exp (1 / (2 * β))
  have ha : 0 < a := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hβpos : 0 < β :=
      (by positivity : 0 < 1 / (2 * Real.log 2)).trans hβ
    have hexponent : 1 / (2 * β) < Real.log 2 := by
      have h := (div_lt_iff₀ (by positivity : 0 < 2 * Real.log 2)).1 hβ
      apply (div_lt_iff₀ (by positivity : 0 < 2 * β)).2
      nlinarith
    have hexp : Real.exp (1 / (2 * β)) < 2 := by
      calc
        Real.exp (1 / (2 * β)) < Real.exp (Real.log 2) :=
          Real.exp_lt_exp.mpr hexponent
        _ = 2 := Real.exp_log (by norm_num)
    dsimp [a]
    linarith
  have hnStar : 0 < nStar :=
    (by omega : 0 < 2).trans_le hclumps.1
  have hrPos : 0 < r :=
    (Nat.mul_pos (by omega) hnStar).trans_le hr
  have hraw :=
    segmentedVandermonde_ge_of_colorFrames μ hd hn hclumps hsplit hK hD
      hτ hr hΔ hmin hscale ha hframe
  exact
    (segmentedLowerBound_le_smoothedRatio
      (Nat.zero_lt_of_lt hn) hnStar hrPos hD ha hΔ).trans hraw

/-- Every frequency queried by a segmented GHM lies in its declared band. -/
theorem segmented_query_in_band
    {d m r D : ℕ} (α β : SegmentedIndex d m r) :
    InFrequencyBand (segmentedCutoff m r D) (fun k =>
      segmentedFrequency d m r D α k +
        segmentedFrequency d m r D β k - segmentedCutoff m r D) := by
  intro k
  simp only [segmentedFrequency, segmentedCutoff]
  have hαr : (α k).1.val ≤ r := Nat.le_of_lt_succ (α k).1.isLt
  have hβr : (β k).1.val ≤ r := Nat.le_of_lt_succ (β k).1.isLt
  have hαm : (α k).2.val ≤ m := Nat.le_of_lt_succ (α k).2.isLt
  have hβm : (β k).2.val ≤ m := Nat.le_of_lt_succ (β k).2.isLt
  have hα : D * (α k).1.val + (α k).2.val ≤ r * D + m := by
    nlinarith [Nat.mul_le_mul_left D hαr]
  have hβ : D * (β k).1.val + (β k).2.val ≤ r * D + m := by
    nlinarith [Nat.mul_le_mul_left D hβr]
  push_cast
  rw [abs_le]
  have hαR : (D : ℝ) * (α k).1.val + (α k).2.val ≤
      (r : ℝ) * D + m := by exact_mod_cast hα
  have hβR : (D : ℝ) * (β k).1.val + (β k).2.val ≤
      (r : ℝ) * D + m := by exact_mod_cast hβ
  constructor <;> nlinarith [show (0 : ℝ) ≤ D * (α k).1.val + (α k).2.val by positivity,
    show (0 : ℝ) ≤ D * (β k).1.val + (β k).2.val by positivity]

/-- Pointwise perturbation bound for the segmented measurement matrix. -/
theorem segmentedMeasurementMatrix_sub_fourier_entry_lt
    {d n m r D : ℕ} {σ : ℝ}
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (hmeasurement : IsBandMeasurement μ (segmentedCutoff m r D) σ Y)
    (α β : SegmentedIndex d m r) :
    ‖(segmentedMeasurementMatrix m r D Y -
        segmentedMeasurementMatrix m r D (fourier μ)) α β‖ < σ := by
  rcases hmeasurement with ⟨W, hW, hY⟩
  let ω : Point d := fun k =>
    segmentedFrequency d m r D α k +
      segmentedFrequency d m r D β k - segmentedCutoff m r D
  have hband : InFrequencyBand (segmentedCutoff m r D) ω :=
    segmented_query_in_band α β
  have hvalue := hY ω hband
  have hnoise := hW ω hband
  simp only [segmentedMeasurementMatrix, Matrix.sub_apply]
  rw [hvalue, add_sub_cancel_left]
  exact hnoise

/-- Every singular value at or beyond the rank vanishes. -/
theorem matrixSingularValue_eq_zero_of_rank_le'
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) {i : ℕ} (hi : A.rank ≤ i) :
    matrixSingularValue A i = 0 := by
  rw [matrixSingularValue]
  apply (A.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range).2
  change Module.finrank ℂ (LinearMap.range
    ((Matrix.toLin (EuclideanSpace.basisFun n ℂ).toBasis
      (EuclideanSpace.basisFun m ℂ).toBasis) A)) ≤ i
  rw [← A.rank_eq_finrank_range_toLin
    (EuclideanSpace.basisFun m ℂ).toBasis
    (EuclideanSpace.basisFun n ℂ).toBasis]
  exact hi

/-- A product through `n` columns vanishes from singular-value index `n` onward. -/
theorem matrixSingularValue_mul_eq_zero_of_card_le'
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix n p ℂ) {i : ℕ}
    (hi : Fintype.card n ≤ i) :
    matrixSingularValue (A * B) i = 0 := by
  apply matrixSingularValue_eq_zero_of_rank_le'
  exact (Matrix.rank_mul_le_left A B).trans
    ((Matrix.rank_le_card_width A).trans hi)

/-- The noiseless segmented matrix has no singular values beyond the source count. -/
theorem segmentedNoiseless_singularValue_eq_zero
    {d n m r D i : ℕ} (μ : AtomicMeasure d n) (hi : n ≤ i) :
    matrixSingularValue (segmentedNoiselessMatrix m r D μ) i = 0 := by
  rw [segmentedNoiselessMatrix]
  apply matrixSingularValue_eq_zero_of_rank_le'
  have hcard : Fintype.card (Fin n) ≤ i := by simpa using hi
  exact
    (Matrix.rank_mul_le_left
      (segmentedVandermonde m r D μ.node *
        Matrix.diagonal (segmentedPhaseAmplitude m r D μ))
      (segmentedColumnVandermonde m r D μ.node)ᵀ).trans
      ((Matrix.rank_le_card_width
        (segmentedVandermonde m r D μ.node *
          Matrix.diagonal (segmentedPhaseAmplitude m r D μ))).trans hcard)

end

end NumDetect
end LeanNumDetect
