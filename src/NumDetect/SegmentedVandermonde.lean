import General.Fourier.FineCubeFrame
import General.Fourier.TranslatedCubeFourier
import General.Fourier.TrigonometricPolynomialParseval
import NumDetect.Matrices
import NumDetect.UniformInterpolation
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

/-- The `L^∞(𝕋^d)` sup norm of the trigonometric polynomial presented by `P`.
All frequencies of a presentation are integers, so `P.value D` is
`2 * Real.pi`-periodic in every coordinate (`value_two_pi_periodic`) and the
supremum over `Point d` agrees with the supremum over one fundamental domain.
`linftyNorm_eq_unitTorusLInfNorm` proves that this is exactly the torus
`L^∞` norm `unitTorusLInfNorm` of the polynomial
`unitTorusTrigPolynomial (P.angularFrequency D) P.coeff` in the manuscript's
normalization, i.e. the manuscript's `‖·‖_{L^∞(𝕋^d)}`. -/
noncomputable def linftyNorm {d m r : ℕ} (P : SegmentedPacket d m r)
    (D : ℕ) : ℝ :=
  ⨆ y : Point d, ‖P.value D y‖

/-- Every evaluation modulus is at most the coefficient `ℓ¹` mass by the
triangle inequality. -/
theorem value_norm_le_mass {d m r : ℕ} (P : SegmentedPacket d m r)
    (D : ℕ) (y : Point d) : ‖P.value D y‖ ≤ P.mass := by
  classical
  change ‖∑ i, P.coeff i * Complex.exp
      (Complex.I *
        ((∑ k, ((D * P.coarse i k + P.fine i k : ℕ) : ℝ) * y k : ℝ) : ℂ))‖ ≤
    P.mass
  refine (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum fun _ _ => by simp [Complex.norm_exp]

/-- The family of evaluation moduli is bounded above by the mass. -/
theorem linftyNorm_bddAbove {d m r : ℕ} (P : SegmentedPacket d m r)
    (D : ℕ) : BddAbove (Set.range fun y : Point d => ‖P.value D y‖) :=
  ⟨P.mass, by
    rintro _ ⟨y, rfl⟩
    exact P.value_norm_le_mass D y⟩

/-- The `L^∞(𝕋^d)` norm is bounded by the coefficient `ℓ¹` mass. -/
theorem linftyNorm_le_mass {d m r : ℕ} (P : SegmentedPacket d m r)
    (D : ℕ) : P.linftyNorm D ≤ P.mass :=
  ciSup_le fun y => P.value_norm_le_mass D y

/-- Every evaluation modulus is bounded by the `L^∞(𝕋^d)` norm. -/
theorem value_norm_le_linftyNorm {d m r : ℕ} (P : SegmentedPacket d m r)
    (D : ℕ) (y : Point d) : ‖P.value D y‖ ≤ P.linftyNorm D :=
  le_ciSup (P.linftyNorm_bddAbove D) y

/-- The integer angular frequency vector of the `i`-th term of a presentation
at scale `D`: coordinate `k` carries the frequency `D * coarse i k + fine i k`
of the manuscript's Fourier kernel $e^{2\pi i \mathbf s \cdot \bm\omega}$
through the angular reduction $\bm\omega = \mathbf y / (2 \pi)$. -/
def angularFrequency {d m r : ℕ} (P : SegmentedPacket d m r) (D : ℕ) :
    P.Index → Fin d → ℤ :=
  fun i k => ((D * P.coarse i k + P.fine i k : ℕ) : ℤ)

/-- Evaluation is the bridge's angular trigonometric polynomial at the
packet's integer angular frequency family: `P.value D` presents the torus
polynomial `unitTorusTrigPolynomial (P.angularFrequency D) P.coeff` of
`General.Fourier.TrigonometricPolynomialParseval` through the angular
reduction $\bm\omega = \mathbf y / (2 \pi)$. -/
theorem value_eq_angularTrigPolynomial {d m r : ℕ} (P : SegmentedPacket d m r)
    (D : ℕ) (x : Point d) :
    P.value D x = angularTrigPolynomial (P.angularFrequency D) P.coeff x := by
  classical
  show (∑ i, P.coeff i * Complex.exp
      (Complex.I * ((∑ k, ((D * P.coarse i k + P.fine i k : ℕ) : ℝ) * x k : ℝ) : ℂ))) = _
  simp only [angularTrigPolynomial, angularFrequency]
  apply Finset.sum_congr rfl
  intro i _
  refine congrArg (fun z : ℂ => P.coeff i * Complex.exp z) ?_
  push_cast
  rfl

/-- `2 * Real.pi`-periodicity of `P.value D` in every coordinate: all
frequencies of a presentation are integers.  This is the periodicity behind
the identification of the global supremum `linftyNorm` with the manuscript's
`L^∞(𝕋^d)` norm over one fundamental domain; see
`linftyNorm_eq_unitTorusLInfNorm`. -/
theorem value_two_pi_periodic {d m r : ℕ} (P : SegmentedPacket d m r)
    (D : ℕ) (x : Point d) (k : Fin d) :
    P.value D (Function.update x k (x k + 2 * Real.pi)) = P.value D x := by
  classical
  unfold SegmentedPacket.value
  apply Finset.sum_congr rfl
  intro i _
  let z : ℤ := ((D * P.coarse i k + P.fine i k : ℕ) : ℤ)
  have hphase :
      (∑ j, ((D * P.coarse i j + P.fine i j : ℕ) : ℝ) *
          Function.update x k (x k + 2 * Real.pi) j) =
        (∑ j, ((D * P.coarse i j + P.fine i j : ℕ) : ℝ) * x j) +
          2 * Real.pi * (z : ℝ) := by
    have hsplit : ∀ j : Fin d,
        ((D * P.coarse i j + P.fine i j : ℕ) : ℝ) *
            Function.update x k (x k + 2 * Real.pi) j =
          ((D * P.coarse i j + P.fine i j : ℕ) : ℝ) * x j +
            (if j = k then
              ((D * P.coarse i j + P.fine i j : ℕ) : ℝ) * (2 * Real.pi) else 0) := by
      intro j
      rw [Function.update_apply]
      by_cases hj : j = k
      · rw [hj, if_pos rfl, if_pos rfl]
        ring
      · rw [if_neg hj, if_neg hj]
        ring
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    have hite : (∑ j : Fin d,
        (if j = k then ((D * P.coarse i j + P.fine i j : ℕ) : ℝ) * (2 * Real.pi) else 0)) =
        2 * Real.pi * (z : ℝ) := by
      rw [Finset.sum_ite_eq' Finset.univ k
        (fun j : Fin d => ((D * P.coarse i j + P.fine i j : ℕ) : ℝ) * (2 * Real.pi)),
        if_pos (Finset.mem_univ k)]
      dsimp [z]
      push_cast
      ring
    rw [hite]
  congr 1
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨z, ?_⟩
  rw [hphase]
  push_cast
  ring

/-- The `L^∞` sup norm `linftyNorm` of a presentation agrees with the torus
`L^∞` norm `unitTorusLInfNorm` of the polynomial it presents, in the
manuscript's normalization $g(\bm\omega) = \sum_i c_i e^{2\pi i \mathbf s_i
\cdot \bm\omega}$ on $\bm\omega \in \mathbb T^d \cong [0,1)^d$.  This is the
identification behind the `L^∞(𝕋^d)` claims of `linftyNorm`, proved through
the bridge's angular layer (`value_eq_angularTrigPolynomial` and
`unitTorusTrigPolynomial_eq_angularTrigPolynomial`): both suprema range over
all of `ℝ^d`, and `value_two_pi_periodic` shows each equals the supremum over
one fundamental domain, e.g. the angular cube `InAngularCube`. -/
theorem linftyNorm_eq_unitTorusLInfNorm {d m r : ℕ} (P : SegmentedPacket d m r)
    (D : ℕ) :
    P.linftyNorm D =
      unitTorusLInfNorm (unitTorusTrigPolynomial (P.angularFrequency D) P.coeff) := by
  classical
  have hass' : BddAbove (Set.range fun ω : Fin d → ℝ =>
      ‖unitTorusTrigPolynomial (P.angularFrequency D) P.coeff ω‖) :=
    ⟨∑ i, ‖P.coeff i‖, by
      rintro _ ⟨ω, rfl⟩
      exact norm_unitTorusTrigPolynomial_le _ _ ω⟩
  apply le_antisymm
  · show (⨆ y : Point d, ‖P.value D y‖) ≤
      (⨆ ω : Fin d → ℝ, ‖unitTorusTrigPolynomial (P.angularFrequency D) P.coeff ω‖)
    apply ciSup_le
    intro y
    have h2π : (2:ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    have hdiv : (fun k : Fin d => 2 * Real.pi * (y k / (2 * Real.pi))) = y := by
      funext k
      field_simp [h2π]
    have h := unitTorusTrigPolynomial_eq_angularTrigPolynomial
      (P.angularFrequency D) P.coeff (fun k => y k / (2 * Real.pi))
    rw [hdiv] at h
    rw [value_eq_angularTrigPolynomial P D y, ← h]
    exact le_ciSup hass' (fun k => y k / (2 * Real.pi))
  · show (⨆ ω : Fin d → ℝ, ‖unitTorusTrigPolynomial (P.angularFrequency D) P.coeff ω‖) ≤
      (⨆ y : Point d, ‖P.value D y‖)
    apply ciSup_le
    intro ω
    rw [unitTorusTrigPolynomial_eq_angularTrigPolynomial,
      ← value_eq_angularTrigPolynomial P D (fun k => 2 * Real.pi * ω k)]
    exact le_ciSup (P.linftyNorm_bddAbove D) (fun k => 2 * Real.pi * ω k)

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

@[simp] theorem linftyNorm_widen {d m r m' r' : ℕ} (P : SegmentedPacket d m r)
    (hm : m ≤ m') (hr : r ≤ r') (D : ℕ) :
    (P.widen hm hr).linftyNorm D = P.linftyNorm D := rfl

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

/-! ### Recentered quantized two-point factors and segmented neighbor products

Manuscript correspondence: `neighborSetSegmented_polynomial` is the NumDetect
manuscript's `lem:neighborset_segmented` at full strength, and
`segmentedNeighborProduct` is its `p = ∞` worst-case-factor corollary. The
construction follows the manuscript's proof: every nonzero node is annihilated
by the recentered quantized two-point factor `twoPointRecentered` at the integer
frequency of `lem:freq_quantization`
(`SegmentedVDM.frequency_quantization_of_budgetScale`), the near/far split is
restored through the budget scale `t = min (M/v) (π/(D‖u‖_{p'}))`, and the `L²`
normalization `√((M/v)^d (m+1)^d)` is carried by the averaging block
`smoothedSegmentedVector`. -/

/-- The two-point quotient of `lem:freq_quantization` at the integer frequency
`k`, recentered so that both frequencies `D k⁺` and `D k⁻` lie in the
nonnegative cube `D{0,…,K}^d`. The recentering prefactor `e^{i D k⁻·x}` has unit
modulus, so the interpolation values and all coefficient-modulus bounds of the
unrecentered two-point factor are preserved. -/
noncomputable def twoPointRecentered {d K : ℕ} (k : Fin d → ℤ)
    (hk : ∀ j, (k j).natAbs ≤ K) (z : ℂ) : SegmentedPacket d 0 K where
  Index := Bool
  finite := inferInstance
  coarse b j := if b then (k j).toNat else (-k j).toNat
  fine _ _ := 0
  coarse_le b j := by
    cases b
    · show (-k j).toNat ≤ K
      exact Int.toNat_le.mpr
        ((Int.le_natAbs (a := -k j)).trans (by rw [Int.natAbs_neg]; exact_mod_cast hk j))
    · show (k j).toNat ≤ K
      exact Int.toNat_le.mpr ((Int.le_natAbs (a := k j)).trans (by exact_mod_cast hk j))
  fine_le _ _ := le_rfl
  coeff b := if b then (1 - z)⁻¹ else -z / (1 - z)

theorem value_twoPointRecentered {d K : ℕ} (k : Fin d → ℤ)
    (hk : ∀ j, (k j).natAbs ≤ K) (z : ℂ) (D : ℕ) (x : Point d) :
    (twoPointRecentered k hk z).value D x =
      Complex.exp (Complex.I * (((D : ℝ) * ∑ j, ((-k j).toNat : ℝ) * x j : ℝ) : ℂ)) *
        ((Complex.exp (Complex.I * (((D : ℝ) * ∑ j, (k j : ℝ) * x j : ℝ) : ℂ)) - z) /
          (1 - z)) := by
  classical
  have htoNat (j : Fin d) : ((k j).toNat : ℝ) = ((-k j).toNat : ℝ) + (k j : ℝ) := by
    have h : ((k j).toNat : ℤ) = ((-k j).toNat : ℤ) + k j := by omega
    exact_mod_cast h
  have hterm (j : Fin d) :
      ((D : ℝ) * ((k j).toNat : ℝ)) * x j
        = (D : ℝ) * (((-k j).toNat : ℝ) * x j) + (D : ℝ) * ((k j : ℝ) * x j) := by
    rw [htoNat j]
    ring
  have hθp : (∑ j, ((D * (k j).toNat + 0 : ℕ) : ℝ) * x j)
      = (D : ℝ) * ∑ j, ((-k j).toNat : ℝ) * x j + (D : ℝ) * ∑ j, (k j : ℝ) * x j := by
    simp only [add_zero, Nat.cast_mul]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib]
    rw [Finset.mul_sum, Finset.mul_sum]
  have hθm : (∑ j, ((D * (-k j).toNat + 0 : ℕ) : ℝ) * x j)
      = (D : ℝ) * ∑ j, ((-k j).toNat : ℝ) * x j := by
    simp only [add_zero, Nat.cast_mul]
    have hterm' : ∀ j : Fin d,
        ((D : ℝ) * ((-k j).toNat : ℝ)) * x j
          = (D : ℝ) * (((-k j).toNat : ℝ) * x j) := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => hterm' j), Finset.mul_sum]
  have hex : Complex.exp
        (Complex.I * (((D : ℝ) * ∑ j, ((-k j).toNat : ℝ) * x j
          + (D : ℝ) * ∑ j, (k j : ℝ) * x j : ℝ) : ℂ))
      = Complex.exp (Complex.I * (((D : ℝ) * ∑ j, ((-k j).toNat : ℝ) * x j : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (((D : ℝ) * ∑ j, (k j : ℝ) * x j : ℝ) : ℂ)) := by
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  show (∑ b : Bool, (if b then (1 - z)⁻¹ else -z / (1 - z)) *
      Complex.exp (Complex.I *
        (((∑ j, ((D * (if b then (k j).toNat else (-k j).toNat) + 0 : ℕ) : ℝ) * x j : ℝ) : ℂ))))
      = _
  rw [Fintype.sum_bool]
  simp only [if_true, if_neg (by decide : ¬(false = true))]
  rw [hθp, hθm, hex]
  ring

theorem value_twoPointRecentered_zero {d K : ℕ} (k : Fin d → ℤ)
    (hk : ∀ j, (k j).natAbs ≤ K) (z : ℂ) (hz : z ≠ 1) (D : ℕ) :
    (twoPointRecentered k hk z).value D 0 = 1 := by
  rw [value_twoPointRecentered]
  simp [sub_ne_zero.mpr (Ne.symm hz)]

theorem value_twoPointRecentered_vanishes {d K : ℕ} (k : Fin d → ℤ)
    (hk : ∀ j, (k j).natAbs ≤ K) (z : ℂ) (D : ℕ) (u : Point d)
    (hz : z = Complex.exp (Complex.I * (((D : ℝ) * ∑ j, (k j : ℝ) * u j : ℝ) : ℂ))) :
    (twoPointRecentered k hk z).value D u = 0 := by
  rw [value_twoPointRecentered, hz, sub_self, zero_div, mul_zero]

theorem mass_twoPointRecentered {d K : ℕ} (k : Fin d → ℤ)
    (hk : ∀ j, (k j).natAbs ≤ K) (z : ℂ) (hz : ‖z‖ = 1) :
    (twoPointRecentered k hk z).mass = 2 / ‖1 - z‖ := by
  simp [SegmentedPacket.mass, twoPointRecentered, Fintype.sum_bool, norm_div, hz]
  ring

/-- One node's recentered quantized two-point factor: the per-node building
block of the NumDetect manuscript's `lem:neighborset_segmented`, applying
`lem:freq_quantization` (`SegmentedVDM.frequency_quantization_of_budgetScale`)
at the budget scale `t`. Every scale `t` with `2 d^{1/p} ≤ t` and
`‖u‖_{p'} ≤ π/(D t)` yields a factor supported in `D{0,…,⌊t⌋}^d`, equal to one at
`0` and zero at `u`, with coefficient `ℓ¹` mass at most
`√2 π/(D t ‖u‖_{p'})`. The near/far split of `lem:neighborset_segmented` is the
choice `t = min (M/v) (π/(D‖u‖_{p'}))`. -/
theorem neighborNodeFactor {d D : ℕ} {p q : ENNReal} (hpq : ENNReal.HolderConjugate p q)
    (hD : 0 < D) (hdim : 0 < (d : ℝ) ^ p.toReal⁻¹)
    {t : ℝ} (ht : 2 * (d : ℝ) ^ p.toReal⁻¹ ≤ t)
    (u : Point d) (hun : 0 < LeanNumDetect.lpNorm q u)
    (hut : LeanNumDetect.lpNorm q u ≤ Real.pi / (D * t)) :
    ∃ P : SegmentedPacket d 0 ⌊t⌋₊,
      P.value D 0 = 1 ∧ P.value D u = 0 ∧
      P.mass ≤ Real.sqrt 2 * Real.pi / (D * t * LeanNumDetect.lpNorm q u) := by
  classical
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have htpos : 0 < t := by
    have h1 : 0 < Real.pi / (D * t) := lt_of_lt_of_le hun hut
    have h2 : 0 < D * t := (div_pos_iff_of_pos_left Real.pi_pos).mp h1
    exact pos_of_mul_pos_right h2 hDpos.le
  obtain ⟨k, hk, hden⟩ := SegmentedVDM.frequency_quantization_of_budgetScale hpq hDpos
    hdim ht u hun hut
  set z : ℂ := Complex.exp (Complex.I * (((D : ℝ) * ∑ j, (k j : ℝ) * u j : ℝ) : ℂ)) with hzdef
  have hzn : ‖z‖ = 1 := by simp [z, Complex.norm_exp]
  have hden' : Real.sqrt 2 * (D * t * LeanNumDetect.lpNorm q u / Real.pi) ≤ ‖1 - z‖ := by
    have he : Real.sqrt 2 * (D * t * LeanNumDetect.lpNorm q u / Real.pi)
        = Real.sqrt 2 * D * t * LeanNumDetect.lpNorm q u / Real.pi := by ring
    rw [he, hzdef]
    exact hden
  have hzne : z ≠ 1 := by
    intro h
    have hp : 0 < Real.sqrt 2 * (D * t * LeanNumDetect.lpNorm q u / Real.pi) := by positivity
    simp [h] at hden'
    linarith
  have hkabs (j : Fin d) : |(k j : ℝ)| ≤ t :=
    (LeanNumDetect.lpNorm_apply_le (holderConjugate_ne_zero hpq).1 (fun j => (k j : ℝ)) j).trans
      hk
  have hkK (j : Fin d) : (k j).natAbs ≤ ⌊t⌋₊ := by
    apply Nat.le_floor
    have h1 : ((k j).natAbs : ℝ) = |(k j : ℝ)| := (Nat.cast_natAbs (k j)).trans Int.cast_abs
    rw [h1]
    exact hkabs j
  refine ⟨twoPointRecentered k hkK z, ?_, ?_, ?_⟩
  · exact value_twoPointRecentered_zero k hkK z hzne D
  · exact value_twoPointRecentered_vanishes k hkK z D u hzdef
  · rw [mass_twoPointRecentered k hkK z hzn]
    have hpos : 0 < Real.sqrt 2 * (D * t * LeanNumDetect.lpNorm q u / Real.pi) := by positivity
    calc
      2 / ‖1 - z‖ ≤ 2 / (Real.sqrt 2 * (D * t * LeanNumDetect.lpNorm q u / Real.pi)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden'
      _ = Real.sqrt 2 * Real.pi / (D * t * LeanNumDetect.lpNorm q u) := by
        have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
        field_simp
        nlinarith

/-- The coefficient `ℓ¹` mass of a spread is at most the `ℓ¹` mass of its
coefficients. -/
theorem spread_norm_sum_le {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ρ]
    (f : ι → ρ) (c : ι → ℂ) :
    (∑ a : ρ, ‖SegmentedVDM.spread f c a‖) ≤ ∑ i : ι, ‖c i‖ := by
  classical
  have happly : ∀ a : ρ, SegmentedVDM.spread f c a
      = ∑ i, c i * (if a = f i then (1 : ℂ) else 0) := by
    intro a
    show (SegmentedVDM.spread f c).ofLp a = _
    simp only [SegmentedVDM.spread, WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  calc
    (∑ a : ρ, ‖SegmentedVDM.spread f c a‖)
        = ∑ a : ρ, ‖∑ i, c i * (if a = f i then (1 : ℂ) else 0)‖ := by simp only [happly]
    _ ≤ ∑ a : ρ, ∑ i, ‖c i * (if a = f i then (1 : ℂ) else 0)‖ :=
      Finset.sum_le_sum fun a _ => norm_sum_le _ _
    _ = ∑ i : ι, ∑ a : ρ, ‖c i * (if a = f i then (1 : ℂ) else 0)‖ := Finset.sum_comm
    _ = ∑ i : ι, ‖c i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      have h1 : ∀ a : ρ, ‖c i * (if a = f i then (1 : ℂ) else 0)‖
          = if a = f i then ‖c i‖ else 0 := by
        intro a
        by_cases h : a = f i
        · rw [if_pos h, if_pos h, mul_one]
        · rw [if_neg h, if_neg h, mul_zero, norm_zero]
      simp only [h1]
      rw [Finset.sum_ite_eq' Finset.univ (f i) (fun _ => ‖c i‖)]
      simp

/-- Collecting a presentation by frequency does not change its coefficient
energy when the frequencies of the presentation are pairwise distinct. -/
theorem energy_coefficientVector_eq_of_injective {d m r : ℕ}
    (P : SegmentedPacket d m r) (hinj : Function.Injective P.frequencyIndex) :
    SegmentedVDM.energy P.coefficientVector = SegmentedVDM.energy P.coeff := by
  classical
  have hsum : (∑ β, ‖∑ i, if P.frequencyIndex i = β then P.coeff i else 0‖ ^ 2)
      = ∑ i, ‖P.coeff i‖ ^ 2 := by
    have hsplit : (∑ β, ‖∑ i, if P.frequencyIndex i = β then P.coeff i else 0‖ ^ 2)
        = ∑ β ∈ Finset.univ.image P.frequencyIndex,
            ‖∑ i, if P.frequencyIndex i = β then P.coeff i else 0‖ ^ 2 := by
      refine (Finset.sum_subset (Finset.subset_univ _) fun β _ hβ => ?_).symm
      have hz : ∀ i, (if P.frequencyIndex i = β then P.coeff i else 0) = (0 : ℂ) := by
        intro i
        apply if_neg
        intro h
        exact hβ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h⟩)
      simp only [hz, Finset.sum_const, zero_smul, norm_zero, ne_eq]
      simp
    rw [hsplit, Finset.sum_image (fun i _ j _ h => hinj h)]
    apply Finset.sum_congr rfl
    intro i _
    have h1 : (∑ j, if P.frequencyIndex j = P.frequencyIndex i then P.coeff j else 0)
        = P.coeff i := by
      rw [Finset.sum_eq_single i]
      · exact if_pos rfl
      · intro b _ hb
        exact if_neg (fun h => hb (hinj h))
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [h1]
  change SegmentedVDM.energy (fun β => ∑ i, if P.frequencyIndex i = β then P.coeff i else 0) = _
  exact hsum

/-- The NumDetect manuscript's `lem:neighborset_segmented` at full strength. The
neighbor set `𝓤 ⊂ (-π, π]^d` of coordinatewise shortest representatives of torus
differences is presented by its distinguished element `0` and the family
`u : Fin (v - 1) → Point d` of its nonzero elements, so `v` is the cardinality of
`𝓤` when `u` is injective; the exclusion of the zero representative is the
hypothesis `0 < ‖u i‖_{p'}`. Here `q` is the Hölder conjugate exponent `p'` of
`p`, `‖·‖_{p'}` is `LeanNumDetect.lpNorm q`, and the dimension factor `d^{1/p}`
is `(d : ℝ) ^ p.toReal⁻¹`. If `‖u i‖_{p'} ≤ π/(2 D d^{1/p})` for all nodes and
`2 d^{1/p} v ≤ M`, there is a polynomial `f ∈ 𝒫(m, M, D, d)`, presented by
`P : SegmentedPacket d m M`, with `P.value D 0 = 1`, `P.value D (u i) = 0`, and

`‖f‖_{L²(𝕋^d)} ≤ (√2)^{v-1} / √((M/v)^d (m+1)^d) * ∏ π v/(M D ‖u‖_{p'})`,

the product running only over the near neighbors `0 < ‖u‖_{p'} ≤ π v/(M D)`
(`SegmentedVDM.neighborScaleFactor`); each far neighbor costs only its share of
`(√2)^{v-1}`. The `L²` norm is realized as
`Real.sqrt (SegmentedVDM.energy P.coefficientVector)`, which is the manuscript's
`‖f‖_{L²(𝕋^d)}` by Parseval on the unit torus with normalized measure (compare
the documentation of `SegmentedVDM.singularValue_ge_of_interpolation`); the
bridge lemma that will discharge this identification is the Parseval statement
being formalized in `General.Fourier.TrigonometricPolynomialParseval`. The same
witness satisfies the coefficient `ℓ¹` mass bound `P.mass ≤ (√2)^{v-1} ∏ …`
without the normalizing denominator, which is the form retained by the
worst-case corollary `segmentedNeighborProduct`.

The hypothesis `m < D` is the manuscript's `D > m`; it makes the frequencies
`D c + j` of a presentation pairwise distinct, so the Parseval identification
applies, and is not used by the finite proof. As in
`SegmentedVDM.frequency_quantization_of_shortest_representative`, the range
condition `u i ∈ (-π, π]^d` of the manuscript is not used by the proof. -/
theorem neighborSetSegmented_polynomial
    {d v M m D : ℕ} {p q : ENNReal} (hpq : ENNReal.HolderConjugate p q)
    (hv : 0 < v) (hmD : m < D)
    (u : Fin (v - 1) → Point d)
    (hun : ∀ i, 0 < LeanNumDetect.lpNorm q (u i))
    (huro : ∀ i, LeanNumDetect.lpNorm q (u i) ≤
      Real.pi / (2 * (D : ℝ) * (d : ℝ) ^ p.toReal⁻¹))
    (hM : 2 * (d : ℝ) ^ p.toReal⁻¹ * v ≤ (M : ℝ)) :
    ∃ P : SegmentedPacket d m M,
      P.value D 0 = 1 ∧
      (∀ i, P.value D (u i) = 0) ∧
      P.mass ≤ (Real.sqrt 2) ^ (v - 1) *
        ∏ i : Fin (v - 1), SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i) ∧
      Real.sqrt (SegmentedVDM.energy P.coefficientVector) ≤
        ((Real.sqrt 2) ^ (v - 1) *
          ∏ i : Fin (v - 1), SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i)) /
          Real.sqrt (((M : ℝ) / v) ^ d * ((m + 1 : ℕ) : ℝ) ^ d) := by
  classical
  have hDposN : 0 < D := by omega
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hDposN
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hdim (i : Fin (v - 1)) : 0 < (d : ℝ) ^ p.toReal⁻¹ := by
    by_contra hnd
    have hz : (d : ℝ) ^ p.toReal⁻¹ = 0 :=
      le_antisymm (le_of_not_gt hnd) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    have h0 : Real.pi / (2 * (D : ℝ) * (d : ℝ) ^ p.toReal⁻¹) = 0 := by
      rw [hz, mul_zero, div_zero]
    have := huro i
    rw [h0] at this
    exact lt_irrefl 0 (lt_of_lt_of_le (hun i) this)
  have hMpos (i : Fin (v - 1)) : 0 < (M : ℝ) :=
    lt_of_lt_of_le (mul_pos (mul_pos (by norm_num) (hdim i)) hvR) hM
  set w : Fin (v - 1) → ℝ := fun i => LeanNumDetect.lpNorm q (u i) with hwdef
  set zN : ℕ := ⌊(M : ℝ) / v⌋₊ with hzNdef
  have hwpos (i : Fin (v - 1)) : 0 < w i := by rw [hwdef]; exact hun i
  have htmin (i : Fin (v - 1)) :
      min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i))
        = min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * LeanNumDetect.lpNorm q (u i))) := by
    rw [hwdef]
  have htb (i : Fin (v - 1)) : 2 * (d : ℝ) ^ p.toReal⁻¹
      ≤ min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) := by
    refine le_min ?_ ?_
    · exact (le_div_iff₀ hvR).mpr hM
    · have hA : w i * (2 * (D : ℝ) * (d : ℝ) ^ p.toReal⁻¹) ≤ Real.pi := by
        have hA0 := (le_div_iff₀
          (mul_pos (mul_pos (by norm_num) hDpos) (hdim i))).mp (huro i)
        exact hA0
      have hA' : 2 * (d : ℝ) ^ p.toReal⁻¹ * ((D : ℝ) * w i) ≤ Real.pi := by
        have he : 2 * (d : ℝ) ^ p.toReal⁻¹ * ((D : ℝ) * w i)
            = w i * (2 * (D : ℝ) * (d : ℝ) ^ p.toReal⁻¹) := by ring
        rw [he]
        exact hA
      exact (le_div_iff₀ (mul_pos hDpos (hwpos i))).2 hA'
  have hut (i : Fin (v - 1)) : w i ≤ Real.pi / ((D : ℝ) * min ((M : ℝ) / v)
      (Real.pi / ((D : ℝ) * w i))) := by
    have hA : min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) * ((D : ℝ) * w i) ≤ Real.pi :=
      (le_div_iff₀ (mul_pos hDpos (hwpos i))).mp (min_le_right _ _)
    have hA' : w i * ((D : ℝ) * min ((M : ℝ) / v)
        (Real.pi / ((D : ℝ) * w i))) ≤ Real.pi := by
      have he : w i * ((D : ℝ) * min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)))
          = min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) * ((D : ℝ) * w i) := by ring
      rw [he]
      exact hA
    have hminpos : 0 < (D : ℝ) * min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) :=
      mul_pos hDpos (lt_min_iff.mpr ⟨div_pos (hMpos i) hvR,
        div_pos Real.pi_pos (mul_pos hDpos (hwpos i))⟩)
    exact (le_div_iff₀ hminpos).2 hA'
  have hnode (i : Fin (v - 1)) : ∃ P : SegmentedPacket d 0 ⌊min ((M : ℝ) / v)
      (Real.pi / ((D : ℝ) * w i))⌋₊,
      P.value D 0 = 1 ∧ P.value D (u i) = 0 ∧
      P.mass ≤ Real.sqrt 2 * Real.pi /
        ((D : ℝ) * min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) * w i) :=
    neighborNodeFactor hpq hDposN (hdim i) (t := min ((M : ℝ) / v)
      (Real.pi / ((D : ℝ) * w i))) (htb i) (u i) (hun i) (hut i)
  choose F hF1 hF0 hFm using hnode
  have htbud (i : Fin (v - 1)) :
      ⌊min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i))⌋₊ ≤ zN := by
    apply Nat.floor_mono
    exact min_le_left _ _
  let G : Fin (v - 1) → SegmentedPacket d 0 zN := fun i => (F i).widen le_rfl (htbud i)
  let Q : SegmentedPacket d ((v - 1) * 0) ((v - 1) * zN) := SegmentedPacket.prod G
  let Q0 : SegmentedPacket d 0 ((v - 1) * zN) := Q.widen (by simp) le_rfl
  have hzNv : zN * v ≤ M := by
    have h1 : ((zN : ℕ) : ℝ) ≤ (M : ℝ) / v := by
      rw [hzNdef]
      exact Nat.floor_le (div_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg v))
    have h2 : ((zN : ℕ) : ℝ) * v ≤ (M : ℝ) := (le_div_iff₀ hvR).mp h1
    exact_mod_cast h2
  have hzsplit : (v - 1) * zN + zN = v * zN := by
    conv_rhs =>
      rw [show v = v - 1 + 1 from (Nat.sub_add_cancel (Nat.succ_le_of_lt hv)).symm,
        Nat.add_mul, one_mul]
  have hzN1 : (M : ℝ) / v ≤ zN + 1 := by
    have h := Nat.lt_floor_add_one ((M : ℝ) / v)
    rw [← hzNdef] at h
    exact h.le
  have hdenle : ((M : ℝ) / v) ^ d * ((m + 1 : ℕ) : ℝ) ^ d
      ≤ ((((zN + 1) * (m + 1)) ^ d : ℕ) : ℝ) := by
    push_cast
    rw [mul_pow]
    gcongr
  have hDnpos : 0 < ((M : ℝ) / v) ^ d * ((m + 1 : ℕ) : ℝ) ^ d := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst d
      simp
    · have hdim0 : 0 < (d : ℝ) ^ p.toReal⁻¹ :=
        Real.rpow_pos_of_pos (by exact_mod_cast hd) _
      have h1 : 0 < 2 * (d : ℝ) ^ p.toReal⁻¹ * (v : ℝ) :=
        mul_pos (mul_pos (by norm_num) hdim0) hvR
      have hMpos' : 0 < (M : ℝ) := lt_of_lt_of_le h1 hM
      have h2 : 0 < (M : ℝ) / v := div_pos hMpos' hvR
      exact mul_pos (pow_pos h2 d)
        (pow_pos (by exact_mod_cast (by omega : 0 < m + 1)) d)
  have hQ0 (x : Point d) : Q0.value D x = ∏ i, (F i).value D x := by
    rw [SegmentedPacket.value_widen, SegmentedPacket.value_prod]
    apply Finset.prod_congr rfl
    intro i _
    exact SegmentedPacket.value_widen (F i) le_rfl (htbud i) D x
  have hQ01 : Q0.value D 0 = 1 := by
    rw [hQ0]
    exact Finset.prod_eq_one fun i _ => hF1 i
  have hQz (j : Fin (v - 1)) : Q0.value D (u j) = 0 := by
    rw [hQ0]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact hF0 j
  let wvec : EuclideanSpace ℂ (SegmentedIndex d (0 + m) ((v - 1) * zN + zN)) :=
    SegmentedPacket.smoothedSegmentedVector Q0 m zN D 0
  have hstep (x : Point d) : Q0.value D x *
      SegmentedPacket.segmentedMeanKernel d m zN D x =
      ofLp wvec ⬝ᵥ SegmentedPacket.segmentedSteering d (0 + m) ((v - 1) * zN + zN) D x := by
    have h := SegmentedPacket.smoothedSegmentedVector_evaluation Q0 m zN D 0 x
    simp only [sub_zero] at h
    rw [← h]
  let P : SegmentedPacket d m M := {
    Index := SegmentedIndex d (0 + m) ((v - 1) * zN + zN)
    finite := inferInstance
    coarse i k := (i k).1.val
    fine i k := (i k).2.val
    coarse_le i k := by
      have h := (i k).1.isLt
      have hz : (v - 1) * zN + zN ≤ M := by
        rw [hzsplit, Nat.mul_comm]
        exact hzNv
      omega
    fine_le i k := by
      have h := (i k).2.isLt
      omega
    coeff i := ofLp wvec i }
  have hval (x : Point d) : P.value D x =
      Q0.value D x * SegmentedPacket.segmentedMeanKernel d m zN D x := by
    have hstep' : P.value D x
        = ofLp wvec ⬝ᵥ SegmentedPacket.segmentedSteering d (0 + m) ((v - 1) * zN + zN) D x := by
      show (∑ i : SegmentedIndex d (0 + m) ((v - 1) * zN + zN),
          ofLp wvec i * Complex.exp (Complex.I *
            ((∑ k, ((D * (i k).1.val + (i k).2.val : ℕ) : ℝ) * x k : ℝ) : ℂ)))
        = ofLp wvec ⬝ᵥ SegmentedPacket.segmentedSteering d (0 + m) ((v - 1) * zN + zN) D x
      rfl
    rw [hstep']
    exact (hstep x).symm
  have hP0 : P.value D 0 = 1 := by
    rw [hval, hQ01, SegmentedPacket.segmentedMeanKernel_zero, one_mul]
  have hPu (j : Fin (v - 1)) : P.value D (u j) = 0 := by
    rw [hval, hQz j, zero_mul]
  have hspreadle (i : Q0.Index) :
      (∑ a : SegmentedIndex d (0 + m) ((v - 1) * zN + zN),
        ‖SegmentedPacket.segmentedAveragingVector Q0 m zN D 0 i a‖) ≤ 1 := by
    refine (spread_norm_sum_le (SegmentedPacket.shiftedSegmentedRow Q0 m zN i) _).trans ?_
    have hexp (q : SegmentedPacket.SmoothingIndex d m zN) :
        ‖Complex.exp (-Complex.I * (((∑ k,
          (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) * (0 : Point d) k)) : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have hcard : Fintype.card (SegmentedPacket.SmoothingIndex d m zN)
        = ((zN + 1) * (m + 1)) ^ d := by
      simp [SegmentedPacket.SmoothingIndex, SegmentedIndex, SegmentedCoordinateIndex]
    have hsum : (∑ q : SegmentedPacket.SmoothingIndex d m zN,
        ‖Complex.exp (-Complex.I * (((∑ k,
          (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) * (0 : Point d) k)) : ℝ) : ℂ)) /
          (((zN + 1) * (m + 1)) ^ d : ℕ)‖) = 1 := by
      simp only [norm_div, hexp, Complex.norm_natCast, one_div]
      rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
      have hne : ((((zN + 1) * (m + 1)) ^ d : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (by positivity : (((zN + 1) * (m + 1)) ^ d : ℕ) ≠ 0)
      field_simp
    exact le_of_eq hsum
  have hmassvec : P.mass ≤ Q0.mass := by
    show (∑ a : SegmentedIndex d (0 + m) ((v - 1) * zN + zN), ‖ofLp wvec a‖) ≤ Q0.mass
    have h1 : ∀ a : SegmentedIndex d (0 + m) ((v - 1) * zN + zN),
        ‖ofLp wvec a‖ ≤ ∑ i : Q0.Index, ‖Q0.coeff i‖ *
          ‖SegmentedPacket.segmentedAveragingVector Q0 m zN D 0 i a‖ := by
      intro a
      have hsum : ofLp wvec a = ∑ i : Q0.Index,
          Q0.coeff i • ofLp (SegmentedPacket.segmentedAveragingVector Q0 m zN D 0 i) a := by
        show (ofLp (∑ i : Q0.Index,
            Q0.coeff i • SegmentedPacket.segmentedAveragingVector Q0 m zN D 0 i)) a = _
        rw [WithLp.ofLp_sum, Finset.sum_apply]
        rfl
      rw [hsum]
      refine (norm_sum_le _ _).trans ?_
      exact Finset.sum_le_sum fun i _ => by
        have h := norm_smul (Q0.coeff i)
          (ofLp (SegmentedPacket.segmentedAveragingVector Q0 m zN D 0 i) a)
        exact le_of_eq h
    calc
      (∑ a : SegmentedIndex d (0 + m) ((v - 1) * zN + zN), ‖ofLp wvec a‖)
          ≤ ∑ a, ∑ i : Q0.Index, ‖Q0.coeff i‖ *
            ‖SegmentedPacket.segmentedAveragingVector Q0 m zN D 0 i a‖ :=
        Finset.sum_le_sum fun a _ => h1 a
      _ = ∑ i : Q0.Index, ∑ a, ‖Q0.coeff i‖ *
          ‖SegmentedPacket.segmentedAveragingVector Q0 m zN D 0 i a‖ := Finset.sum_comm
      _ = ∑ i : Q0.Index, ‖Q0.coeff i‖ *
          ∑ a, ‖SegmentedPacket.segmentedAveragingVector Q0 m zN D 0 i a‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.mul_sum]
      _ ≤ ∑ i : Q0.Index, ‖Q0.coeff i‖ * 1 :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hspreadle i) (norm_nonneg _)
      _ = Q0.mass := by simp [SegmentedPacket.mass]
  have hinj : Function.Injective P.frequencyIndex := by
    intro i j h
    funext k
    have hk := congrFun h k
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun a => a.1.val) hk
    · apply Fin.ext
      exact congrArg (fun a => a.2.val) hk
  have henergy : SegmentedVDM.energy P.coefficientVector = ‖wvec‖ ^ 2 := by
    rw [energy_coefficientVector_eq_of_injective P hinj]
    show SegmentedVDM.energy (fun i => ofLp wvec i) = ‖wvec‖ ^ 2
    simp only [SegmentedVDM.energy]
    exact (EuclideanSpace.norm_sq_eq wvec).symm
  have hnSF (i : Fin (v - 1)) :
      0 ≤ SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i) := by
    unfold SegmentedVDM.neighborScaleFactor
    split_ifs with h
    · exact div_nonneg (by positivity)
        (mul_nonneg (mul_nonneg (hMpos i).le hDpos.le) (hun i).le)
    · exact zero_le_one
  have hfac (i : Fin (v - 1)) :
      Real.sqrt 2 * Real.pi /
        ((D : ℝ) * min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) * w i)
        = Real.sqrt 2 * SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i) := by
    have hMDpos : 0 < (M : ℝ) * (D : ℝ) := mul_pos (hMpos i) hDpos
    have hminpos : 0 < min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) :=
      lt_min_iff.mpr ⟨div_pos (hMpos i) hvR, div_pos Real.pi_pos (mul_pos hDpos (hwpos i))⟩
    by_cases h : LeanNumDetect.lpNorm q (u i) ≤ Real.pi * (v : ℝ) / ((M : ℝ) * (D : ℝ))
    · rw [SegmentedVDM.neighborScaleFactor_of_le h]
      have h1 : min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) = (M : ℝ) / v := by
        refine min_eq_left ((le_div_iff₀ (mul_pos hDpos (hwpos i))).2 ?_)
        have h2 : w i * ((M : ℝ) * (D : ℝ)) ≤ Real.pi * (v : ℝ) :=
          (le_div_iff₀ hMDpos).mp h
        have h3 : ((M : ℝ) / v) * ((D : ℝ) * w i) = w i * ((M : ℝ) * (D : ℝ)) / v := by ring
        rw [h3]
        have h4 : w i * ((M : ℝ) * (D : ℝ)) / v ≤ (Real.pi * (v : ℝ)) / v :=
          div_le_div_of_nonneg_right h2 (Nat.cast_nonneg v)
        have h5 : (Real.pi * (v : ℝ)) / v = Real.pi := mul_div_cancel_right₀ _ hvR.ne'
        rwa [h5] at h4
      rw [h1, show w i = LeanNumDetect.lpNorm q (u i) from rfl]
      field_simp [(hwpos i).ne', hDpos.ne', hvR.ne', (hMpos i).ne'] <;> try ring
    · rw [SegmentedVDM.neighborScaleFactor_of_lt (lt_of_not_ge h)]
      have h1 : min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i))
          = Real.pi / ((D : ℝ) * w i) := by
        apply min_eq_right
        have h2 : Real.pi * (v : ℝ) < w i * ((M : ℝ) * (D : ℝ)) :=
          (div_lt_iff₀ hMDpos).mp (lt_of_not_ge h)
        have h3 : Real.pi ≤ ((M : ℝ) / v) * ((D : ℝ) * w i) := by
          have h4 : Real.pi = Real.pi * (v : ℝ) / v := (mul_div_cancel_right₀ _ hvR.ne').symm
          rw [h4]
          have h5 : (Real.pi * (v : ℝ)) / v ≤ w i * ((M : ℝ) * (D : ℝ)) / v :=
            div_le_div_of_nonneg_right h2.le (Nat.cast_nonneg v)
          have h6 : w i * ((M : ℝ) * (D : ℝ)) / v = ((M : ℝ) / v) * ((D : ℝ) * w i) := by ring
          rwa [h6] at h5
        exact (div_le_iff₀ (mul_pos hDpos (hwpos i))).2 h3
      rw [h1]
      field_simp [(hwpos i).ne', hDpos.ne'] <;> try ring
  have hBpos : 0 ≤ (Real.sqrt 2) ^ (v - 1) *
      ∏ i : Fin (v - 1), SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i) :=
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) _) (Finset.prod_nonneg fun i _ => hnSF i)
  have hprod : Q0.mass ≤ (Real.sqrt 2) ^ (v - 1) *
      ∏ i : Fin (v - 1), SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i) := by
    have hmassQ : Q0.mass = ∏ i : Fin (v - 1), (F i).mass := by
      simp only [Q0, Q, G, SegmentedPacket.mass_widen, SegmentedPacket.mass_prod]
    calc
      Q0.mass = ∏ i : Fin (v - 1), (F i).mass := hmassQ
      _ ≤ ∏ i : Fin (v - 1), Real.sqrt 2 * Real.pi /
          ((D : ℝ) * min ((M : ℝ) / v) (Real.pi / ((D : ℝ) * w i)) * w i) :=
        Finset.prod_le_prod (fun i _ => (F i).mass_nonneg) (fun i _ => hFm i)
      _ = ∏ i : Fin (v - 1), Real.sqrt 2 *
          SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i) :=
        Finset.prod_congr rfl fun i _ => hfac i
      _ = (Real.sqrt 2) ^ (v - 1) *
          ∏ i : Fin (v - 1), SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hnorm : Real.sqrt (SegmentedVDM.energy P.coefficientVector) ≤
      ((Real.sqrt 2) ^ (v - 1) *
        ∏ i : Fin (v - 1), SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i)) /
        Real.sqrt (((M : ℝ) / v) ^ d * ((m + 1 : ℕ) : ℝ) ^ d) := by
    have h1 : ‖wvec‖ ≤ Q0.mass / Real.sqrt ((((zN + 1) * (m + 1)) ^ d : ℕ) : ℝ) :=
      SegmentedPacket.smoothedSegmentedVector_norm_le Q0 m zN D 0
    have h2 : Real.sqrt (((M : ℝ) / v) ^ d * ((m + 1 : ℕ) : ℝ) ^ d)
        ≤ Real.sqrt ((((zN + 1) * (m + 1)) ^ d : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt hdenle
    rw [henergy, Real.sqrt_sq (norm_nonneg wvec)]
    calc
      ‖wvec‖ ≤ Q0.mass / Real.sqrt ((((zN + 1) * (m + 1)) ^ d : ℕ) : ℝ) := h1
      _ ≤ ((Real.sqrt 2) ^ (v - 1) *
          ∏ i : Fin (v - 1), SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i)) /
          Real.sqrt ((((zN + 1) * (m + 1)) ^ d : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hprod (Real.sqrt_nonneg _)
      _ ≤ ((Real.sqrt 2) ^ (v - 1) *
          ∏ i : Fin (v - 1), SegmentedVDM.neighborScaleFactor q (v : ℝ) (M : ℝ) (D : ℝ) (u i)) /
          Real.sqrt (((M : ℝ) / v) ^ d * ((m + 1 : ℕ) : ℝ) ^ d) :=
        div_le_div_of_nonneg_left hBpos (Real.sqrt_pos.mpr hDnpos) h2
  exact ⟨P, hP0, hPu, hmassvec.trans hprod, hnorm⟩

/-- The `p = ∞`, worst-case-factor corollary of `lem:neighborset_segmented`
(`neighborSetSegmented_polynomial`): a product of recentered two-point factors
annihilating a finite family of short wrapped differences, with every
near-neighbor factor `π v/(MD‖u‖_{p'})` flattened to its worst case
`π/(T D Δ)` over the scale range `Δ ≤ ‖u‖₁ ≤ π/(2 D)`. The `L²` normalization of
`neighborSetSegmented_polynomial` is dropped in favor of the coefficient `ℓ¹`
mass bound. -/
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
  have hpq : ENNReal.HolderConjugate ⊤ 1 := inferInstance
  have hdim : (0 : ℝ) < (d : ℝ) ^ ((⊤ : ENNReal).toReal)⁻¹ := by simp
  have hL1 (i : Fin q) : LeanNumDetect.lpNorm 1 (u i) = l1Norm (u i) := by
    rw [LeanNumDetect.lpNorm_one]
    rfl
  have hLpos (i : Fin q) : 0 < LeanNumDetect.lpNorm 1 (u i) := by
    rw [hL1 i]
    exact lt_of_lt_of_le hΔ (hΔu i)
  have hLΔ (i : Fin q) : Δ ≤ LeanNumDetect.lpNorm 1 (u i) := by
    rw [hL1 i]
    exact hΔu i
  have htu (i : Fin q) : 2 ≤ Real.pi / (D * LeanNumDetect.lpNorm 1 (u i)) := by
    rw [hL1 i]
    apply (le_div_iff₀ (mul_pos hDR (lt_of_lt_of_le hΔ (hΔu i)))).2
    have h2 : l1Norm (u i) * (2 * (D : ℝ)) ≤ Real.pi :=
      (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hDR)).mp (hu i)
    have he : 2 * ((D : ℝ) * l1Norm (u i)) = l1Norm (u i) * (2 * (D : ℝ)) := by ring
    rw [he]
    exact h2
  choose F hF1 hF0 hFm using fun i =>
    neighborNodeFactor hpq hD hdim
      (t := min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))))
      (by
        have h1 : 2 * (d : ℝ) ^ ((⊤ : ENNReal).toReal)⁻¹ = 2 := by simp
        rw [h1]
        exact le_min hT (htu i))
      (u i) (hLpos i)
      (by
        have h1 := min_le_right T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i)))
        have h2 : min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) *
            (D * LeanNumDetect.lpNorm 1 (u i)) ≤ Real.pi :=
          (le_div_iff₀ (mul_pos hDR (hLpos i))).mp h1
        have h3 : LeanNumDetect.lpNorm 1 (u i) *
            (D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))))
            = min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) *
              (D * LeanNumDetect.lpNorm 1 (u i)) := by ring
        have h3' : LeanNumDetect.lpNorm 1 (u i) *
            (D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i)))) ≤ Real.pi := by
          rw [h3]
          exact h2
        have hminpos : 0 < D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) :=
          mul_pos hDR (lt_min_iff.mpr ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hT,
            div_pos Real.pi_pos (mul_pos hDR (hLpos i))⟩)
        exact (le_div_iff₀ hminpos).2 h3')
  have htd (i : Fin q) : T * D * Δ ≤
      D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) *
        LeanNumDetect.lpNorm 1 (u i) := by
    have h0 : T * D * Δ ≤ min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) * D *
        LeanNumDetect.lpNorm 1 (u i) := by
      rw [min_mul_of_nonneg _ _ hDR.le,
        min_mul_of_nonneg _ _ (hLpos i).le]
      apply le_min
      · have h := hLΔ i
        gcongr
      · have he : Real.pi / (D * LeanNumDetect.lpNorm 1 (u i)) * D *
            LeanNumDetect.lpNorm 1 (u i) = Real.pi := by
          rw [mul_assoc, div_mul_cancel₀ Real.pi (mul_ne_zero hDR.ne' (hLpos i).ne')]
        rwa [he]
    have he : D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) *
        LeanNumDetect.lpNorm 1 (u i)
        = min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) * D *
          LeanNumDetect.lpNorm 1 (u i) := by ring
    rw [he]
    exact h0
  have hfac (i : Fin q) : Real.sqrt 2 * Real.pi /
      (D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) * LeanNumDetect.lpNorm 1 (u i))
      ≤ Real.sqrt 2 / (T * D * Δ / Real.pi) := by
    have hnum : 0 ≤ Real.sqrt 2 * Real.pi := by positivity
    have hTDΔpos : 0 < T * D * Δ :=
      mul_pos (mul_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hT) hDR) hΔ
    have hdenpos : 0 < D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) *
        LeanNumDetect.lpNorm 1 (u i) :=
      mul_pos (mul_pos hDR (lt_min_iff.mpr ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hT,
        div_pos Real.pi_pos (mul_pos hDR (hLpos i))⟩)) (hLpos i)
    calc
      Real.sqrt 2 * Real.pi /
          (D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) *
            LeanNumDetect.lpNorm 1 (u i))
          ≤ Real.sqrt 2 * Real.pi / (T * D * Δ) :=
        div_le_div_of_nonneg_left hnum hTDΔpos (htd i)
      _ = Real.sqrt 2 / (T * D * Δ / Real.pi) := by
        field_simp [(hLpos i).ne', hDR.ne', hΔ.ne',
          (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hT).ne'] <;> try ring
  have hpos (i : Fin q) : 0 ≤ Real.sqrt 2 * Real.pi /
      (D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) * LeanNumDetect.lpNorm 1 (u i)) := by
    refine div_nonneg (by positivity) ?_
    have hmin : 0 ≤ min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) :=
      le_min (le_of_lt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hT))
        (div_nonneg Real.pi_pos.le (mul_nonneg hDR.le (hLpos i).le))
    exact mul_nonneg (mul_nonneg hDR.le hmin) (hLpos i).le
  let Q (i : Fin q) : SegmentedPacket d 0 ⌊T⌋₊ :=
    (F i).widen le_rfl (Nat.floor_mono (min_le_left _ _))
  let P : SegmentedPacket d 0 (q * ⌊T⌋₊) :=
    (SegmentedPacket.prod Q).widen (by simp) le_rfl
  have hQ (x : Point d) : P.value D x = ∏ i, (F i).value D x := by
    simp only [P, Q, SegmentedPacket.value_widen, SegmentedPacket.value_prod]
  have hmassQ : P.mass = ∏ i, (F i).mass := by
    simp only [P, Q, SegmentedPacket.mass_widen, SegmentedPacket.mass_prod]
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [hQ]
    exact Finset.prod_eq_one fun i _ => hF1 i
  · intro j
    rw [hQ]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact hF0 j
  · rw [hmassQ]
    calc
      (∏ i : Fin q, (F i).mass)
          ≤ ∏ i : Fin q, Real.sqrt 2 * Real.pi /
            (D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) *
              LeanNumDetect.lpNorm 1 (u i)) :=
        Finset.prod_le_prod (fun i _ => (F i).mass_nonneg) (fun i _ => hFm i)
      _ ≤ ∏ _i : Fin q, Real.sqrt 2 / (T * D * Δ / Real.pi) :=
        Finset.prod_le_prod (fun i _ => hpos i) (fun i _ => hfac i)
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

/-- The wrapped distance in one coordinate vanishes at equal points. -/
private theorem periodicCoordinateDistance_self (v : ℝ) :
    periodicCoordinateDistance v v = 0 := by
  unfold periodicCoordinateDistance
  rw [sub_self, abs_zero, sub_zero]
  exact min_eq_left (by positivity)

/-- The wrapped `ℓ^∞` distance of a point to itself vanishes. -/
private theorem periodicLInfDistance_self {d : ℕ} (u : Point d) :
    periodicLInfDistance u u = 0 := by
  have hfun : (fun k => periodicCoordinateDistance (u k) (u k)) = fun _ => (0:ℝ) := by
    funext k
    exact periodicCoordinateDistance_self (u k)
  unfold periodicLInfDistance
  rw [hfun]
  exact norm_zero

/-- The coefficient-mass constant `(1 / √a) ^ n` is the real power
`a ^ (-n / 2)` used by the manuscript. -/
private theorem inv_sqrt_pow_eq_rpow {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (1 / Real.sqrt a) ^ n = a ^ (-(n : ℝ) / 2) := by
  have hsqrt : (Real.sqrt a) ^ n = a ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ha.le]
    congr 1
    ring
  have h : (1 / Real.sqrt a) ^ n = ((Real.sqrt a) ^ n)⁻¹ := by
    rw [one_div, inv_pow]
  rw [h, hsqrt, ← Real.rpow_neg ha.le ((n : ℝ) / 2)]
  congr 1
  exact (neg_div _ _).symm

/-- The frame constant `a_β = 2 - exp (1 / (2 * β))` of manuscript
`thm:well_separated_segmented` is positive in the range `β > 1 / (2 * log 2)`. -/
private theorem wellSeparatedFrameConstant_pos {β : ℝ}
    (hβ : 1 / (2 * Real.log 2) < β) : 0 < 2 - Real.exp (1 / (2 * β)) := by
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
  linarith

/-- The frame constant `a_β = 2 - exp (1 / (2 * β))` is at most one. -/
private theorem wellSeparatedFrameConstant_le_one {β : ℝ}
    (hβ : 1 / (2 * Real.log 2) < β) : 2 - Real.exp (1 / (2 * β)) ≤ 1 := by
  have hβpos : 0 < β :=
    (by positivity : 0 < 1 / (2 * Real.log 2)).trans hβ
  have hone : 1 ≤ Real.exp (1 / (2 * β)) :=
    Real.one_le_exp (by positivity)
  linarith

/-- The fine-cube Fourier energy of a node family is the squared `ℓ²` energy of
its evaluation on the nonnegative frequency cube. -/
private theorem fineCubeFourierEnergy_eq_energy_fineCubeEvaluation
    {d : ℕ} {ι : Type*} [Fintype ι] (K : ℕ) (x : ι → Point d)
    (v : ι → ℂ) :
    FineCubeFrame.fineCubeFourierEnergy K x v =
      SegmentedVDM.energy (fineCubeEvaluation K x *ᵥ v) := by
  classical
  simp only [FineCubeFrame.fineCubeFourierEnergy, SegmentedVDM.energy,
    fineCubeEvaluation, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro α _
  apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
  apply Finset.sum_congr rfl
  intro j _
  have hphase :
      Complex.I * (∑ k, ((α k : ℕ) : ℂ) * x j k) =
        Complex.I * ((∑ k, (α k : ℝ) * x j k : ℝ) : ℂ) := by
    congr 1
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [mul_comm (v j), hphase]

/-! ### Normalization bridge to the translated-cube frame

The remaining analytic input is the fine-cube lower frame bound with constant
`2 - exp (1 / (2 * β))`, i.e. the `r = 0`, `m = K` case of manuscript
`thm:well_separated_segmented`.  Its proved form
`BartonCubeFrame.fineCubeFourier_bounds_of_translatedCube` cannot be invoked
here because `General.Fourier.BartonCubeFrame` imports this module
(`NumDetect.SegmentedVandermonde`) to expose the `HasFineCubeFrame` interface.
The normalization bridge to the importable translated-cube frame
`External.translatedCubeFourier_lowerFrame` is the shared conversion
`FineCubeFrame.translatedCubeFourierEnergy_normalizedAngularPoint` through
`FineCubeFrame.normalizedAngularPoint`. -/

/-- The fine-cube lower frame bound with constant `a_β` on an `η`-separated
angular node family.  This is the `r = 0`, `m = K` case of manuscript
`thm:well_separated_segmented`, obtained from the proved translated-cube
Barton frame through the normalization bridge above. -/
private theorem fineCube_frame_of_angularSeparation
    {d : ℕ} {ι : Type} [Fintype ι] {K : ℕ} {β : ℝ}
    (hd : 1 ≤ d) (hK : 1 ≤ K) (hβ : 1 / (2 * Real.log 2) ≤ β)
    (x : ι → Point d)
    (hx : ∀ j, InAngularCube (x j))
    (hsep : ∀ i j, i ≠ j →
      4 * Real.pi * β * d / (K + 1) ≤ periodicLInfDistance (x i) (x j)) :
    ∀ v,
      (2 - Real.exp (1 / (2 * β))) * (((K + 1) ^ d : ℕ) : ℝ) *
          SegmentedVDM.energy v ≤
        SegmentedVDM.energy (fineCubeEvaluation K x *ᵥ v) := by
  intro v
  have hN : 2 ≤ K + 1 := by omega
  have hx' :
      ∀ j, External.InUnitHalfOpenCube
        (FineCubeFrame.normalizedAngularPoint (x j)) :=
    fun j => FineCubeFrame.normalizedAngularPoint_mem_halfOpenCube (hx j)
  have hsep' :
      ∀ i j, i ≠ j →
        2 * β * d / (K + 1) ≤
          External.unitPeriodicLInfDistance
            (FineCubeFrame.normalizedAngularPoint (x i))
            (FineCubeFrame.normalizedAngularPoint (x j)) := by
    intro i j hij
    rw [FineCubeFrame.normalizedAngularPoint_lInfDistance (hx i) (hx j)]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    calc
      (2 * β * d / (K + 1)) * (2 * Real.pi) =
          4 * Real.pi * β * d / (K + 1) := by ring
      _ ≤ periodicLInfDistance (x i) (x j) := hsep i j hij
  have h := External.translatedCubeFourier_lowerFrame β
    (fun j => FineCubeFrame.normalizedAngularPoint (x j)) hd hN hβ hx'
    (by simpa only [Nat.cast_add, Nat.cast_one] using hsep') v
  rw [FineCubeFrame.translatedCubeFourierEnergy_normalizedAngularPoint] at h
  rwa [← fineCubeFourierEnergy_eq_energy_fineCubeEvaluation]

/-- Product of one cardinal factor per color class, realizing the decomposition
of manuscript `prop:decomposition` by the injective slots of `C`.  The
anchor's value is one, every node of a family covered by the non-anchor labels
is annihilated, and the coefficient `ℓ¹` mass is at most `(1 / √a) ^ nStar`
when each color class carries a fine-cube frame with constant `a`.  This is the
constructive core of manuscript `lem:localization`. -/
theorem localizationPacket_of_colorCover
    {d n A nStar K : ℕ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x) (anchor : Fin n)
    (outside : Fin n → Prop)
    (hcover : ∀ j, outside j → C.label j ≠ C.label anchor)
    {a : ℝ} (ha : 0 < a)
    (hframe : ∀ color (v : ↥(clumpColorClass C anchor color) → ℂ),
      a * (((K + 1) ^ d : ℕ) : ℝ) * SegmentedVDM.energy v ≤
        SegmentedVDM.energy
          (fineCubeEvaluation K
            (fun j : ↥(clumpColorClass C anchor color) => x j) *ᵥ v)) :
    ∃ P : SegmentedPacket d (nStar * K) 0,
      (∀ D, P.value D (x anchor) = 1) ∧
      (∀ D j, outside j → P.value D (x j) = 0) ∧
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
    have hne : C.label j ≠ C.label anchor := hcover j hj
    have hmem : j ∈ clumpColorClass C anchor (C.slot j) := by
      simp [hne]
    have hzero := (hF (C.slot j)).1 D ⟨j, hmem⟩
    have haj : anchor ≠ j := by
      intro he
      exact hne (congrArg C.label he.symm)
    simpa [Subtype.ext_iff, haj] using hzero
  · simp only [P, SegmentedPacket.mass_widen, SegmentedPacket.mass_prod]
    calc
      _ ≤ ∏ _color : Fin nStar, 1 / Real.sqrt a :=
        Finset.prod_le_prod
          (fun color _ => (F color).mass_nonneg)
          (fun color _ => (hF color).2)
      _ = _ := by simp

/-- Product of one cardinal factor per color eliminates every node outside the
anchor's clump.  This is the color-class form of the general localization
theorem `localizationPolynomial_of_angularClumpStructure` (manuscript
`lem:localization`): the vanishing set is phrased by non-anchor labels and the
fine-cube frame hypothesis is kept explicit. -/
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
      P.mass ≤ (1 / Real.sqrt a) ^ nStar :=
  localizationPacket_of_colorCover C anchor
    (fun j => C.label j ≠ C.label anchor) (fun _ hj => hj) ha hframe

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

/-- Manuscript `lem:localization` at full strength, with the `L^∞(𝕋^d)`
conclusion in the manuscript's own normalization.  Let `x` form
`(A, ∞, τ, η, nStar)`-clumps and let `m < D`.  With `K = ⌊m / nStar⌋`, if
`β > 1 / (2 * log 2)` and `η ≥ 4 * π * β * d / (K + 1)`, then for every node
`x anchor` there exists `P : SegmentedPacket d m 0`, the finite presentation of
a polynomial of `𝒫(m, 0, D, d)`, with `P.value D (x anchor) = 1`, with
`P.value D (x j) = 0` for every `j ∉ localNeighborhood x anchor τ`, and with

$$
\|g_k\|_{L^\infty(\mathbb T^d)}\le
\left(2-e^{1/(2\beta)}\right)^{-n^\star/2},
\qquad
g_k(\bm\omega) = \sum_i c_i\, e^{2\pi i\, \mathbf s_i \cdot \bm\omega} .
$$

Here `P.value D (x j)` is the manuscript's `g_k(y_j / (2 * π))` in the angular
normalization (the `1 / (2 * π)` is absorbed by `SegmentedPacket.value`), and
the norm bound is the genuine torus `L^∞` norm `unitTorusLInfNorm` of the
polynomial `unitTorusTrigPolynomial (P.angularFrequency D) P.coeff` presented
by `P`, which equals the packet sup norm `P.linftyNorm D` by
`SegmentedPacket.linftyNorm_eq_unitTorusLInfNorm`
(cf. `localizationPolynomial_of_angularClumpStructure_linftyNorm`).  The
conclusion is derived from the coefficient `ℓ¹` mass bound
`P.mass ≤ (1 / Real.sqrt a) ^ nStar` of `localizationPacket_of_colorCover`,
the coefficient form of the conclusion, through the triangle-inequality sup
bound `unitTorusLInfNorm_le` of the Parseval bridge; as the bridge states, the
sup bound needs no frequency distinctness.  The color decomposition is
manuscript `prop:decomposition` realized by the injective slots of `ClumpSlots`,
and the frame constant `2 - exp (1 / (2 * β))` is the fine-cube (`r = 0`,
`m = K`) case of manuscript `thm:well_separated_segmented`. -/
theorem localizationPolynomial_of_angularClumpStructure
    {d n A nStar m D : ℕ} {x : Fin n → Point d} {τ η β : ℝ}
    (hclumps : IsAngularClumpStructure x A nStar τ η)
    (_hDm : m < D) (hβ : 1 / (2 * Real.log 2) < β)
    (hη : 4 * Real.pi * β * d / ((m / nStar : ℕ) + 1) ≤ η)
    (anchor : Fin n) :
    ∃ P : SegmentedPacket d m 0,
      P.value D (x anchor) = 1 ∧
      (∀ j, j ∉ localNeighborhood x anchor τ → P.value D (x j) = 0) ∧
      unitTorusLInfNorm (unitTorusTrigPolynomial (P.angularFrequency D) P.coeff) ≤
        (2 - Real.exp (1 / (2 * β))) ^ (-(nStar : ℝ) / 2) := by
  classical
  obtain ⟨C, hsame, hcross⟩ := clumpStructure_has_slots hclumps
  have hτ : 0 < τ := hclumps.2.1
  have hτη : τ ≤ η := hclumps.2.2.1
  have hcube : ∀ j, InAngularCube (x j) := hclumps.2.2.2.1
  have hneighborhood (j : Fin n) :
      localNeighborhood x j τ =
        Finset.univ.filter fun k => C.label k = C.label j :=
    localNeighborhood_eq_of_clumpLabels hτη hsame hcross j
  have hbridge (j : Fin n) (hj : j ∉ localNeighborhood x anchor τ) :
      C.label j ≠ C.label anchor := by
    intro hlabel
    apply hj
    rw [hneighborhood anchor]
    simp [hlabel]
  have haβpos : 0 < 2 - Real.exp (1 / (2 * β)) :=
    wellSeparatedFrameConstant_pos hβ
  have hrpow : (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar =
      (2 - Real.exp (1 / (2 * β))) ^ (-(nStar : ℝ) / 2) :=
    inv_sqrt_pow_eq_rpow haβpos nStar
  have hone : (1 : ℝ) ≤ (2 - Real.exp (1 / (2 * β))) ^ (-(nStar : ℝ) / 2) := by
    have haβle := wellSeparatedFrameConstant_le_one hβ
    have hneg : (-(nStar : ℝ) / 2) ≤ 0 := by
      rw [neg_div 2 (nStar : ℝ)]
      exact neg_nonpos.mpr
        (div_nonneg (Nat.cast_nonneg nStar) (by norm_num))
    calc
      (1 : ℝ) = (2 - Real.exp (1 / (2 * β))) ^ (0 : ℝ) :=
        (Real.rpow_zero _).symm
      _ ≤ (2 - Real.exp (1 / (2 * β))) ^ (-(nStar : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_ge haβpos haβle hneg
  by_cases hout : ∃ j, j ∉ localNeighborhood x anchor τ
  · obtain ⟨j₀, hj₀⟩ := hout
    -- In the nontrivial case the dimension is positive.
    have hd : 1 ≤ d := by
      by_contra hnd
      have hd0 : d = 0 := by omega
      haveI hempty : IsEmpty (Fin d) :=
        ⟨fun i => by have hi := i.isLt; omega⟩
      haveI : Subsingleton (Point d) :=
        ⟨fun u v => funext fun k => hempty.elim k⟩
      have heq : x anchor = x j₀ := Subsingleton.elim _ _
      apply hj₀
      simp only [localNeighborhood, Finset.mem_filter, Finset.mem_univ,
        true_and]
      rw [heq, periodicLInfDistance_self]
      exact hτ.le
    -- The manuscript argument gives `K = ⌊m / nStar⌋ ≥ 1`.
    have hK : 1 ≤ (m / nStar : ℕ) := by
      by_contra hnk
      have hK0 : (m / nStar : ℕ) = 0 := by
        by_contra hk
        exact hnk (Nat.one_le_iff_ne_zero.2 hk)
      have hη' : 4 * Real.pi * β * d ≤ η := by
        have hden : (((m / nStar : ℕ) : ℝ) + 1) = 1 := by
          rw [hK0]
          simp
        rw [hden, div_one] at hη
        exact hη
      have hquarter : (1 : ℝ) / 4 < 1 / (2 * Real.log 2) := by
        rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
        nlinarith [Real.log_two_lt_d9]
      have hβq : (1 : ℝ) / 4 < β := hquarter.trans hβ
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hfac : (1 : ℝ) < 4 * β * d := by
        have h1 : (1 : ℝ) < 4 * β := by nlinarith
        calc
          (1:ℝ) = 1 * 1 := by ring
          _ < (4 * β) * 1 := by nlinarith
          _ ≤ (4 * β) * d := mul_le_mul_of_nonneg_left hdR (by positivity)
          _ = 4 * β * d := by ring
      have hlt : Real.pi < 4 * Real.pi * β * d := by
        have heq : 4 * Real.pi * β * d = Real.pi * (4 * β * d) := by ring
        rw [heq]
        simpa using mul_lt_mul_of_pos_left hfac Real.pi_pos
      have hfar : η < periodicLInfDistance (x anchor) (x j₀) :=
        hcross anchor j₀ (hbridge j₀ hj₀).symm
      have hle : periodicLInfDistance (x anchor) (x j₀) ≤ Real.pi :=
        periodicLInfDistance_le_pi (hcube anchor) (hcube j₀)
      linarith
    -- Each color class is `η`-separated, hence a fine-cube frame at `K`.
    have hframe (color : Fin nStar)
        (v : ↥(clumpColorClass C anchor color) → ℂ) :
        (2 - Real.exp (1 / (2 * β))) *
            ((((m / nStar) + 1) ^ d : ℕ) : ℝ) * SegmentedVDM.energy v ≤
          SegmentedVDM.energy
            (fineCubeEvaluation (m / nStar)
              (fun j : ↥(clumpColorClass C anchor color) => x j) *ᵥ v) := by
      refine fineCube_frame_of_angularSeparation hd hK (le_of_lt hβ)
        (fun j : ↥(clumpColorClass C anchor color) => x j)
        (fun j => hcube j) (fun i j hij => ?_) v
      have hsep' :
          4 * Real.pi * β * d / ((m / nStar : ℕ) + 1) ≤
            periodicLInfDistance (x i) (x j) :=
        hη.trans
          (hcross i j
            (clumpColorClass_labels_ne C anchor color i j hij)).le
      simpa using hsep'
    obtain ⟨P₀, hP₀one, hP₀zero, hP₀mass⟩ :=
      localizationPacket_of_colorCover C anchor
        (fun j => j ∉ localNeighborhood x anchor τ)
        (fun j hj => hbridge j hj) haβpos hframe
    let P : SegmentedPacket d m 0 :=
      P₀.widen (by simpa [Nat.mul_comm] using Nat.div_mul_le_self m nStar)
        le_rfl
    refine ⟨P, ?_, ?_, ?_⟩
    · show P.value D (x anchor) = 1
      exact hP₀one D
    · intro j hj
      show P.value D (x j) = 0
      exact hP₀zero D j hj
    · show unitTorusLInfNorm (unitTorusTrigPolynomial (P.angularFrequency D) P.coeff) ≤
        (2 - Real.exp (1 / (2 * β))) ^ (-(nStar : ℝ) / 2)
      calc
        unitTorusLInfNorm (unitTorusTrigPolynomial (P.angularFrequency D) P.coeff)
            ≤ ∑ i, ‖P.coeff i‖ :=
          unitTorusLInfNorm_le (P.angularFrequency D) P.coeff
        _ = P.mass := rfl
        _ = P₀.mass := rfl
        _ ≤ (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar := hP₀mass
        _ = (2 - Real.exp (1 / (2 * β))) ^ (-(nStar : ℝ) / 2) := hrpow
  · -- The complement of the neighborhood is empty: the constant polynomial
    -- works, as in the manuscript.
    have hall : ∀ j : Fin n, j ∈ localNeighborhood x anchor τ := by
      intro j
      by_contra hk
      exact hout ⟨j, hk⟩
    let P : SegmentedPacket d m 0 :=
      (SegmentedPacket.one d).widen (Nat.zero_le m) le_rfl
    refine ⟨P, ?_, ?_, ?_⟩
    · show P.value D (x anchor) = 1
      simp [P]
    · intro j hj
      exact absurd (hall j) hj
    · show unitTorusLInfNorm (unitTorusTrigPolynomial (P.angularFrequency D) P.coeff) ≤
        (2 - Real.exp (1 / (2 * β))) ^ (-(nStar : ℝ) / 2)
      calc
        unitTorusLInfNorm (unitTorusTrigPolynomial (P.angularFrequency D) P.coeff)
            ≤ ∑ i, ‖P.coeff i‖ :=
          unitTorusLInfNorm_le (P.angularFrequency D) P.coeff
        _ = P.mass := rfl
        _ = 1 := by simp [P]
        _ ≤ (2 - Real.exp (1 / (2 * β))) ^ (-(nStar : ℝ) / 2) := hone

/-- The `L^∞` conclusion of `localizationPolynomial_of_angularClumpStructure`
phrased with the packet sup norm `SegmentedPacket.linftyNorm` over all of
`Point d`; it equals the torus `L^∞` norm of the presented polynomial by
`SegmentedPacket.linftyNorm_eq_unitTorusLInfNorm`. -/
theorem localizationPolynomial_of_angularClumpStructure_linftyNorm
    {d n A nStar m D : ℕ} {x : Fin n → Point d} {τ η β : ℝ}
    (hclumps : IsAngularClumpStructure x A nStar τ η)
    (hDm : m < D) (hβ : 1 / (2 * Real.log 2) < β)
    (hη : 4 * Real.pi * β * d / ((m / nStar : ℕ) + 1) ≤ η)
    (anchor : Fin n) :
    ∃ P : SegmentedPacket d m 0,
      P.value D (x anchor) = 1 ∧
      (∀ j, j ∉ localNeighborhood x anchor τ → P.value D (x j) = 0) ∧
      P.linftyNorm D ≤ (2 - Real.exp (1 / (2 * β))) ^ (-(nStar : ℝ) / 2) := by
  obtain ⟨P, hone, hzero, hnorm⟩ :=
    localizationPolynomial_of_angularClumpStructure hclumps hDm hβ hη anchor
  refine ⟨P, hone, hzero, ?_⟩
  rw [P.linftyNorm_eq_unitTorusLInfNorm]
  exact hnorm

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
