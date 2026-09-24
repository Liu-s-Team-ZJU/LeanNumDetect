import NumDetect.Matrices
import General.Fourier.TrigonometricPolynomialParseval
import General.Fourier.FineCubeFrame
import General.Fourier.TranslatedCubeFourier
import SegmentedVDM.Interpolation
import SegmentedVDM.UniformFrame
import SegmentedVDM.UniformInterpolation
import SegmentedVDM.Smoothing
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
The function space `𝒫(m,r,D,d)` of Appendix B, Definition B.1.  Its
coefficients are indexed once by the Cartesian product of the disjoint
segments.  The condition `m < D` is stored in every member of the space.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- The frequency `D s + h` of a canonical segmented index. -/
def segmentedPolynomialFrequency (d m r D : ℕ)
    (a : SegmentedIndex d m r) : Fin d → ℤ :=
  fun k => ((D * (a k).1 + (a k).2 : ℕ) : ℤ)

/-- If `D > m`, the canonical index labels distinct frequency vectors. -/
theorem segmentedPolynomialFrequency_injective {d m r D : ℕ} (hmD : m < D) :
    Function.Injective (segmentedPolynomialFrequency d m r D) := by
  have hDpos : 0 < D := by omega
  intro a b hab
  have hval : ∀ k : Fin d,
      (D * (a k).1 + (a k).2 : ℕ) = (D * (b k).1 + (b k).2 : ℕ) := by
    intro k
    have hk := congrFun hab k
    simp only [segmentedPolynomialFrequency] at hk
    exact_mod_cast hk
  have hcoarse : ∀ k : Fin d, ((a k).1 : ℕ) = ((b k).1 : ℕ) := by
    intro k
    have ha : ((a k).2 : ℕ) < D :=
      lt_of_le_of_lt (Nat.le_of_lt_succ (a k).2.isLt) hmD
    have hb : ((b k).2 : ℕ) < D :=
      lt_of_le_of_lt (Nat.le_of_lt_succ (b k).2.isLt) hmD
    have hdiv := congrArg (fun n : ℕ => n / D) (hval k)
    have h1 : (D * (a k).1 + (a k).2 : ℕ) / D = ((a k).1 : ℕ) := by
      rw [add_comm, Nat.add_mul_div_left ((a k).2 : ℕ) ((a k).1 : ℕ) hDpos,
        Nat.div_eq_of_lt ha, zero_add]
    have h2 : (D * (b k).1 + (b k).2 : ℕ) / D = ((b k).1 : ℕ) := by
      rw [add_comm, Nat.add_mul_div_left ((b k).2 : ℕ) ((b k).1 : ℕ) hDpos,
        Nat.div_eq_of_lt hb, zero_add]
    rw [h1, h2] at hdiv
    exact hdiv
  have hfine : ∀ k : Fin d, ((a k).2 : ℕ) = ((b k).2 : ℕ) := by
    intro k
    have hk := hval k
    rw [hcoarse k] at hk
    exact Nat.add_left_cancel hk
  funext k
  exact Prod.ext (Fin.ext (hcoarse k)) (Fin.ext (hfine k))

/-- Appendix B's `𝒫(m,r,D,d)`, represented by its unique frequency
coefficients and carrying the required disjointness assumption `D > m`. -/
structure SegmentedPolynomial (d m r D : ℕ) where
  hD : m < D
  coeff : SegmentedIndex d m r → ℂ

namespace SegmentedPolynomial

/-- The exact finite series in Definition B.1, with the `2π` phase. -/
def eval {d m r D : ℕ} (P : SegmentedPolynomial d m r D)
    (ω : Point d) : ℂ :=
  unitTorusTrigPolynomial (segmentedPolynomialFrequency d m r D) P.coeff ω

instance {d m r D : ℕ} : CoeFun (SegmentedPolynomial d m r D)
    (fun _ => Point d → ℂ) := ⟨eval⟩

theorem eval_eq_sum {d m r D : ℕ} (P : SegmentedPolynomial d m r D)
    (ω : Point d) :
    P ω = ∑ a : SegmentedIndex d m r,
      P.coeff a * Complex.exp
        (Complex.I * (((2 * Real.pi) *
          (∑ k, ((D * (a k).1 + (a k).2 : ℕ) : ℝ) * ω k) : ℝ) : ℂ)) := by
  rfl

/-- Evaluation at an angular node `y` equals `P(y/(2π))`. -/
def angularValue {d m r D : ℕ} (P : SegmentedPolynomial d m r D)
    (y : Point d) : ℂ :=
  P (fun k => y k / (2 * Real.pi))

theorem angularValue_eq_angularTrigPolynomial {d m r D : ℕ}
    (P : SegmentedPolynomial d m r D) (y : Point d) :
    P.angularValue y =
      angularTrigPolynomial (segmentedPolynomialFrequency d m r D) P.coeff y := by
  have h2π : (2:ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hscale : (fun k : Fin d => 2 * Real.pi * (y k / (2 * Real.pi))) = y := by
    funext k
    field_simp [h2π]
  unfold angularValue eval
  rw [unitTorusTrigPolynomial_eq_angularTrigPolynomial, hscale]

/-- Coefficients are canonical: no two indices have the same frequency. -/
theorem frequency_injective {d m r D : ℕ} (P : SegmentedPolynomial d m r D) :
    Function.Injective (segmentedPolynomialFrequency d m r D) :=
  segmentedPolynomialFrequency_injective P.hD

/-- Definition B.2: each polynomial takes the Kronecker value at every
node, evaluated in the manuscript's normalized coordinate. -/
def IsLagrangeFamily {d m r D n : ℕ} (node : Fin n → Point d)
    (F : Fin n → SegmentedPolynomial d m r D) : Prop :=
  ∀ k ℓ : Fin n, (F k).angularValue (node ℓ) = if k = ℓ then 1 else 0

@[ext] theorem ext {d m r D : ℕ} {P Q : SegmentedPolynomial d m r D}
    (h : P.coeff = Q.coeff) : P = Q := by
  cases P
  cases Q
  simp_all

instance {d m r D : ℕ} : Add (SegmentedPolynomial d m r D) where
  add P Q := ⟨P.hD, P.coeff + Q.coeff⟩

instance {d m r D : ℕ} : Neg (SegmentedPolynomial d m r D) where
  neg P := ⟨P.hD, -P.coeff⟩

instance {d m r D : ℕ} : Sub (SegmentedPolynomial d m r D) where
  sub P Q := P + -Q

def zero {d m r D : ℕ} (hmD : m < D) : SegmentedPolynomial d m r D :=
  ⟨hmD, 0⟩

instance {d m r D : ℕ} [Fact (m < D)] : Zero (SegmentedPolynomial d m r D) where
  zero := zero Fact.out

@[simp] theorem coeff_add {d m r D : ℕ} (P Q : SegmentedPolynomial d m r D)
    (a : SegmentedIndex d m r) : (P + Q).coeff a = P.coeff a + Q.coeff a := rfl

@[simp] theorem coeff_neg {d m r D : ℕ} (P : SegmentedPolynomial d m r D)
    (a : SegmentedIndex d m r) : (-P).coeff a = -P.coeff a := rfl

@[simp] theorem eval_add {d m r D : ℕ} (P Q : SegmentedPolynomial d m r D)
    (ω : Point d) : (P + Q) ω = P ω + Q ω := by
  simp [eval, unitTorusTrigPolynomial, Finset.sum_add_distrib, add_mul]

@[simp] theorem eval_neg {d m r D : ℕ} (P : SegmentedPolynomial d m r D)
    (ω : Point d) : (-P) ω = -P ω := by
  simp [eval, unitTorusTrigPolynomial, ← Finset.sum_neg_distrib]

@[simp] theorem eval_zero {d m r D : ℕ} (hmD : m < D) (ω : Point d) :
    (zero (d := d) (r := r) hmD) ω = 0 := by
  simp [zero, eval, unitTorusTrigPolynomial]

/-- The constant one in the smallest segmented support. -/
def one (d D : ℕ) (hD : 0 < D) : SegmentedPolynomial d 0 0 D where
  hD := hD
  coeff _ := 1

@[simp] theorem eval_one (d D : ℕ) (hD : 0 < D) (ω : Point d) :
    (one d D hD) ω = 1 := by
  simp [eval, one, unitTorusTrigPolynomial, unitTorusAtom,
    segmentedPolynomialFrequency]

/-- The coefficient `ℓ¹` mass of the canonical finite series. -/
def mass {d m r D : ℕ} (P : SegmentedPolynomial d m r D) : ℝ :=
  ∑ a, ‖P.coeff a‖

@[simp] theorem mass_one (d D : ℕ) (hD : 0 < D) :
    (one d D hD).mass = 1 := by
  simp [mass, one]

theorem mass_nonneg {d m r D : ℕ} (P : SegmentedPolynomial d m r D) :
    0 ≤ P.mass := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem eval_norm_le_mass {d m r D : ℕ}
    (P : SegmentedPolynomial d m r D) (ω : Point d) :
    ‖P ω‖ ≤ P.mass :=
  norm_unitTorusTrigPolynomial_le _ _ _

/-- The supremum norm over the unit torus, in Definition B.1's coordinates. -/
def linftyNorm {d m r D : ℕ} (P : SegmentedPolynomial d m r D) : ℝ :=
  unitTorusLInfNorm P

theorem linftyNorm_le_mass {d m r D : ℕ}
    (P : SegmentedPolynomial d m r D) : P.linftyNorm ≤ P.mass :=
  unitTorusLInfNorm_le _ _

/-- Inclusion of a segmented index into larger fine and coarse budgets. -/
def embedIndex {d m r m' r' : ℕ} (hm : m ≤ m') (hr : r ≤ r')
    (a : SegmentedIndex d m r) : SegmentedIndex d m' r' :=
  fun k =>
    (⟨(a k).1.val, by omega⟩, ⟨(a k).2.val, by omega⟩)

theorem embedIndex_injective {d m r m' r' : ℕ}
    (hm : m ≤ m') (hr : r ≤ r') :
    Function.Injective (embedIndex (d := d) hm hr) := by
  intro a b hab
  funext k
  have hk := congrFun hab k
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun p => p.1.val) hk
  · apply Fin.ext
    exact congrArg (fun p => p.2.val) hk

theorem frequency_embedIndex {d m r m' r' D : ℕ}
    (hm : m ≤ m') (hr : r ≤ r') (a : SegmentedIndex d m r) :
    segmentedPolynomialFrequency d m' r' D (embedIndex hm hr a) =
      segmentedPolynomialFrequency d m r D a := by
  rfl

/-- Regard the same polynomial as having larger support budgets. -/
def widen {d m r m' r' D : ℕ} (P : SegmentedPolynomial d m r D)
    (hm : m ≤ m') (hr : r ≤ r') (hmD' : m' < D) :
    SegmentedPolynomial d m' r' D where
  hD := hmD'
  coeff c := ∑ a : SegmentedIndex d m r,
    if embedIndex hm hr a = c then P.coeff a else 0

@[simp] theorem eval_widen {d m r m' r' D : ℕ}
    (P : SegmentedPolynomial d m r D) (hm : m ≤ m') (hr : r ≤ r')
    (hmD' : m' < D) (ω : Point d) :
    (P.widen hm hr hmD') ω = P ω := by
  classical
  change (∑ c : SegmentedIndex d m' r',
      (∑ a : SegmentedIndex d m r,
        if embedIndex hm hr a = c then P.coeff a else 0) *
        unitTorusAtom (segmentedPolynomialFrequency d m' r' D c) ω) =
    ∑ a : SegmentedIndex d m r,
      P.coeff a * unitTorusAtom (segmentedPolynomialFrequency d m r D a) ω
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq Finset.univ (embedIndex hm hr a)
    (fun c => P.coeff a * unitTorusAtom (segmentedPolynomialFrequency d m' r' D c) ω),
    if_pos (Finset.mem_univ (embedIndex hm hr a)), frequency_embedIndex]

@[simp] theorem angularValue_widen {d m r m' r' D : ℕ}
    (P : SegmentedPolynomial d m r D) (hm : m ≤ m') (hr : r ≤ r')
    (hmD' : m' < D) (y : Point d) :
    (P.widen hm hr hmD').angularValue y = P.angularValue y :=
  eval_widen P hm hr hmD' _

@[simp] theorem mass_widen {d m r m' r' D : ℕ}
    (P : SegmentedPolynomial d m r D) (hm : m ≤ m') (hr : r ≤ r')
    (hmD' : m' < D) :
    (P.widen hm hr hmD').mass = P.mass := by
  classical
  let e := embedIndex (d := d) hm hr
  have he : Function.Injective e := embedIndex_injective hm hr
  have hnorm (c : SegmentedIndex d m' r') :
      ‖∑ a : SegmentedIndex d m r,
          if e a = c then P.coeff a else 0‖ =
        ∑ a : SegmentedIndex d m r,
          if e a = c then ‖P.coeff a‖ else 0 := by
    by_cases hc : ∃ a, e a = c
    · obtain ⟨a, ha⟩ := hc
      have hsingle (f : SegmentedIndex d m r → ℂ) :
          (∑ i : SegmentedIndex d m r,
            if e i = c then f i else 0) = f a := by
        rw [Finset.sum_eq_single a]
        · simp [ha]
        · intro i _ hia
          have hi : e i ≠ c := by
            intro h
            exact hia (he (h.trans ha.symm))
          simp [hi]
        · simp
      have hsingleR :
          (∑ i : SegmentedIndex d m r,
            if e i = c then ‖P.coeff i‖ else 0) = ‖P.coeff a‖ := by
        rw [Finset.sum_eq_single a]
        · simp [ha]
        · intro i _ hia
          have hi : e i ≠ c := by
            intro h
            exact hia (he (h.trans ha.symm))
          simp [hi]
        · simp
      rw [hsingle, hsingleR]
    · have hall (a : SegmentedIndex d m r) : e a ≠ c := by
        intro h
        exact hc ⟨a, h⟩
      simp [hall]
  change (∑ c : SegmentedIndex d m' r',
      ‖∑ a : SegmentedIndex d m r,
        if e a = c then P.coeff a else 0‖) =
    ∑ a : SegmentedIndex d m r, ‖P.coeff a‖
  simp_rw [hnorm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_ite_eq Finset.univ (e a)
    (fun _ => ‖P.coeff a‖), if_pos (Finset.mem_univ (e a))]

@[simp] theorem l2Norm_widen {d m r m' r' D : ℕ}
    (P : SegmentedPolynomial d m r D) (hm : m ≤ m') (hr : r ≤ r')
    (hmD' : m' < D) :
    unitTorusL2Norm (P.widen hm hr hmD') = unitTorusL2Norm P := by
  congr 1
  funext ω
  exact eval_widen P hm hr hmD' ω

/-- Addition of block and within-block indices. The result lies in the
expanded budgets, with no carry between the two parts. -/
def addIndex {d m₁ m₂ r₁ r₂ : ℕ}
    (a : SegmentedIndex d m₁ r₁) (b : SegmentedIndex d m₂ r₂) :
    SegmentedIndex d (m₁ + m₂) (r₁ + r₂) :=
  fun k =>
    (⟨(a k).1.val + (b k).1.val, by omega⟩,
      ⟨(a k).2.val + (b k).2.val, by omega⟩)

theorem frequency_addIndex {d m₁ m₂ r₁ r₂ D : ℕ}
    (a : SegmentedIndex d m₁ r₁) (b : SegmentedIndex d m₂ r₂) :
    segmentedPolynomialFrequency d (m₁ + m₂) (r₁ + r₂) D (addIndex a b) =
      segmentedPolynomialFrequency d m₁ r₁ D a +
        segmentedPolynomialFrequency d m₂ r₂ D b := by
  funext k
  simp only [segmentedPolynomialFrequency, addIndex, Pi.add_apply]
  push_cast
  ring

/-- Fourier atoms multiply by adding their integer frequencies. -/
private theorem atom_mul {d : ℕ} (s t : Fin d → ℤ) (ω : Point d) :
    unitTorusAtom (s + t) ω = unitTorusAtom s ω * unitTorusAtom t ω := by
  simp only [unitTorusAtom]
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, Int.cast_add, add_mul]
  rw [Finset.sum_add_distrib]
  push_cast
  ring

/-- Convolution collects every product contribution at its single canonical
output index. The hypothesis also establishes `D > m₁ + m₂` for the output. -/
def mul {d m₁ m₂ r₁ r₂ D : ℕ}
    (P : SegmentedPolynomial d m₁ r₁ D)
    (Q : SegmentedPolynomial d m₂ r₂ D) (hsum : m₁ + m₂ < D) :
    SegmentedPolynomial d (m₁ + m₂) (r₁ + r₂) D where
  hD := hsum
  coeff c := ∑ a : SegmentedIndex d m₁ r₁,
    ∑ b : SegmentedIndex d m₂ r₂,
      if addIndex a b = c then P.coeff a * Q.coeff b else 0

theorem coeff_mul {d m₁ m₂ r₁ r₂ D : ℕ}
    (P : SegmentedPolynomial d m₁ r₁ D)
    (Q : SegmentedPolynomial d m₂ r₂ D) (hsum : m₁ + m₂ < D)
    (c : SegmentedIndex d (m₁ + m₂) (r₁ + r₂)) :
    (P.mul Q hsum).coeff c =
      ∑ a : SegmentedIndex d m₁ r₁,
        ∑ b : SegmentedIndex d m₂ r₂,
          if addIndex a b = c then P.coeff a * Q.coeff b else 0 := rfl

theorem eval_mul {d m₁ m₂ r₁ r₂ D : ℕ}
    (P : SegmentedPolynomial d m₁ r₁ D)
    (Q : SegmentedPolynomial d m₂ r₂ D) (hsum : m₁ + m₂ < D)
    (ω : Point d) :
    (P.mul Q hsum) ω = P ω * Q ω := by
  classical
  change (∑ c : SegmentedIndex d (m₁ + m₂) (r₁ + r₂),
    (∑ a : SegmentedIndex d m₁ r₁,
      ∑ b : SegmentedIndex d m₂ r₂,
        if addIndex a b = c then P.coeff a * Q.coeff b else 0) *
      unitTorusAtom (segmentedPolynomialFrequency d (m₁ + m₂) (r₁ + r₂) D c) ω) =
    (∑ a : SegmentedIndex d m₁ r₁,
      P.coeff a * unitTorusAtom (segmentedPolynomialFrequency d m₁ r₁ D a) ω) *
    (∑ b : SegmentedIndex d m₂ r₂,
      Q.coeff b * unitTorusAtom (segmentedPolynomialFrequency d m₂ r₂ D b) ω)
  have hcollect :
      (∑ c : SegmentedIndex d (m₁ + m₂) (r₁ + r₂),
        (∑ a : SegmentedIndex d m₁ r₁,
          ∑ b : SegmentedIndex d m₂ r₂,
            if addIndex a b = c then P.coeff a * Q.coeff b else 0) *
          unitTorusAtom (segmentedPolynomialFrequency d (m₁ + m₂) (r₁ + r₂) D c) ω) =
        ∑ a : SegmentedIndex d m₁ r₁,
          ∑ b : SegmentedIndex d m₂ r₂,
            P.coeff a * Q.coeff b *
              unitTorusAtom
                (segmentedPolynomialFrequency d (m₁ + m₂) (r₁ + r₂) D
                  (addIndex a b)) ω := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ (addIndex a b)
      (fun c => P.coeff a * Q.coeff b *
        unitTorusAtom (segmentedPolynomialFrequency d (m₁ + m₂) (r₁ + r₂) D c) ω),
      if_pos (Finset.mem_univ (addIndex a b))]
  rw [hcollect]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [frequency_addIndex, atom_mul]
  ring

theorem angularValue_mul {d m₁ m₂ r₁ r₂ D : ℕ}
    (P : SegmentedPolynomial d m₁ r₁ D)
    (Q : SegmentedPolynomial d m₂ r₂ D) (hsum : m₁ + m₂ < D)
    (y : Point d) :
    (P.mul Q hsum).angularValue y =
      P.angularValue y * Q.angularValue y :=
  eval_mul P Q hsum _

/-- Convolution may combine several contributions at a frequency, so the
coefficient mass of a product is bounded by the product of the masses. -/
theorem mass_mul_le {d m₁ m₂ r₁ r₂ D : ℕ}
    (P : SegmentedPolynomial d m₁ r₁ D)
    (Q : SegmentedPolynomial d m₂ r₂ D) (hsum : m₁ + m₂ < D) :
    (P.mul Q hsum).mass ≤ P.mass * Q.mass := by
  classical
  unfold mass mul
  calc
    (∑ c : SegmentedIndex d (m₁ + m₂) (r₁ + r₂),
      ‖∑ a : SegmentedIndex d m₁ r₁,
        ∑ b : SegmentedIndex d m₂ r₂,
          if addIndex a b = c then P.coeff a * Q.coeff b else 0‖)
      ≤ ∑ c : SegmentedIndex d (m₁ + m₂) (r₁ + r₂),
          ∑ a : SegmentedIndex d m₁ r₁,
            ∑ b : SegmentedIndex d m₂ r₂,
              ‖if addIndex a b = c then P.coeff a * Q.coeff b else 0‖ := by
        apply Finset.sum_le_sum
        intro c _
        exact (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ = ∑ a : SegmentedIndex d m₁ r₁,
          ∑ b : SegmentedIndex d m₂ r₂, ‖P.coeff a * Q.coeff b‖ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        have hterm : ∀ c : SegmentedIndex d (m₁ + m₂) (r₁ + r₂),
            ‖if addIndex a b = c then P.coeff a * Q.coeff b else 0‖ =
              if addIndex a b = c then ‖P.coeff a * Q.coeff b‖ else 0 := by
          intro c
          split_ifs <;> simp
        simp_rw [hterm]
        rw [Finset.sum_ite_eq Finset.univ (addIndex a b)
          (fun _ => ‖P.coeff a * Q.coeff b‖),
          if_pos (Finset.mem_univ (addIndex a b))]
    _ = (∑ a, ‖P.coeff a‖) * (∑ b, ‖Q.coeff b‖) := by
        simp only [norm_mul]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]

end SegmentedPolynomial
end
end NumDetect
end LeanNumDetect

/-! Translation and finite products in the canonical Appendix B polynomial space. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect
namespace SegmentedPolynomial

noncomputable section

/-- Identify the canonical one-block indices with the ordinary fine cube. -/
def fineCubeIndexEquiv (d K : ℕ) :
    SegmentedIndex d K 0 ≃ UniformIndex d K where
  toFun a := fun k => (a k).2
  invFun a := fun k => (⟨0, by omega⟩, a k)
  left_inv a := by
    funext k
    have hfirst : (a k).1 = (⟨0, by omega⟩ : Fin 1) := Fin.ext (by omega)
    exact Prod.ext hfirst.symm rfl
  right_inv a := rfl

/-- A coefficient vector on `{0, ..., K}^d` as a canonical member of
`𝒫(K,0,D,d)`. -/
def ofFineCube {d K D : ℕ} (hKD : K < D)
    (c : UniformIndex d K → ℂ) : SegmentedPolynomial d K 0 D where
  hD := hKD
  coeff a := c (fineCubeIndexEquiv d K a)

theorem angularValue_ofFineCube {d K D : ℕ} (hKD : K < D)
    (c : UniformIndex d K → ℂ) (y : Point d) :
    (ofFineCube hKD c).angularValue y =
      ∑ a : UniformIndex d K,
        c a * Complex.exp
          (Complex.I * ((∑ k, (a k : ℝ) * y k : ℝ) : ℂ)) := by
  classical
  rw [angularValue_eq_angularTrigPolynomial]
  unfold angularTrigPolynomial
  apply Fintype.sum_equiv (fineCubeIndexEquiv d K) _ _
  intro a
  simp only [ofFineCube]
  congr 1
  apply congrArg Complex.exp
  congr 1
  apply congrArg (fun z : ℝ => (z : ℂ))
  apply Finset.sum_congr rfl
  intro k _
  have hzero : ((a k).1 : ℕ) = 0 := by omega
  simp [segmentedPolynomialFrequency, fineCubeIndexEquiv, hzero]

theorem mass_ofFineCube {d K D : ℕ} (hKD : K < D)
    (c : UniformIndex d K → ℂ) :
    (ofFineCube hKD c).mass = ∑ a, ‖c a‖ := by
  classical
  unfold mass
  apply Fintype.sum_equiv (fineCubeIndexEquiv d K) _ _
  intro a
  rfl

/-- Angular translation changes coefficient phases while preserving the
canonical support and its disjointness hypothesis. -/
def translate {d m r D : ℕ} (P : SegmentedPolynomial d m r D)
    (y : Point d) : SegmentedPolynomial d m r D where
  hD := P.hD
  coeff a := P.coeff a * Complex.exp
    (-Complex.I *
      ((∑ k, ((segmentedPolynomialFrequency d m r D a k : ℤ) : ℝ) * y k : ℝ) : ℂ))

theorem angularValue_translate {d m r D : ℕ}
    (P : SegmentedPolynomial d m r D) (y x : Point d) :
    (P.translate y).angularValue x = P.angularValue (x - y) := by
  classical
  rw [angularValue_eq_angularTrigPolynomial,
    angularValue_eq_angularTrigPolynomial]
  unfold angularTrigPolynomial
  apply Finset.sum_congr rfl
  intro a _
  simp only [translate]
  rw [mul_assoc, ← Complex.exp_add]
  congr 1
  have hsum :
      (∑ k, (segmentedPolynomialFrequency d m r D a k : ℝ) * (x - y) k) =
        (∑ k, (segmentedPolynomialFrequency d m r D a k : ℝ) * x k) -
          ∑ k, (segmentedPolynomialFrequency d m r D a k : ℝ) * y k := by
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hsum]
  push_cast
  ring

theorem mass_translate {d m r D : ℕ}
    (P : SegmentedPolynomial d m r D) (y : Point d) :
    (P.translate y).mass = P.mass := by
  classical
  apply Finset.sum_congr rfl
  intro a _
  simp [mass, translate, Complex.norm_exp]

/-- A product of `q` polynomials with common budgets belongs to
`𝒫(qm,qr,D,d)` provided its total fine budget remains below `D`.
The type writes these products as `m * q` and `r * q` for recursive reduction. -/
def prod {d m r D : ℕ} :
    (q : ℕ) → (Fin q → SegmentedPolynomial d m r D) →
      (m * q < D) → SegmentedPolynomial d (m * q) (r * q) D
  | 0, _, hq => by
      exact one d D (by simpa only [Nat.mul_zero] using hq)
  | q + 1, F, hq => by
      have hsum : m * q + m < D := by
        simpa only [Nat.mul_succ] using hq
      have htail : m * q < D := by omega
      let Q := prod q (fun i => F i.succ) htail
      exact Q.mul (F 0) hsum

theorem angularValue_prod {d m r D q : ℕ}
    (F : Fin q → SegmentedPolynomial d m r D)
    (hq : m * q < D) (y : Point d) :
    (prod q F hq).angularValue y = ∏ i, (F i).angularValue y := by
  induction q with
  | zero =>
      simpa [prod, angularValue] using
        (eval_one d D (by simpa using hq)
          (fun k => y k / (2 * Real.pi)))
  | succ q ih =>
      have hsum : m * q + m < D := by
        simpa only [Nat.mul_succ] using hq
      have htail : m * q < D := by omega
      simp only [prod, angularValue_mul, Fin.prod_univ_succ]
      rw [ih (fun i => F i.succ) htail]
      exact mul_comm _ _

theorem mass_prod_le {d m r D q : ℕ}
    (F : Fin q → SegmentedPolynomial d m r D)
    (hq : m * q < D) :
    (prod q F hq).mass ≤ ∏ i, (F i).mass := by
  induction q with
  | zero =>
      simpa [prod] using
        (le_of_eq (mass_one d D (by simpa using hq)))
  | succ q ih =>
      have hsum : m * q + m < D := by
        simpa only [Nat.mul_succ] using hq
      have htail : m * q < D := by omega
      simp only [prod, Fin.prod_univ_succ]
      calc
        ((prod q (fun i => F i.succ) htail).mul (F 0) hsum).mass
            ≤ (prod q (fun i => F i.succ) htail).mass * (F 0).mass :=
          mass_mul_le _ _ _
        _ ≤ (∏ i : Fin q, (F i.succ).mass) * (F 0).mass :=
          mul_le_mul_of_nonneg_right
            (ih (fun i => F i.succ) htail) (F 0).mass_nonneg
        _ = (F 0).mass * ∏ i : Fin q, (F i.succ).mass := mul_comm _ _

end
end SegmentedPolynomial
end NumDetect
end LeanNumDetect

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect
noncomputable section
namespace SegmentedPolynomial

/-- A cube of extra segmented frequencies used to average polynomial coefficients. -/
abbrev SmoothingIndex (d b z : ℕ) :=
  SegmentedIndex d b z

/-- Add one smoothing frequency to a canonical segmented row. -/
def shiftedSegmentedRow {d m r D : ℕ} (P : SegmentedPolynomial d m r D)
    (b z : ℕ) (i : SegmentedIndex d m r) (q : SmoothingIndex d b z) :
    SegmentedIndex d (m + b) (r + z) :=
  fun k =>
    (⟨(i k).1.val + (q k).1, by
        have hp := Nat.le_of_lt_succ (i k).1.isLt
        have hq := (q k).1.isLt
        omega⟩,
      ⟨(i k).2.val + (q k).2, by
        have hp := Nat.le_of_lt_succ (i k).2.isLt
        have hq := (q k).2.isLt
        omega⟩)

theorem shiftedSegmentedRow_injective
    {d m r D : ℕ} (P : SegmentedPolynomial d m r D)
    (b z : ℕ) (i : SegmentedIndex d m r) :
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
    {d m r D : ℕ} (P : SegmentedPolynomial d m r D)
    (b z : ℕ) (y : Point d) (i : SegmentedIndex d m r) :
    EuclideanSpace ℂ (SegmentedIndex d (m + b) (r + z)) :=
  SegmentedVDM.spread (shiftedSegmentedRow P b z i) fun q =>
    Complex.exp
        (-Complex.I *
          ((∑ k, (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) *
            y k) : ℝ) : ℂ)) /
      (((z + 1) * (b + 1)) ^ d : ℕ)

theorem segmentedAveragingVector_norm
    {d m r D : ℕ} (P : SegmentedPolynomial d m r D)
    (b z : ℕ) (y : Point d) (i : SegmentedIndex d m r) :
    ‖segmentedAveragingVector P b z y i‖ =
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
  change ‖segmentedAveragingVector P b z y i‖ ^ 2 = _ at hh
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

/-- Average every coefficient over the same translated frequency cube. -/
noncomputable def smoothedSegmentedVector
    {d m r D : ℕ} (P : SegmentedPolynomial d m r D)
    (b z : ℕ) (y : Point d) :
    EuclideanSpace ℂ (SegmentedIndex d (m + b) (r + z)) :=
  ∑ i, P.coeff i • segmentedAveragingVector P b z y i

theorem smoothedSegmentedVector_norm_le
    {d m r D : ℕ} (P : SegmentedPolynomial d m r D)
    (b z : ℕ) (y : Point d) :
    ‖smoothedSegmentedVector P b z y‖ ≤
      P.mass /
        Real.sqrt ((((z + 1) * (b + 1)) ^ d : ℕ) : ℝ) := by
  calc
    _ ≤ ∑ i, ‖P.coeff i • segmentedAveragingVector P b z y i‖ :=
      norm_sum_le _ _
    _ = _ := by
      simp only [norm_smul, segmentedAveragingVector_norm, mul_one_div,
        ← Finset.sum_div, SegmentedPolynomial.mass]

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
    {d m r D : ℕ} (P : SegmentedPolynomial d m r D)
    (b z : ℕ) (y x : Point d) (i : SegmentedIndex d m r) :
    ofLp (segmentedAveragingVector P b z y i) ⬝ᵥ
        segmentedSteering d (m + b) (r + z) D x =
      Complex.exp
          (Complex.I *
            ((∑ k, (((D * (i k).1.val + (i k).2.val : ℕ) : ℝ) *
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
            (((D * ((i k).1.val + (q k).1.val) +
              ((i k).2.val + (q k).2.val) : ℕ) : ℝ) * x k) : ℝ) : ℂ)) =
      Complex.exp
          (Complex.I *
            ((∑ k, (((D * (i k).1.val + (i k).2.val : ℕ) : ℝ) *
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
            (((D * ((i k).1.val + (q k).1.val) +
              ((i k).2.val + (q k).2.val) : ℕ) : ℝ) * x k) : ℝ) : ℂ) =
      Complex.I *
          ((∑ k, (((D * (i k).1.val + (i k).2.val : ℕ) : ℝ) *
            x k) : ℝ) : ℂ) +
        Complex.I *
          ((∑ k, (((D * (q k).1.val + (q k).2.val : ℕ) : ℝ) *
            (x - y) k) : ℝ) : ℂ) := by
    have hadd :
        (∑ k,
            (((D * ((i k).1.val + (q k).1.val) +
              ((i k).2.val + (q k).2.val) : ℕ) : ℝ) * x k)) =
          (∑ k, (((D * (i k).1.val + (i k).2.val : ℕ) : ℝ) * x k)) +
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
    {d m r D : ℕ} (P : SegmentedPolynomial d m r D)
    (b z : ℕ) (y x : Point d) :
    ofLp (smoothedSegmentedVector P b z y) ⬝ᵥ
        segmentedSteering d (m + b) (r + z) D x =
      P.angularValue x * segmentedMeanKernel d b z D (x - y) := by
  simp only [smoothedSegmentedVector, WithLp.ofLp_sum, sum_dotProduct,
    WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul,
    segmentedAveragingVector_evaluation]
  rw [angularValue_eq_angularTrigPolynomial]
  unfold angularTrigPolynomial
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [segmentedPolynomialFrequency]
  push_cast
  ring

/-- Frequency-cube smoothing and Lagrange duality for segmented polynomials. -/
theorem singularValue_ge_of_smoothedSegmentedPolynomials
    {d n m r b z D : ℕ} (hn : 0 < n) (x : Fin n → Point d)
    (P : Fin n → SegmentedPolynomial d m r D)
    (hinterp : IsLagrangeFamily x P) (hsum : m + b < D)
    {H : ℝ} (hH : 0 < H) (hP : ∀ k, (P k).mass ≤ H) :
    Real.sqrt ((((z + 1) * (b + 1)) ^ d : ℕ) : ℝ) /
        (Real.sqrt n * H) ≤
      matrixSingularValue
        (segmentedVandermonde (m + b) (r + z) D x) (n - 1) := by
  classical
  let C : Matrix (Fin n) (SegmentedIndex d (m + b) (r + z)) ℂ :=
    fun k => ofLp (smoothedSegmentedVector (P k) b z (x k))
  have hCV : C * segmentedVandermonde (m + b) (r + z) D x = 1 := by
    ext k j
    change
      ofLp (smoothedSegmentedVector (P k) b z (x k)) ⬝ᵥ
          (fun α => segmentedVandermonde (m + b) (r + z) D x α j) =
        (1 : Matrix (Fin n) (Fin n) ℂ) k j
    rw [← segmentedSteering_eq_vandermonde,
      smoothedSegmentedVector_evaluation, hinterp k j]
    by_cases hkj : k = j
    · subst j
      simp
    · simp [hkj]
  have hC (k : Fin n) :
      SegmentedVDM.energy (C k) ≤
        (H /
          Real.sqrt ((((z + 1) * (b + 1)) ^ d : ℕ) : ℝ)) ^ 2 := by
    change (∑ i, ‖(smoothedSegmentedVector (P k) b z (x k)) i‖ ^ 2) ≤ _
    rw [← EuclideanSpace.norm_sq_eq]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).2
    exact (smoothedSegmentedVector_norm_le (P k) b z (x k)).trans
      (div_le_div_of_nonneg_right (hP k) (Real.sqrt_nonneg _))
  have hh := SegmentedVDM.singularValue_ge_of_interpolation
    (segmentedVandermonde (m + b) (r + z) D x)
    C hCV hn (by positivity :
      0 < H / Real.sqrt ((((z + 1) * (b + 1)) ^ d : ℕ) : ℝ)) hC
  convert! hh using 1
  field_simp

end SegmentedPolynomial
end
end NumDetect
end LeanNumDetect
