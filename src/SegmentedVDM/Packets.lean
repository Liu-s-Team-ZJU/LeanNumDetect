import SegmentedVDM.Interpolation

/-! Finite presentations of segmented trigonometric polynomials. Repeated
frequencies are allowed in a presentation and are collected only when a matrix
coefficient vector is formed. This makes multiplication purely finite algebra. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace SegmentedVDM

structure Packet (m r : ℕ) where
  Index : Type
  finite : Fintype Index
  coarse : Index → ℕ
  fine : Index → ℕ
  coarse_le : ∀ i, coarse i ≤ r
  fine_le : ∀ i, fine i ≤ m
  coeff : Index → ℂ

attribute [instance] Packet.finite

namespace Packet

noncomputable def value {m r : ℕ} (P : Packet m r) (D x : ℝ) : ℂ :=
  ∑ i, P.coeff i * Complex.exp (Complex.I * (((P.coarse i : ℝ) * D + P.fine i) * x : ℝ))

noncomputable def mass {m r : ℕ} (P : Packet m r) : ℝ := ∑ i, ‖P.coeff i‖

theorem mass_nonneg {m r : ℕ} (P : Packet m r) : 0 ≤ P.mass :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

noncomputable def mul {m₁ m₂ r₁ r₂ : ℕ} (P : Packet m₁ r₁) (Q : Packet m₂ r₂) :
    Packet (m₁ + m₂) (r₁ + r₂) where
  Index := P.Index × Q.Index
  finite := inferInstance
  coarse i := P.coarse i.1 + Q.coarse i.2
  fine i := P.fine i.1 + Q.fine i.2
  coarse_le i := Nat.add_le_add (P.coarse_le _) (Q.coarse_le _)
  fine_le i := Nat.add_le_add (P.fine_le _) (Q.fine_le _)
  coeff i := P.coeff i.1 * Q.coeff i.2

theorem value_mul {m₁ m₂ r₁ r₂ : ℕ} (P : Packet m₁ r₁) (Q : Packet m₂ r₂)
    (D x : ℝ) : (P.mul Q).value D x = P.value D x * Q.value D x := by
  unfold value mul
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : Complex.I * ((((P.coarse i + Q.coarse j : ℕ) : ℝ) * D +
      (P.fine i + Q.fine j : ℕ)) * x : ℝ) =
      Complex.I * (((P.coarse i : ℝ) * D + P.fine i) * x : ℝ) +
      Complex.I * (((Q.coarse j : ℝ) * D + Q.fine j) * x : ℝ) := by push_cast; ring
  rw [he, Complex.exp_add]
  ring

theorem mass_mul {m₁ m₂ r₁ r₂ : ℕ} (P : Packet m₁ r₁) (Q : Packet m₂ r₂) :
    (P.mul Q).mass = P.mass * Q.mass := by
  change (∑ i : P.Index × Q.Index, ‖P.coeff i.1 * Q.coeff i.2‖) = _
  simp only [mass, norm_mul, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

noncomputable def one : Packet 0 0 where
  Index := Unit
  finite := inferInstance
  coarse _ := 0
  fine _ := 0
  coarse_le _ := le_rfl
  fine_le _ := le_rfl
  coeff _ := 1

@[simp] theorem value_one (D x : ℝ) : one.value D x = 1 := by simp [value, one]
@[simp] theorem mass_one : one.mass = 1 := by simp [mass, one]

def widen {m r m' r' : ℕ} (P : Packet m r) (hm : m ≤ m') (hr : r ≤ r') :
    Packet m' r' where
  Index := P.Index
  finite := P.finite
  coarse := P.coarse
  fine := P.fine
  coarse_le i := (P.coarse_le i).trans hr
  fine_le i := (P.fine_le i).trans hm
  coeff := P.coeff

@[simp] theorem value_widen {m r m' r' : ℕ} (P : Packet m r)
    (hm : m ≤ m') (hr : r ≤ r') (D x : ℝ) :
    (P.widen hm hr).value D x = P.value D x := rfl

@[simp] theorem mass_widen {m r m' r' : ℕ} (P : Packet m r)
    (hm : m ≤ m') (hr : r ≤ r') : (P.widen hm hr).mass = P.mass := rfl

/-- A product of uniformly supported factors, retaining its exact bandwidth. -/
noncomputable def prod {m r q : ℕ} (P : Fin q → Packet m r) : Packet (q*m) (q*r) where
  Index := (i : Fin q) → (P i).Index
  finite := inferInstance
  coarse a := ∑ i, (P i).coarse (a i)
  fine a := ∑ i, (P i).fine (a i)
  coarse_le a := by
    simpa using (Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => (P i).coarse_le (a i)))
  fine_le a := by
    simpa using (Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => (P i).fine_le (a i)))
  coeff a := ∏ i, (P i).coeff (a i)

theorem mass_prod {m r q : ℕ} (P : Fin q → Packet m r) :
    (prod P).mass = ∏ i, (P i).mass := by
  simp only [mass, prod, norm_prod]
  exact (Fintype.prod_sum (fun i a => ‖(P i).coeff a‖)).symm

theorem value_prod {m r q : ℕ} (P : Fin q → Packet m r) (D x : ℝ) :
    (prod P).value D x = ∏ i, (P i).value D x := by
  classical
  simp only [value, prod]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  have he : Complex.I *
      ((((∑ i, (P i).coarse (a i) : ℕ) : ℝ) * D +
        ((∑ i, (P i).fine (a i) : ℕ) : ℝ)) * x : ℝ) =
      ∑ i, Complex.I * ((((P i).coarse (a i) : ℝ) * D + (P i).fine (a i)) * x : ℝ) := by
    push_cast
    simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_add, add_mul]

  rw [he, Complex.exp_sum, ← Finset.prod_mul_distrib]

@[simp] theorem value_zero {m r : ℕ} (P : Packet m r) (D : ℝ) :
    P.value D 0 = ∑ i, P.coeff i := by simp [value]

/-- Translation changes only unimodular coefficient phases. -/
noncomputable def translate {m r : ℕ} (P : Packet m r) (D y : ℝ) : Packet m r :=
  { P with coeff := fun i => P.coeff i *
      Complex.exp (-Complex.I * (((P.coarse i : ℝ) * D + P.fine i) * y : ℝ)) }

theorem value_translate {m r : ℕ} (P : Packet m r) (D y x : ℝ) :
    (P.translate D y).value D x = P.value D (x-y) := by
  apply Finset.sum_congr rfl
  intro i _
  dsimp [translate]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem mass_translate {m r : ℕ} (P : Packet m r) (D y : ℝ) :
    (P.translate D y).mass = P.mass := by
  apply Finset.sum_congr rfl
  intro i _
  simp [translate, norm_mul, Complex.norm_exp]

end Packet
end SegmentedVDM
