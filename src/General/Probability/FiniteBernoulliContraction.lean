import General.Probability.FiniteBernoulliProcess
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Contraction for finite Bernoulli averages

The one-coordinate comparison is proved directly from the defining least
upper bounds. Coordinatewise iteration then gives the usual contraction
inequality for a finite real process class. No concentration estimate or
covering-number hypothesis is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

/-- The two possible signs at one coordinate may be contracted using only
the pairwise Lipschitz estimate on the values attained by the process. The
index class itself need not be finite. -/
theorem bernoulli_coordinate_contraction
    {T : Type*} [Nonempty T] (A x y : T → ℝ) {L : ℝ}
    (hLip : ∀ t u, |y t - y u| ≤ L * |x t - x u|)
    (hplus : BddAbove (Set.range fun t => A t + L * x t))
    (hminus : BddAbove (Set.range fun t => A t - L * x t)) :
    sSup (Set.range fun t => A t + y t) +
        sSup (Set.range fun t => A t - y t) ≤
      sSup (Set.range fun t => A t + L * x t) +
        sSup (Set.range fun t => A t - L * x t) := by
  let H := sSup (Set.range fun t => A t + L * x t) +
    sSup (Set.range fun t => A t - L * x t)
  have hpair (t u : T) : (A t + y t) + (A u - y u) ≤ H := by
    have htplus := le_csSup hplus (Set.mem_range_self t)
    have htminus := le_csSup hminus (Set.mem_range_self t)
    have huplus := le_csSup hplus (Set.mem_range_self u)
    have huminus := le_csSup hminus (Set.mem_range_self u)
    have hdiff := (le_abs_self (y t - y u)).trans (hLip t u)
    rcases le_total (x u) (x t) with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hdiff
      dsimp [H]
      linarith
    · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hdiff
      dsimp [H]
      linarith
  have hminus' (t : T) : sSup (Set.range fun u => A u - y u) ≤ H - (A t + y t) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨u, rfl⟩
    linarith [hpair t u]
  have hplus' : sSup (Set.range fun t => A t + y t) ≤
      H - sSup (Set.range fun u => A u - y u) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨t, rfl⟩
    linarith [hminus' t]
  change _ ≤ H
  linarith

/-- The uniform Bernoulli average consists of the two opposite signs. -/
theorem finiteAverage_bool_true_first (f : Bool → ℝ) :
    finiteAverage f = (f true + f false) / 2 := by
  simp [finiteAverage, add_comm, div_eq_mul_inv, mul_comm]

/-- A real-valued tuple average may be split into its first Bernoulli
coordinate and the remaining coordinates. -/
theorem finiteAverage_finSucc {m : ℕ} (f : (Fin (m + 1) → Bool) → ℝ) :
    finiteAverage f = finiteAverage (fun b : Bool =>
      finiteAverage (fun σ : Fin m → Bool => f (Fin.cons b σ))) := by
  have h := finiteAverage_comp_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Bool)) f
  change (finiteAverage (fun p : Bool × (Fin m → Bool) =>
    f (Fin.cons p.1 p.2))) = finiteAverage f at h
  rw [finiteAverage_prod (fun (b : Bool) (σ : Fin m → Bool) => f (Fin.cons b σ))] at h
  exact h.symm

/-- Coordinatewise bounds give upper bounds for every finite linear
combination, uniformly over an arbitrary index class. -/
theorem bddAbove_range_add_linear_combination
    {T : Type*} {m : ℕ} (A : T → ℝ) (x : T → Fin m → ℝ) (c : Fin m → ℝ)
    (hA : BddAbove (Set.range A))
    (hx : ∀ i, BddAbove (Set.range fun t => |x t i|)) :
    BddAbove (Set.range fun t => A t + ∑ i, c i * x t i) := by
  classical
  obtain ⟨B, hB⟩ := hA
  choose C hC using hx
  refine ⟨B + ∑ i, |c i| * C i, ?_⟩
  rintro _ ⟨t, rfl⟩
  apply add_le_add (hB (Set.mem_range_self t))
  apply Finset.sum_le_sum
  intro i _
  calc
    c i * x t i ≤ |c i * x t i| := le_abs_self _
    _ = |c i| * |x t i| := abs_mul _ _
    _ ≤ |c i| * C i := mul_le_mul_of_nonneg_left
      (hC i (Set.mem_range_self t)) (abs_nonneg _)

/-- Coordinatewise Lipschitz contraction for an arbitrary bounded index
class. Boundedness is stated as deterministic coordinatewise bounds, and
does not impose finiteness, compactness, or measurability on the class. -/
theorem bernoulli_bounded_supremum_contraction
    {T : Type*} [Nonempty T] {m : ℕ}
    (A : T → ℝ) (x y : T → Fin m → ℝ) {L : ℝ}
    (hLip : ∀ i t u, |y t i - y u i| ≤ L * |x t i - x u i|)
    (hA : BddAbove (Set.range A))
    (hx : ∀ i, BddAbove (Set.range fun t => |x t i|))
    (hy : ∀ i, BddAbove (Set.range fun t => |y t i|)) :
    finiteAverage (fun σ : Fin m → Bool => sSup (Set.range fun t =>
      A t + ∑ i, finiteBernoulliSign (σ i) * y t i)) ≤
    finiteAverage (fun σ : Fin m → Bool => sSup (Set.range fun t =>
      A t + ∑ i, finiteBernoulliSign (σ i) * (L * x t i))) := by
  induction m generalizing A with
  | zero => simp
  | succ m ih =>
    rw [finiteAverage_finSucc, finiteAverage_finSucc]
    have hfirst : finiteAverage (fun b : Bool => finiteAverage (fun σ : Fin m → Bool =>
        sSup (Set.range fun t => A t +
          ∑ i, finiteBernoulliSign (Fin.cons (α := fun _ => Bool) b σ i) * y t i))) ≤
        finiteAverage (fun b : Bool => finiteAverage (fun σ : Fin m → Bool =>
          sSup (Set.range fun t => A t + finiteBernoulliSign b * (L * x t 0) +
            ∑ i, finiteBernoulliSign (σ i) * y t i.succ))) := by
      rw [finiteAverage_comm (fun (b : Bool) (σ : Fin m → Bool) =>
        sSup (Set.range fun t => A t +
          ∑ i, finiteBernoulliSign (Fin.cons (α := fun _ => Bool) b σ i) * y t i))]
      rw [finiteAverage_comm (fun (b : Bool) (σ : Fin m → Bool) =>
        sSup (Set.range fun t => A t + finiteBernoulliSign b * (L * x t 0) +
          ∑ i, finiteBernoulliSign (σ i) * y t i.succ))]
      apply finiteAverage_mono
      intro σ
      let A' := fun t => A t + ∑ i, finiteBernoulliSign (σ i) * y t i.succ
      have hA' : BddAbove (Set.range A') := bddAbove_range_add_linear_combination A
        (fun t i => y t i.succ) (fun i => finiteBernoulliSign (σ i)) hA (fun i => hy i.succ)
      have hp : BddAbove (Set.range fun t => A' t + L * x t 0) := by
        simpa using bddAbove_range_add_linear_combination A'
          (fun t (_ : Fin 1) => x t 0) (fun _ => L) hA' (fun _ => hx 0)
      have hm : BddAbove (Set.range fun t => A' t - L * x t 0) := by
        simpa [sub_eq_add_neg] using bddAbove_range_add_linear_combination A'
          (fun t (_ : Fin 1) => x t 0) (fun _ => -L) hA' (fun _ => hx 0)
      have h := bernoulli_coordinate_contraction A' (fun t => x t 0)
        (fun t => y t 0) (hLip 0) hp hm
      simp_rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [finiteAverage_bool_true_first, finiteAverage_bool_true_first]
      simpa [A', finiteBernoulliSign, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)
    apply hfirst.trans
    apply finiteAverage_mono
    intro b
    have hA' : BddAbove (Set.range fun t => A t + finiteBernoulliSign b * (L * x t 0)) := by
      simpa [mul_assoc] using bddAbove_range_add_linear_combination A
        (fun t (_ : Fin 1) => x t 0) (fun _ => finiteBernoulliSign b * L) hA (fun _ => hx 0)
    have h := ih (fun t => A t + finiteBernoulliSign b * (L * x t 0))
      (fun t i => x t i.succ) (fun t i => y t i.succ)
      (fun i t u => hLip i.succ t u) hA' (fun i => hx i.succ) (fun i => hy i.succ)
    simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_assoc] using h

/-- Contraction for a finite real process class, with an arbitrary
deterministic offset. The pairwise Lipschitz hypothesis is sufficient;
the contractions need not be defined outside the attained coordinate values. -/
theorem finiteBernoulli_supremum_contraction
    {T : Type*} [Fintype T] [Nonempty T] {m : ℕ}
    (A : T → ℝ) (x y : T → Fin m → ℝ) {L : ℝ}
    (hLip : ∀ i t u, |y t i - y u i| ≤ L * |x t i - x u i|) :
    finiteAverage (fun σ : Fin m → Bool => sSup (Set.range fun t =>
      A t + ∑ i, finiteBernoulliSign (σ i) * y t i)) ≤
    finiteAverage (fun σ : Fin m → Bool => sSup (Set.range fun t =>
      A t + ∑ i, finiteBernoulliSign (σ i) * (L * x t i))) := by
  exact bernoulli_bounded_supremum_contraction A x y hLip
    (Set.finite_range _).bddAbove (fun _ => (Set.finite_range _).bddAbove)
    (fun _ => (Set.finite_range _).bddAbove)

/-- Coordinatewise bounded classes also have bounded absolute linear
suprema. -/
theorem bddAbove_range_abs_linear_combination
    {T : Type*} {m : ℕ} (x : T → Fin m → ℝ) (c : Fin m → ℝ)
    (hx : ∀ i, BddAbove (Set.range fun t => |x t i|)) :
    BddAbove (Set.range fun t => |∑ i, c i * x t i|) := by
  classical
  choose C hC using hx
  refine ⟨∑ i, |c i| * C i, ?_⟩
  rintro _ ⟨t, rfl⟩
  calc
    _ ≤ ∑ i, |c i * x t i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hC i (Set.mem_range_self t)) (abs_nonneg _)

/-- Reversing every Bernoulli sign is a permutation of the cube. -/
def finiteBernoulliNegate {m : ℕ} : (Fin m → Bool) ≃ (Fin m → Bool) where
  toFun σ i := !(σ i)
  invFun σ i := !(σ i)
  left_inv σ := by funext i; simp
  right_inv σ := by funext i; simp

@[simp] theorem finiteBernoulliSign_not (b : Bool) :
    finiteBernoulliSign (!b) = -finiteBernoulliSign b := by
  cases b <;> norm_num [finiteBernoulliSign]

/-- A class containing the zero process has absolute contraction with
the usual factor two. The index class can be infinite. -/
theorem bernoulli_bounded_absoluteSupremum_contraction
    {T : Type*} [Nonempty T] {m : ℕ}
    (x y : T → Fin m → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ i t u, |y t i - y u i| ≤ L * |x t i - x u i|)
    (hx : ∀ i, BddAbove (Set.range fun t => |x t i|))
    (hy : ∀ i, BddAbove (Set.range fun t => |y t i|))
    (t₀ : T) (hyzero : ∀ i, y t₀ i = 0) :
    finiteAverage (fun σ : Fin m → Bool => sSup (Set.range fun t =>
      |∑ i, finiteBernoulliSign (σ i) * y t i|)) ≤
    2 * L * finiteAverage (fun σ : Fin m → Bool => sSup (Set.range fun t =>
      |∑ i, finiteBernoulliSign (σ i) * x t i|)) := by
  let H := fun σ : Fin m → Bool => sSup (Set.range fun t =>
    ∑ i, finiteBernoulliSign (σ i) * y t i)
  have hHbounded (σ : Fin m → Bool) : BddAbove (Set.range fun t =>
      ∑ i, finiteBernoulliSign (σ i) * y t i) := by
    simpa using bddAbove_range_add_linear_combination (fun _ : T => (0 : ℝ)) y
      (fun i => finiteBernoulliSign (σ i)) (by simp) hy
  have hHnonneg (σ : Fin m → Bool) : 0 ≤ H σ := by
    have h := le_csSup (hHbounded σ) (Set.mem_range_self t₀)
    simpa [H, hyzero] using h
  have hpoint (σ : Fin m → Bool) : sSup (Set.range fun t =>
      |∑ i, finiteBernoulliSign (σ i) * y t i|) ≤
      H σ + H (finiteBernoulliNegate σ) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨t, rfl⟩
    have hp := le_csSup (hHbounded σ) (Set.mem_range_self t)
    have hm := le_csSup (hHbounded (finiteBernoulliNegate σ)) (Set.mem_range_self t)
    change _ ≤ H σ at hp
    change (∑ i, finiteBernoulliSign (!(σ i)) * y t i) ≤ H (finiteBernoulliNegate σ) at hm
    simp only [finiteBernoulliSign_not, neg_mul, Finset.sum_neg_distrib] at hm
    apply abs_le.mpr
    constructor <;> linarith [hHnonneg σ, hHnonneg (finiteBernoulliNegate σ)]
  have hcontract : finiteAverage H ≤ finiteAverage (fun σ : Fin m → Bool =>
      sSup (Set.range fun t => ∑ i, finiteBernoulliSign (σ i) * (L * x t i))) := by
    simpa [H] using bernoulli_bounded_supremum_contraction
      (fun _ : T => (0 : ℝ)) x y hLip (by simp) hx hy
  have hscale (σ : Fin m → Bool) : sSup (Set.range fun t =>
      ∑ i, finiteBernoulliSign (σ i) * (L * x t i)) ≤
      L * sSup (Set.range fun t => |∑ i, finiteBernoulliSign (σ i) * x t i|) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨t, rfl⟩
    have h := le_csSup (bddAbove_range_abs_linear_combination x
      (fun i => finiteBernoulliSign (σ i)) hx) (Set.mem_range_self t)
    calc
      _ = L * ∑ i, finiteBernoulliSign (σ i) * x t i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ L * |∑ i, finiteBernoulliSign (σ i) * x t i| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hL
      _ ≤ _ := mul_le_mul_of_nonneg_left h hL
  calc
    _ ≤ finiteAverage (fun σ : Fin m → Bool => H σ + H (finiteBernoulliNegate σ)) :=
      finiteAverage_mono hpoint
    _ = 2 * finiteAverage H := by
      rw [finiteAverage_add, finiteAverage_comp_equiv]
      ring
    _ ≤ 2 * finiteAverage (fun σ : Fin m → Bool =>
        sSup (Set.range fun t => ∑ i, finiteBernoulliSign (σ i) * (L * x t i))) := by
      exact mul_le_mul_of_nonneg_left hcontract (by norm_num)
    _ ≤ 2 * finiteAverage (fun σ : Fin m → Bool =>
        L * sSup (Set.range fun t => |∑ i, finiteBernoulliSign (σ i) * x t i|)) := by
      exact mul_le_mul_of_nonneg_left (finiteAverage_mono hscale) (by norm_num)
    _ = _ := by
      rw [show (fun σ : Fin m → Bool => L * sSup (Set.range fun t =>
        |∑ i, finiteBernoulliSign (σ i) * x t i|)) = (fun σ : Fin m → Bool =>
          L • sSup (Set.range fun t => |∑ i, finiteBernoulliSign (σ i) * x t i|)) from rfl,
        finiteAverage_smul]
      simp only [smul_eq_mul]
      ring

end LeanNumDetect.FiniteMatrixSampling
