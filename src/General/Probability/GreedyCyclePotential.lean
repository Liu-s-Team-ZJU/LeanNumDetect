import General.Probability.MatrixLaplace

/-!
The scalar potential for greedy cycles of a thick finite frame. The decrease
is the same at an ordinary acceptance and at the acceptance completing a
cycle. Consequently a codimension proportion of acceptable draws gives a
dimension-only exponential decay under independent uniform sampling.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

noncomputable section
attribute [local instance] Classical.propDecidable

def greedyCycleRatio (n : ℕ) : ℝ := 1 / (4 * (n : ℝ) + 1)

def greedyCyclePotential (n J r : ℕ) : ℝ :=
  greedyCycleRatio n ^ J * ((n : ℝ) - r + 1 / 4) / ((n : ℝ) + 1 / 4)

def greedyCycleDrop (n J : ℕ) : ℝ :=
  greedyCycleRatio n ^ J / ((n : ℝ) + 1 / 4)

def greedyCycleDecay (n : ℕ) : ℝ := 1 - 2 / (5 * (n : ℝ))

theorem greedyCycleRatio_pos (n : ℕ) : 0 < greedyCycleRatio n := by
  unfold greedyCycleRatio
  positivity

theorem greedyCycleDecay_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ greedyCycleDecay n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold greedyCycleDecay
  have hden : (0 : ℝ) < 5 * n := by positivity
  have : 2 / (5 * (n : ℝ)) ≤ 1 := (div_le_one hden).mpr (by linarith)
  linarith

theorem greedyCyclePotential_initial (n : ℕ) : greedyCyclePotential n 0 0 = 1 := by
  unfold greedyCyclePotential
  simp only [pow_zero, Nat.cast_zero, sub_zero, one_mul]
  exact div_self (by positivity)

theorem greedyCyclePotential_nonneg {n J r : ℕ} (hr : r < n) :
    0 ≤ greedyCyclePotential n J r := by
  have hr' : (r : ℝ) ≤ n := by exact_mod_cast hr.le
  unfold greedyCyclePotential
  exact div_nonneg
    (mul_nonneg (pow_nonneg (greedyCycleRatio_pos n).le _)
      (by linarith)) (by positivity)

theorem greedyCycleDrop_nonneg (n J : ℕ) : 0 ≤ greedyCycleDrop n J := by
  unfold greedyCycleDrop
  exact div_nonneg (pow_nonneg (greedyCycleRatio_pos n).le _) (by positivity)

/-- A nonterminal acceptance subtracts one unit of potential. -/
theorem greedyCyclePotential_accept (n J r : ℕ) :
    greedyCyclePotential n J (r + 1) =
      greedyCyclePotential n J r - greedyCycleDrop n J := by
  unfold greedyCyclePotential greedyCycleDrop
  push_cast
  ring

/-- Completing a cycle causes exactly the same decrease as any acceptance. -/
theorem greedyCyclePotential_reset {n J r : ℕ} (hr : r + 1 = n) :
    greedyCyclePotential n (J + 1) 0 =
      greedyCyclePotential n J r - greedyCycleDrop n J := by
  have hden : (n : ℝ) + 1 / 4 ≠ 0 := by positivity
  have hratio : 4 * (n : ℝ) + 1 ≠ 0 := by positivity
  have hr' : (r : ℝ) + 1 = n := by exact_mod_cast hr
  unfold greedyCyclePotential greedyCycleDrop greedyCycleRatio
  rw [pow_succ]
  simp only [Nat.cast_zero, sub_zero]
  field_simp
  nlinarith

/-- The contraction calculation uses only that at least one direction is
missing from the current incomplete cycle. -/
theorem greedyCyclePotential_contraction {n J r : ℕ} (hn : 0 < n) (hr : r < n)
    {p : ℝ} (hp : ((n : ℝ) - r) / (2 * n) ≤ p) :
    greedyCyclePotential n J r - p * greedyCycleDrop n J ≤
      greedyCycleDecay n * greedyCyclePotential n J r := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr' : (r : ℝ) + 1 ≤ n := by exact_mod_cast hr
  have hq : 0 ≤ greedyCycleRatio n ^ J := pow_nonneg (greedyCycleRatio_pos n).le _
  have hd : (0 : ℝ) < (n : ℝ) + 1 / 4 := by positivity
  calc
    _ ≤ greedyCyclePotential n J r -
        (((n : ℝ) - r) / (2 * n)) * greedyCycleDrop n J := by
      exact sub_le_sub_left (mul_le_mul_of_nonneg_right hp (greedyCycleDrop_nonneg n J)) _
    _ ≤ _ := by
      unfold greedyCyclePotential greedyCycleDrop greedyCycleDecay
      apply (mul_le_mul_iff_of_pos_right hd).mp
      field_simp
      nlinarith

/-- The uniform expectation of a two-valued function records exactly the
finite counting probability of its first branch. -/
theorem finiteAverage_ite_eq_probability {κ : Type*} [Fintype κ] [Nonempty κ]
    (P : κ → Prop) (a b : ℝ) :
    finiteAverage (fun k => if P k then a else b) =
      probability P * a + (1 - probability P) * b := by
  classical
  have hc : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard : ((Finset.univ.filter P).card : ℝ) +
      ((Finset.univ.filter (fun k => ¬ P k)).card : ℝ) = Fintype.card κ := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := Finset.univ) P
  simp only [finiteAverage, probability, Finset.sum_ite, Finset.sum_const,
    nsmul_eq_mul, smul_eq_mul]
  field_simp
  have hh := congrArg (fun x : ℝ => x * b) hcard
  nlinarith [hh]

/-- A codimension counting bound is the acceptance probability used by the
scalar iteration. All subtraction and uniform-law normalization are explicit. -/
theorem greedy_acceptance_probability_of_card {N n r : ℕ}
    (hN : 0 < N) (hn : 0 < n) (hr : r < n) (P : Fin N → Prop)
    (hcard : N * (n - r) ≤ 2 * n * (Finset.univ.filter P).card) :
    ((n : ℝ) - r) / (2 * n) ≤ probability P := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : (N : ℝ) * ((n - r : ℕ) : ℝ) ≤
      2 * (n : ℝ) * ((Finset.univ.filter P).card : ℝ) := by exact_mod_cast hcard
  rw [Nat.cast_sub hr.le] at hh
  unfold probability
  rw [Fintype.card_fin]
  apply (div_le_div_iff₀ (by positivity) hN').mpr
  nlinarith

/-- One accepted draw decreases the potential by the prescribed amount;
rejecting a draw leaves it unchanged. -/
theorem finiteAverage_greedyCycle_step {κ S : Type*} [Fintype κ] [Nonempty κ]
    {n : ℕ} (hn : 0 < n) (J r : S → ℕ) (hr : ∀ s, r s < n)
    (accept : S → κ → Prop) (next : S → κ → S)
    (haccept : ∀ s, ((n : ℝ) - r s) / (2 * n) ≤ probability (accept s))
    (hnext : ∀ s k, greedyCyclePotential n (J (next s k)) (r (next s k)) =
      if accept s k then
        greedyCyclePotential n (J s) (r s) - greedyCycleDrop n (J s)
      else greedyCyclePotential n (J s) (r s)) (s : S) :
    finiteAverage (fun k => greedyCyclePotential n (J (next s k)) (r (next s k))) ≤
      greedyCycleDecay n * greedyCyclePotential n (J s) (r s) := by
  simp_rw [hnext]
  rw [finiteAverage_ite_eq_probability]
  have h := greedyCyclePotential_contraction hn (hr s) (J := J s) (haccept s)
  convert h using 1
  ring

/-- A finite deterministic transition applied successively to iid draws. -/
def greedyRun {κ S : Type*} (next : S → κ → S) :
    (m : ℕ) → (Fin m → κ) → S → S
  | 0, _, s => s
  | m + 1, ω, s => greedyRun next m (fun i => ω i.succ) (next s (ω 0))

@[simp] theorem greedyRun_cons {κ S : Type*} (next : S → κ → S)
    {m : ℕ} (k : κ) (ω : Fin m → κ) (s : S) :
    greedyRun next (m + 1) (Fin.cons k ω) s = greedyRun next m ω (next s k) := rfl

/-- A uniform one-step scalar estimate iterates for arbitrary finite-state
transitions. No matrix moment bound is assumed by this statement. -/
theorem finiteAverage_greedyRun_le {κ S : Type*} [Fintype κ] [Nonempty κ]
    (next : S → κ → S) (g : S → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hstep : ∀ s, finiteAverage (fun k => g (next s k)) ≤ c * g s)
    (m : ℕ) (s : S) :
    finiteAverage (fun ω : Fin m → κ => g (greedyRun next m ω s)) ≤ c ^ m * g s := by
  induction m generalizing s with
  | zero => simp [greedyRun]
  | succ m ih =>
    rw [finiteAverage_fin_succ]
    simp only [greedyRun_cons]
    calc
      _ ≤ finiteAverage (fun k => c ^ m * g (next s k)) :=
        finiteAverage_mono (fun k => ih (next s k))
      _ = c ^ m * finiteAverage (fun k => g (next s k)) := by
        exact finiteAverage_smul (c ^ m) _
      _ ≤ c ^ m * (c * g s) :=
        mul_le_mul_of_nonneg_left (hstep s) (pow_nonneg hc _)
      _ = c ^ (m + 1) * g s := by rw [pow_succ]; ring

theorem finiteAverage_greedyCyclePotential_le {κ S : Type*}
    [Fintype κ] [Nonempty κ] {n : ℕ} (hn : 0 < n)
    (J r : S → ℕ) (hr : ∀ s, r s < n)
    (accept : S → κ → Prop) (next : S → κ → S)
    (haccept : ∀ s, ((n : ℝ) - r s) / (2 * n) ≤ probability (accept s))
    (hnext : ∀ s k, greedyCyclePotential n (J (next s k)) (r (next s k)) =
      if accept s k then
        greedyCyclePotential n (J s) (r s) - greedyCycleDrop n (J s)
      else greedyCyclePotential n (J s) (r s))
    (m : ℕ) (s : S) :
    finiteAverage (fun ω : Fin m → κ =>
      greedyCyclePotential n (J (greedyRun next m ω s)) (r (greedyRun next m ω s))) ≤
      greedyCycleDecay n ^ m * greedyCyclePotential n (J s) (r s) :=
  finiteAverage_greedyRun_le next (fun s => greedyCyclePotential n (J s) (r s))
    (greedyCycleDecay_nonneg hn) (finiteAverage_greedyCycle_step hn J r hr accept next haccept hnext) m s

end

end LeanNumDetect.FiniteMatrixSampling
