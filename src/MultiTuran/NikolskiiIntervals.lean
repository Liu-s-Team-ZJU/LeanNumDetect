import MultiTuran.Nikolskii
import MultiTuran.NikolskiiAffine
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Exact Nikolskii bounds on intervals and finite unions

The norms use the actual Lebesgue integral over the union and its actual
supremum. Disjointness is unnecessary for this `L²`--`L∞` specialization:
the integral over an individual interval is dominated by that over the union.
-/

set_option autoImplicit false
open scoped BigOperators
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- The actual supremum of a complex function over a specified set. -/
def setSupNorm {α : Type*} (f : α → ℂ) (E : Set α) : ℝ :=
  sSup ((fun t => ‖f t‖) '' E)

/-- A finite family of genuine closed real intervals. -/
def intervalUnion {B : Type*} (a b : B → ℝ) : Set ℝ :=
  ⋃ i, Set.Icc (a i) (b i)

theorem exponentialSum_interval_norm_sq_le {n : ℕ} (hn : 0 < n)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) {a b x : ℝ}
    (hab : a < b) (hx : x ∈ Set.Icc a b) :
    (b - a) * ‖ExponentialSumEstimates.exponentialSum frequency c x‖ ^ 2 ≤
      (Real.pi ^ 2 * (n : ℝ) ^ 2 / 4) *
        ∫ t in Set.Icc a b, ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ^ 2 := by
  let f := ExponentialSumEstimates.exponentialSum frequency c
  let L := b - a
  have hL : 0 < L := sub_pos.mpr hab
  have ht : (x - a) / L ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hL.le
    · apply (div_le_one hL).2
      dsimp [L]
      linarith [hx.2]
  have hEndpoint : ∀ (ω : Fin n → ℝ) (z : Fin n → ℂ),
      ‖ExponentialSumEstimates.exponentialSum ω z 0‖ ^ 2 ≤
        (Real.pi * n / 2) ^ 2 *
          ExponentialSumEstimates.unitEnergy (ExponentialSumEstimates.exponentialSum ω z) := by
    intro ω z
    convert exponentialSum_endpoint_norm_sq_le hn ω z using 1 <;> ring
  have hpoint := ExponentialSumEstimates.pointwise_energy_bound_of_endpoint hEndpoint
    (fun j => L * frequency j)
    (fun j => c j * Complex.exp (Complex.I * ((a * frequency j : ℝ) : ℂ))) ht
  simp only [ExponentialSumEstimates.unitEnergy,
    ExponentialSumEstimates.exponentialSum_affine] at hpoint
  have hxchange : L * ((x - a) / L) + a = x := by field_simp; ring
  rw [hxchange] at hpoint
  have hchange : L * (∫ u in (0 : ℝ)..1, ‖f (L * u + a)‖ ^ 2) =
      ∫ t in a..b, ‖f t‖ ^ 2 := by
    simpa only [smul_eq_mul, mul_zero, zero_add, mul_one, L, sub_add_cancel] using
      (intervalIntegral.smul_integral_comp_mul_add (fun t => ‖f t‖ ^ 2)
        (a := 0) (b := 1) L a)
  have hscaled := mul_le_mul_of_nonneg_left hpoint hL.le
  change L * ‖f x‖ ^ 2 ≤ L * ((Real.pi * n / 2) ^ 2 *
    ∫ u in (0 : ℝ)..1, ‖f (L * u + a)‖ ^ 2) at hscaled
  rw [mul_left_comm L ((Real.pi * n / 2) ^ 2), hchange] at hscaled
  have hfinal : L * ‖f x‖ ^ 2 ≤ (Real.pi ^ 2 * (n : ℝ) ^ 2 / 4) *
      ∫ t in a..b, ‖f t‖ ^ 2 := by
    nlinarith only [hscaled]
  rwa [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc] at hfinal

theorem intervalUnion_isCompact {B : Type*} [Finite B] (a b : B → ℝ) :
    IsCompact (intervalUnion a b) :=
  isCompact_iUnion fun _ => isCompact_Icc

theorem intervalUnion_energy_integrable {B : Type*} [Finite B] {n : ℕ}
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) (a b : B → ℝ) :
    IntegrableOn (fun t => ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ^ 2)
      (intervalUnion a b) := by
  exact ContinuousOn.integrableOn_compact (intervalUnion_isCompact a b)
    ((ExponentialSumEstimates.continuous_exponentialSum frequency c).norm.pow 2).continuousOn

/-- Squared pointwise form, valid for any finite union of sufficiently long intervals. -/
theorem exponentialSum_intervalUnion_norm_sq_le {B : Type*} [Finite B]
    {n : ℕ} (hn : 0 < n) (frequency : Fin n → ℝ) (c : Fin n → ℂ)
    (a b : B → ℝ) {Lmin : ℝ} (hLmin : 0 < Lmin)
    (hlength : ∀ i, Lmin ≤ b i - a i) {x : ℝ} (hx : x ∈ intervalUnion a b) :
    Lmin * ‖ExponentialSumEstimates.exponentialSum frequency c x‖ ^ 2 ≤
      (Real.pi ^ 2 * (n : ℝ) ^ 2 / 4) *
        ∫ t in intervalUnion a b, ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ^ 2 := by
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  have hlen : a i < b i := by linarith [hlength i]
  have hlocal := exponentialSum_interval_norm_sq_le hn frequency c hlen hi
  have hsubset : Set.Icc (a i) (b i) ⊆ intervalUnion a b := by
    intro t ht
    exact Set.mem_iUnion.mpr ⟨i,ht⟩
  have hintegral := setIntegral_mono_set (intervalUnion_energy_integrable frequency c a b)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall (fun _ hx => hsubset hx))
  calc
    _ ≤ (b i - a i) * ‖ExponentialSumEstimates.exponentialSum frequency c x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hlength i) (sq_nonneg _)
    _ ≤ _ := hlocal.trans
      (mul_le_mul_of_nonneg_left hintegral (by positivity))

/-- Divided squared form convenient for repeated integration in product sets. -/
theorem exponentialSum_intervalUnion_norm_sq_le_div {B : Type*} [Finite B]
    {n : ℕ} (hn : 0 < n) (frequency : Fin n → ℝ) (c : Fin n → ℂ)
    (a b : B → ℝ) {Lmin : ℝ} (hLmin : 0 < Lmin)
    (hlength : ∀ i, Lmin ≤ b i - a i) {x : ℝ} (hx : x ∈ intervalUnion a b) :
    ‖ExponentialSumEstimates.exponentialSum frequency c x‖ ^ 2 ≤
      ((Real.pi * n / 2) ^ 2 / Lmin) *
        ∫ t in intervalUnion a b, ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ^ 2 := by
  have h := exponentialSum_intervalUnion_norm_sq_le hn frequency c a b hLmin hlength hx
  calc
    _ ≤ ((Real.pi ^ 2 * (n : ℝ) ^ 2 / 4) *
        ∫ t in intervalUnion a b, ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ^ 2) /
        Lmin := (le_div_iff₀ hLmin).2 (by simpa only [mul_comm] using h)
    _ = _ := by ring

private theorem norm_le_scaled_sqrt_of_energy {p E L K : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hL : 0 < L) (hK : 0 ≤ K)
    (h : L * p ^ 2 ≤ K ^ 2 * E) : p ≤ K / Real.sqrt L * Real.sqrt E := by
  have hprod : Real.sqrt L * p ≤ K * Real.sqrt E := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rwa [mul_pow, mul_pow, Real.sq_sqrt hL.le, Real.sq_sqrt hE]
  have hdiv : p ≤ (K * Real.sqrt E) / Real.sqrt L :=
    (le_div_iff₀ (Real.sqrt_pos.mpr hL)).2 (by simpa only [mul_comm] using hprod)
  convert hdiv using 1
  ring

/-- The precise pointwise `π n / (2 √Lmin)` estimate with the true union integral. -/
theorem exponentialSum_intervalUnion_norm_le {B : Type*} [Finite B]
    {n : ℕ} (hn : 0 < n) (frequency : Fin n → ℝ) (c : Fin n → ℂ)
    (a b : B → ℝ) {Lmin : ℝ} (hLmin : 0 < Lmin)
    (hlength : ∀ i, Lmin ≤ b i - a i) {x : ℝ} (hx : x ∈ intervalUnion a b) :
    ‖ExponentialSumEstimates.exponentialSum frequency c x‖ ≤
      (Real.pi * n / (2 * Real.sqrt Lmin)) *
        Real.sqrt (∫ t in intervalUnion a b,
          ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ^ 2) := by
  have hpoint := exponentialSum_intervalUnion_norm_sq_le hn frequency c a b hLmin hlength hx
  have hpoint' : Lmin * ‖ExponentialSumEstimates.exponentialSum frequency c x‖ ^ 2 ≤
      (Real.pi * n / 2) ^ 2 * ∫ t in intervalUnion a b,
        ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ^ 2 := by
    convert hpoint using 1
    ring
  have h := norm_le_scaled_sqrt_of_energy
    (p := ‖ExponentialSumEstimates.exponentialSum frequency c x‖)
    (E := ∫ t in intervalUnion a b, ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ^ 2)
    (K := Real.pi * n / 2) (norm_nonneg _)
    (integral_nonneg (fun _ => sq_nonneg _)) hLmin (by positivity) hpoint'
  convert h using 1
  ring

/-- The article's finite-union `L²`--`L∞` interface, using an actual supremum. -/
theorem exponentialSum_intervalUnion_supNorm_le {B : Type*} [Finite B] [Nonempty B]
    {n : ℕ} (hn : 0 < n) (frequency : Fin n → ℝ) (c : Fin n → ℂ)
    (a b : B → ℝ) {Lmin : ℝ} (hLmin : 0 < Lmin)
    (hlength : ∀ i, Lmin ≤ b i - a i) :
    setSupNorm (ExponentialSumEstimates.exponentialSum frequency c) (intervalUnion a b) ≤
      (Real.pi * n / (2 * Real.sqrt Lmin)) *
        Real.sqrt (∫ t in intervalUnion a b,
          ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ^ 2) := by
  have hne : (intervalUnion a b).Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty B›
    refine ⟨a i, Set.mem_iUnion.mpr ⟨i, ?_⟩⟩
    exact ⟨le_rfl, by linarith [hlength i]⟩
  apply csSup_le (hne.image _)
  rintro y ⟨x,hx,rfl⟩
  exact exponentialSum_intervalUnion_norm_le hn frequency c a b hLmin hlength hx

end
end LeanNumDetect.MultiTuran
