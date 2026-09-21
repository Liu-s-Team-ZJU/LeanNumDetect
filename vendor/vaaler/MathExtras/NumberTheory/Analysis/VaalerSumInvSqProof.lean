/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AnalyticNT.Diophantine.VaalerBeurlingNonneg

/-!
# Discharge of `VaalerSumInvSqIdentity`: the classical squared cosecant identity

This leaf proves, fully `sorry`/`axiom`-free, the classical squared cotangent /
cosecant identity

`∑_{n∈ℤ} (x − n)⁻² = (π / sin πx)²`   for `x ∉ ℤ`,

in the `ℕ`-split form consumed by `VaalerBeurlingNonneg`, namely

`vaalerSumInvSqIdentity_holds : VaalerSumInvSqIdentity`.

The route is the **identity theorem** (analytic continuation) over `ℂ`:

* `S z = ∑' n : ℤ, 1/(z+n)²` and `C z = (π / sin (π z))²`.
* Mathlib's `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow` (with `k = 1`) gives
  `S z = C z` on the upper half plane `ℍₒ` after identifying the iterated-derivative-within
  with the ordinary `deriv` of `π·cot(π·)` and computing the latter as `−(π/sin πz)²`.
* `S` is `DifferentiableOn ℂ` on the open connected set `ℂ_ℤ = (range Int.cast)ᶜ`
  (proved locally on small balls via `differentiableOn_tsum_of_summable_norm`).
* `C` is `DifferentiableOn ℂ` on `ℂ_ℤ` (denominator nonvanishing).
* `ℂ_ℤ` is preconnected (complement of a countable set in `ℝ`-rank-2 space).
* `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` propagates `S = C` from `ℍₒ`
  to all of `ℂ_ℤ`.
* Specialize to real `x ∉ ℤ`, split the `ℤ`-sum into the two `ℕ`-tails, cast down to `ℝ`.
-/

noncomputable section

open Real Complex Filter Topology
open scoped BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerSumInvSqProof

local notation "ℂ_ℤ" => Complex.integerComplement
local notation "ℍₒ" => UpperHalfPlane.upperHalfPlaneSet

/-- The full integer Eisenstein-type sum `S z = ∑_{n∈ℤ} 1/(z+n)²`. -/
def S (z : ℂ) : ℂ := ∑' n : ℤ, 1 / (z + n) ^ 2

/-- The squared cosecant `C z = (π / sin (π z))²`. -/
def C (z : ℂ) : ℂ := ((π : ℂ) / Complex.sin (π * z)) ^ 2

/-! ## `ℂ_ℤ` is open, preconnected, and the term-summability holds everywhere -/

/-- `ℂ_ℤ` is open. -/
theorem isOpen_integerComplement : IsOpen ℂ_ℤ := Complex.isOpen_compl_range_intCast

/-- For every `z`, the term family `n ↦ 1/(z+n)²` is summable over `ℤ`. -/
theorem summable_term (z : ℂ) : Summable (fun n : ℤ => 1 / (z + n) ^ 2) := by
  have h := EisensteinSeries.linear_right_summable z 1 (k := 2) (by norm_num)
  refine h.congr ?_
  intro n
  rw [Int.cast_one, one_mul, one_div]
  rfl

/-! ## Step 1: `S = C` on the upper half plane -/

/-- `Complex.cot` has derivative `-1/(sin z)²` wherever `sin z ≠ 0`. -/
theorem hasDerivAt_cot {z : ℂ} (hz : Complex.sin z ≠ 0) :
    HasDerivAt Complex.cot (-1 / (Complex.sin z) ^ 2) z := by
  have hcot : Complex.cot = fun w => Complex.cos w / Complex.sin w := by
    funext w; exact Complex.cot_eq_cos_div_sin w
  rw [hcot]
  have hnum : HasDerivAt Complex.cos (-Complex.sin z) z := Complex.hasDerivAt_cos z
  have hden : HasDerivAt Complex.sin (Complex.cos z) z := Complex.hasDerivAt_sin z
  have hq := hnum.div hden hz
  -- derivative = ((-sin)·sin − cos·cos)/sin² = -(sin²+cos²)/sin² = -1/sin²
  have hpyth : Complex.sin z ^ 2 + Complex.cos z ^ 2 = 1 := Complex.sin_sq_add_cos_sq z
  refine hq.congr_deriv ?_
  rw [div_eq_div_iff (pow_ne_zero 2 hz) (pow_ne_zero 2 hz)]
  linear_combination -(Complex.sin z ^ 2) * hpyth

/-- `deriv (fun z => π * cot (π * z)) z = -(π/sin(πz))²` where `sin(πz) ≠ 0`. -/
theorem deriv_pi_cot {z : ℂ} (hz : Complex.sin (π * z) ≠ 0) :
    deriv (fun w : ℂ => (π : ℂ) * Complex.cot (π * w)) z = - C z := by
  -- inner map w ↦ π * w has derivative π
  have hinner : HasDerivAt (fun w : ℂ => (π : ℂ) * w) (π : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (π : ℂ)
  -- cot at π*z
  have hcot : HasDerivAt Complex.cot (-1 / (Complex.sin (π * z)) ^ 2) (π * z) :=
    hasDerivAt_cot hz
  -- chain rule: cot (π * w) has derivative (-1/sin²)·π
  have hcomp : HasDerivAt (fun w : ℂ => Complex.cot (π * w))
      ((-1 / (Complex.sin (π * z)) ^ 2) * (π : ℂ)) z := hcot.comp z hinner
  -- multiply by constant π
  have hfull : HasDerivAt (fun w : ℂ => (π : ℂ) * Complex.cot (π * w))
      ((π : ℂ) * ((-1 / (Complex.sin (π * z)) ^ 2) * (π : ℂ))) z := hcomp.const_mul (π : ℂ)
  rw [hfull.deriv]
  unfold C
  have hsin : Complex.sin (π * z) ^ 2 ≠ 0 := pow_ne_zero 2 hz
  rw [div_pow, mul_comm]
  field_simp

/-- **Step 1.** `S z = C z` for `z ∈ ℍₒ`. -/
theorem S_eq_C_on_upperHalfPlane {z : ℂ} (hz : z ∈ ℍₒ) : S z = C z := by
  have hmem : z ∈ ℂ_ℤ := UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩
  have hsin : Complex.sin (π * z) ≠ 0 := sin_pi_mul_ne_zero hmem
  -- Mathlib: iteratedDerivWithin 1 (π cot(π·)) ℍₒ z = (-1)·1!·∑ 1/(z+n)²
  have hmain := iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow (k := 1) (by norm_num) hz
  -- LHS is derivWithin = deriv on the open set ℍₒ
  rw [iteratedDerivWithin_one] at hmain
  rw [derivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hz] at hmain
  rw [deriv_pi_cot hsin] at hmain
  -- RHS: (-1)^1 * 1! * ∑' n, 1/(z+n)^(1+1) = - S z
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one, neg_mul, one_mul] at hmain
  -- hmain : - C z = - ∑' n, 1/(z+n)^(1+1)
  show S z = C z
  unfold S
  have heq : (∑' n : ℤ, 1 / (z + (n : ℂ)) ^ (1 + 1)) = ∑' n : ℤ, 1 / (z + (n : ℂ)) ^ 2 := by
    norm_num
  rw [heq] at hmain
  -- hmain : - C z = - ∑' n, 1/(z+n)^2
  exact (neg_injective hmain).symm

/-! ## Step 2: `S` is differentiable on `ℂ_ℤ` -/

/-- Each term `z ↦ 1/(z+n)²` is differentiable on `ℂ_ℤ`. -/
theorem term_differentiableOn (n : ℤ) :
    DifferentiableOn ℂ (fun z : ℂ => 1 / (z + n) ^ 2) ℂ_ℤ := by
  apply DifferentiableOn.div
  · fun_prop
  · fun_prop
  · intro z hz
    have : z + (n : ℂ) ≠ 0 := Complex.integerComplement_add_ne_zero hz n
    exact pow_ne_zero 2 this

/-- Key local bound: for `z₀ ∈ ℂ_ℤ`, set `δ = infDist z₀ (range Int.cast) > 0` and `r = δ/2`.
On `ball z₀ r`, every term satisfies `‖1/(z+n)²‖ ≤ 4 * ‖1/(z₀+n)²‖`. -/
theorem S_differentiableAt {z₀ : ℂ} (hz₀ : z₀ ∈ ℂ_ℤ) : DifferentiableAt ℂ S z₀ := by
  classical
  set s : Set ℂ := Set.range ((↑) : ℤ → ℂ) with hs
  have hsclosed : IsClosed s := Complex.isClosed_range_intCast
  have hz₀s : z₀ ∉ s := hz₀
  have hsne : s.Nonempty := ⟨(0 : ℂ), ⟨0, by simp⟩⟩
  set δ : ℝ := Metric.infDist z₀ s with hδ
  have hδpos : 0 < δ := by
    rw [hδ, ← hsclosed.notMem_iff_infDist_pos hsne]; exact hz₀s
  set r : ℝ := δ / 2 with hr
  have hrpos : 0 < r := by positivity
  -- on ball z₀ r, S is differentiable (then differentiableAt)
  have hball_open : IsOpen (Metric.ball z₀ r) := Metric.isOpen_ball
  -- uniform bound
  set u : ℤ → ℝ := fun n => 4 * ‖(1 : ℂ) / (z₀ + n) ^ 2‖ with hu
  have husum : Summable u := by
    refine Summable.mul_left 4 ?_
    exact (summable_term z₀).norm
  -- lower bound on ‖z₀+n‖
  have hlb₀ : ∀ n : ℤ, δ ≤ ‖z₀ + (n : ℂ)‖ := by
    intro n
    have hmem : (-(n : ℂ)) ∈ s := ⟨-n, by push_cast; ring⟩
    have := Metric.infDist_le_dist_of_mem (x := z₀) hmem
    rw [Complex.dist_eq] at this
    calc δ ≤ ‖z₀ - (-(n : ℂ))‖ := this
      _ = ‖z₀ + (n : ℂ)‖ := by rw [sub_neg_eq_add]
  have hbound : ∀ (n : ℤ) (z : ℂ), z ∈ Metric.ball z₀ r → ‖(1 : ℂ) / (z + n) ^ 2‖ ≤ u n := by
    intro n z hz
    have hzdist : ‖z - z₀‖ < r := by
      rw [Metric.mem_ball, Complex.dist_eq] at hz; exact hz
    -- ‖z+n‖ ≥ ‖z₀+n‖ - ‖z-z₀‖ ≥ ‖z₀+n‖ - r ≥ ‖z₀+n‖/2
    have hge : ‖z₀ + (n : ℂ)‖ / 2 ≤ ‖z + (n : ℂ)‖ := by
      have htri : ‖z₀ + (n : ℂ)‖ - ‖z - z₀‖ ≤ ‖z + (n : ℂ)‖ := by
        have : ‖z₀ + (n : ℂ)‖ ≤ ‖z + (n : ℂ)‖ + ‖z - z₀‖ := by
          calc ‖z₀ + (n : ℂ)‖ = ‖(z + (n : ℂ)) - (z - z₀)‖ := by ring_nf
            _ ≤ ‖z + (n : ℂ)‖ + ‖z - z₀‖ := norm_sub_le _ _
        linarith
      have hrle : r ≤ ‖z₀ + (n : ℂ)‖ / 2 := by
        have h1 := hlb₀ n; rw [hr]; linarith
      linarith
    have hz₀n_pos : 0 < ‖z₀ + (n : ℂ)‖ := lt_of_lt_of_le (by have := hlb₀ n; linarith) (hlb₀ n)
    have hzn_pos : 0 < ‖z + (n : ℂ)‖ := lt_of_lt_of_le (by linarith) hge
    -- norms: ‖1/(z+n)²‖ = 1/‖z+n‖²
    have hlhs : ‖(1 : ℂ) / (z + (n : ℂ)) ^ 2‖ = 1 / ‖z + (n : ℂ)‖ ^ 2 := by
      rw [norm_div, norm_one, norm_pow]
    have hun : u n = 4 / ‖z₀ + (n : ℂ)‖ ^ 2 := by
      rw [hu]; simp only [norm_div, norm_one, norm_pow]; ring
    rw [hlhs, hun]
    -- 1/‖z+n‖² ≤ 4/‖z₀+n‖²  since ‖z+n‖ ≥ ‖z₀+n‖/2
    have hsq : (‖z₀ + (n : ℂ)‖ / 2) ^ 2 ≤ ‖z + (n : ℂ)‖ ^ 2 := by
      apply sq_le_sq'
      · linarith [hge, hzn_pos]
      · exact hge
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsq, hz₀n_pos, hzn_pos]
  -- ball ⊆ ℂ_ℤ
  have hball_sub : Metric.ball z₀ r ⊆ ℂ_ℤ := by
    intro z hz
    rw [Metric.mem_ball] at hz
    -- z ∉ s : if z = m, dist z₀ z ≥ δ > r
    intro hzmem
    obtain ⟨m, hm⟩ := hzmem
    have : δ ≤ dist z₀ z := by rw [hδ]; exact Metric.infDist_le_dist_of_mem ⟨m, hm⟩
    rw [dist_comm] at this
    rw [hr] at hz; linarith
  have hdiffOn : DifferentiableOn ℂ S (Metric.ball z₀ r) := by
    have := differentiableOn_tsum_of_summable_norm (U := Metric.ball z₀ r)
      (F := fun n : ℤ => fun z : ℂ => (1 : ℂ) / (z + n) ^ 2) husum
      (fun n => (term_differentiableOn n).mono hball_sub) hball_open hbound
    exact this
  exact hdiffOn.differentiableAt (hball_open.mem_nhds (Metric.mem_ball_self hrpos))

/-- **Step 2.** `S` is differentiable on `ℂ_ℤ`. -/
theorem S_differentiableOn : DifferentiableOn ℂ S ℂ_ℤ :=
  fun z hz => (S_differentiableAt hz).differentiableWithinAt

/-! ## Step 3: `C` is differentiable on `ℂ_ℤ` -/

/-- **Step 3.** `C` is differentiable on `ℂ_ℤ`. -/
theorem C_differentiableOn : DifferentiableOn ℂ C ℂ_ℤ := by
  apply DifferentiableOn.pow
  apply DifferentiableOn.div
  · fun_prop
  · fun_prop
  · intro z hz
    exact sin_pi_mul_ne_zero hz

/-! ## Step 4: identity theorem on `ℂ_ℤ` -/

/-- `ℂ_ℤ` is preconnected. -/
theorem isPreconnected_integerComplement : IsPreconnected ℂ_ℤ := by
  have hcount : (Set.range ((↑) : ℤ → ℂ)).Countable := Set.countable_range _
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  exact (hcount.isConnected_compl_of_one_lt_rank hrank).isPreconnected

/-- **Step 4.** `S = C` on all of `ℂ_ℤ`. -/
theorem S_eq_C_on_integerComplement : Set.EqOn S C ℂ_ℤ := by
  have hSan : AnalyticOnNhd ℂ S ℂ_ℤ := S_differentiableOn.analyticOnNhd isOpen_integerComplement
  have hCan : AnalyticOnNhd ℂ C ℂ_ℤ := C_differentiableOn.analyticOnNhd isOpen_integerComplement
  -- use I ∈ ℍₒ ⊆ ℂ_ℤ as the base point
  have hI_upper : Complex.I ∈ ℍₒ := by
    show (0 : ℝ) < Complex.I.im; simp
  have hI_mem : Complex.I ∈ ℂ_ℤ := UpperHalfPlane.coe_mem_integerComplement ⟨Complex.I, hI_upper⟩
  -- S = C eventually at I (they agree on the open nbhd ℍₒ)
  have hev : S =ᶠ[𝓝 Complex.I] C := by
    apply Filter.eventuallyEq_of_mem (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hI_upper)
    intro z hz; exact S_eq_C_on_upperHalfPlane hz
  exact hSan.eqOn_of_preconnected_of_eventuallyEq hCan isPreconnected_integerComplement hI_mem hev

/-! ## Step 5: specialize to real `x`, split the `ℤ`-sum, descend to `ℝ` -/

/-- For real `x` with `sin (π x) ≠ 0`, the cast `(x : ℂ)` lies in `ℂ_ℤ`. -/
theorem ofReal_mem_integerComplement {x : ℝ} (hx : Real.sin (π * x) ≠ 0) :
    (x : ℂ) ∈ ℂ_ℤ := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  -- if x = n then sin (π x) = sin (π n) = 0
  have hxn : x = (n : ℝ) := by exact_mod_cast hn.symm
  apply hx
  rw [hxn]
  rw [show (π * (n : ℝ)) = (n : ℝ) * π by ring, Real.sin_int_mul_pi]

/-- **Main theorem.** The classical squared cosecant identity in the `ℕ`-split form. -/
theorem vaalerSumInvSqIdentity_holds :
    MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg.VaalerSumInvSqIdentity := by
  intro x hx
  -- complex membership and the identity S x = C x
  have hmem : (x : ℂ) ∈ ℂ_ℤ := ofReal_mem_integerComplement hx
  have hSC : S (x : ℂ) = C (x : ℂ) := S_eq_C_on_integerComplement hmem
  -- split the ℤ-sum
  set f : ℤ → ℂ := fun n => 1 / ((x : ℂ) + n) ^ 2 with hf
  -- summability of the two ℕ-tails via injective reindexing of the full ℤ-sum
  have hsumZ : Summable f := summable_term (x : ℂ)
  have hsumP : Summable (fun n : ℕ => f (n + 1)) := by
    have hinj : Function.Injective (fun n : ℕ => ((n : ℤ) + 1)) := by
      intro a b hab; simpa using hab
    have := hsumZ.comp_injective hinj
    refine this.congr ?_; intro n; simp [hf]
  have hsumN : Summable (fun n : ℕ => f (-(n + 1))) := by
    have hinj : Function.Injective (fun n : ℕ => (-((n : ℤ) + 1))) := by
      intro a b hab; simpa using hab
    have := hsumZ.comp_injective hinj
    refine this.congr ?_; intro n; simp [hf]
  have hsplit : (∑' n : ℤ, f n)
      = (∑' n : ℕ, f (n + 1)) + f 0 + ∑' n : ℕ, f (-(n + 1)) :=
    tsum_of_add_one_of_neg_add_one hsumP hsumN
  -- rewrite S as the split
  have hSsplit : S (x : ℂ) = (∑' n : ℕ, f (n + 1)) + f 0 + ∑' n : ℕ, f (-(n + 1)) := by
    rw [show S (x : ℂ) = ∑' n : ℤ, f n from rfl, hsplit]
  -- now identify each ℂ piece with the ofReal of a real piece
  have hPcast : (∑' n : ℕ, f (n + 1))
      = ((∑' n : ℕ, (x + ((n : ℕ) + 1 : ℕ))⁻¹ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr ?_
    intro n; rw [hf]; push_cast [one_div, inv_pow]; ring_nf
  have hNcast : (∑' n : ℕ, f (-(n + 1)))
      = ((∑' n : ℕ, (x - ((n : ℕ) + 1 : ℕ))⁻¹ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr ?_
    intro n; rw [hf]; push_cast [one_div, inv_pow]; ring_nf
  have hCcast : f 0 = ((x⁻¹ ^ 2 : ℝ) : ℂ) := by
    rw [hf]; push_cast [one_div, inv_pow]; norm_num
  -- C (x:ℂ) = ↑((π/sin(πx))²)
  have hCval : C (x : ℂ) = (((π / Real.sin (π * x)) ^ 2 : ℝ) : ℂ) := by
    rw [show C (x : ℂ) = ((π : ℂ) / Complex.sin (π * x)) ^ 2 from rfl]
    rw [show ((π : ℂ) * (x : ℂ)) = ((π * x : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_sin]
    push_cast
    ring
  -- assemble the ℂ equation and descend to ℝ via ofReal_injective
  rw [hSsplit, hPcast, hNcast, hCcast, hCval] at hSC
  have hSC' : (((∑' n : ℕ, (x + ((n : ℕ) + 1 : ℕ))⁻¹ ^ 2)
        + x⁻¹ ^ 2 + ∑' n : ℕ, (x - ((n : ℕ) + 1 : ℕ))⁻¹ ^ 2 : ℝ) : ℂ)
      = (((π / Real.sin (π * x)) ^ 2 : ℝ) : ℂ) := by
    push_cast at hSC ⊢
    linear_combination hSC
  have hreal := Complex.ofReal_injective hSC'
  -- target ordering: (∑ (x-(k+1))⁻²) + (∑ (x+(k+1))⁻²) + x⁻² = (π/sin)²
  linarith [hreal]

#print axioms vaalerSumInvSqIdentity_holds

end MathExtras.NumberTheory.Analysis.VaalerSumInvSqProof
