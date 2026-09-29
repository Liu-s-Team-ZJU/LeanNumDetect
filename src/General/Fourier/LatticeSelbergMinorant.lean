import General.Fourier.TranslatedCubeFourier

/-! Selberg lattice minorants with enlarged open endpoints.  The interval
`(-1,M+1)` has exactly the integer points `0,...,M`; its minorant has mass
`M+2-δ⁻¹`. The vanishing endpoint inequalities are proved explicitly. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.LatticeSelbergMinorant
noncomputable section
open MathExtras.NumberTheory.Analysis
open VaalerBeurlingNonneg VaalerThm16Mechanism VaalerCor7Closed
open SelbergIntervalMajorantClosed SelbergIntervalPoissonClosed LargeSieve

/-- The lower member of Selberg's interval pair. -/
def intervalMinorant (a b δ t : ℝ) : ℝ :=
  selbergIntervalMajorant a b δ t - selbergIntervalMajorant a a δ t -
    selbergIntervalMajorant b b δ t

private theorem fejerK_neg (x : ℝ) : fejerK (-x) = fejerK x := by
  unfold fejerK
  rw [show Real.pi * -x = -(Real.pi * x) by ring, Real.sin_neg]
  by_cases hx : x = 0
  · subst x; simp
  · rw [if_neg (neg_ne_zero.mpr hx), if_neg hx, inv_neg]
    ring

/-- Reflection exchanges Selberg's lower and upper interval functions. -/
theorem intervalMinorant_eq_neg_reversed (a b δ t : ℝ) :
    intervalMinorant a b δ t = -selbergIntervalMajorant b a δ t := by
  unfold intervalMinorant selbergIntervalMajorant beurlingBClosed
  rw [show δ * (a - t) = -(δ * (t - a)) by ring,
    show δ * (t - b) = -(δ * (b - t)) by ring,
    interpH_neg, interpH_neg, fejerK_neg, fejerK_neg]
  ring

/-- At the endpoints the lower function is nonpositive, so the bounded
indicator is that of the open interval, including for lattice applications. -/
theorem intervalMinorant_le_openIndicator {a b δ : ℝ}
    (hab : a < b) (hδ : 0 < δ) (t : ℝ) :
    intervalMinorant a b δ t ≤ if a < t ∧ t < b then 1 else 0 := by
  rw [intervalMinorant_eq_neg_reversed,
    selbergIntervalMajorant_eq_signPair_add_phi hδ]
  have h1 : 0 ≤ phi (δ * (a - t)) := vaalerBeurlingMajorant_closed.nonneg _
  have h2 : 0 ≤ phi (δ * (t - b)) := vaalerBeurlingMajorant_closed.nonneg _
  rcases lt_trichotomy t a with hta | rfl | hat
  · rw [if_neg (by rintro ⟨h, h'⟩; linarith)]
    have hbt : 0 < b - t := by linarith
    simp only [intervalSignPair, Real.sign_of_pos (sub_pos.mpr hta),
      Real.sign_of_neg (by linarith : t - b < 0)]
    linarith
  · rw [if_neg (by simp)]
    simp only [sub_self, mul_zero, phi_zero, intervalSignPair, Real.sign_zero,
      Real.sign_of_neg (sub_neg.mpr hab)]
    linarith
  · rcases lt_trichotomy t b with htb | rfl | hbt
    · rw [if_pos ⟨hat, htb⟩]
      simp only [intervalSignPair, Real.sign_of_neg (sub_neg.mpr hat),
        Real.sign_of_neg (sub_neg.mpr htb)]
      linarith
    · rw [if_neg (by simp)]
      simp only [sub_self, mul_zero, phi_zero, intervalSignPair, Real.sign_zero,
        Real.sign_of_neg (sub_neg.mpr hab)]
      linarith
    · rw [if_neg (by rintro ⟨h, h'⟩; linarith)]
      simp only [intervalSignPair, Real.sign_of_neg (by linarith : a - t < 0),
        Real.sign_of_pos (sub_pos.mpr hbt)]
      linarith

/-- The majorant includes both closed endpoints. -/
theorem one_le_majorant_closed {a b δ t : ℝ}
    (hab : a < b) (hδ : 0 < δ) (hat : a ≤ t) (htb : t ≤ b) :
    1 ≤ selbergIntervalMajorant a b δ t := by
  rcases hat.eq_or_lt with rfl | hat
  · rw [selbergIntervalMajorant_eq_signPair_add_phi hδ]
    have hs : intervalSignPair a b a = 1 / 2 := by
      simp [intervalSignPair, Real.sign_of_pos (sub_pos.mpr hab)]
    rw [hs]
    simp only [sub_self, mul_zero, phi_zero]
    have hnonneg : 0 ≤ phi (δ * (b - a)) := vaalerBeurlingMajorant_closed.nonneg _
    linarith
  · exact one_le_selbergIntervalMajorant hδ hat htb

theorem majorant_hasSum {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    HasSum (fun n : ℤ => (selbergIntervalMajorant a b δ (n : ℝ) : ℂ))
      (((b - a) + δ⁻¹ : ℝ) : ℂ) := by
  have hs := selbergIntervalMajorant_mul_echar_int_summable hab hδ 0
  have hs' : Summable
      (fun n : ℤ => (selbergIntervalMajorant a b δ (n : ℝ) : ℂ)) := by
    simpa [echar] using hs
  exact hs'.hasSum_iff.mpr (tsum_selbergIntervalMajorant_eq_mass hab hδ hδ1)

theorem intervalMinorant_hasSum {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    HasSum (fun n : ℤ => (intervalMinorant a b δ (n : ℝ) : ℂ))
      (((b - a) - δ⁻¹ : ℝ) : ℂ) := by
  have h := ((majorant_hasSum hab hδ hδ1).sub
    (majorant_hasSum (a := a) (b := a) le_rfl hδ hδ1)).sub
      (majorant_hasSum (a := b) (b := b) le_rfl hδ hδ1)
  have heq : (((b - a) + δ⁻¹ : ℝ) : ℂ) -
      (((a - a) + δ⁻¹ : ℝ) : ℂ) - (((b - b) + δ⁻¹ : ℝ) : ℂ) =
      (((b - a) - δ⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [heq] at h
  exact h.congr_fun (fun n => by simp only [intervalMinorant]; push_cast; ring)

theorem majorantModulated_hasSum_zero {a b δ θ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hsep : δ ≤ circleDist θ 0) :
    HasSum (fun n : ℤ =>
      (selbergIntervalMajorant a b δ (n : ℝ) : ℂ) * echar θ (n : ℝ)) 0 := by
  exact (selbergIntervalMajorant_mul_echar_int_summable hab hδ θ).hasSum_iff.mpr
    (tsum_selbergIntervalMajorant_mul_echar_eq_zero hab hδ hsep)

theorem intervalMinorantModulated_summable {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (θ : ℝ) :
    Summable (fun n : ℤ => (intervalMinorant a b δ (n : ℝ) : ℂ) * echar θ (n : ℝ)) := by
  have h := ((selbergIntervalMajorant_mul_echar_int_summable hab hδ θ).sub
    (selbergIntervalMajorant_mul_echar_int_summable (a := a) (b := a) le_rfl hδ θ)).sub
      (selbergIntervalMajorant_mul_echar_int_summable (a := b) (b := b) le_rfl hδ θ)
  exact h.congr (fun n => by simp only [intervalMinorant]; push_cast; ring)

theorem intervalMinorantModulated_hasSum_zero {a b δ θ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hsep : δ ≤ circleDist θ 0) :
    HasSum (fun n : ℤ => (intervalMinorant a b δ (n : ℝ) : ℂ) * echar θ (n : ℝ)) 0 := by
  have h := ((majorantModulated_hasSum_zero hab hδ hsep).sub
    (majorantModulated_hasSum_zero (a := a) (b := a) le_rfl hδ hsep)).sub
      (majorantModulated_hasSum_zero (a := b) (b := b) le_rfl hδ hsep)
  simpa only [sub_zero] using h.congr_fun
    (fun n => by simp only [intervalMinorant]; push_cast; ring)


set_option maxHeartbeats 800000 in
private theorem hasSum_pi_prod
    {α : Type} [Fintype α]
    (f : α → ℤ → ℂ) (s : α → ℂ)
    (h : ∀ i, HasSum (f i) (s i)) :
    HasSum (fun n : α → ℤ => ∏ i, f i (n i)) (∏ i, s i) := by
  classical
  refine Fintype.induction_empty_option
    (P := fun (α : Type) [Fintype α] =>
      ∀ (f : α → ℤ → ℂ) (s : α → ℂ),
        (∀ i, HasSum (f i) (s i)) →
          HasSum (fun n : α → ℤ => ∏ i, f i (n i)) (∏ i, s i))
    ?_ ?_ ?_ α f s h
  · intro α β _ e ih f s h
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let ep : (α → ℤ) ≃ (β → ℤ) := Equiv.piCongrLeft (fun _ => ℤ) e
    have hi := ih (fun i n => f (e i) n) (fun i => s (e i))
      (fun i => h (e i))
    have heqf : (fun n : α → ℤ => ∏ i, f (e i) (n i)) =
        (fun n : β → ℤ => ∏ i, f i (n i)) ∘ ep := by
      funext n
      simpa [ep, Equiv.piCongrLeft] using
        e.prod_comp (fun x : β => f x (n (e.symm x)))
    have heqs : (∏ i : α, s (e i)) = ∏ i : β, s i := by
      exact e.prod_comp (fun i => s i)
    have hi' : HasSum
        ((fun n : β → ℤ => ∏ i, f i (n i)) ∘ ep) (∏ i : α, s (e i)) :=
      heqf ▸ hi
    rw [heqs] at hi'
    exact ep.hasSum_iff.mp hi'
  · intro f s h
    simp
  · intro α _ ih f s h
    let e : (Option α → ℤ) ≃ ℤ × (α → ℤ) := Equiv.piOptionEquivProd
    have hnone := h none
    have hsome := ih (fun i n => f (some i) n) (fun i => s (some i))
      (fun i => h (some i))
    have hjoint : Summable (fun p : ℤ × (α → ℤ) =>
        f none p.1 * ∏ i, f (some i) (p.2 i)) :=
      summable_mul_of_summable_norm
        (f := f none) (g := fun n : α → ℤ => ∏ i, f (some i) (n i))
        hnone.summable.norm hsome.summable.norm
    have htsum := tsum_mul_tsum_of_summable_norm
      (f := f none) (g := fun n : α → ℤ => ∏ i, f (some i) (n i))
      hnone.summable.norm hsome.summable.norm
    rw [hnone.tsum_eq, hsome.tsum_eq] at htsum
    have hp : HasSum (fun p : ℤ × (α → ℤ) =>
        f none p.1 * ∏ i, f (some i) (p.2 i))
        (s none * ∏ i, s (some i)) :=
      hjoint.hasSum_iff.mpr htsum.symm
    have heqf : (fun p : ℤ × (α → ℤ) =>
        f none p.1 * ∏ i, f (some i) (p.2 i)) =
        (fun n : Option α → ℤ => ∏ i, f i (n i)) ∘ e.symm := by
      funext p
      simp [e, Equiv.piOptionEquivProd_symm_apply]
    have heqs : s none * ∏ i, s (some i) = ∏ i, s i := by
      rw [Fintype.prod_option]
    rw [heqf, heqs] at hp
    exact e.symm.hasSum_iff.mp hp


/-- First-order tensor correction for a one-dimensional lattice sandwich. -/
def tensorMinorant {d : ℕ} (U L : ℤ → ℝ) (n : Fin d → ℤ) : ℝ :=
  ∏ i, U (n i) - ∑ r : Fin d, ∏ i, if i = r then U (n i) - L (n i) else U (n i)

private theorem mixed_prod {α R : Type*} [Fintype α] [DecidableEq α]
    [CommMonoid R] (f : α → R) (r : α) (D : α → R) :
    (∏ i, if i = r then D i else f i) = D r * ∏ i ∈ Finset.univ.erase r, f i := by
  rw [← Finset.mul_prod_erase Finset.univ
    (fun i => if i = r then D i else f i) (Finset.mem_univ r)]
  simp only
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [if_neg (Finset.ne_of_mem_erase hi)]

private theorem prod_sub_sum_le_prod {α : Type*} [DecidableEq α]
    (s : Finset α) (U L f : α → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i)
    (hU : ∀ i ∈ s, f i ≤ U i)
    (hL : ∀ i ∈ s, L i ≤ f i) :
    (∏ i ∈ s, U i) - ∑ r ∈ s, (U r - L r) * ∏ i ∈ s.erase r, U i ≤
      ∏ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hf' : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hU' : ∀ i ∈ s, f i ≤ U i := fun i hi => hU i (Finset.mem_insert_of_mem hi)
    have hL' : ∀ i ∈ s, L i ≤ f i := fun i hi => hL i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a s)
    have hUa := hU a (Finset.mem_insert_self a s)
    have hLa := hL a (Finset.mem_insert_self a s)
    have hrest : ∑ r ∈ s, (U r - L r) * ∏ i ∈ (insert a s).erase r, U i =
        U a * ∑ r ∈ s, (U r - L r) * ∏ i ∈ s.erase r, U i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hra : r ≠ a := fun heq => ha (heq ▸ hr)
      rw [Finset.erase_insert_of_ne hra.symm, Finset.prod_insert (by simp [ha])]
      ring
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Finset.erase_insert ha, hrest, Finset.prod_insert ha]
    have hrec := mul_le_mul_of_nonneg_left (ih hf' hU' hL') (hfa.trans hUa)
    have hp : (∏ i ∈ s, f i) ≤ ∏ i ∈ s, U i := Finset.prod_le_prod hf' hU'
    have hp0 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg hf'
    have hD : 0 ≤ U a - L a := by linarith
    have hDp := mul_le_mul_of_nonneg_left hp hD
    have hDf := mul_le_mul_of_nonneg_right (show U a - f a ≤ U a - L a by linarith) hp0
    nlinarith

/-- A lattice sandwich tensorizes without any sign hypothesis on the minorant. -/
theorem tensorMinorant_le_indicator {d : ℕ} (U L : ℤ → ℝ) (P : ℤ → Prop)
    [DecidablePred P] (_hU0 : ∀ n, 0 ≤ U n)
    (hU : ∀ n, (if P n then 1 else 0) ≤ U n)
    (hL : ∀ n, L n ≤ if P n then 1 else 0) (n : Fin d → ℤ) :
    tensorMinorant U L n ≤ if ∀ i, P (n i) then 1 else 0 := by
  classical
  have h := prod_sub_sum_le_prod Finset.univ (fun i => U (n i))
    (fun i => L (n i)) (fun i => if P (n i) then 1 else 0)
    (fun i _ => by split <;> norm_num) (fun i _ => hU _) (fun i _ => hL _)
  have heq : (∏ i, if P (n i) then (1 : ℝ) else 0) =
      if ∀ i, P (n i) then 1 else 0 := by
    by_cases hall : ∀ i, P (n i)
    · simp [hall]
    · rw [if_neg hall]
      obtain ⟨i, hi⟩ := not_forall.mp hall
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  rw [heq] at h
  simpa only [tensorMinorant, mixed_prod] using h


/-- The exact lattice mass of the first-order tensor correction. -/
theorem tensorMinorant_hasSum {d : ℕ} (U L : ℤ → ℝ) (A B : ℝ)
    (hU : HasSum (fun n => (U n : ℂ)) (A : ℂ))
    (hL : HasSum (fun n => (L n : ℂ)) (B : ℂ)) :
    HasSum (fun n : Fin d → ℤ => tensorMinorant U L n)
      (A ^ d - d * (A - B) * A ^ (d - 1)) := by
  classical
  have hbase := hasSum_pi_prod (α := Fin d) (fun _ n => (U n : ℂ))
    (fun _ => (A : ℂ)) (fun _ => hU)
  have hterm (r : Fin d) := hasSum_pi_prod (α := Fin d)
    (fun i n => if i = r then (U n : ℂ) - L n else (U n : ℂ))
    (fun i => if i = r then (A : ℂ) - B else (A : ℂ))
    (fun i => by split <;> first | exact hU.sub hL | exact hU)
  have hterm' (r : Fin d) :
      HasSum (fun n : Fin d → ℤ =>
        ∏ i, if i = r then (U (n i) : ℂ) - L (n i) else (U (n i) : ℂ))
        (((A - B) * A ^ (d - 1) : ℝ) : ℂ) := by
    have h := hterm r
    simp only [mixed_prod, Finset.prod_const, Finset.card_erase_of_mem
      (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin] at h
    convert h using 1
    · funext n; exact mixed_prod _ _ _
    · push_cast; rfl
  have hsum := hasSum_sum (s := Finset.univ) (fun r _ => hterm' r)
  have h := hbase.sub hsum
  have hreal := Complex.hasSum_re h
  convert hreal using 1
  · funext n
    simp only [tensorMinorant, Complex.sub_re, Complex.re_sum]
    have hprod (f : Fin d → ℝ) : (∏ i, (f i : ℂ)).re = ∏ i, f i := by
      rw [← Complex.ofReal_prod]; rfl
    rw [hprod]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    have hp : (∏ i, if i = r then (U (n i) : ℂ) - L (n i) else (U (n i) : ℂ)) =
        ∏ i, ((if i = r then U (n i) - L (n i) else U (n i) : ℝ) : ℂ) := by
      apply Finset.prod_congr rfl
      intro i _
      split <;> simp
    rw [hp, hprod]
  · simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_const, nsmul_eq_mul]
    push_cast
    simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
    ring

private theorem tensorModulated_hasSum_zero {d : ℕ}
    (f : Fin d → ℤ → ℝ) (θ : Fin d → ℝ)
    (hcomp : ∀ i, Summable (fun n : ℤ => (f i n : ℂ) * echar (θ i) (n : ℝ)))
    (k : Fin d)
    (hk : HasSum (fun n : ℤ => (f k n : ℂ) * echar (θ k) (n : ℝ)) 0) :
    HasSum (fun n : Fin d → ℤ =>
      (∏ i, (f i (n i) : ℂ)) * Complex.exp
        (-2 * Real.pi * Complex.I * ∑ i, ((n i : ℤ) : ℂ) * θ i)) 0 := by
  let F : Fin d → ℤ → ℂ := fun i n => (f i n : ℂ) * echar (θ i) (n : ℝ)
  have h := hasSum_pi_prod F (fun i => if i = k then 0 else ∑' n, F i n)
    (fun i => by
      by_cases hik : i = k
      · subst i; simpa [F] using hk
      · simpa [hik, F] using (hcomp i).hasSum)
  have hz : (∏ i, if i = k then 0 else ∑' n, F i n) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  rw [hz] at h
  exact h.congr_fun (fun n => by
    have hp : (∏ i, echar (θ i) (n i : ℝ)) =
        Complex.exp (-2 * Real.pi * Complex.I * ∑ i, ((n i : ℤ) : ℂ) * θ i) := by
      simp only [echar, ← Complex.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring
    simp only [F, Finset.prod_mul_distrib, hp])

/-- A common vanishing coordinate of the two one-dimensional transforms
annihilates every mixed tensor term. -/
theorem tensorMinorantModulated_hasSum_zero {d : ℕ}
    (U L : ℤ → ℝ) (θ : Fin d → ℝ)
    (hU : ∀ i, Summable (fun n : ℤ => (U n : ℂ) * echar (θ i) (n : ℝ)))
    (hL : ∀ i, Summable (fun n : ℤ => (L n : ℂ) * echar (θ i) (n : ℝ)))
    (k : Fin d)
    (hUk : HasSum (fun n : ℤ => (U n : ℂ) * echar (θ k) (n : ℝ)) 0)
    (hLk : HasSum (fun n : ℤ => (L n : ℂ) * echar (θ k) (n : ℝ)) 0) :
    HasSum (fun n : Fin d → ℤ => (tensorMinorant U L n : ℂ) *
      Complex.exp (-2 * Real.pi * Complex.I * ∑ i, ((n i : ℤ) : ℂ) * θ i)) 0 := by
  classical
  have hbase := tensorModulated_hasSum_zero (fun _ => U) θ hU k hUk
  have hterm (r : Fin d) := tensorModulated_hasSum_zero
    (fun i n => if i = r then U n - L n else U n) θ
    (fun i => by
      by_cases hir : i = r
      · simpa [hir, sub_mul] using (hU i).sub (hL i)
      · simpa [hir] using hU i) k (by
      by_cases hkr : k = r
      · simpa [hkr, sub_mul] using hUk.sub hLk
      · simpa [hkr] using hUk)
  have hsum := hasSum_sum (s := Finset.univ) (fun r _ => hterm r)
  have h := hbase.sub hsum
  simp only [Finset.sum_const_zero, sub_zero] at h
  exact h.congr_fun (fun n => by
    simp only [tensorMinorant]
    push_cast
    rw [sub_mul, Finset.sum_mul])

end
end LeanNumDetect.LatticeSelbergMinorant
