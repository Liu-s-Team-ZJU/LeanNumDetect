import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Multiset.Fintype
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-!
# Matching roots along a polynomial homotopy

A finite union of compact root configurations supplies a closed partition of
polynomial evaluation functions. Connectedness of a homotopy preserves the
number of roots in each separated group, including algebraic multiplicity.
-/

noncomputable section
open scoped BigOperators
open Set Polynomial
namespace LeanNumDetect

/-- Equality of finite root multisets gives a permutation of the indexed lists. -/
theorem exists_perm_of_multiset_map_eq {n : ℕ} (a b : Fin n → ℂ)
    (h : Finset.univ.val.map a = Finset.univ.val.map b) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, a i = b (σ i) := by
  classical
  have hc (w : ℂ) : Fintype.card {i // a i = w} = Fintype.card {i // b i = w} := by
    have := congrArg (Multiset.count w) h
    simpa only [Multiset.count_map, Multiset.countP_eq_card_filter,
      ← Finset.filter_val, ← Finset.card_def, Fintype.card_subtype, eq_comm] using this
  let e (w : ℂ) := Fintype.equivOfCardEq (hc w)
  exact ⟨Equiv.ofFiberEquiv e, fun i => (Equiv.ofFiberEquiv_map e i).symm⟩

/-- The monic polynomial with an indexed root list, viewed as a continuous function. -/
def rootProduct {n : ℕ} (a : Fin n → ℂ) : ℂ → ℂ :=
  fun w => ∏ i, (w - a i)

theorem continuous_rootProduct {n : ℕ} : Continuous (@rootProduct n) := by
  unfold rootProduct
  fun_prop

/-- Equality of the polynomials preserves every root's multiplicity. -/
theorem rootProduct_eq_iff {n : ℕ} (a b : Fin n → ℂ) :
    rootProduct a = rootProduct b ↔
      ∃ σ : Equiv.Perm (Fin n), ∀ i, a i = b (σ i) := by
  classical
  constructor
  · intro h
    have hp : (∏ i, (X - C (a i))) = (∏ i, (X - C (b i))) := by
      apply Polynomial.funext
      intro w
      simpa [rootProduct, Polynomial.eval_prod] using congrFun h w
    have hr := congrArg Polynomial.roots hp
    have ha := Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map a)
    have hb := Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map b)
    have hmap : Finset.univ.val.map a = Finset.univ.val.map b := by
      simp only [Multiset.map_map, Function.comp_def] at ha hb
      exact ha.symm.trans (hr.trans hb)
    exact exists_perm_of_multiset_map_eq a b hmap
  · rintro ⟨σ, hσ⟩
    funext w
    exact (Finset.prod_congr rfl (fun i _ => congrArg (fun z => w - z) (hσ i))).trans
      (Equiv.prod_comp σ (fun i => w - b i))

/-- Root multiplicities cannot move between separated groups along a continuous
polynomial homotopy. The relation records the permitted groups of disc centers. -/
theorem rootProduct_homotopy_matching {n : ℕ}
    (a z : Fin n → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (R : Fin n → Fin n → Prop)
    (hrefl : ∀ i, R i i)
    (htrans : ∀ {i j k}, R i j → R j k → R i k)
    (hnear : ∀ i j w, dist w (a i) ≤ r → dist w (a j) ≤ r → R i j)
    (p : ℝ → ℂ → ℂ) (hp : ContinuousOn p (Icc 0 1))
    (hp0 : p 0 = rootProduct a) (hp1 : p 1 = rootProduct z)
    (hroots : ∀ t ∈ Icc (0 : ℝ) 1, ∃ b : Fin n → ℂ,
      p t = rootProduct b ∧ ∀ j, ∃ i, dist (b j) (a i) ≤ r) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, ∃ j,
      R i j ∧ dist (z (σ i)) (a j) ≤ r := by
  classical
  let C (c : Fin n → Fin n) : Set (Fin n → ℂ) :=
    {b | ∀ j, dist (b j) (a (c j)) ≤ r}
  have hC (c : Fin n → Fin n) : IsCompact (C c) := by
    convert isCompact_pi_infinite (fun j : Fin n => isCompact_closedBall (a (c j)) r) using 1
    ext b
    simp [C, Metric.mem_closedBall]
  let Good (c : Fin n → Fin n) : Prop :=
    ∃ σ : Equiv.Perm (Fin n), ∀ i, R i (c (σ i))
  let U : Set (ℂ → ℂ) := ⋃ c : {c // Good c}, rootProduct '' C c.val
  let V : Set (ℂ → ℂ) := ⋃ c : {c // ¬Good c}, rootProduct '' C c.val
  have hU : IsClosed U := by
    apply IsCompact.isClosed
    change IsCompact (⋃ c : {c // Good c}, rootProduct '' C c.val)
    apply isCompact_iUnion
    intro c
    exact (hC c.val).image (@continuous_rootProduct n)
  have hV : IsClosed V := by
    apply IsCompact.isClosed
    change IsCompact (⋃ c : {c // ¬Good c}, rootProduct '' C c.val)
    apply isCompact_iUnion
    intro c
    exact (hC c.val).image (@continuous_rootProduct n)
  have hdis : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro f hfU hfV
    obtain ⟨c, b, hb, hbf⟩ := Set.mem_iUnion.mp hfU
    obtain ⟨d, e, he, hef⟩ := Set.mem_iUnion.mp hfV
    obtain ⟨τ, hτ⟩ := (rootProduct_eq_iff b e).mp (hbf.trans hef.symm)
    obtain ⟨σ, hσ⟩ := c.property
    apply d.property
    refine ⟨σ.trans τ, fun i => htrans (hσ i) ?_⟩
    exact hnear _ _ (b (σ i)) (hb (σ i)) (by rw [hτ]; exact he (τ (σ i)))
  have hcover : p '' Icc (0 : ℝ) 1 ⊆ U ∪ V := by
    rintro f ⟨t, ht, rfl⟩
    obtain ⟨b, hpb, hb⟩ := hroots t ht
    choose c hc using hb
    by_cases hgood : Good c
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨c, hgood⟩, b, hc, hpb.symm⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨c, hgood⟩, b, hc, hpb.symm⟩)
  have hzero : p 0 ∈ U := by
    refine Set.mem_iUnion.mpr ⟨⟨id, Equiv.refl _, hrefl⟩, a, ?_, hp0.symm⟩
    intro j
    simpa using hr
  have hone : p 1 ∈ U := by
    by_contra hnot
    have h1 : p 1 ∈ p '' Icc (0 : ℝ) 1 := ⟨1, by simp, rfl⟩
    have hbad := (hcover h1).resolve_left hnot
    have hconnected := isPreconnected_Icc.image p hp
    obtain ⟨f, _, hf⟩ := isPreconnected_closed_iff.mp hconnected U V hU hV hcover
      ⟨p 0, ⟨0, by simp, rfl⟩, hzero⟩ ⟨p 1, h1, hbad⟩
    exact Set.disjoint_left.mp hdis hf.1 hf.2
  obtain ⟨c, b, hb, hbp⟩ := Set.mem_iUnion.mp hone
  obtain ⟨τ, hτ⟩ := (rootProduct_eq_iff b z).mp (hbp.trans hp1)
  obtain ⟨σ, hσ⟩ := c.property
  refine ⟨σ.trans τ, fun i => ⟨c.val (σ i), hσ i, ?_⟩⟩
  change dist (z (τ (σ i))) (a (c.val (σ i))) ≤ r
  rw [← hτ]
  exact hb (σ i)

end LeanNumDetect
