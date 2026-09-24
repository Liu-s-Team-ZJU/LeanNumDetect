import NumDetect.Basic
import General.Fourier.FineCubeFrame
import General.Fourier.TranslatedCubeFourier
import General.Fourier.TrigonometricPolynomialParseval
import NumDetect.Matrices
import NumDetect.UniformInterpolation
import SegmentedVDM.Interpolation
import SegmentedVDM.UniformFrame
import SegmentedVDM.UniformInterpolation
import Mathlib.LinearAlgebra.Matrix.Rank
import NumDetect.Segmented.Polynomial
import NumDetect.Segmented.NeighborFactors

/-!
The partition of an arbitrary nonempty subset of clumped nodes into at most
`nStar` separated classes (manuscript Proposition `prop:decomposition`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- A bounded clump size gives a slot in `Fin nStar` for every node, injective
within each clump. -/
private theorem exists_clump_slot
    {n A nStar : ℕ} (label : Fin n → Fin A)
    (hsize : ∀ a, (Finset.univ.filter fun j => label j = a).card ≤ nStar) :
    ∃ slot : Fin n → Fin nStar,
      ∀ i j, label i = label j → slot i = slot j → i = j := by
  classical
  let S (a : Fin A) := {j : Fin n // label j = a}
  have hc (a : Fin A) : Fintype.card (S a) ≤ Fintype.card (Fin nStar) := by
    simpa [S, Fintype.card_subtype] using hsize a
  let e (a : Fin A) : S a ↪ Fin nStar :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (hc a))
  let slot (j : Fin n) := e (label j) ⟨j, rfl⟩
  refine ⟨slot, ?_⟩
  intro i j hl hs
  change e (label i) ⟨i, rfl⟩ = e (label j) ⟨j, rfl⟩ at hs
  have transport (a b : Fin A) (hab : a = b) (u : Fin n)
      (hu : label u = a) :
      e a ⟨u, hu⟩ = e b ⟨u, hu.trans hab⟩ := by
    subst b
    rfl
  have hs' : e (label j) ⟨i, hl⟩ = e (label j) ⟨j, rfl⟩ :=
    (transport (label i) (label j) hl i rfl).symm.trans hs
  exact congrArg Subtype.val ((e (label j)).injective hs')

/-- Manuscript Proposition `prop:decomposition`. Every nonempty subset of
clumped nodes has a partition into between one and `nStar` nonempty classes;
distinct nodes in each class have periodic `ℓ∞` distance greater than `η`.
The subset is represented by its finite node indices. -/
theorem angularClump_decomposition
    {d n A nStar : ℕ} {x : Fin n → Point d} {τ η : ℝ}
    (hclumps : IsAngularClumpStructure x A nStar τ η)
    (Y : Finset (Fin n)) (hY : Y.Nonempty) :
    ∃ (ν : ℕ) (pieces : Fin ν → Finset (Fin n)),
      1 ≤ ν ∧ ν ≤ nStar ∧
      (∀ ℓ, (pieces ℓ).Nonempty) ∧
      (∀ ℓ k, ℓ ≠ k → Disjoint (pieces ℓ) (pieces k)) ∧
      Y = Finset.univ.biUnion pieces ∧
      (∀ ℓ i j, i ∈ pieces ℓ → j ∈ pieces ℓ → i ≠ j →
        η < periodicLInfDistance (x i) (x j)) := by
  classical
  obtain ⟨_hnStar, _hτ, _hτη, _hcube, label, _hsurj,
    hsize, _hmax, _hwithin, hcross⟩ := hclumps
  obtain ⟨slot, hslot⟩ := exists_clump_slot label hsize
  let Used := {c : Fin nStar // ∃ j ∈ Y, slot j = c}
  let ν := Fintype.card Used
  have hνpos : 1 ≤ ν := by
    obtain ⟨j, hj⟩ := hY
    have : Nonempty Used := ⟨⟨slot j, j, hj, rfl⟩⟩
    exact Fintype.card_pos_iff.mpr this
  have hνle : ν ≤ nStar := by
    simpa [ν] using
      (Fintype.card_le_of_injective (Subtype.val : Used → Fin nStar)
        Subtype.val_injective)
  let e : Fin ν ≃ Used :=
    (Fintype.equivFinOfCardEq (by simp [ν])).symm
  let pieces (ℓ : Fin ν) : Finset (Fin n) :=
    Y.filter fun j => slot j = (e ℓ).val
  have hmem (ℓ : Fin ν) (j : Fin n) :
      j ∈ pieces ℓ ↔ j ∈ Y ∧ slot j = (e ℓ).val := by
    simp [pieces]
  refine ⟨ν, pieces, hνpos, hνle, ?_, ?_, ?_, ?_⟩
  · intro ℓ
    obtain ⟨j, hj, hslotj⟩ := (e ℓ).property
    exact ⟨j, (hmem ℓ j).mpr ⟨hj, hslotj⟩⟩
  · intro ℓ k hne
    apply Finset.disjoint_left.mpr
    intro j hjℓ hjk
    have heq : e ℓ = e k := Subtype.ext
      (((hmem ℓ j).mp hjℓ).2.symm.trans (((hmem k j).mp hjk).2))
    exact hne (e.injective heq)
  · ext j
    constructor
    · intro hj
      let c : Used := ⟨slot j, j, hj, rfl⟩
      refine Finset.mem_biUnion.mpr ⟨e.symm c, Finset.mem_univ _, ?_⟩
      exact (hmem (e.symm c) j).mpr ⟨hj, by simp [c]⟩
    · intro hj
      obtain ⟨ℓ, _hℓ, hjℓ⟩ := Finset.mem_biUnion.mp hj
      exact ((hmem ℓ j).mp hjℓ).1
  · intro ℓ i j hi hj hij
    apply hcross i j
    intro hl
    apply hij
    apply hslot i j hl
    exact ((hmem ℓ i).mp hi).2.trans ((hmem ℓ j).mp hj).2.symm

end
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
theorem withinClumpPolynomial
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
    ∃ P : SegmentedPolynomial d 0 (r - r / nStar) D,
      (∀ j, C.label j = C.label anchor →
        P.angularValue (x j) = if anchor = j then 1 else 0) ∧
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
    SegmentedPolynomial.segmentedNeighborProduct hT hD hΔ u hΔu hu hscale'
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
  let P : SegmentedPolynomial d 0 (r - r / nStar) D :=
    (B.translate (x anchor)).widen le_rfl hcoarse hD
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
    simp only [P, SegmentedPolynomial.angularValue_widen,
      SegmentedPolynomial.angularValue_translate]
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
        B.angularValue
          (wrappedDifference (x (e (e.symm j'))) (x anchor)) = 0 at hz
      rw [he] at hz
      rw [SegmentedPolynomial.angularValue_sub_eq_wrappedDifference, hz]
  · simp only [P, SegmentedPolynomial.mass_widen,
      SegmentedPolynomial.mass_translate]
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
theorem fineCube_cardinalPolynomial
    {d K D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hKD : K < D)
    (x : ι → Point d) (j : ι) {a : ℝ} (ha : 0 < a)
    (hframe : ∀ v,
      a * (((K + 1) ^ d : ℕ) : ℝ) * SegmentedVDM.energy v ≤
        SegmentedVDM.energy (fineCubeEvaluation K x *ᵥ v)) :
    ∃ P : SegmentedPolynomial d K 0 D,
      (∀ k, P.angularValue (x k) = if j = k then 1 else 0) ∧
      P.mass ≤ 1 / Real.sqrt a := by
  obtain ⟨c, hc, hcnorm⟩ :=
    SegmentedVDM.cardinal_coefficients_of_frame (fineCubeEvaluation K x)
      (show 0 < a * (((K + 1) ^ d : ℕ) : ℝ) by positivity)
      (by
        intro v
        simpa only [mul_assoc] using hframe v)
      j
  let P : SegmentedPolynomial d K 0 D :=
    SegmentedPolynomial.ofFineCube hKD c
  refine ⟨P, ?_, ?_⟩
  · intro k
    convert! hc k using 1
    simp [P, SegmentedPolynomial.angularValue_ofFineCube,
      fineCubeEvaluation, dotProduct]
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
      simpa [P, SegmentedPolynomial.mass_ofFineCube] using hs.trans h
    have he : (1 / Real.sqrt a) ^ 2 = 1 / a := by
      rw [div_pow, one_pow, Real.sq_sqrt ha.le]
    exact (sq_le_sq₀ P.mass_nonneg (by positivity)).mp (by rwa [he])

end
end NumDetect
end LeanNumDetect
