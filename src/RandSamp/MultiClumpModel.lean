import RandSamp.RandomModel
import General.Finite.PeriodicClumpLift
import MathExtras.NumberTheory.Analysis.LargeSieveInequality

/-!
Exact geometric and combinatorial data for a fixed one-dimensional multiclump
Fourier support.  Angles are measured in radians on `ℝ/(2πℤ)`.  Arbitrary real
representatives are permitted; none of the hypotheses depends on their lifts.

The manuscript's clumps are the fibers of a surjective label map.  In
particular, every clump is nonempty and every node belongs to exactly one
clump.  `HasMaxClumpSize` records both the upper bound and attainment of the
maximum, which is needed for the smallest-singular-value upper estimate.
-/

set_option autoImplicit false

open scoped BigOperators

namespace LeanNumDetect.RandSamp

noncomputable section

open MathExtras.NumberTheory.Analysis.LargeSieve

/-- Angular distance on `ℝ/(2πℤ)`, defined through nearest-integer distance.
This agrees with `min_{p ∈ ℤ} |x - y + 2πp|`; the equivalence with the
lower-bound characterization is proved below. -/
def angularTorusDistance (x y : ℝ) : ℝ :=
  2 * Real.pi * circleDist (x / (2 * Real.pi)) (y / (2 * Real.pi))

theorem angularTorusDistance_nonneg (x y : ℝ) :
    0 ≤ angularTorusDistance x y := by
  exact mul_nonneg (by positivity) (circleDist_nonneg _ _)

theorem angularTorusDistance_le_winding (x y : ℝ) (p : ℤ) :
    angularTorusDistance x y ≤ |x - y + 2 * Real.pi * p| := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have h := circleDist_le_int (x / (2 * Real.pi)) (y / (2 * Real.pi)) (-p)
  have he : x / (2 * Real.pi) - y / (2 * Real.pi) - ((-p : ℤ) : ℝ) =
      (x - y + 2 * Real.pi * p) / (2 * Real.pi) := by
    push_cast
    field_simp
    ring
  rw [he, abs_div, abs_of_pos hπ] at h
  have := mul_le_mul_of_nonneg_left h hπ.le
  simpa only [angularTorusDistance, mul_div_cancel₀ _ hπ.ne'] using this

/-- The minimum winding distance is achieved, rather than merely an infimum. -/
theorem angularTorusDistance_eq_winding (x y : ℝ) :
    ∃ p : ℤ, angularTorusDistance x y = |x - y + 2 * Real.pi * p| := by
  refine ⟨-round (x / (2 * Real.pi) - y / (2 * Real.pi)), ?_⟩
  have hπ : 0 < 2 * Real.pi := by positivity
  unfold angularTorusDistance circleDist
  rw [show 2 * Real.pi *
      |x / (2 * Real.pi) - y / (2 * Real.pi) -
        (round (x / (2 * Real.pi) - y / (2 * Real.pi)) : ℝ)| =
      |2 * Real.pi * (x / (2 * Real.pi) - y / (2 * Real.pi) -
        (round (x / (2 * Real.pi) - y / (2 * Real.pi)) : ℝ))| by
    rw [abs_mul, abs_of_pos hπ]]
  congr 1
  push_cast
  field_simp
  ring

/-- A lower bound for the angular distance is exactly a lower bound for every
integer winding.  This matches the existing angular separation convention. -/
theorem le_angularTorusDistance_iff (x y r : ℝ) :
    r ≤ angularTorusDistance x y ↔
      ∀ p : ℤ, r ≤ |x - y + 2 * Real.pi * p| := by
  constructor
  · intro h p
    exact h.trans (angularTorusDistance_le_winding x y p)
  · intro h
    obtain ⟨p, hp⟩ := angularTorusDistance_eq_winding x y
    rw [hp]
    exact h p

/-- An upper bound for the angular distance is exactly existence of a short
integer winding; this is the hypothesis used by the clump-lifting lemma. -/
theorem angularTorusDistance_le_iff (x y r : ℝ) :
    angularTorusDistance x y ≤ r ↔
      ∃ p : ℤ, |x - y + 2 * Real.pi * p| ≤ r := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := angularTorusDistance_eq_winding x y
    exact ⟨p, hp ▸ h⟩
  · rintro ⟨p, hp⟩
    exact (angularTorusDistance_le_winding x y p).trans hp

theorem angularTorusDistance_comm (x y : ℝ) :
    angularTorusDistance x y = angularTorusDistance y x := by
  apply le_antisymm
  · apply (le_angularTorusDistance_iff _ _ _).2
    intro p
    have h := angularTorusDistance_le_winding x y (-p)
    have he : x - y + 2 * Real.pi * ((-p : ℤ) : ℝ) =
        -(y - x + 2 * Real.pi * p) := by push_cast; ring
    simpa only [he, abs_neg] using h
  · apply (le_angularTorusDistance_iff _ _ _).2
    intro p
    have h := angularTorusDistance_le_winding y x (-p)
    have he : y - x + 2 * Real.pi * ((-p : ℤ) : ℝ) =
        -(x - y + 2 * Real.pi * p) := by push_cast; ring
    simpa only [he, abs_neg] using h

@[simp] theorem angularTorusDistance_self (x : ℝ) :
    angularTorusDistance x x = 0 := by
  apply le_antisymm
  · simpa using angularTorusDistance_le_winding x x 0
  · exact angularTorusDistance_nonneg x x

theorem angularTorusDistance_le_pi (x y : ℝ) :
    angularTorusDistance x y ≤ Real.pi := by
  obtain ⟨p, hp⟩ := LeanNumDetect.exists_periodic_gap_le_pi (x - y)
  exact (angularTorusDistance_le_winding x y (-p)).trans
    (by simpa only [Int.cast_neg, mul_neg, ← sub_eq_add_neg] using hp)

theorem angularTorusDistance_eq_zero_iff (x y : ℝ) :
    angularTorusDistance x y = 0 ↔
      ∃ p : ℤ, x - y + 2 * Real.pi * p = 0 := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := angularTorusDistance_eq_winding x y
    exact ⟨p, abs_eq_zero.mp (hp.symm.trans h)⟩
  · rintro ⟨p, hp⟩
    apply le_antisymm
    · simpa only [hp, abs_zero] using angularTorusDistance_le_winding x y p
    · exact angularTorusDistance_nonneg x y

/-- Changing a source representative by an integral turn preserves distance. -/
theorem angularTorusDistance_add_winding_left (x y : ℝ) (q : ℤ) :
    angularTorusDistance (x + 2 * Real.pi * q) y = angularTorusDistance x y := by
  apply le_antisymm
  · apply (le_angularTorusDistance_iff _ _ _).2
    intro p
    have h := angularTorusDistance_le_winding (x + 2 * Real.pi * q) y (p - q)
    have he : x + 2 * Real.pi * q - y + 2 * Real.pi * ((p - q : ℤ) : ℝ) =
        x - y + 2 * Real.pi * p := by push_cast; ring
    simpa only [he] using h
  · apply (le_angularTorusDistance_iff _ _ _).2
    intro p
    have h := angularTorusDistance_le_winding x y (p + q)
    have he : x - y + 2 * Real.pi * ((p + q : ℤ) : ℝ) =
        x + 2 * Real.pi * q - y + 2 * Real.pi * p := by push_cast; ring
    simpa only [he] using h

theorem angularTorusDistance_add_winding_right (x y : ℝ) (q : ℤ) :
    angularTorusDistance x (y + 2 * Real.pi * q) = angularTorusDistance x y := by
  rw [angularTorusDistance_comm, angularTorusDistance_add_winding_left,
    angularTorusDistance_comm]

/-- A short clump in angular distance has real lifts with the same ordinary
diameter bound.  This is a proved adaptation of the shared lifting lemma. -/
theorem angular_short_clump_lift {q : ℕ} (hq : 0 < q) (Y : Fin q → ℝ)
    {w : ℝ} (hw : 0 ≤ w) (hshort : 3 * w < 2 * Real.pi)
    (hpair : ∀ i j, angularTorusDistance (Y i) (Y j) ≤ w) :
    ∃ p : Fin q → ℤ,
      Metric.diam (Set.range (fun j => Y j - 2 * Real.pi * p j)) ≤ w := by
  apply LeanNumDetect.periodic_clump_lift hq Y hw hshort
  intro i j
  obtain ⟨p, hp⟩ := (angularTorusDistance_le_iff _ _ _).1 (hpair i j)
  exact ⟨-p, by simpa only [Int.cast_neg, mul_neg, sub_neg_eq_add] using hp⟩

/-- A partition of `n` labeled sources into `A` nonempty clumps. -/
structure ClumpPartition (n A : ℕ) where
  label : Fin n → Fin A
  surjective : Function.Surjective label

namespace ClumpPartition

variable {n A : ℕ} (P : ClumpPartition n A)

/-- The source indices of a clump. -/
def members (a : Fin A) : Finset (Fin n) :=
  Finset.univ.filter (fun j => P.label j = a)

/-- Number of sources in a clump. -/
def size (a : Fin A) : ℕ := (P.members a).card

/-- The deterministic size parameter in the random sampling rate. -/
def sizeSquareSum : ℕ := ∑ a : Fin A, P.size a ^ 2

@[simp] theorem mem_members (a : Fin A) (j : Fin n) :
    j ∈ P.members a ↔ P.label j = a := by
  simp [members]

theorem members_nonempty (a : Fin A) : (P.members a).Nonempty := by
  obtain ⟨j, hj⟩ := P.surjective a
  exact ⟨j, (P.mem_members a j).2 hj⟩

theorem size_pos (a : Fin A) : 0 < P.size a :=
  Finset.card_pos.mpr (P.members_nonempty a)

theorem size_le_n (a : Fin A) : P.size a ≤ n := by
  simpa [size] using Finset.card_le_card (P.members a).subset_univ

/-- Exact cardinality identity for the disjoint exhaustive clumps. -/
theorem sum_sizes : ∑ a : Fin A, P.size a = n := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin n)) (Finset.univ : Finset (Fin A)) P.label
  simpa [size, members] using h

include P in
/-- The number of nonempty clumps cannot exceed the number of sources. -/
theorem clump_count_le : A ≤ n := by
  calc
    A = ∑ _a : Fin A, 1 := by simp
    _ ≤ ∑ a : Fin A, P.size a :=
      Finset.sum_le_sum fun a _ => P.size_pos a
    _ = n := P.sum_sizes

/-- Every nonempty clump contributes at least its size to the squared sum. -/
theorem n_le_sizeSquareSum : n ≤ P.sizeSquareSum := by
  calc
    n = ∑ a : Fin A, P.size a := P.sum_sizes.symm
    _ ≤ P.sizeSquareSum := by
      apply Finset.sum_le_sum
      intro a _
      have hp := P.size_pos a
      nlinarith

/-- The sum of squared clump sizes is at most `n` times any upper bound on
the clump size, with no geometric or spacing hypothesis. -/
theorem sizeSquareSum_le {nstar : ℕ} (hsize : ∀ a, P.size a ≤ nstar) :
    P.sizeSquareSum ≤ n * nstar := by
  calc
    P.sizeSquareSum ≤ ∑ a : Fin A, P.size a * nstar := by
      apply Finset.sum_le_sum
      intro a _
      simpa only [pow_two] using Nat.mul_le_mul_left (P.size a) (hsize a)
    _ = (∑ a : Fin A, P.size a) * nstar := (Finset.sum_mul _ _ _).symm
    _ = n * nstar := by rw [P.sum_sizes]

theorem sizeSquareSum_le_real {nstar : ℕ} (hsize : ∀ a, P.size a ≤ nstar) :
    (P.sizeSquareSum : ℝ) ≤ (n : ℝ) * (nstar : ℝ) := by
  exact_mod_cast P.sizeSquareSum_le hsize

end ClumpPartition

/-- Exact maximum clump size, including an attaining clump. -/
def HasMaxClumpSize {n A : ℕ} (P : ClumpPartition n A) (nstar : ℕ) : Prop :=
  (∀ a, P.size a ≤ nstar) ∧ ∃ a, P.size a = nstar

/-- Distinct torus sources, independently of their chosen real lifts. -/
def DistinctAngularNodes {n : ℕ} (Y : Fin n → ℝ) : Prop :=
  ∀ i j, i ≠ j → ∀ p : ℤ, Y i - Y j + 2 * Real.pi * p ≠ 0

theorem distinctAngularNodes_iff_distance_pos {n : ℕ} (Y : Fin n → ℝ) :
    DistinctAngularNodes Y ↔
      ∀ i j, i ≠ j → 0 < angularTorusDistance (Y i) (Y j) := by
  constructor
  · intro h i j hij
    apply lt_of_le_of_ne (angularTorusDistance_nonneg _ _)
    intro hz
    obtain ⟨p, hp⟩ := (angularTorusDistance_eq_zero_iff _ _).1 hz.symm
    exact h i j hij p hp
  · intro h i j hij p hp
    have hz := (angularTorusDistance_eq_zero_iff _ _).2 ⟨p, hp⟩
    exact (h i j hij).ne' hz

/-- Geometry of a fixed multiclump source set at measurement bandwidth `M`.
The constants' positivity and admissible ranges belong in the theorem's
outer quantifiers, rather than being hidden in this geometric predicate. -/
structure MultiClumpGeometry {n A : ℕ} (M : ℕ) (c0 C0 : ℝ)
    (Y : Fin n → ℝ) (P : ClumpPartition n A) : Prop where
  distinct : DistinctAngularNodes Y
  within : ∀ i j, P.label i = P.label j →
    angularTorusDistance (Y i) (Y j) ≤ c0 / (M : ℝ)
  between : ∀ i j, P.label i ≠ P.label j →
    C0 / (M : ℝ) ≤ angularTorusDistance (Y i) (Y j)

/-- All distinct pairs inside every clump have distances in `[Δ,KΔ]`.
Singleton clumps impose no additional condition. -/
def ComparableClumpSpacing {n A : ℕ} (P : ClumpPartition n A)
    (Y : Fin n → ℝ) (Δ K : ℝ) : Prop :=
  ∀ i j, i ≠ j → P.label i = P.label j →
    Δ ≤ angularTorusDistance (Y i) (Y j) ∧
      angularTorusDistance (Y i) (Y j) ≤ K * Δ

theorem hasMaxClumpSize_squareSum_le {n A nstar : ℕ}
    {P : ClumpPartition n A} (hmax : HasMaxClumpSize P nstar) :
    P.sizeSquareSum ≤ n * nstar := P.sizeSquareSum_le hmax.1

theorem hasMaxClumpSize_le_n {n A nstar : ℕ}
    {P : ClumpPartition n A} (hmax : HasMaxClumpSize P nstar) : nstar ≤ n := by
  obtain ⟨a, ha⟩ := hmax.2
  rw [← ha]
  exact P.size_le_n a

theorem hasMaxClumpSize_squareSum_le_real {n A nstar : ℕ}
    {P : ClumpPartition n A} (hmax : HasMaxClumpSize P nstar) :
    (P.sizeSquareSum : ℝ) ≤ (n : ℝ) * (nstar : ℝ) :=
  P.sizeSquareSum_le_real hmax.1

end

end LeanNumDetect.RandSamp
