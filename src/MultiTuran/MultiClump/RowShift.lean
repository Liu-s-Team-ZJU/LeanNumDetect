import MultiTuran.FullAperture.FullAperture
import MultiTuran.Preliminaries.Translation
import MultiTuran.Norming.ProductDiscretization

/-! # Arbitrary common translations of the measured row frequencies

A common row translation multiplies the source coefficients by a unitary
diagonal phase. Thus it preserves the least column singular value, including
when the translated rows do not start at zero.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

theorem exponentialSum_phaseCoefficients {d n : ℕ} (Y : Fin n → Point d)
    (c : Fin n → ℂ) (a t : Point d) :
    exponentialSum Y (phaseCoefficients Y c a) t = exponentialSum Y c (t+a) := by
  unfold exponentialSum phaseCoefficients
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  have hsum : (∑ q, a q*Y j q)+(∑ q, t q*Y j q) =
      ∑ q, (t+a) q*Y j q := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    simp only [Pi.add_apply]
    ring
  rw [← mul_add, ← Complex.ofReal_add, hsum]

theorem vandermonde_rowShift_energy_lower {ι : Type*} [Fintype ι] {d n : ℕ}
    (frequency : ι → Point d) (Y : Fin n → Point d) (hn : 0 < n)
    (a : Point d) (c : Fin n → ℂ) :
    matrixSingularValue (vandermondeMatrix frequency Y) (n-1)^2*(∑ j, ‖c j‖^2) ≤
      ∑ k, ‖exponentialSum Y c (frequency k+a)‖^2 := by
  let z : EuclideanSpace ℂ (Fin n) := toLp 2 (phaseCoefficients Y c a)
  have h := lastMatrixSingularValue_mul_norm_le (vandermondeMatrix frequency Y)
    (by simpa using hn) z
  have hs := (sq_le_sq₀
    (mul_nonneg ((vandermondeMatrix frequency Y).toEuclideanLin.singularValues_nonneg _)
      (norm_nonneg z)) (norm_nonneg _)).mpr h
  have hz : ‖z‖^2 = ∑ j, ‖c j‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [z,norm_phaseCoefficients]
  have hnorm : ‖(vandermondeMatrix frequency Y).toEuclideanLin z‖^2 =
      ∑ k, ‖exponentialSum Y c (frequency k+a)‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ k, ‖(vandermondeMatrix frequency Y *ᵥ phaseCoefficients Y c a) k‖^2) = _
    simp only [vandermondeMatrix_mulVec,exponentialSum_phaseCoefficients]
  rw [mul_pow,hz,hnorm] at hs
  simpa only [Fintype.card_fin,matrixSingularValue] using hs

theorem minimumSingularValue_le_rowShift {ι : Type*} [Fintype ι] {d n : ℕ}
    (frequency : ι → Point d) (Y : Fin n → Point d) (hn : 0 < n) (a : Point d) :
    matrixSingularValue (vandermondeMatrix frequency Y) (n-1) ≤
      matrixSingularValue (vandermondeMatrix (fun k => frequency k+a) Y) (n-1) := by
  apply minimumSingularValue_ge_of_energy_lower _ hn
    ((vandermondeMatrix frequency Y).toEuclideanLin.singularValues_nonneg _)
  intro c
  have h := vandermonde_rowShift_energy_lower frequency Y hn a c
  have he : (∑ k, ‖∑ j, vandermondeMatrix (fun k => frequency k+a) Y k j*c j‖^2) =
      ∑ k, ‖exponentialSum Y c (frequency k+a)‖^2 := by
    apply Finset.sum_congr rfl
    intro k _
    change ‖(vandermondeMatrix (fun k => frequency k+a) Y *ᵥ c) k‖^2 = _
    rw [vandermondeMatrix_mulVec]
  rw [he]
  exact h

theorem minimumSingularValue_rowShift {ι : Type*} [Fintype ι] {d n : ℕ}
    (frequency : ι → Point d) (Y : Fin n → Point d) (hn : 0 < n) (a : Point d) :
    matrixSingularValue (vandermondeMatrix (fun k => frequency k+a) Y) (n-1) =
      matrixSingularValue (vandermondeMatrix frequency Y) (n-1) := by
  apply le_antisymm
  · have h := minimumSingularValue_le_rowShift (fun k => frequency k+a) Y hn (-a)
    simpa only [add_neg_cancel_right] using h
  · exact minimumSingularValue_le_rowShift frequency Y hn a

/-- The actual shifted row matrix has precisely the original least singular
value. This applies to every nonzero starting position of a product row set. -/
theorem generalizedVandermonde_rowShift_minimumSingularValue {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (hn : 0 < n) (a : Point d) :
    matrixSingularValue (vandermondeMatrix (fun k : G.Row => G.rowPoint k+a) Y) (n-1) =
      matrixSingularValue (generalizedVandermonde G Y) (n-1) :=
  minimumSingularValue_rowShift G.rowPoint Y hn a

private theorem first_start_le {r : ℕ} (a l : Fin (r+1) → ℕ)
    (hseparated : ∀ i j : Fin (r+1), i < j → a i+l i+1 ≤ a j)
    (m : Fin (r+1)) : a 0 ≤ a m := by
  by_cases hm : m = 0
  · rw [hm]
  · have hlt : (0 : Fin (r+1)) < m := by
      have hval : m.val ≠ 0 := by intro h; exact hm (Fin.ext h)
      change 0 < m.val
      omega
    have h := hseparated 0 m hlt
    omega

/-- Normalize arbitrary nonzero block starts by their first starting point.
No rows are discarded, inserted, or merged. -/
def normalizedProductGrid {d : ℕ} (hd : 0 < d) (r : Fin d → ℕ)
    (a l : (q : Fin d) → Fin (r q+1) → ℕ)
    (hseparated : ∀ q (i j : Fin (r q+1)), i < j → a q i+l q i+1 ≤ a q j) :
    SegmentedGrid d where
  dimension_pos := hd
  blockCount := r
  start := fun q m => a q m-a q 0
  length := l
  start_zero := by intro q; simp
  separated := by
    intro q i j hij
    have hi := first_start_le (a q) (l q) (hseparated q) i
    have hj := first_start_le (a q) (l q) (hseparated q) j
    have h := hseparated q i j hij
    omega

@[simp] theorem normalizedProductGrid_start_add {d : ℕ} (hd : 0 < d)
    (r : Fin d → ℕ) (a l : (q : Fin d) → Fin (r q+1) → ℕ)
    (hseparated : ∀ q (i j : Fin (r q+1)), i < j → a q i+l q i+1 ≤ a q j)
    (q : Fin d) (m : Fin (r q+1)) :
    (normalizedProductGrid hd r a l hseparated).start q m+a q 0 = a q m :=
  Nat.sub_add_cancel (first_start_le (a q) (l q) (hseparated q) m)

@[simp] theorem normalizedProductGrid_thickLength {d : ℕ} (hd : 0 < d)
    (r : Fin d → ℕ) (a l : (q : Fin d) → Fin (r q+1) → ℕ)
    (hseparated : ∀ q (i j : Fin (r q+1)), i < j → a q i+l q i+1 ≤ a q j)
    (q : Fin d) (m : Fin (r q+1)) :
    (normalizedProductGrid hd r a l hseparated).thickLength q m = l q m+1 := rfl

/-- A full enclosing box with any prescribed positive integer side lengths.
Its auxiliary sampled rows are never used in the general product theorem. -/
def enclosingBoxGrid {d : ℕ} (hd : 0 < d) (N : Fin d → ℕ)
    (_hN : ∀ q, 0 < N q) : SegmentedGrid d where
  dimension_pos := hd
  blockCount := fun _ => 0
  start := fun _ _ => 0
  length := fun q _ => N q-1
  start_zero := fun _ => rfl
  separated := by
    intro q i j hij
    have he : i = j := by
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      omega
    exact False.elim ((ne_of_lt hij) he)

@[simp] theorem enclosingBoxGrid_aperture {d : ℕ} (hd : 0 < d)
    (N : Fin d → ℕ) (hN : ∀ q, 0 < N q) (q : Fin d) :
    (enclosingBoxGrid hd N hN).aperture q = N q := by
  change 0+(N q-1)+1 = N q
  have h := hN q
  omega

@[simp] theorem normalizedProductGrid_aperture_add {d : ℕ} (hd : 0 < d)
    (r : Fin d → ℕ) (a l : (q : Fin d) → Fin (r q+1) → ℕ)
    (hseparated : ∀ q (i j : Fin (r q+1)), i < j → a q i+l q i+1 ≤ a q j)
    (q : Fin d) :
    (normalizedProductGrid hd r a l hseparated).aperture q+a q 0 =
      a q ⟨r q, by omega⟩+l q ⟨r q, by omega⟩+1 := by
  have h := normalizedProductGrid_start_add hd r a l hseparated q ⟨r q, by omega⟩
  change (a q ⟨r q, by omega⟩-a q 0)+a q 0 = _ at h
  change (a q ⟨r q, by omega⟩-a q 0)+l q ⟨r q, by omega⟩+1+a q 0 = _
  omega

theorem normalizedProductGrid_le_enclosingBoxGrid {d : ℕ} (hd : 0 < d)
    (r : Fin d → ℕ) (a l : (q : Fin d) → Fin (r q+1) → ℕ)
    (hseparated : ∀ q (i j : Fin (r q+1)), i < j → a q i+l q i+1 ≤ a q j)
    (N : Fin d → ℕ) (hN : ∀ q, 0 < N q)
    (hlast : ∀ q, a q ⟨r q, by omega⟩+l q ⟨r q, by omega⟩+1 ≤ N q)
    (q : Fin d) :
    (normalizedProductGrid hd r a l hseparated).aperture q ≤
      (enclosingBoxGrid hd N hN).aperture q := by
  rw [enclosingBoxGrid_aperture]
  have h := normalizedProductGrid_aperture_add hd r a l hseparated q
  have hq := hlast q
  omega

/-- Exact row-set identity after normalization of arbitrary starting points. -/
theorem mem_normalizedProductGrid_rows {d : ℕ} (hd : 0 < d)
    (r : Fin d → ℕ) (a l : (q : Fin d) → Fin (r q+1) → ℕ)
    (hseparated : ∀ q (i j : Fin (r q+1)), i < j → a q i+l q i+1 ≤ a q j)
    (q : Fin d) (t : ℕ) :
    t ∈ (normalizedProductGrid hd r a l hseparated).coordinateRows q ↔
      ∃ m : Fin (r q+1), a q m ≤ t+a q 0 ∧ t+a q 0 ≤ a q m+l q m := by
  let G := normalizedProductGrid hd r a l hseparated
  change t ∈ G.coordinateRows q ↔ _
  rw [G.mem_coordinateRows]
  constructor
  · rintro ⟨m,hm⟩
    obtain ⟨hlo,hhi⟩ := (G.mem_blockRows q m t).mp hm
    have hstart := normalizedProductGrid_start_add hd r a l hseparated q m
    change a q m-a q 0+a q 0 = a q m at hstart
    change a q m-a q 0 ≤ t at hlo
    change t ≤ a q m-a q 0+l q m at hhi
    exact ⟨m,by omega,by omega⟩
  · rintro ⟨m,hlo,hhi⟩
    have hstart := normalizedProductGrid_start_add hd r a l hseparated q m
    change a q m-a q 0+a q 0 = a q m at hstart
    refine ⟨m,(G.mem_blockRows q m t).mpr ?_⟩
    change a q m-a q 0 ≤ t ∧ t ≤ a q m-a q 0+l q m
    omega

end
end LeanNumDetect.MultiTuran.MultiClump
