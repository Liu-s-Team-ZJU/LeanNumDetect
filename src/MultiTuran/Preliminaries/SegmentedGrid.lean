import MultiTuran.Preliminaries.Geometry

/-!
# Cartesian products of consecutive integer blocks

The initial block starts at zero. `length` denotes the manuscript's `l`, so
each block contains `length + 1` rows and its closed thickening has that length.
The last block determines the aperture exactly; no enclosing-box enlargement
is made in any parameter.  Correspondence: `subsec:app-md`,
`eq:product-thickening`, `eq:general-filling-ratio`, `eq:rhoL`.
-/

set_option autoImplicit false
open scoped BigOperators
open Matrix

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- A nonempty-dimensional segmented product grid. The pairwise order field is
equivalent to the manuscript's adjacent-block inequality. -/
structure SegmentedGrid (d : ℕ) where
  dimension_pos : 0 < d
  blockCount : Fin d → ℕ
  start : (q : Fin d) → Fin (blockCount q + 1) → ℕ
  length : (q : Fin d) → Fin (blockCount q + 1) → ℕ
  start_zero : ∀ q, start q 0 = 0
  separated : ∀ q (i j : Fin (blockCount q + 1)), i < j →
    start q i + length q i + 1 ≤ start q j

namespace SegmentedGrid

/-- The article's adjacent-block condition implies separation of every pair
of blocks. This constructor lets clients supply precisely those hypotheses. -/
theorem separated_of_consecutive (r : ℕ) (a l : Fin (r + 1) → ℕ)
    (h : ∀ m : Fin r,
      a ⟨m.val, by omega⟩ + l ⟨m.val, by omega⟩ + 1 ≤
        a ⟨m.val + 1, by omega⟩) :
    ∀ i j : Fin (r + 1), i < j → a i + l i + 1 ≤ a j := by
  have haux : ∀ (j : ℕ) (hj : j < r + 1) (i : Fin (r + 1)),
      i.val < j → a i + l i + 1 ≤ a ⟨j,hj⟩ := by
    intro j
    induction j with
    | zero => intro hj i hi; omega
    | succ j ih =>
      intro hj i hi
      have hjr : j < r := by omega
      have hadj : a ⟨j,by omega⟩ + l ⟨j,by omega⟩ + 1 ≤ a ⟨j+1,hj⟩ := h ⟨j,hjr⟩
      by_cases he : i.val = j
      · have hifin : i = ⟨j, by omega⟩ := Fin.ext he
        rw [hifin]
        exact hadj
      · have hprev := ih (by omega) i (by omega)
        exact hprev.trans (by omega)
  intro i j hij
  exact haux j.val j.isLt i hij

/-- Build the exact segmented row pattern using only the manuscript's
adjacent-block ordering and its initial-zero convention. -/
def ofConsecutive {d : ℕ} (hd : 0 < d) (r : Fin d → ℕ)
    (a l : (q : Fin d) → Fin (r q + 1) → ℕ)
    (ha : ∀ q, a q 0 = 0)
    (hnext : ∀ q (m : Fin (r q)),
      a q ⟨m.val, by omega⟩ + l q ⟨m.val, by omega⟩ + 1 ≤
        a q ⟨m.val + 1, by omega⟩) : SegmentedGrid d where
  dimension_pos := hd
  blockCount := r
  start := a
  length := l
  start_zero := ha
  separated := fun q => separated_of_consecutive (r q) (a q) (l q) (hnext q)

variable {d : ℕ} (G : SegmentedGrid d)

abbrev Block (q : Fin d) := Fin (G.blockCount q + 1)

/-- The last block is included, also when there is only the initial block. -/
def lastBlock (q : Fin d) : G.Block q := ⟨G.blockCount q, by omega⟩

/-- Exact coordinate aperture `N_q = D_{q,r_q} + l_{q,r_q} + 1`. -/
def aperture (q : Fin d) : ℕ :=
  G.start q (G.lastBlock q) + G.length q (G.lastBlock q) + 1

def blockRows (q : Fin d) (m : G.Block q) : Finset ℕ :=
  Finset.Icc (G.start q m) (G.start q m + G.length q m)

/-- The actual finite coordinate row set, with every integer in each block. -/
def coordinateRows (q : Fin d) : Finset ℕ :=
  Finset.univ.biUnion (G.blockRows q)

/-- Rows are indexed by the Cartesian product, independently of the choice of
lexicographic enumeration. -/
abbrev Row := (q : Fin d) → {k : ℕ // k ∈ G.coordinateRows q}

def rowVector (k : G.Row) (q : Fin d) : ℕ := (k q).val

/-- Total number of measured rows. -/
def rowCount : ℕ := ∏ q, (G.coordinateRows q).card

def omega : ℕ := Finset.univ.sup G.aperture

private theorem coordinate_nonempty (G : SegmentedGrid d) :
    (Finset.univ : Finset (Fin d)).Nonempty :=
  ⟨⟨0,G.dimension_pos⟩, Finset.mem_univ _⟩

/-- The minimum coordinate aperture `N_min`. -/
def minAperture : ℕ := Finset.univ.inf' G.coordinate_nonempty G.aperture

def thickLength (q : Fin d) (m : G.Block q) : ℕ := G.length q m + 1

def coordinateMinLength (q : Fin d) : ℕ :=
  Finset.univ.inf' (Finset.univ_nonempty) (G.thickLength q)

/-- The global minimum thickened block length `L_*`. -/
def minThickLength : ℕ :=
  Finset.univ.inf' G.coordinate_nonempty G.coordinateMinLength

/-- The global minimum integer block degree `l_*`. -/
def minLength : ℕ :=
  Finset.univ.inf' G.coordinate_nonempty (fun q =>
    Finset.univ.inf' Finset.univ_nonempty (G.length q))

/-- The enclosing box volume `|J|`. -/
def boxVolume : ℝ := ∏ q, (G.aperture q : ℝ)

/-- The exact filling ratio `|Λ|/∏q N_q`. -/
def fillingRatio : ℝ := (G.rowCount : ℝ) / G.boxVolume

/-- The geometric long-block factor from `eq:rhoL`. -/
def rhoL : ℝ := Real.sqrt ((∏ q, (G.coordinateMinLength q : ℝ)) / G.boxVolume)

/-- Closed thickening of one coordinate row set. -/
def coordinateThickening (q : Fin d) : Set ℝ :=
  ⋃ m : G.Block q, Set.Icc (G.start q m : ℝ)
    (G.start q m + G.thickLength q m : ℕ)

def thickening : Set (Point d) :=
  Set.pi Set.univ G.coordinateThickening

@[simp] theorem card_row : Fintype.card G.Row = G.rowCount := by
  simp [Row, rowCount, Fintype.card_pi, Fintype.card_coe]

@[simp] theorem aperture_pos (q : Fin d) : 0 < G.aperture q := by
  unfold aperture
  omega

theorem aperture_le_omega (q : Fin d) : G.aperture q ≤ G.omega :=
  Finset.le_sup (Finset.mem_univ q)

theorem minAperture_le (q : Fin d) : G.minAperture ≤ G.aperture q :=
  Finset.inf'_le _ (Finset.mem_univ q)

theorem minAperture_pos : 0 < G.minAperture := by
  rw [minAperture, Finset.lt_inf'_iff]
  intro q _
  exact G.aperture_pos q

theorem omega_pos : 0 < G.omega := by
  exact (G.aperture_pos ⟨0,G.dimension_pos⟩).trans_le (G.aperture_le_omega _)

theorem minAperture_le_omega : G.minAperture ≤ G.omega :=
  (G.minAperture_le ⟨0,G.dimension_pos⟩).trans (G.aperture_le_omega _)

@[simp] theorem mem_blockRows (q : Fin d) (m : G.Block q) (k : ℕ) :
    k ∈ G.blockRows q m ↔ G.start q m ≤ k ∧ k ≤ G.start q m + G.length q m :=
  Finset.mem_Icc

@[simp] theorem mem_coordinateRows (q : Fin d) (k : ℕ) :
    k ∈ G.coordinateRows q ↔ ∃ m, k ∈ G.blockRows q m := by
  simp [coordinateRows]

theorem block_end_le_last (q : Fin d) (m : G.Block q) :
    G.start q m + G.length q m ≤
      G.start q (G.lastBlock q) + G.length q (G.lastBlock q) := by
  by_cases he : m = G.lastBlock q
  · rw [he]
  · have hm : m < G.lastBlock q := by
      change m.val < G.blockCount q
      have hne : m.val ≠ G.blockCount q := by
        intro h
        exact he (Fin.ext h)
      have := m.isLt
      omega
    have := G.separated q m (G.lastBlock q) hm
    omega

theorem coordinate_lt_aperture (q : Fin d) {k : ℕ}
    (hk : k ∈ G.coordinateRows q) : k < G.aperture q := by
  obtain ⟨m,hm⟩ := (G.mem_coordinateRows q k).1 hk
  have hle := ((G.mem_blockRows q m k).1 hm).2
  have hend := G.block_end_le_last q m
  unfold aperture
  omega

theorem rowVector_lt_aperture (k : G.Row) (q : Fin d) :
    G.rowVector k q < G.aperture q :=
  G.coordinate_lt_aperture q (k q).property

theorem coordinate_zero_mem (q : Fin d) : 0 ∈ G.coordinateRows q := by
  rw [G.mem_coordinateRows]
  refine ⟨0, ?_⟩
  simp [G.mem_blockRows, G.start_zero]

theorem coordinateRows_nonempty (q : Fin d) : (G.coordinateRows q).Nonempty :=
  ⟨0,G.coordinate_zero_mem q⟩

@[simp] theorem blockRows_card (q : Fin d) (m : G.Block q) :
    (G.blockRows q m).card = G.thickLength q m := by
  simp only [blockRows, Nat.card_Icc, thickLength]
  omega

theorem blockRows_disjoint (q : Fin d) {i j : G.Block q} (hij : i ≠ j) :
    Disjoint (G.blockRows q i) (G.blockRows q j) := by
  apply Finset.disjoint_left.mpr
  intro k hki hkj
  obtain ⟨hi₁,hi₂⟩ := (G.mem_blockRows q i k).1 hki
  obtain ⟨hj₁,hj₂⟩ := (G.mem_blockRows q j k).1 hkj
  obtain hlt | hgt := lt_or_gt_of_ne hij
  · have := G.separated q i j hlt
    omega
  · have := G.separated q j i hgt
    omega

/-- Counting the disjoint blocks gives their exact total thickened length. -/
theorem coordinateRows_card (q : Fin d) :
    (G.coordinateRows q).card = ∑ m, G.thickLength q m := by
  rw [coordinateRows, Finset.card_biUnion]
  · simp only [G.blockRows_card]
  · intro i _ j _ hij
    exact G.blockRows_disjoint q hij

theorem rowCount_pos : 0 < G.rowCount := by
  apply Finset.prod_pos
  intro q _
  exact Finset.card_pos.mpr (G.coordinateRows_nonempty q)

theorem minLength_le (q : Fin d) (m : G.Block q) :
    G.minLength ≤ G.length q m :=
  (Finset.inf'_le _ (Finset.mem_univ q)).trans
    (Finset.inf'_le _ (Finset.mem_univ m))

theorem coordinateMinLength_le (q : Fin d) (m : G.Block q) :
    G.coordinateMinLength q ≤ G.thickLength q m :=
  Finset.inf'_le _ (Finset.mem_univ m)

theorem minLength_add_one_le_coordinateMinLength (q : Fin d) :
    G.minLength + 1 ≤ G.coordinateMinLength q := by
  apply Finset.le_inf'
  intro m _
  exact Nat.add_le_add_right (G.minLength_le q m) 1

theorem minLength_add_one_le_minThickLength :
    G.minLength + 1 ≤ G.minThickLength := by
  apply Finset.le_inf'
  intro q _
  exact G.minLength_add_one_le_coordinateMinLength q

theorem boxVolume_pos : 0 < G.boxVolume := by
  apply Finset.prod_pos
  intro q _
  exact_mod_cast G.aperture_pos q

theorem fillingRatio_pos : 0 < G.fillingRatio := by
  exact div_pos (by exact_mod_cast G.rowCount_pos) G.boxVolume_pos

theorem coordinateMinLength_pos (q : Fin d) : 0 < G.coordinateMinLength q := by
  have := G.minLength_add_one_le_coordinateMinLength q
  omega

theorem rhoL_pos : 0 < G.rhoL := by
  apply Real.sqrt_pos.2
  apply div_pos _ G.boxVolume_pos
  apply Finset.prod_pos
  intro q _
  exact_mod_cast G.coordinateMinLength_pos q

theorem coordinateRows_card_le_aperture (q : Fin d) :
    (G.coordinateRows q).card ≤ G.aperture q := by
  calc
    (G.coordinateRows q).card ≤ (Finset.range (G.aperture q)).card :=
      Finset.card_le_card (fun k hk => Finset.mem_range.2 (G.coordinate_lt_aperture q hk))
    _ = G.aperture q := Finset.card_range _

theorem fillingRatio_le_one : G.fillingRatio ≤ 1 := by
  apply (div_le_one G.boxVolume_pos).2
  unfold rowCount boxVolume
  push_cast
  apply Finset.prod_le_prod
  · intro q _
    positivity
  · intro q _
    exact_mod_cast G.coordinateRows_card_le_aperture q

theorem noWrap_of_localized_nodes {n : ℕ} (Y : Fin n → Point d)
    (center : Point d) (hn : 4 ≤ n)
    (hY : ∀ j, InCube (2 * Real.pi / (G.omega : ℝ)) center (Y j)) :
    ((G.minAperture / n : ℕ) : ℝ) * nodeDiameter Y ≤ Real.pi :=
  noWrap_of_small_cube Y center G.minAperture G.omega G.omega_pos
    G.minAperture_le_omega hn hY

/-- The literal open-cube localization in manuscript `lem:sv-md-array`
implies its no-wrap condition. -/
theorem noWrap_of_nodes_in_open_cube {n : ℕ} (Y : Fin n → Point d)
    (center : Point d) (hn : 4 ≤ n)
    (hY : ∀ j, InOpenCube (2 * Real.pi / (G.omega : ℝ)) center (Y j)) :
    ((G.minAperture / n : ℕ) : ℝ) * nodeDiameter Y ≤ Real.pi :=
  G.noWrap_of_localized_nodes Y center hn (fun j => (hY j).inCube)

end SegmentedGrid

/-- The actual segmented generalized Vandermonde matrix of the manuscript. -/
def generalizedVandermonde {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) : Matrix G.Row (Fin n) ℂ :=
  vandermondeMatrix (fun k q => (G.rowVector k q : ℝ)) Y

@[simp] theorem generalizedVandermonde_mulVec {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (c : Fin n → ℂ) (k : G.Row) :
    (generalizedVandermonde G Y *ᵥ c) k =
      exponentialSum Y c (fun q => (G.rowVector k q : ℝ)) := by
  simp only [Matrix.mulVec, dotProduct, generalizedVandermonde,
    vandermondeMatrix, exponentialSum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end LeanNumDetect.MultiTuran
