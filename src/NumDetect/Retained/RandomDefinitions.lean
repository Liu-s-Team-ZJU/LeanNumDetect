import NumDetect.Preliminaries.Basic

/-! Definitions used by the retained one-dimensional nonuniform sampling results. -/

set_option autoImplicit false

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Sampling spread of order `n` for a finite integer frequency set. The `sSup`
form is equivalent to maximizing the minimum pairwise spacing over all `n`-subsets. -/
noncomputable def samplingSpread (n : ℕ) (Λ : Finset ℤ) : ℝ :=
  sSup {γ : ℝ | ∃ S : Finset ℤ,
    S ⊆ Λ ∧ S.card = n ∧
    ∀ lam ∈ S, ∀ mu ∈ S, lam ≠ mu → γ ≤ |(lam : ℝ) - (mu : ℝ)|}

/-- Maximum absolute frequency of an ordered one-dimensional integer sampling set. -/
noncomputable def maximumAbsFrequency {M : ℕ} (frequency : Fin M → ℤ)
    (hM : 0 < M) : ℝ :=
  Finset.univ.sup' (fin_univ_nonempty hM) fun j => |(frequency j : ℝ)|

/-- The local-cluster condition used by the external nonuniform Vandermonde estimate. -/
def IsLocalCluster1D {n : ℕ} (x : Fin n → ℝ) (hn : 2 ≤ n)
    (center τ : ℝ) : Prop :=
  ∀ j, |x j - center| ≤ τ * minimumSeparation1D x hn / 2

end

end NumDetect
end LeanNumDetect
