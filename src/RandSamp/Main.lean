import RandSamp.NonuniformVandermonde
import RandSamp.FixedSeparated
import RandSamp.FixedSeparatedCube
import RandSamp.FixedSupport
import RandSamp.DFTGridOne
import RandSamp.UniformSeparated
import RandSamp.UniformOffGridRelativeGram
import RandSamp.SeparatedOffGridRelativeGram
import RandSamp.OffGridBiasOperator
import RandSamp.MultiClumpTheorem

/-! Public entry point for nonuniform Vandermonde scaling, uniform and fixed
separated-node random sampling, simultaneous DFT-grid RIP in any dimension,
the near-linear one-dimensional off-grid relative Gram estimate, and
multiclump relative cube sampling with the rate
`3072*512^(d-1) ρ⁻² (Σ n_a^(2d)) log(2n/δ)`, a sharp worst-case
lower spectral exponent, and the exact dimension-one corollary with the
original absolute constant `3072`.

Every result is fully proved. `RandSamp.OffGridAudit` checks the complete
off-grid probability chain, and `RandSamp.MultiClumpAudit` checks the
complete multiclump theorem. Both reject project admissions and project
axioms and require only standard Lean axioms. -/
