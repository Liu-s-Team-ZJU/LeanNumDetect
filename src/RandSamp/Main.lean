import RandSamp.NonuniformVandermonde
import RandSamp.FixedSeparated
import RandSamp.FixedSeparatedCube
import RandSamp.FixedSupport
import RandSamp.DFTGridOne
import RandSamp.UniformSeparated
import RandSamp.UniformOffGridRelativeGram
import RandSamp.SeparatedOffGridRelativeGram
import RandSamp.OffGridBiasOperator

/-! Public entry point for nonuniform Vandermonde scaling, uniform and fixed
separated-node random sampling, simultaneous DFT-grid RIP in any dimension,
and the near-linear one-dimensional off-grid relative Gram estimate.

The latter has the explicit original-external-theorem boundary documented
in `RandSamp/README.md` and checked separately in `RandSamp.OffGridAudit`. -/
