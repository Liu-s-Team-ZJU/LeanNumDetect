# Vaaler–Selberg proof dependency

This directory contains the minimal transitive source closure needed for
`MathExtras.NumberTheory.Analysis.SelbergIntervalPoissonClosed`.

The files are vendored from
[`gersh/ternary-goldbach-lean`](https://github.com/gersh/ternary-goldbach-lean)
at commit `27df23af`, under the Apache License 2.0 reproduced in `LICENSE`.
They provide the proved Vaaler–Selberg extremal-function and Poisson-summation
results used by NumDetect's translated-cube lower frame theorem. No declarations
with `sorry` or project-specific axioms are used by that theorem.
