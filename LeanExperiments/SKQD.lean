import LeanExperiments.SKQD.Basic
import LeanExperiments.SKQD.Krylov
import LeanExperiments.SKQD.Phase
import LeanExperiments.SKQD.Sparsity
import LeanExperiments.SKQD.Theorem1
import LeanExperiments.SKQD.Sampling
import LeanExperiments.SKQD.Filter
import LeanExperiments.SKQD.Fourier
import LeanExperiments.SKQD.Resources
import LeanExperiments.SKQD.ExactGuarantee
import LeanExperiments.SKQD.ConstructiveBudget

/-!
# SKQD convergence (arXiv:2501.09702v1, Appendix B)

Machine-checked deterministic Lemmas 1–5, exact unitary Krylov evolution,
phase alignment, independent Born sampling, sampled-subspace minimization,
and the exact-family probability guarantee from spectral input data.
The concrete Chebyshev filter, decay bound, finite expansion, spectral
Rayleigh quotient, witness construction, endpoint and parity cases are proved.
`paper_theorem1` assumes no Krylov approximation witness.
`paper_theorem1_constructive` also derives sufficient dimension and shots;
`resourceCounts_isBigO` proves polynomial resource scaling. These are
mathematical guarantees, not a verified numerical eigensolver implementation.
-/
