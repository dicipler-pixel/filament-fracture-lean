# Provenance

`FilamentFracture/Basic.lean` and the three files in `FalseControls/` were written for this
repository from the Revision 3 LaTeX source (`filament_operator_v3.tex`, 24 September 2026),
whose Theorems 1–2 and Proposition 3 carry into the deposited Revision 4 (DOI
10.5281/zenodo.21184980).

`FilamentFracture/OperatorNorm.lean` states no result of the source that `Basic.lean` did not
already state. It proves that the closed forms there — `resNorm`, `gain`, `ε_crit` and the
`σ²` of `top_singular` — are the operator norms named in the source, and nothing in it is taken
from the source beyond those definitions. One statement of the source, the semigroup bound, is
recorded in `LIMITATIONS.md` with the interface block `J_γ` rather than `J`; the version with `J`
is false, and the counterexample is given there.
