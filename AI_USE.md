# AI use

The research questions and the physics behind this library are Jeromie
Beasley's. AI tools (Claude and ChatGPT) were used to search the literature,
write and repair Lean proofs, and organise this repository.

The operator-norm layer in `FilamentFracture/OperatorNorm.lean` was formalised in a multi-agent
session on Open Math OS: eight agents took one direction each, and the coordinating agent refereed
every submission — recompiling it, re-running the axiom audit, and testing the statement rather
than trusting the report. The correction recorded in `LIMITATIONS.md`, that the interface block is
`J_γ = [[b, μ], [γ, b]]` and that the semigroup bound with `J = [[b, μ], [0, b]]` is false, came
out of that review.

No statement here rests on an AI's say-so. Every proof is checked by the Lean
kernel and replayed by an independent kernel checker on every push, every
theorem's axioms are audited, and every false control must be rejected for the
check to pass. What the statements mean, and what they do not claim, is set
out in plain words in `README.md` and `LIMITATIONS.md`.
