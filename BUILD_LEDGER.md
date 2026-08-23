# Yang–Mills Lean Formalization — Build Ledger

This ledger records certified milestones of the project.

A milestone is GREEN only after:

1. its target Lean file compiles;
2. the full project builds;
3. the endpoint axiom footprint is inspected;
4. the corresponding Git commit is pushed.

The Git history and GitHub CI are the authoritative machine records.

| ID | Endpoint | Mathematical content | Status | Axiom policy |
|---|---|---|---|---|
| YM-000 | Project bootstrap | Lean/Mathlib repository initialized | GREEN | — |
| YM-001 | `SU2.Kstar_K` | Exact twisted-cell identity `K* K = 8 I` | GREEN | standard Lean trio only |
| YM-002 | `SU2.gaugeProjection_idempotent` | `P_gauge = (1/8) K K*` is a projection | ACTIVE | standard Lean trio only |

## Axiom policy

Certified mathematical endpoints must have no `sorry`, no `admit`,
and no project-specific axioms.

The expected foundational footprint is:

- `propext`
- `Classical.choice`
- `Quot.sound`

Open Yang–Mills research frontiers are represented explicitly as
unproved target propositions or theorem hypotheses. They are never
silently promoted to axioms.
