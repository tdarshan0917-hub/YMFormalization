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
| YM-002 | `SU2.gaugeProjection_idempotent` | `P_gauge = (1/8) K K*` is a projection | GREEN | standard Lean trio only |
| YM-003 | `SU2.physicalProjection_idempotent` | `P_perp = I - P_gauge` is the complementary projection | GREEN | standard Lean trio only |
| YM-004 | `SU2.plaquetteLinearization_K` | Linearized plaquette map annihilates gauge directions `L(Kη)=0` | GREEN | standard Lean trio only |
| YM-005 | `SU2.plaquetteAdjoint_spec` | Explicit `Lstar` satisfies `<LX,Y> = <X,Lstar Y>` | GREEN | standard Lean trio only |
| YM-006 | `SU2.plaquetteAdjoint_linearization_eq_eight_physicalProjection` | Exact operator identity `Lstar L = 8 P_perp` | GREEN | standard Lean trio only |
| YM-007 | `SU2.twistConjugation_su2` | Pauli twist-eaters induce the explicit SU(2) adjoint rotations | GREEN | standard Lean trio only |
| YM-008 | `SU2.su2OfVec_cellA_eq_sub_twistConjugation` | Exact bridge `A_mu = I - Ad_Gamma` | GREEN | standard Lean trio only |
| YM-009 | `SU2.plaquetteLinearization_eq_zero_iff_exists_K` | Exact kernel identity `ker L = im K` | GREEN | standard Lean trio only |
| YM-010 | `SU2.plaquetteQuadratic_linearization_of_physical` | Exact quadratic/coercivity identity on physical slice | GREEN | standard Lean trio only |
| YM-011 | `SU2.linearizedWilsonOperator_eq_eight_beta_physical` | Linearized Wilson operator `β Lstar L = 8β P_perp` | GREEN | standard Lean trio only |
| YM-012 | `SU2.backgroundTwistedPlaquette_eq_one` | All six twisted plaquettes equal identity at the Pauli background | GREEN | standard Lean trio only |

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
