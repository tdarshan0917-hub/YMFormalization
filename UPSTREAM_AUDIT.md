# Yang–Mills Lean Formalization — Upstream Audit

Before building major infrastructure, this project checks whether a
machine-verified implementation already exists publicly.

## Mathlib

Primary foundational dependency.

Use upstream linear algebra, matrices, finite-dimensional analysis,
Lie/root-system infrastructure, Haar measure, distributions, and
functional analysis wherever appropriate.

## mrdouglasny/lgt

Public Lean lattice-gauge-theory development.

Relevant existing infrastructure includes:

- lattice sites, links, and plaquettes;
- gauge fields and holonomy;
- Wilson action and gauge invariance;
- product Haar Yang–Mills measure;
- Gibbs/DLR infrastructure;
- Dobrushin uniqueness;
- strong-coupling exponential correlation decay.

This is highly relevant to later lattice-measure layers, but it does
not establish the four-dimensional continuum Clay theorem.

Public license: Apache-2.0.
Recorded public toolchain at audit: Lean 4.30.0.

## mrdouglasny/OSforGFF

Public constructive-QFT / Osterwalder–Schrader development.

Relevant infrastructure includes:

- Schwartz test functions;
- tempered distributions;
- Gaussian measures and Minlos machinery;
- Euclidean symmetries;
- reflection positivity;
- Schwinger-function APIs;
- Osterwalder–Schrader axiom formulations;
- clustering infrastructure.

This is free-field QFT rather than interacting Yang–Mills, but it is
a major candidate for later continuum/OS reuse.

Public license: Apache-2.0.
Recorded public toolchain at audit: Lean 4.33.0-rc1.

## THE-ERIKSSON-PROGRAMME

Large public Lean programme directed toward Yang–Mills.

Relevant formal infrastructure includes:

- SU(N) Haar/lattice mathematics;
- KP/Mayer cluster-expansion machinery;
- Wilson-loop area laws;
- lattice clustering;
- RG and physical-operator interfaces.

The programme explicitly records the concrete Yang–Mills activity
decay theorem (`hRpoly`) as an open frontier and records the
four-dimensional continuum construction / OS-Wightman reconstruction
as open.

Public license: AGPL-3.0.
Recorded public toolchain at audit: Lean 4.29.0-rc6.

Study freely. Do not copy substantial source code without an explicit
license/dependency decision.

## LeanMillenniumPrizeProblems

Useful primarily as a Clay-statement comparator.

Its Yang–Mills modules make the intended continuum existence and
spectral-gap endpoint explicit. We should eventually compare our
capstone theorem against such a Clay-aligned statement to prevent
proving a weaker object under the name "mass gap."

## Project-specific mathematics

The present project begins with a different finite-dimensional spine:

    twisted SU(2) root cell
        ↓
    explicit adjoint rotations A_mu
        ↓
    K* K = 8 I
        ↓
    P_gauge = (1/8) K K*
        ↓
    P_perp
        ↓
    L* L = 8 P_perp
        ↓
    exact Wilson-cell Hessian
        ↓
    compact-simple root-cell extension

This layer should be formalized independently before introducing
larger external dependencies.

## Research frontier policy

The following kinds of statements must remain explicit frontier gates
until proved from the actual Yang–Mills model:

- a genuinely dynamical physical mass-gap mechanism;
- model-specific Yang–Mills polymer/activity decay;
- uniform continuum construction;
- regulator/stabilizer irrelevance at the quantum-measure level;
- nontrivial interacting continuum limit;
- OS reconstruction inputs sufficient for the physical Hamiltonian gap.
