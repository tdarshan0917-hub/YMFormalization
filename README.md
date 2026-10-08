# YMFormalization

**Lean 4 proofs of twisted SU(2) cell geometry and the nonlinear Wilson plaquette quadratic limit.**

By Travis Darshan. This repository develops a machine-checked, finite-dimensional foundation for a larger Yang–Mills research program. Its current milestone connects an actual nonlinear matrix-exponential plaquette path to its certified linearization and quadratic Wilson coefficient.

This description covers the plaquette milestone at `f4e3591` and the subsequent full cell-action quadratic-limit development. It does **not** establish the four-dimensional continuum Yang–Mills existence and mass-gap problem.

## Main result

For each of the six plaquettes `p` and every fixed cell tangent `X`, the code proves

$$
\lim_{t\to0,\ t\ne0}\frac{W(P_p(tX))}{t^2}
=\frac12\langle L_pX,L_pX\rangle,
\qquad W(U)=1-\frac12\operatorname{Re}\operatorname{Tr}(U).
$$

Here `P_p(tX)` is the genuine twisted plaquette built from exponential link paths, and `L_p X` is its certified Pauli-coordinate linearization. The endpoint is `YMFormalization.SU2.twistedPlaquetteWilsonCostD_quadratic_limit` in [WilsonPlaquetteSecondVariation.lean](YMFormalization/SU2/WilsonPlaquetteSecondVariation.lean).

This is a directional quadratic limit for every fixed `X`. A classical Hessian identification, a remainder estimate uniform over directions, and nonlinear neighborhood coercivity remain further obligations.

## Full nonlinear cell-action coefficient

For the actual six-plaquette action
`Sβ(tX) = β ∑p W(P_p(tX))`, the code also proves

$$
\lim_{t\to0,\ t\ne0}\frac{S_\beta(tX)}{t^2}
=4\beta\langle X,P_\perp X\rangle.
$$

On the physical slice `P_perp X = X`, this becomes
`4β ⟨X,X⟩`. The endpoints are
`wilsonCellActionPathD_quadratic_limit` and
`wilsonCellActionPathD_quadratic_limit_of_physical` in
[WilsonCellQuadraticLimit.lean](YMFormalization/SU2/WilsonCellQuadraticLimit.lean).

The proof sums the six plaquette limits and applies the certified
identity `L* L = 8 P_perp`. The coefficient `4β` is the
Taylor coefficient; it is not itself a classical second derivative.
Hessian regularity and uniform remainder bounds remain to be proved.

## Setting and normalization

The model has four link tangent vectors in `Vec3 = Fin 3 → ℝ` and six plaquettes. Its Pauli background is

$$
\Gamma_1=i\sigma_1,\quad\Gamma_2=i\sigma_2,\quad
\Gamma_3=i\sigma_3,\quad\Gamma_4=I.
$$

The Lie-algebra realization is `su2OfVec η = i η·σ`. Forward link paths have the form `exp(t • su2OfVec η) * Γ`, with no extra factor of one half in the exponential generator. All coefficients below use this convention.

## Formalized results

All endpoints below belong to the namespace `YMFormalization.SU2`.

| Result | Lean endpoint | Source |
|---|---|---|
| Gauge-map normalization `K* K = 8 I` | `Kstar_K` | [GaugeMap](YMFormalization/SU2/GaugeMap.lean) |
| Idempotent gauge and complementary physical projections | `gaugeProjection_idempotent`, `physicalProjection_idempotent` | [GaugeProjection](YMFormalization/SU2/GaugeProjection.lean), [PhysicalProjection](YMFormalization/SU2/PhysicalProjection.lean) |
| Exact kernel characterization `ker L = im K` | `plaquetteLinearization_eq_zero_iff_exists_K` | [PlaquetteKernel](YMFormalization/SU2/PlaquetteKernel.lean) |
| Exact operator identity `L* L = 8 P_perp` | `plaquetteAdjoint_linearization_eq_eight_physicalProjection` | [PlaquetteLaplacian](YMFormalization/SU2/PlaquetteLaplacian.lean) |
| Physical-slice identity `⟨LX,LX⟩ = 8 ⟨X,X⟩` when `P_perp X = X` | `plaquetteQuadratic_linearization_of_physical` | [PlaquetteQuadratic](YMFormalization/SU2/PlaquetteQuadratic.lean) |
| Linearized Wilson operator `β L* L = 8β P_perp` | `linearizedWilsonOperator_eq_eight_beta_physical` | [WilsonQuadratic](YMFormalization/SU2/WilsonQuadratic.lean) |
| All six twisted background plaquettes equal identity | `backgroundTwistedPlaquette_eq_one` | [TwistedBackgroundPlaquette](YMFormalization/SU2/TwistedBackgroundPlaquette.lean) |
| Derivative of the nonlinear plaquette equals `su2OfVec (L_p X)` | `twistedPlaquettePathD_hasDerivAt_linearization` | [WilsonPlaquetteSecondVariation](YMFormalization/SU2/WilsonPlaquetteSecondVariation.lean) |
| Determinant one along the actual plaquette path | `twistedPlaquettePathD_det_one` | [WilsonPlaquetteSecondVariation](YMFormalization/SU2/WilsonPlaquetteSecondVariation.lean) |
| Nonlinear Wilson quadratic limit | `twistedPlaquetteWilsonCostD_quadratic_limit` | [WilsonPlaquetteSecondVariation](YMFormalization/SU2/WilsonPlaquetteSecondVariation.lean) |

The [build ledger](BUILD_LEDGER.md) records successive milestones.

## The nonlinear proof bridge

For a determinant-one 2×2 matrix, the proof establishes the exact identity

$$
W(U)=\frac12\operatorname{Re}\det(U-I).
$$

The derivative gives `(P_p(tX) - I) / t → su2OfVec (L_p X)`, with division interpreted as real scalar multiplication. Continuity and degree-two homogeneity of the determinant, together with `det(su2OfVec η) = ⟨η,η⟩`, yield the quadratic limit. This extracts the coefficient from a first-order matrix derivative without differentiating the entire four-factor plaquette twice.

The release contributes an explicit, checkable chain from cell algebra to nonlinear plaquette asymptotics. It makes no priority claim for the underlying identities. Kernel checking validates the stated Lean propositions; their relation to a larger physical model also requires mathematical justification.

## Reproduce the milestone

Install Git and [elan](https://github.com/leanprover/elan), the Lean toolchain manager. With `lake` on your `PATH`, run:

```sh
git clone https://github.com/tdarshan0917-hub/YMFormalization.git
cd YMFormalization
git rev-parse HEAD
lake exe cache get
lake build
lake env lean YMFormalization/SU2/WilsonPlaquetteSecondVariation.lean
lake env lean YMFormalization/SU2/WilsonCellQuadraticLimit.lean
```

The project uses Lean `v4.34.0-rc2`. Record the full commit hash printed above; use `git checkout --detach <hash>` to reproduce that exact revision later. Retain its committed `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` when reproducing the result. The cache command downloads precompiled dependencies; subsequent commands build the project and print endpoint axiom reports.

The author's recorded full build for the earlier plaquette milestone succeeded with 8,780 jobs. This is a recorded build result, not a claim of independent replication. Successful verification should produce no Lean errors and report the headline theorem's dependencies as:

```text
[propext, Classical.choice, Quot.sound]
```

These are the accepted foundational axioms for this project. Certified endpoints must not depend on `sorryAx` or project-specific axioms. A successful build alone is insufficient: inspect the axiom reports as well. Style/linter warnings may appear in this revision.

## Next milestones

1. Establish the classical Hessian and quantitative remainder bounds needed for nonlinear local coercivity on the physical slice.
2. Develop and verify the separate analytic infrastructure beyond this finite cell, including estimates uniform in volume and lattice spacing, continuum construction, and a physical mass-gap argument.

The current finite-cell identities and directional limit do not discharge those analytic obligations. The larger research manuscript is not certified in full by the present Lean development.

## Attribution

Research and project development: Travis Darshan, with AI assistance in proof development and documentation. When referencing this milestone, cite the repository, author, full commit hash printed during verification, and the specific theorem used. Reviews, independent build reports, and precise reports of mathematical or formalization issues are welcome.
