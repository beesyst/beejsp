# JSP-000089 Iteration 4 evidence

## Current record and competition/formalization check

The managed catalog at commit `bcf1866ea9a4ae82b32bd95b82ffd812b9ee80d2`
records JSP-000089 as **Solved**, Lean proof **No**, and eligible to claim
**No**. It is pinned reference evidence, not live competition state.

At `2026-09-22T12:31:42Z`, bounded public read-only GitHub API reads of
`TheJustinSunPrize/awards` found open exact-ID records: issue
[#998](https://github.com/TheJustinSunPrize/awards/issues/998), PR
[#996](https://github.com/TheJustinSunPrize/awards/pull/996), PR
[#1414](https://github.com/TheJustinSunPrize/awards/pull/1414), and PR
[#2648](https://github.com/TheJustinSunPrize/awards/pull/2648). Their titles
report an award claim or Lean work; no body, repository, proof, CI result, or
author claim was executed or treated as verification. Public GitHub code search
for exact `JSP-000089` in `leanprover-community/mathlib4` returned zero hits.
This bounded result does not establish global absence. The active unverified
claims are submission/process risk, not a concrete blocker that makes the
local representation spike pointless.

## Mathlib discovery and dependency review

Focused inspection at Mathlib `v4.19.0` found:

- `Mathlib.Combinatorics.SimpleGraph.Path`: `SimpleGraph.Walk.IsCycle`,
  `Walk.length`, and `IsCycle`'s non-repeating-tail contract;
- the same file's `IsPath.length_lt`, supporting the finite vertex-bound
  reasoning used by the spike;
- `Mathlib.Combinatorics.SimpleGraph.Finite`: `edgeFinset`; and
- `Mathlib.Combinatorics.SimpleGraph.DegreeSum`:
  `sum_degrees_eq_twice_card_edges`, supporting the stated average-degree
  encoding.

Lean `v4.19.0` was selected after this API check, not assumed merely because
the smoke template uses it: the installed toolchain and Mathlib's compatible
`v4.19.0` tag elaborate the exact `SimpleGraph.Walk.IsCycle`, finite-set, and
statement-contract code in this project. No additional direct Lean dependency
is needed for the bounded spike.

## Supply-chain / SCA review

Reviewed on 2026-09-22 at `13:27:59Z`. This is a bounded manual review of the
actual Lake dependency closure, not a claim that no vulnerabilities exist. The
method was: read `lake-manifest.json`; compare each local checkout's `HEAD`
with its manifest revision and inspect its license; read public GitHub repository
metadata and the repository `security-advisories` endpoint for every listed
repository; and check for locally installed `osv-scanner`, `trivy`, and `grype`
(none was available). No third-party setup script, network installation, or
application process was run for this review. The separate expected `lake build`
does elaborate the pinned Lean dependency closure as executable build input; no
dependency is granted an application-service, external-write, or network role
by this proof project.

| dependency (identity) | role and necessity | immutable manifest revision | maintenance and license | advisory result |
| --- | --- | --- | --- | --- |
| [`mathlib`](https://github.com/leanprover-community/mathlib4) | Direct: supplies the graph, finite-set, and degree-sum APIs used by the spike. | `c44e0c8ee63ca166450922a373c7409c5d26b00b` (`v4.19.0`) | Not archived or disabled; repository metadata showed a 2026-09-22 push. Apache-2.0. | 0 published repository advisories. |
| [`plausible`](https://github.com/leanprover-community/plausible) | Transitive Mathlib build dependency; no BeeJSP module imports it directly. | `77e08eddc486491d7b9e470926b3dbe50319451a` | Not archived or disabled; metadata showed a 2026-09-16 push. Apache-2.0. | 0 published repository advisories. |
| [`LeanSearchClient`](https://github.com/leanprover-community/LeanSearchClient) | Transitive Mathlib dependency; no BeeJSP module imports it directly. | `25078369972d295301f5a1e53c3e5850cf6d9d4c` | Not archived or disabled; metadata showed a 2026-09-16 push. Apache-2.0. | 0 published repository advisories. |
| [`importGraph`](https://github.com/leanprover-community/import-graph) | Transitive Mathlib dependency; no BeeJSP module imports it directly. | `e6a9f0f5ee3ccf7443a0070f92b62f8db12ae82b` | Not archived or disabled; metadata showed a 2026-09-19 push. Apache-2.0. | 0 published repository advisories. |
| [`proofwidgets`](https://github.com/leanprover-community/ProofWidgets4) | Transitive Mathlib dependency; no BeeJSP module imports it directly. | `c4919189477c3221e6a204008998b0d724f49904` | Not archived or disabled; metadata showed a 2026-09-21 push. Apache-2.0. | 0 published repository advisories. |
| [`aesop`](https://github.com/leanprover-community/aesop) | Transitive Mathlib dependency; no BeeJSP module imports it directly. | `5d50b08dedd7d69b3d9b3176e0d58a23af228884` | Not archived or disabled; metadata showed a 2026-09-16 push. Apache-2.0. | 0 published repository advisories. |
| [`Qq`](https://github.com/leanprover-community/quote4) | Transitive Mathlib dependency; no BeeJSP module imports it directly. | `fa4f7f15d97591a9cf3aa7724ba371c7fc6dda02` | Not archived or disabled; metadata showed a 2026-09-16 push. Apache-2.0. | 0 published repository advisories. |
| [`batteries`](https://github.com/leanprover-community/batteries) | Transitive Mathlib dependency; no BeeJSP module imports it directly. | `f5d04a9c4973d401c8c92500711518f7c656f034` | Not archived or disabled; metadata showed a 2026-09-22 push. Apache-2.0. | 0 published repository advisories. |
| [`Cli`](https://github.com/leanprover/lean4-cli) | Transitive Mathlib dependency; no BeeJSP module imports it directly. | `02dbd02bc00ec4916e99b04b2245b30200e200d0` | Not archived or disabled; metadata showed a 2026-09-16 push. MIT. | 0 published repository advisories. |

The public [GitHub Advisory Database supported-ecosystem list](https://github.com/github/advisory-database/blob/main/README.md#supported-ecosystems)
and [Dependabot vulnerability-detection guidance](https://docs.github.com/en/code-security/reference/supply-chain-security/troubleshoot-dependabot/vulnerability-detection)
do not provide a Lean/Lake package ecosystem or package-coordinate lookup for
this git-pinned dependency graph. Accordingly, a version-specific global
GHSA/CVE determination is not applicable from those sources. The per-repository
endpoint result only means that no published repository advisory was returned
at the review time; it is not evidence of vulnerability absence. Recent public
activity and non-archived status are maintenance indicators, not a maintenance
guarantee.

No concrete advisory or license conflict was found in this bounded review, and
every local checkout matched its pinned manifest revision. Therefore it does
not add a current blocker to the Iteration 4 GO decision, which remains limited
to the representation spike. A newly published relevant advisory, a pin
mismatch, or an unreviewed dependency change requires reassessment before a
subsequent decision.

## Spike result, audit, and decision

`Main.lean` directly attempts the selected boundary. It defines
`IsCycleLength`, proves that a simple cycle's length is bounded by the finite
vertex cardinality, enumerates those lengths in `cycleLengths`, and proves
`hasCycleLengthIn_iff_filter_nonempty`. The exact theorem has no `sorry`,
`admit`, or custom axiom. There are no exploratory placeholders.

Decision: **GO**. The finite cycle representation and finite-set equivalence
build against the pinned environment. This is positive feasibility evidence
only; the density estimate and the main extremal graph proof remain substantial
Iteration 5 work. Reassess the live competition evidence before any external
submission activity.
