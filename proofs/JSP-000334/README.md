# JSP-000334 — Newman's conjecture

The principal theorem is `JSP000334.newman_conjecture_complete : NewmanConjecture`, in [NewmanCompletion.lean](SubspaceBridge/NewmanCompletion.lean). It establishes an absolute bound on the number of ordered nonnegative exponent tuples `(a,b,c,d)` satisfying `n = 2^a + 3^b + 2^c * 3^d`, for every positive natural `n`.

`Exponents` has four independent natural fields. Zero exponents and repeated summands are included. `solutions_finite` proves that `Set.ncard` counts a finite solution set. There are no coprimality, distinctness or exponent-cutoff assumptions. [STATEMENT.md](STATEMENT.md) explains the exact definitions, the source parameter permutation and the proved multiset/tuple bridge `multisetCount ≤ tupleCount ≤ 6 * multisetCount`. The qualitative theorem does not assert the later numerical bound 9 for raw tuples.

## Build and verify

Prerequisites: Git, Bash, Python 3.11 or later (standard library only), curl and tar for optional cache downloads, and elan with Lean/Lake `leanprover/lean4:v4.19.0`. No BeeJSP Python package is required. Network access is needed to obtain the pinned Lean toolchain, dependency sources and optional official Mathlib cache. Keep dependency checkouts unmodified.

From this directory, initialize dependencies and optionally obtain their compiled cache:

```bash
lake exe cache get
```

The canonical normal build is:

```bash
lake build
```

The existing single library includes `SubspaceBridge.NewmanCompletion` among its roots. Its import closure is therefore part of the default build. The explicit endpoint build is:

```bash
lake build SubspaceBridge.NewmanCompletion
```

Run the full verification suite:

```bash
bash verify.sh
```

The verifier checks actual dependency HEADs and cleanliness against `lake-manifest.json`, the compiler version, all 608 local modules of the principal source closure for forbidden shortcuts, the independently expanded tuple-count endpoint, actual source parameterization/group/nondegeneracy definitions, M257/M258/M259 interfaces, fixed S-unit finiteness and unconditional Newman endpoint. It traverses every elaborated type/value dependency of the principal theorem and rejects axioms outside `propext`, `Classical.choice`, `Quot.sound`. It freshly checks standalone `Audit.lean` and the explicit replay inputs in [portable-suite.json](verification/portable-suite.json), including accepted final raw/literal/literal-source and regression challenges. Each replay compares its exact axiom-map digest and observation count with the retained baseline metadata. Historical helper imports are compiled from retained source into a new temporary directory. No PDF, private scratch path, repository Python environment or preexisting project object cache is required; normal Lake builds may reuse valid project objects. Inherited Lean search paths are cleared, and newly compiled verification helpers take priority over cached helper objects.

The retained axiom evidence records observations, not a fixed dependency-node-count contract: the current dependency artifacts yielded 58,634 reachable constants, while a fresh official pinned Mathlib cache yielded 58,630. The only graph difference was four auxiliary `_proof_*` declarations under `Cardinal.le_range_of_union_finset_eq_top` and `StieltjesFunction.measure_singleton`; the pinned source files and all first-party dependency edges agreed. Both runs used only the same three standard axioms. Compiled dependency proof-term sharing can change this diagnostic count; full traversal, the standard axiom set and the exact local source closure are the verification requirements.

Every run prints its unique `/tmp/beejsp-000334-verify-*` directory. Complete command arrays, working directories, exits, timings, logs, dependency revisions, source hashes and axiom summary remain there. Checks run at their existing source limits, with at most three replay processes, each using `-j1`. A failed check makes the verifier exit nonzero. Large historical replays can take several hours; a cached Lake message is not a fresh standalone Audit result.

## Mathematical source correspondence

| Mathematical step | Retained Lean source / interface |
| --- | --- |
| Newman problem; equivalent source exponent ordering | `Statement.lean`: `source_parameterization_count` |
| Permutation conventions and finite tuple counting | `Counting.lean`: `counting_conventions_equivalent` |
| Minimal signed zero blocks and fixed-reference representation coding | `FixedReference.lean`: `newman_of_fixed_sunit_finiteness` |
| Rational mixed-place auxiliary polynomial and local-index ingredients | `SubspaceBridge.lean`, `SubspaceBridge/SchmidtHilfssatz12.lean` and their explicit imports |
| Schlickewei selected forms, changing dual lattices and fixed directions | `SubspaceBridge/SchlickeweiSatz41Selected6.lean`, `SubspaceBridge/SchlickeweiSatz51Selected6.lean` and their explicit imports |
| All-point proper covers, including low heights | `SubspaceBridge/AllPointFiniteCover3.lean`, `AllPointFiniteCover4.lean`, `AllPointFiniteCover5.lean` |
| M257 original six-term cover | `JSP000334.source_six_term_finite_cover5` |
| M258 arbitrary nonzero rational coefficient finiteness | `JSP000334.weighted_five_term_finite` |
| M259 all annihilator supports and full six-coordinate fibers | `SubspaceBridge/SixTermFiniteness5.lean`: `fixed_six_term_finite` |
| Exact lengths 2–6, then the original tuple-count conclusion | `SubspaceBridge/NewmanCompletion.lean`: `fixed_sunit_finiteness_complete`, `newman_conjecture_complete` |

The complete dependency map is the source import graph and the verifier's regenerated type/value closure. The principal Lean theorem has no remaining analytic or S-unit finiteness hypothesis. Successful compilation and axiom checks support proof completeness; mathematical source correspondence also requires independent reading of the statement and source map.

Original problem: D. J. Newman, recorded by Erdős–Graham (1980), p.80. Mathematical solution: Evertse–Győry–Stewart–Tijdeman (1988), Theorem 7(a), pp.138–139. The formalization uses the qualitative mixed-place route, including Schlickewei and Schmidt ingredients, rather than the later effective numerical classification. The fixed-reference coding strategy was informed by static inspection of plby's mathematical strategy; no competing Lean project is a build dependency. Original Lean authoring and local verification used OpenAI Codex assistance. This does not transfer mathematical authorship or establish independent final approval. [SOURCES.md](SOURCES.md) records editions, corrections and all eleven local PDF hashes.

## Evidence and reproducibility boundary

**COMMITTED REPRODUCIBLE EVIDENCE** is the intended publication category for the selected Lean sources, pinned metadata, these instructions and explicit verification inputs. This worktree is currently uncommitted: the category describes what the proposed package will make reproducible after review and commit. It does not claim that a proof commit already exists. An isolated manifest-only copy test is an uncommitted package smoke test. Clean committed-source reproduction remains a later required gate.

**LOCAL HISTORICAL EVIDENCE** comprises milestone receipts, failed/partial experiments, source-reading notes and generated logs preserved in the original worktree. The historical portions of [EVIDENCE.md](EVIDENCE.md), [PLAN.md](PLAN.md) and [PROGRESS.md](PROGRESS.md) retain their original facts and references. References there to excluded files, old scratch paths, source images or historical command receipts are informational local history, not required publication inputs. Not all receipts are included. The replay manifest records informational historical receipt names; fresh verification consumes its source paths and hashes, not those archived receipts.

The replay selection preserves the explicit accepted M205 historical schedule (standalone Audit, historical replay checks and supplementary checks), adds accepted later source/literal/raw/regression checks and deduplicates byte-identical inputs. Developmental spikes, failed variants, obsolete WIP endpoints and generated logs are not executable publication requirements. Historical partial results checked by the suite remain partial claims, even when later production proves the final theorem. Every selected input has an explicit verifier consumer; excluded local artifacts remain preserved.

No local copyrighted PDFs, scans or extracted source text are distributed. PDF hash matching is an optional source-identity check after obtaining the matching editions lawfully; the PDFs are not needed to compile or replay this proof. Their absence limits independent source reading, not Lean compilation. No official acceptance, priority, award, submission, Issue closure or Iteration 8 completion is claimed.
