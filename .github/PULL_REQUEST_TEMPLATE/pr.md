### Summary

What was done in this PR.

Include short, concrete statements:

- what behavior / contract / proof changed;
- what files / modules were touched;
- what was intentionally not changed.

### Related issue

Closes #

If relevant, also reference:

- ROADMAP iteration:
- related docs:
- affected JSP:
- upstream reference:
- follow-up issues:

### Iteration

- Iteration:
- Goal:
- Change level:
  - [ ] low-risk
  - [ ] runtime-risk
  - [ ] security-sensitive
- Formalization-sensitive:
  - [ ] no
  - [ ] yes

> Use the current iteration from `docs/ROADMAP.md`.
> Change level should match `AGENTS.md` / `docs/SECURITY.md`.

### Scope

What is included / excluded.

**Included**

- ...
- ...

**Excluded**

- ...
- ...

### Changes

- ...
- ...
- ...

### Package / Public API / Contract impact

Mark what changed:

- [ ] no package, public API or contract changes
- [ ] Python public / package behavior changed
- [ ] problem-bank / normalized data contract changed
- [ ] scanner / filtering / scoring behavior changed
- [ ] generated artifact / report contract changed
- [ ] managed JSP vendor contract changed
- [ ] Lean statement / proof changed
- [ ] Lean toolchain / dependencies changed
- [ ] formalization provenance / attribution changed
- [ ] submission evidence / workflow changed
- [ ] package metadata / build behavior changed
- [ ] Python runtime dependency surface changed
- [ ] backward compatibility / migration behavior changed
- [ ] docs updated

If applicable, specify:

**New / changed public behavior**

- `...`

**New / changed contracts**

- `...`

**Lean / formalization impact**

- `...`

**Compatibility / migration impact**

- `...`

### Verification level

Required checks for this PR.

**Python / package**

- [ ] targeted tests completed
- [ ] `uv run pytest -q`
- [ ] `uv run ruff check .`
- [ ] `uv run ruff format --check .`
- [ ] `uv build` when package / build behavior is affected
- [ ] package import smoke completed when applicable

**Managed JSP reference**

- [ ] vendor synchronization checked when required
- [ ] `UPSTREAM_REF` / `UPSTREAM_COMMIT` checked when required
- [ ] second-run sync idempotence checked when required
- [ ] vendor contents changed only through the managed sync flow

**Lean / formalization**

- [ ] `lake build` completed when required
- [ ] exact statement / original scope checked when required
- [ ] no `sorry` / `admit` when required
- [ ] axiom audit completed when required
- [ ] clean proof reproduction completed when required
- [ ] solver / formalizer provenance checked when required

**Quality / security checks**

Mark only what is required for this PR:

- [ ] SAST completed
- [ ] SCA completed
- [ ] fuzzing completed
- [ ] not applicable (explained in Notes)

> Only mark checks that are required for this change.
> Use `AGENTS.md`, `docs/SECURITY.md`, and `docs/FORMALIZATION.md` as applicable.

#### Test details

Commands / scenarios used:

- `...`
- `...`

Include Python, vendor, Lean, formalization, integration, and security verification when relevant.

#### Manual scenarios checked

- ...
- ...
- ...

### Artifacts

What was created or verified:

- ...
- ...
- ...

If applicable, list exact files, for example:

- `tests/...`
- `src/beejsp/...`
- `proofs/JSP-XXXXXX/...`
- `scripts/sync_jsp_docs.sh`
- `docs/vendor/jsp/...`
- `README.md`
- `docs/ROADMAP.md`
- `docs/ARCHITECTURE.md`
- `docs/FORMALIZATION.md`
- `docs/SUBMISSION.md`
- `docs/SECURITY.md`
- `docs/DEV_GUIDE.md`
- `pyproject.toml`
- `uv.lock`
- built wheel / source distribution
- generated report / proof-verification evidence

### Security review

Fill only if relevant for this PR:

- external / untrusted input affected:
- filesystem / path handling affected:
- shell / process execution affected:
- network / GitHub / external API integration affected:
- managed vendor synchronization affected:
- credentials / tokens affected:
- identity / KYC / payment data affected:
- dependency surface changed:
- cross-repository compatibility required:

### Formalization review

Fill only if formalization-sensitive:

- source mathematical problem:
- source mathematical solution:
- top-level Lean statement:
- full source scope preserved:
- assumptions preserved:
- proof builds:
- `sorry` / `admit` absent:
- axiom audit:
- toolchain / dependencies pinned:
- solver attribution:
- formalizer attribution:
- reproducibility evidence:

### Checklist

#### Scope

- [ ] change stays within current iteration / declared standalone scope
- [ ] Issue, code, proofs, tests, docs, and PR are aligned
- [ ] `docs/ROADMAP.md` updated if roadmap status or planned contract changed
- [ ] related docs updated if needed (`DEV_GUIDE`, `README.md`, `FORMALIZATION`, `SUBMISSION`, `SECURITY`, `ARCHITECTURE`)

#### Package / contracts

- [ ] Python public behavior remains explicit when applicable
- [ ] backward compatibility is preserved or migration is documented
- [ ] managed vendor remains generated / read-only
- [ ] Python dependencies remain unchanged unless explicitly approved
- [ ] package builds and imports as expected when applicable

#### Formalization

- [ ] exact mathematical scope is preserved when applicable
- [ ] no unsupported mathematical authorship claim was introduced
- [ ] proof provenance / attribution is explicit when applicable
- [ ] successful compilation is not being used as the sole statement-fidelity evidence

#### Security

- [ ] no secrets, KYC material, private payment data, or unrelated private data committed
- [ ] dependency changes were reviewed when applicable
- [ ] security checks required for this PR were completed
- [ ] external-input / filesystem / network boundaries were reviewed when applicable

#### Code quality

- [ ] change follows KISS
- [ ] no unnecessary abstraction / refactor was added
- [ ] no second source of truth was introduced
- [ ] project style respected

#### Version / release

- [ ] no version change required
- [ ] version / changelog change is intentional and release-related
- [ ] breaking compatibility impact is explicitly documented if applicable

### Limitations / follow-ups

Anything intentionally left out of scope:

- ...
- ...

### Notes

Anything important for reviewer.

Examples:

- why some checks are marked not applicable;
- known limitations;
- proof/source references;
- compatibility notes;
- upstream JSP context;
- what to inspect first during review.
