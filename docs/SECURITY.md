# SECURITY — BeeJSP

## Purpose

This document defines practical security rules for `beejsp`.

BeeJSP consumes external mathematical, GitHub and Lean ecosystem content and may build executable proof dependencies.

Its primary security concerns are:

- untrusted external content;
- managed vendor integrity;
- filesystem boundaries;
- shell/process safety;
- dependency and supply-chain integrity;
- GitHub automation permissions;
- credential protection;
- identity/KYC/payment privacy;
- proof provenance integrity.

BeeJSP does not currently own a long-running service runtime.

Use this document with:

- `docs/ARCHITECTURE.md`;
- `docs/FORMALIZATION.md`;
- `docs/SUBMISSION.md`;
- `docs/ROADMAP.md`;
- `AGENTS.md`.

## Core security principle

External mathematical or repository content is information.

It must not silently become execution authority.

Canonical distinction:

```text
external content
≠ trusted code

vendor snapshot
≠ executable authority

proof result
≠ GitHub write authority

submission evidence
≠ identity/payment data
```

## What we protect

At minimum BeeJSP protects:

- repository integrity;
- managed vendor provenance;
- filesystem boundaries;
- developer workstation integrity;
- CI integrity;
- GitHub write boundary;
- dependency integrity;
- Lean proof environment integrity;
- proof provenance;
- attribution integrity;
- credentials and tokens;
- private identity information;
- payment information.

## Trust boundaries

Primary trust flow:

```text
external repository / paper / GitHub data
        ↓ untrusted
BeeJSP ingestion / inspection
        ↓ bounded normalized/reference data
BeeJSP tooling / formalization
        ↓ reviewed source
local or CI verification
        ↓ evidence
review / optional submission
```

No step may silently convert external content into unrestricted execution or write authority.

## Import safety

Importing:

```python
import beejsp
```

must not unexpectedly:

- access the network;
- synchronize external repositories;
- invoke Git;
- execute shell commands;
- invoke Lean;
- modify vendor files;
- create runtime directories;
- access credentials;
- contact GitHub.

Python package import should remain side-effect free.

## External input is untrusted

Treat as untrusted:

- official JSP repository content;
- mathematical documents;
- external Lean repositories;
- GitHub API responses;
- Issue/PR bodies;
- catalog records;
- filenames from remote repositories;
- downloaded archives;
- generated third-party artifacts;
- external dependency metadata.

Validate external data according to how it is used.

## Managed JSP snapshot

Managed destination:

```text
docs/vendor/jsp/
```

Canonical update path:

```text
scripts/sync_jsp_docs.sh
```

Do not manually maintain vendor content.

The sync process must preserve:

```text
UPSTREAM_REF
UPSTREAM_COMMIT
```

and upstream licensing/attribution.

## Vendor path safety

Remote-controlled paths must not escape the intended staging or destination directory.

Do not trust:

- archive paths;
- symlink targets;
- unexpected file names;
- upstream directory layout changes;

without validation where relevant.

The synchronization implementation should materialize only explicitly selected paths.

Avoid broad extraction of arbitrary archive contents into repository root.

## Vendor fail-closed behavior

The active snapshot should only be replaced after the staged snapshot is complete enough to satisfy the required contract.

Examples of blocking sync failures:

- upstream ref cannot be resolved;
- required file missing;
- resolved commit invalid;
- required problem catalog missing;
- required verification guidance missing;
- staging incomplete.

Incorrect model:

```text
delete current snapshot
→ network failure
→ leave incomplete snapshot
```

Preferred model:

```text
fetch into temporary staging
→ validate
→ replace managed destination
```

## Vendor provenance

`UPSTREAM_COMMIT` must identify the exact upstream revision represented by the snapshot.

Do not:

- invent a commit;
- store only a human label when exact commit is required;
- claim a snapshot is fresh without checking;
- preserve stale upstream files that are no longer part of the managed
  selection.

## Vendor licensing

Preserve applicable upstream:

- licenses;
- copyright notices;
- attribution.

Do not remove licensing merely because files are copied automatically.

BeeJSP's own license and upstream vendor licenses are separate concerns.

## Network access

Network access is allowed only when the task requires it.

Examples:

- managed vendor synchronization;
- live GitHub competition query;
- dependency resolution;
- explicit research tooling.

Do not add hidden network calls during:

```text
import beejsp
```

or unrelated deterministic operations.

External network behavior should be explicit and bounded.

## GitHub write boundary

Reading public GitHub data and writing GitHub state are different authority levels.

Read operations may include:

- current problem records;
- PR discovery;
- Issue discovery;
- repository metadata.

Write operations include:

- pushing branches;
- opening PRs;
- commenting;
- creating Issues;
- merging;
- editing official records.

Do not add GitHub write automation without explicit approved scope.

Write automation is security-sensitive.

## GitHub Actions permissions

Use minimum GitHub Actions permissions.

Read-only workflows should prefer:

```yaml
permissions:
  contents: read
```

A workflow that intentionally creates a synchronization PR may require:

```yaml
permissions:
  contents: write
  pull-requests: write
```

Do not grant broader permissions without need.

Do not expose repository secrets to untrusted pull-request code.

## Sync workflow safety

The managed sync workflow may:

```text
fetch official public source
→ update managed vendor branch
→ create/update a BeeJSP PR
```

It must not:

- push directly to `main`;
- merge its own changes automatically;
- modify unrelated repository paths;
- execute upstream repository scripts.

The synchronized material remains subject to normal review.

## Shell safety

Shell scripts are security-sensitive when they process external values.

Use:

```bash
set -euo pipefail
```

where appropriate.

Quote variable expansions.

Avoid:

```bash
eval
```

and dynamic command construction from untrusted values.

Do not accept arbitrary destination paths from remote metadata.

## Temporary files

Use isolated temporary directories for synchronization and external inspection.

Clean them on exit.

Do not use predictable shared temporary filenames when collisions or cross-process influence would be unsafe.

## External repositories

Do not execute arbitrary external repository code merely to inspect:

- README;
- Lean theorem statement;
- metadata;
- catalog content.

Clone/read access does not imply execution approval.

Before building an external formalization:

- inspect repository provenance;
- inspect build files;
- inspect dependencies;
- prefer an isolated environment when the repository is not BeeJSP-owned.

## Lean source is executable build input

Lean elaboration, macros, dependencies and build tooling are code.

Treat untrusted Lean projects as code, not inert text.

For BeeJSP-owned proof projects:

- review source;
- pin environment;
- use expected Lake commands;
- keep dependencies minimal.

For third-party proof verification:

- avoid running arbitrary setup scripts;
- isolate execution when appropriate;
- inspect Lake configuration and dependencies first.

## Dependency integrity

Python source of truth:

```text
pyproject.toml
uv.lock
```

Lean source of truth is proof-project specific and may include:

```text
lean-toolchain
lakefile.toml
lake-manifest.json
```

Dependency additions require review for:

- necessity;
- maintenance quality;
- vulnerability surface;
- transitive dependencies;
- licensing;
- execution behavior.

Never add a dependency "just in case".

## Python dependency changes

When the approved Issue has no Python dependency change:

- do not modify dependency declarations;
- do not regenerate `uv.lock`.

When an approved dependency change exists:

- use minimum necessary dependency;
- update the normal dependency metadata;
- inspect relevant lockfile diff;
- perform applicable SCA.

Do not require:

```text
uv lock --check
```

## Lean dependency changes

Changing:

- Lean toolchain;
- Mathlib revision;
- another Lean dependency;

can change proof behavior.

Treat such changes as formalization-sensitive.

Rerun applicable:

- build;
- placeholder checks;
- axiom audit;
- statement/proof review.

## Proof provenance integrity

A proof's source identity is security-relevant evidence.

Do not submit or report an exact commit without confirming it contains the claimed proof.

Do not substitute:

- mutable branch name;
- local working tree;
- unpublished patch;
- unrelated tag;

for immutable evidence when exact commit provenance is required.

## Attribution integrity

Do not misattribute:

- mathematical discovery;
- Lean formalization;
- verification.

Intentional attribution falsification is a provenance failure.

AI assistance must not be used to erase original solver credit.

## Mathematical integrity

Security includes protection against false formalization claims.

Blocking examples:

```text
weaker theorem
reported as full theorem

missing case
reported as complete

custom axiom
reported as proved lemma

successful build
reported as statement equivalence
```

Formalization integrity rules live in:

```text
docs/FORMALIZATION.md
```

## Credentials

Do not commit real:

- GitHub tokens;
- API keys;
- SSH private keys;
- service credentials;
- passwords.

Use supported local/CI secret mechanisms when authenticated access is required.

Never print complete environment dumps into logs as a debugging shortcut.

## KYC and identity data

External award/claim processes may require identity verification.

Do not commit:

- passport scans;
- identity documents;
- home addresses;
- tax documents;
- private phone numbers;
- private identity evidence;
- private compliance correspondence.

Identity verification belongs in the official private channel required by the current external process.

## Payment information

Do not place private payment details in BeeJSP source unless the applicable official process explicitly requires a public value and the owner has approved publication.

Private payout information belongs in official private communication channels.

Do not store:

- private wallet keys;
- seed phrases;
- custodial credentials.

A public receive address, where explicitly required and approved, is not a private key and must still be handled deliberately.

## Personal information

The repository should contain only public attribution needed for:

- authorship;
- contribution;
- formalization provenance;
- external submission.

Do not collect unrelated personal data.

## Generated reports

Generated candidate or competition reports may aggregate public data.

Do not include:

- access tokens;
- private emails;
- private identity documents;
- private payment data;
- full environment contents.

## Logs

Keep diagnostic output bounded.

Do not log:

- secrets;
- authentication headers;
- private keys;
- full credential-bearing URLs;
- KYC data;
- unnecessary personal information.

## Public repository assumption

BeeJSP is designed as a public repository.

Treat every committed value as potentially public.

Do not use repository privacy as a security boundary.

## Public proof branches

A proof may be developed locally until it is ready for public evidence.

Do not rely on private/local Git timestamps as external priority evidence.

When a public exact commit is required for submission, publish deliberately and record the exact immutable identifier.

## Formalization confidentiality

Do not place confidential third-party mathematical material in the public repository unless distribution is permitted.

A problem may be publicly listed while a source document has separate copyright/access constraints.

Reference sources rather than copying restricted material unnecessarily.

## Copyright

Do not copy complete copyrighted mathematical publications into BeeJSP merely for convenience.

Store:

- citations;
- public links;
- original BeeJSP formalization;
- permitted excerpts where appropriate.

Managed vendor content must follow its upstream licensing.

## Security checks

Use only checks appropriate to the change.

### SAST

Expected for security-sensitive implementation such as:

- shell scripts;
- external-input parsing affecting paths/commands;
- network integrations;
- GitHub write automation;
- synchronization code;
- archive extraction;
- non-trivial filesystem handling.

Look for:

- command injection;
- unsafe path construction;
- path traversal;
- symlink problems;
- hidden network I/O;
- credential exposure;
- unintended writes.

### SCA

Required when dependency surface materially changes.

Review relevant Python or Lean dependencies.

Check:

- direct dependency;
- transitive dependency;
- necessity;
- known vulnerabilities where applicable;
- maintenance state;
- licensing.

### DAST

Not normally applicable because BeeJSP has no public runtime service.

Use only if a future approved change creates an externally reachable service.

### IAST

Not a default requirement.

Use only when a future instrumentable runtime surface exists.

### Fuzzing

Consider when BeeJSP adds:

- complex parser;
- archive/parser handling;
- structured untrusted normalization;
- syntax parser;
- path-producing external-data transformation.

Simple documentation changes do not require fuzzing.

## Change levels

### low-risk

Examples:

- documentation;
- prompt/skill maintenance;
- test-only changes;
- metadata changes without executable behavior.

Usually:

- relevant targeted validation.

### runtime-risk

Examples:

- Python scanner/parser behavior;
- deterministic scoring;
- report generation;
- vendor sync logic;
- CI logic;
- package/public behavior;
- external read integration.

Usually:

- targeted tests;
- full Python tests when applicable;
- Ruff;
- package checks when applicable;
- integration/idempotence checks where relevant.

### security-sensitive

Examples:

- shell construction from external data;
- path handling;
- archive extraction;
- external code execution;
- GitHub writes;
- credentials;
- identity/payment handling;
- material dependency expansion.

Usually:

- applicable runtime-risk checks;
- explicit security review;
- SAST;
- SCA when dependencies change;
- negative tests;
- path/permission checks.

### formalization-sensitive

Formalization sensitivity is independent from normal change level.

It applies when the proof contract changes.

Required proof checks come from:

```text
docs/FORMALIZATION.md
```

## Negative security scenarios

Test only scenarios relevant to actual implementation.

Examples for synchronization:

```text
required upstream file missing
→ sync fails

invalid resolved commit
→ sync fails

upstream fetch failure
→ current valid snapshot preserved

unexpected remote path
→ cannot escape destination

same upstream commit synchronized twice
→ no second diff
```

Examples for GitHub automation:

```text
read-only task
→ no write permission

sync PR
→ writes only approved sync branch

workflow failure
→ no direct main mutation
```

## Minimal developer security checklist

Before a significant PR ask:

- does external input influence filesystem paths?
- does external input influence shell commands?
- is network access explicit?
- does the change execute third-party code?
- did GitHub permissions expand?
- did dependency surface change?
- can vendor provenance become false?
- can private data reach the repository?
- can proof provenance become ambiguous?
- is the change really owned by BeeJSP?

## Minimal reviewer checklist

Reviewer should verify:

- external data remains untrusted;
- managed vendor boundaries remain explicit;
- GitHub permissions are minimal;
- no direct sync-to-main behavior was introduced;
- dependency additions are justified;
- proof provenance is intact;
- attribution is accurate;
- secrets/private data are absent;
- required negative tests exist;
- no unrelated execution surface was introduced.

## Supply-chain and release security

Release/package metadata should remain reproducible.

Python sources of truth:

```text
pyproject.toml
uv.lock
```

Release automation should use reviewed repository configuration.

Do not:

- commit local virtual environments;
- commit generated package metadata;
- upload unreviewed build artifacts manually as canonical releases;
- add arbitrary release scripts with hidden network behavior;
- bundle unrelated vendor/proof files into the Python package unintentionally.

## What not to do

Avoid:

- arbitrary command execution APIs;
- remote-controlled destination paths;
- direct vendor sync to `main`;
- hidden GitHub writes;
- hidden credential loading;
- dynamic plugin installation;
- arbitrary external repository setup scripts;
- unreviewed dependency expansion;
- storing KYC/payment secrets;
- treating private repository state as a confidentiality guarantee;
- security theater requiring every tool for every change.

## Summary

BeeJSP security is primarily:

```text
untrusted external content
+ safe vendor synchronization
+ bounded filesystem/network behavior
+ minimal GitHub authority
+ dependency integrity
+ proof provenance
+ attribution integrity
+ private identity/payment handling
```

The repository should remain safe enough that helping verify mathematics does not require granting external content unnecessary authority.
