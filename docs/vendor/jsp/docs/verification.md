# Formal verification: evidence and review

Public verification records connect the original mathematical problem, formal statement, pinned proof source, reproduction evidence, and review conclusions. A formal statement alone is not a verified proof, and proof checking must also address whether the statement represents the intended problem.

Review the mathematical solution before accepting its Lean formalization.
A Lean submission identifies the mathematical solution and review evidence, or
supplies the solution evidence for review in the same PR. Lean verification and
candidate registration do not require a prior solver candidate or award record.
The solver need not have registered or submitted a claim. Review combined
submissions by contribution type without imposing a contributor-registration order.

A source link or successful build alone is not a completed verification record. Maintainers review the evidence and reproduce proof verification before acceptance.

See the [record guide](records.md) for maintaining public evidence. Publish only evidence authorized for public release.

## Recommended Lean pre-submission check

For Lean proof submissions, we recommend using the repository's
[`lean-verify` skill](../skills/lean-verify/SKILL.md) to check the exact proof commit
before opening a PR. The skill is optional, including for initial proofs,
replacement proofs and combined solver/Lean submissions. Contributors may use
other verification methods and are not required to provide a self-check declaration
or report. Mathematical solvers submitting only a solution, publication or solver
information need no Lean repository or self-check.

Any declaration, report or logs supplied by the contributor are supporting evidence.
Maintainers independently check statement correspondence and reproduce verification
before acceptance, following mathematical review as described above. A self-check
does not approve attribution, priority, a merge or an award.

### Run the skill before a PR exists

The complete skill is versioned under `skills/lean-verify/`, including its
references, target-manifest example, audit script and regression tests. Give your
coding agent the skill file and request the full workflow. If your agent supports
installed skills, copy the complete `lean-verify` directory into its skill
directory and invoke `$lean-verify`. Reading the instructions or running only
`scripts/audit.py` is not a completed verification.

Supply the JSP problem ID, catalog entry and original mathematical source,
plus the proof repository, branch, full 40-character commit SHA, project path and
target theorem names. A PR URL is not required for this direct-source check.
For example, replace the bracketed values in this request:

```text
Use the skill at skills/lean-verify/SKILL.md to perform a full pre-submission
verification of JSP-[number], catalog entry [path/link], against the original
problem at [source and exact location].
Proof repository: [URL]
Branch: [branch]
Commit: [full 40-character SHA]
Lean project and target theorem(s): [paths and fully qualified names]
No PR has been opened yet. Verify this exact commit, all original problem
requirements, the clean build and the proof's transitive axiom dependencies.
Write the report in English for public submission, with the final verdict,
actual verification levels, trust dependencies and supporting evidence paths.
```

The workflow checks statement correspondence and full coverage as well as actual
Lean execution. It must retain the pinned toolchain and dependencies, use an
isolated environment, and report any missing proof steps or extra assumptions.
Follow its instructions for kernel replay and independent checks, recording the
levels actually completed and any limitations. Preserve the full report and
underlying evidence locally for follow-up review. Publishing links to those
materials is recommended, not a prerequisite for opening the PR.

### Optionally attach the result to the PR

If you choose to share a self-check, use the template's optional
**Pre-submission Lean verification** section. Useful details include:

- The verification tool or method and version, if available.
- The exact proof repository and commit checked; identify any difference from the
  version submitted for review.
- The verification date and actual conclusion, including incomplete or failed checks.
- A short summary of statement correspondence, coverage, Lean checks, trust
  dependencies and limitations for each problem and proof version.

You may identify the awards repository commit containing the skill used, and link
the full report, target manifest, build/axiom logs and checker evidence. A short
report may instead be pasted into the PR body. A bare local filesystem path is not
a public link. All of these self-check materials are optional.

To share longer evidence, first verify proof commit **A**, then save the report
and logs under `verification/` in your own proof repository in a later commit
**B**. Link the files at **B** and state clearly that they describe proof commit
**A**. Adding evidence does not require rechecking **A** if it remains the selected
proof version. Before presenting a report as verification of **B** or another
selected commit, check that version; an older report cannot certify a newer commit.

The requirement to submit a complete proof still applies. Report any known gaps
or limitations accurately; an optional self-check does not relax acceptance criteria.
Resolve proof defects before requesting acceptance. Only describe a self-check as
passed when the checks actually support that conclusion.

The audit helper's exit code 0 means only that its listed mechanical checks
succeeded with the observed standard axioms. It does not establish original
problem correspondence or a complete solution. Maintainers independently examine
the original problem and proof and reproduce the checks; a checkbox, summary or
report alone cannot establish acceptance. They may request supporting logs when
resolving a verification issue.

Publish only authorized evidence, with private information and credentials
removed. When sharing full reports, logs or proof artifacts, use the external
proof repository or a stable public evidence archive and link them from the PR.
Short reports may stay in the PR body. Keep Lean proof
source, dependencies and build artifacts out of this repository. The bundled
skill and its synthetic regression fixtures are verification tooling maintained
by this repository, not submitted problem solutions.
