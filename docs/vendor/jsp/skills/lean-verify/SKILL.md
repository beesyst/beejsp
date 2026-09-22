---
name: lean-verify
description: "Independently verify Lean mathematical proofs in awards PRs, Erdős problems, or pinned source revisions. Check the original statement, coverage, reproducibility, and axiom dependencies, then produce an English evidence report. Applies to Lean proofs, not solver-only submissions; does not repair proofs, modify submissions, or publish reviews automatically."
---

# Independent Lean proof verification

Verify a complete formal proof of a specified mathematical problem at a specified source commit. Assess source traceability, correspondence to the original problem, reproducibility, and coverage separately. A successful build, an author's claim, a catalog's `Solved/Yes` status, or PR CI cannot replace these conclusions.

Write reports in English by default, unless the user requests another language. Preserve Lean identifiers, original problem statements, and raw logs. Verification includes necessary dependency downloads, isolated environment setup, and local audit files. It does not include modifying the original proof, upgrading its toolchain, posting GitHub comments, merging PRs, or changing catalog status.

## Scope

This skill is a recommended pre-submission self-check for Lean proofs, not a requirement for opening a PR. Contributors may use other verification methods; not using this skill is not a submission defect. Contributors submitting only mathematical solutions, papers, or solver information need neither this skill nor a Lean repository, self-check declaration, or verification report. The absence of a Lean proof does not invalidate a mathematical submission. For combined submissions, apply this skill only to the Lean contribution.

For a solver-only PR, state "Lean verification is not applicable" and end this workflow. Do not request Lean materials or classify the submission as "Verification failed" or "Insufficient evidence." Mathematical correctness and attribution remain subject to the mathematical review process.

## Inputs and working directory

- Accept awards PRs (normalize `/files`, `/commits`, and comment anchors), Erdős problem numbers/URLs, or Lean repositories/commits/PRs with an original problem source. Use JSP catalog entries in awards mode; for Erdős and direct-source inputs, first read [Input routing](references/input-routing.md). A homepage or PR list alone does not authorize choosing an arbitrary problem or submission.
- The user may specify a historical PR head, problem, scope, resource limits, and output directory. Without a historical revision, snapshot the current PR head and cover every problem and every Lean version claimed complete in that PR. For other inputs, determine scope using the routing reference.
- Create a separate run directory outside the repository, such as `lean-verify-problem-or-pr-timestamp` in the system temporary directory. Store `evidence/`, `sources/`, `audit/`, `logs/`, and `report.md`. Trusted tool caches may be reused; do not overwrite the user's working tree. Provide absolute artifact paths and identify where temporary outputs are stored.
- Ask only when missing information blocks a judgment; continue independent checks. If the specified source or original problem cannot be obtained, report "Insufficient evidence" rather than substituting a similar problem or the latest branch.

## 1. Pin the input, original problem, and source revision

The awards-specific steps below apply only to awards PRs. Use the routing reference for other inputs without inventing JSP identifiers or PR acceptance criteria.

Use GitHub tools/API or `gh` to retrieve the PR body, paginated file list, diff, commits, issue comments, reviews, and inline comments. Read linked issues and complete source files when needed; use Git snapshots when API patches are truncated. Record retrieval times and evidence gaps.

Keep two sets of revisions distinct:

1. **Awards PR:** repository, PR URL, base/head repositories and branches, and full base/head SHAs. Review the head contents; do not mistake GitHub's test merge commit for the submission head.
2. **Lean proof:** original link, repository, project subdirectory, submitter-specified branch, full 40-character commit SHA, source files, and fully qualified declaration names.

Locate `JSP-xxxxxx` in the changed `problems/catalog-*.md` files and PR body. Read the complete entry and original mathematical sources. JSP numbers differ from Erdős and other source identifiers. Compare problem descriptions at PR base/head to detect a narrowed or rewritten problem; do not verify solely against the submitter's revised statement.

Prefer the explicitly submitted source commit. If only a branch/tag is supplied, resolve its full SHA as a **temporary audit snapshot** and record the time. The missing submission revision remains a traceability gap; do not claim the snapshot was the version submitted. When links, body, comments, and catalog disagree, list the conflicts and use explicit update evidence to select a version. Do not silently combine evidence from different revisions.

Verify that the commit exists, checkout HEAD matches, and the files exist at that commit. Resolve the current branch tip and check whether the selected commit is its ancestor; the branch may advance, so the commit need not equal the tip. If deletion or force-pushing prevents checking historical membership, report that limitation. Current non-membership does not prove past non-membership. Re-read the PR head after the audit; if it changed, limit the report to the original snapshot rather than following updates indefinitely.

## 2. Check that the proof addresses the original problem

Follow [Target manifests and automated checks](references/automation.md) to independently enumerate all original requirements in `targets.json`. Map each requirement to targets/bridges and explicitly retain uncovered requirements. Use one manifest per pinned source project; create separate manifests for different repositories/revisions and summarize them together. Review the manifest itself: the script cannot detect natural-language requirements omitted from it.

Follow [Statement and completeness audit](references/statement-audit.md) to produce a matrix: original requirement → Lean definition/declaration → correspondence → evidence → gap.

Establish the intended target from original sources before inspecting the submitted Lean formulation. Expand parameters, implicit arguments, section variables, typeclass instances, definitions, and notation. Compare objects, quantifiers, scope, assumptions, conclusions, and boundary cases. An equivalent formulation or stronger result may solve the problem, but the implication bridge must be checked. A counterexample may also fully resolve it; verify that it refutes the same proposition.

When execution is possible, write a minimal target statement and `example : IntendedStatement := ...` in a separate audit file, connecting it to the submitted theorem. Build the intended definitions from original sources and trusted libraries; renaming a suspect definition is not an independent check. Correspondence between prose and a formal statement still requires mathematical review and is not automatically proved by this bridge.

If scope does not match, continue independent build/axiom checks where possible. Report "the code can be checked" separately from "the specified problem is not solved."

## 3. Set up and reproduce

Follow [Pinned revisions and reproduction](references/reproduction.md). Start with `scripts/audit.py preflight` to identify revision, file, and lockfile gaps. Manually verify isolation, actual dependency SHAs, tool versions, and checker compatibility; preflight neither executes project code nor establishes environment safety. Read the pinned `lean-toolchain`, Lake configuration, manifest, and CI. Use the exact toolchain and dependencies; do not choose the latest versions and claim the original submission passed.

In an isolated environment without exposed credentials or host write access, build the original project, explicitly check each target module, and check the audit files. Confirm whether each target belongs to the default build; explicitly check those that do not. Library proofs need no `main`, and ordinary program execution or `#eval` output does not replace theorem checking.

After the unmodified clean build, run `scripts/audit.py run` inside the isolated environment to check each target's build, source, and axioms. It does not replace the clean build, semantic review, or independent checkers. For unsupported versions/identifiers, perform equivalent manual checks under the reproduction reference and record limitations; do not modify the proof to fit the tool.

Retain commands, working directories, versions, dependency SHAs, exit codes, elapsed times, and complete logs. Distinguish network failures, resource exhaustion, environment incompatibility, and theorem-check failures. Diagnostic repairs belong in a separate copy with a recorded patch and retest; success after repair is not success of the original submission.

## 4. Proof completeness and trust boundaries

Run `#check`, `#print`, and `#print axioms` for **every target theorem and audit bridge**, preserving output. Inspect the actual meaning and dependencies of key definitions. Keyword scans locate leads but do not replace transitive dependency audits. Failed commands or missing expected output cannot establish "no axioms/no sorry."

- A target depending on `sorryAx`, the expansion of `admit`, placeholders, or unproved axioms replacing essential proof steps is incomplete.
- Treat ordinary `propext`, `Classical.choice`, and `Quot.sound` as the standard classical Lean foundations, not missing proofs.
- Retain assumptions present in the original problem, but exclude extra, circular, or impossible premises. Local assumptions may not appear in `#print axioms`.
- Review each custom axiom's source and necessity; do not allow it by name alone. For problems about axiom systems or independence, model the object-level meaning rather than assuming the desired conclusion at Lean's metalevel.
- Report dependencies from `native_decide`, `decide +native`, or other native computation separately. Record actual axiom names for that toolchain and the compiler/runtime/external implementation being trusted. These are neither equivalent to `sorry` nor free of additional trust.
- Trace `debug.skipKernelTC`, environment-modifying metaprograms, fabricated output, `implemented_by`/`extern`, and related mechanisms along the target's dependency path. Determine their actual effect; the mere presence of `unsafe` does not invalidate the entire proof.

For award PRs, attempt kernel replay compatible with the pinned toolchain. Where compatible, also use an independently defined challenge with a comparator/external checker. Follow the reproduction reference for version adaptation. Record the levels actually completed; unavailable tools leave a stated gap, not a claim of independent verification. Describe which guarantees a failure affects; checker incompatibility is not a mathematical counterexample.

## 5. Verdict and deliverables

Use the [Report template](references/report-template.md) for a self-contained `report.md`, in English by default, with `targets.json`, automated results, and raw logs. Script exit code 0 only means the listed targets completed that level of mechanical checking with only standard axioms observed. It does not directly establish "Verification passed" or "Fully solved." For each problem, report traceability, semantic correspondence, build results, completeness, coverage, and verification levels. Support every key finding with a commit-pinned link or local file:line, original source, and log location.

Choose and justify one overall verdict:

| Verdict | Conditions |
| --- | --- |
| Verification passed | The specified revision is traceable; all original requirements match the formal statement; the unmodified build and all target checks pass; no proof gaps or unresolved extra assumptions remain; trust dependencies are verified. State the actual verification levels and trust scope. |
| Conditional pass | Full semantic coverage and checks hold, but rely on explicit, explainable extended trust, such as native computation. This cannot excuse missing proofs or unproved assumptions stronger than the original problem. |
| Partial coverage | Checked proofs cover some requirements, but others remain unresolved. This is not a complete formalization. |
| Verification failed | The specified submission fails in a matching environment, or evidence establishes a statement mismatch, proof gap, or similar defect. Identify the failing dimension. |
| Insufficient evidence | Required materials cannot be obtained/pinned, checks cannot be completed, the original meaning is unclear, or essential dependencies remain unverified. Do not infer that the mathematical result is false. |

Record verification levels separately: static review, actual Lean checks, kernel replay, and independent challenge + external checking. Multiple completed levels may be listed. Static review alone cannot yield "Verification passed." Do not hide a failed cross-check behind an overall pass; explain its cause and the remaining guarantees.

A multi-problem PR passes overall only if every problem meets the requirements. Highlight any confirmed failure while listing other blockers and partial successes separately. Judge completeness by coverage of original obligations, not source lines, theorem counts, or invented percentages. Do not infer award eligibility, identity, priority, or prize decisions.

### Give an explicit conclusion

Start both the report and final user response with the verdict, not only a procedure, logs, or a request to read the report. Select a verdict above, then state **whether this Lean submission fully solves the specified original problem at the checked commit, and why**.

Answer each question explicitly with decisive evidence:

1. **Does the proof address the specified original problem?** Yes / No / Cannot yet determine. Identify correspondence or mismatch in key definitions, quantifiers, and scope.
2. **Did the specified commit actually pass verification?** Yes / No / Verification incomplete. State target-check results; do not substitute another commit or a patched version.
3. **Does it fully solve the original problem?** Yes / No / Cannot yet determine. A complete disproof may warrant "Yes," with an explanation. Partial results, missing subproblems, or a target depending on `sorry` or circular assumptions require "No." A build failure alone, without a confirmed mathematical gap, does not establish that no complete proof exists.
4. **Does it meet the Lean completeness requirements for this verification (the PR's acceptance requirements, when applicable)?** Meets / Does not meet / Cannot yet determine. Limit this judgment to mathematics and formal verification, not merging or awards.

Acceptance rules: use "Meets" when all necessary checks pass with full coverage; "Does not meet" for a confirmed mismatch, proof gap, partial coverage, or failure of the specified version in a matching environment; otherwise use "Cannot yet determine" when necessary evidence/checks are missing and no disqualifying defect is confirmed. A "Conditional pass" must explain the extended trust and its effect. Only if the applicable acceptance criteria explicitly accept that trust may the answer be "Meets (within the stated trust scope)." Otherwise use "Cannot yet determine"; do not assume unspecified criteria accept it.

An explicit conclusion need not be binary. "Cannot yet determine" is valid if accompanied by missing evidence, affected judgments, and the minimum next actions. Avoid vague endings such as "mostly fine," "probably passes," or "looks complete." Assess each problem before summarizing; one success cannot conceal another failure or unknown.

The final response includes the overall verdict, all four judgments, key evidence/outstanding checks, and the report link. Publish reports or comments only when explicitly requested.

## Maintenance and regression checks

After modifying the automation script, run `python3 -m unittest discover -s tests -v` from the skill directory. Optionally set `LEAN_AUDIT_TEST_LAKE` to an installed, trusted Lake executable's absolute path for real Lean regression tests without third-party dependencies. These run only the skill's fixed fixtures. See [Automation and test boundaries](references/automation.md). Do not present simulated-output tests as actual Lean checks.
