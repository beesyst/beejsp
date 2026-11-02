## Publication packaging boundary

Current portable instructions and source mapping are in [README.md](README.md); the eleven-edition provenance inventory is in [SOURCES.md](SOURCES.md). The selected reproducible check inputs are listed explicitly in `verification/portable-suite.json`. These files describe the proposed COMMITTED REPRODUCIBLE EVIDENCE category; no proof commit or clean committed reproduction is claimed yet.

All content below this boundary is preserved LOCAL HISTORICAL EVIDENCE. Historical references to receipts, generated logs, excluded verification files, PDFs, scans and old absolute scratch paths are informational local references. They do not add required files or commands to the portable package. Historical COMPLETE, PARTIAL, FAILED and pending claims retain their original time-specific meaning; this packaging notice does not rewrite a milestone or create M260. Not all historical receipts are included in the proposed publication.

---

# JSP-000334 statement contract

Status: the original principal theorem is proved locally by `JSP000334.newman_conjecture_complete` in M259, within Issue #22 and existing Iteration 8. Exact endpoint, literal/raw, axiom and regression evidence is recorded in `verification/six-term-newman-259-*`. Independent final read-only review and committed-source clean reproduction remain separate delivery gates; this status does not close the Issue or Iteration.

The target is JSP-000334 / Erdős Problem #407, attributed to D. J. Newman and recorded in Erdős–Graham (1980), page 80. Tijdeman–Wang (1988), page 177, explicitly describe the original function as the number of solutions of `n = 2^a + 3^b + 2^c * 3^d`. EGST88, Theorem 7(a), pages 138–139, proves the corresponding qualitative boundedness result. Its general convention identifies permutations of summands. The approved Issue fixes ordered exponent tuples as the BeeJSP contract.

`JSP000334.Exponents` contains four independent natural numbers, including zero. `solutions n` is the set of all such records with `value r = n`. `tupleCount n` is its `Set.ncard`. `solutions_finite` proves that every solution has all four exponents strictly below `n`, including the mixed term's two exponents; hence `Set.ncard` is an actual finite count rather than its value on infinite sets. `zero_solutions` handles zero separately. No coprimality, distinct-summand, positive-exponent or upper-bound restriction enters the solution predicate.

The exact principal proposition, already checked by Lean, is:

```lean
def NewmanConjecture : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, 0 < n → tupleCount n ≤ C
```

The unconditional declaration is `JSP000334.newman_conjecture_complete : NewmanConjecture` in `SubspaceBridge/NewmanCompletion.lean`. The earlier reserved name `jsp_000334` is not declared; no placeholder or additional assumption is introduced.

## Parameterization

The source parameterization is `2^a * 3^b + 2^c + 3^d`. `sourceEquiv` sends `(a,b,c,d)` to `(c,d,a,b)` and is its own inverse. `sourceValue_eq` proves equality of represented values, and `source_parameterization_count` proves exact equality of the two raw tuple counts for every `n`.

## Counting conventions

`summandList` is `[2^a, 3^b, 2^c * 3^d]`; `summands` is its multiset, retaining repeated summands. `multisetSolutions n` is the image of all solutions under `summands`. `multisetCount n` counts these images.

`mixed_exponents_injective` recovers the mixed exponents from prime factorizations at 2 and 3. Together with injectivity of powers, `summandList_injective` shows that a labeled numerical triple determines the four exponents. For a fixed multiset, all such lists are among the permutations of one length-three list. The length of its permutation list is `3! = 6`, even when some permutations coincide. Summing this fiber bound proves:

```text
multisetCount n ≤ tupleCount n ≤ 6 * multisetCount n
```

`counting_conventions_equivalent` proves equivalence of the two qualitative uniform-boundedness statements, with the bound transformed by multiplication by 6. No claim is made that the optimal fiber bound is 6 or that the two counts coincide. The later bound 9 must not be assigned directly to the raw count. The conservative bridge would give 54 if that multiset bound were separately proved.

Tijdeman–Wang's definition is explicitly permutation equivalence. Bajpai–Bennett display braces in their distinctness definition; this project uses the multiset convention requested by the Issue. The selected qualitative route uses Tijdeman–Wang's unambiguous convention and does not require a set-versus-multiset interpretation of the later numerical bound.

## Attribution

Mathematical problem: D. J. Newman, recorded by Paul Erdős and Ronald Graham. Original solution: Jan-Hendrik Evertse, Kálmán Győry, Cameron L. Stewart and Robert Tijdeman. Later results: Robert Tijdeman and Lianxiang Wang; Prajeet Bajpai and Michael A. Bennett. Current original Lean definitions and elementary proofs were authored with OpenAI Codex assistance in this worktree. No independent verifier, mathematical discovery, official acceptance or priority is claimed.

## Conditional fixed-group theorem (M3.2)

`FixedReference.lean` defines `fixedSUnitGroup = Subgroup.closure {-1, twoUnit, threeUnit}`, where the generator values are exactly `-1`, `2`, `3` in `ℚˣ`. `FixedSUnitFiniteness` is `∀ m : Fin 5, (normalizedRelations fixedSUnitGroup (m.val + 1)).Finite`. Since a relation in that set has `m.val + 2` coordinates, this asserts normalized nondegenerate finiteness at exactly lengths 2–6, for this fixed group only. Normalization, nonzero coordinates, total zero sum and all proper nonempty subsum conditions are inherited unchanged from `Spike.lean`.

The checked declaration is `newman_of_fixed_sunit_finiteness (hfin : FixedSUnitFiniteness) : NewmanConjecture`. Its conclusion is the original proposition above, counting all ordered natural exponent tuples for every positive `n`. Its explicit hypothesis is now proved unconditionally by `fixed_sunit_finiteness_complete`, using the exact accepted two-, three-, four-, five- and six-term finiteness endpoints. The unchanged conditional implication yields `newman_conjecture_complete`; `jsp_000334` is not declared.

The proof compares every representation with one fixed representation of the same `n`. Each selected term lies in a minimal signed zero block containing an opposite-side term. Ratios extracted from normalized blocks lie in one finite set independent of `n`; choices of three reference indices and three ratios give an injective code for exponent tuples. Empty solution sets have count zero. No distinct-summand or positive-exponent assumption is used, so repeated summands and zero exponents remain included. The existing ordered/multiset counting bridge is preserved; this direct argument bounds ordered tuples without needing that bridge as an intermediate step.
