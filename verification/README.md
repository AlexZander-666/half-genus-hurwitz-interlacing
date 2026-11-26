# Statement map and reproduction

| Paper claim | Lean declaration |
| --- | --- |
| Theorem 1, original consecutive rows, simple roots, degree, and strict interlacing after removing zero | [`HalfWords.hurwitz_consecutive`](../formal/HalfWords/HurwitzVerified.lean) |
| Theorem 1, polynomial identity and each binomial coefficient | [`HalfWords.hurwitz_binomial_polynomial` and `HalfWords.hurwitz_coefficient`](../formal/HalfWords/BinomialFormula.lean) |
| Theorem 1, rows at $b=0$ and part size 1 | [`HalfWords.zero_mark_row` and `HalfWords.degree_one_row`](../formal/HalfWords/ZeroRows.lean) |
| Theorem 2, normalized Gegenbauer difference for every positive parameter | [`HalfGenus.consecutive_differences`](../formal/HalfGenus/Verified.lean) |
| Original labeled matching words and the counting recurrence | [`HalfWords.raw_cyclic_eq_dp`](../formal/HalfWords/Canonical.lean), [`HalfWords.original_half`](../formal/HalfWords/OriginalCorollary.lean) and [`HalfWords.true_profile`](../formal/HalfWords/ProfileInduction.lean) |
| Formal generating function and the change of variable | [`HalfWords.exact_generating_function`](../formal/HalfWords/ClassicalSeries.lean) and [`HalfWords.pullback`](../formal/HalfWords/Mobius.lean) |

The paper uses part size $m$. In Lean the normalized row parameter `m` means part size `m+1`. The code divides the raw one-part matching-word sum by its part size, in agreement with the paper. The consecutive-root declaration indexes the two starting part sizes as `d+2` and `d+3`.

[`HalfWordsAudit.lean`](../formal/HalfWordsAudit.lean) prints the transitive axioms for the core declarations. The source-cold verifier rebuilds these sources with warnings treated as errors and kernel-replays every local module in a separate process, sharing only the third-party Lake package cache. The [cold-build receipt](lean-cold-receipt.json) records 63 individual replays and 16 declaration audits on the ARM64 Spark. The audit found only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. [Pinned dependency receipt](dependency-receipt.txt)

The independent [Python receipt](python-receipt.txt) concerns the stated finite coefficient and original-word checks. Run `python3 -B certificates/check_half_genus.py` to replay those checks. They serve as corroboration alongside the all-degree Lean proof.

The [reproduction notes](ERRATA.md) give the Python archive layout and clarify two comments in the frozen Lean files. A second source-cold build ran the supplied verifier on x86-64 Lean 4.33.1. The retrieved audit transcript records 63 separate kernel replays, 16 declaration audits, and hashes for all 63 objects. Those hashes match the separate ARM64 Spark receipt. The transcript SHA-256 is `8b876247ae622c0a9924929c3a3530ea94d55959a92f165859be83bb6a7f1748`. The downloaded review ZIP was checked against the frozen source bytes, the nine locked dependencies, and the Spark receipt.
