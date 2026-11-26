# Reproduction and wording clarifications

The finite Python checks belong to the complete research ZIP. From its root, run `python3 -B certificates/check_half_genus.py`. The directory contains the two companion Python modules it imports. The standalone Lean ZIP has its own `verify.py` and pinned Lake manifest. To run both checks from separate downloads, use this repository or the complete research ZIP for Python and the standalone Lean ZIP for the source-cold Lean check.

The original review packet's `verification/STATEMENTS.md` pointed to the Python certificate path without including the certificate directory. The complete research ZIP includes and runs that program, its local imports, and its expected output.

Two comments in the frozen Lean source need clarification. In [`HalfWords/HurwitzVerified.lean`](../formal/HalfWords/HurwitzVerified.lean#L50), (d+2) and (d+3) are **part sizes**. The degrees of the two original polynomials are (d+1) and (d+2), as stated in the theorem. In [`Hurwitz/WordWeights.lean`](../formal/Hurwitz/WordWeights.lean#L111), the normalization in Proposition 4.18 is the product of **all** profile parts. For the one-part profiles here, that factor is the part size.

The PDF, Lean source and Lean verifier are the frozen versions whose bytes are identified in the audit receipts.
