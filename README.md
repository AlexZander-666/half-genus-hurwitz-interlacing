# Half-genus monotone Hurwitz polynomials

Bowen Zuo, East China University of Science and Technology.

For the connected one-part half-genus $bt$-monotone Hurwitz polynomials of Coulter and Do, the paper proves the coefficient identity and the real-rootedness and consecutive interlacing assertions in every nontrivial degree. For $m\ge2$ and every real $b\ne0$, the degree-$m-1$ row has a simple zero at zero and $m-2$ simple negative zeros. Consecutive rows strictly interlace on the negative axis. The original rows share zero and interlace weakly. The row vanishes for $b=0$ or $m=1$. The same theorem covers the polynomial specialization at $b=-1$. [Paper](paper/main.pdf) · [Single-entry TeX archive](paper/arxiv-source.zip)

The paper also proves both endpoint simplicity and strict consecutive interlacing after removing the two common endpoints from the difference between first-kind Chebyshev and normalized Gegenbauer polynomials with a fixed positive parameter. The binomial sequence itself is known from infinitesimal Wishart and Laguerre moments. The contribution is its identification with the original Hurwitz word sum and the consecutive zero comparison. [Scope and prior work](PRIOR-ART.md)

## Reproduce the results

Run the finite corroboration in Python 3. It independently checks the cut–join–flip coefficient rows through 30 and the original matching words through degree 6.

```sh
python3 -B certificates/check_half_genus.py
```

For the all-degree Lean proof, use the locked Lean v4.33.1 toolchain and the Mathlib revision in `formal/lake-manifest.json`. With compiled third-party packages in a matching Lake cache, run the source-cold verification from the repository root. The audit rebuilds all local modules in a new temporary directory and starts a separate Lean kernel replay for each module.

```sh
python3 -B scripts/check_lock.py /path/to/locked/.lake/packages
python3 -u formal/verify.py /path/to/locked/.lake/packages
```

For a new dependency cache, copy the three project configuration files to a scratch directory with no project sources, then run `lake exe cache get` there. The checked-in manifest pins the resolved dependency revisions. [Lean statements, normalization, and verification](verification/README.md)

The four-page PDF was built using TeX Live 2026 (pdfTeX 1.40.29). With pdfLaTeX including Latin Modern and AMS fonts on the path, copy `paper/main.tex` and `paper/reproduce.py` to a scratch directory and run `python3 reproduce.py` there. The script compiles the source twice from scratch with reproducible settings, doing two LaTeX passes in each directory. Compare the result with the paper and TeX archive hashes in `MANIFEST.sha256`.

[Software and manuscript rights](LICENSE-SCOPE.md) · [Citation](CITATION.cff)

## Authorship

The tagged release v1.0.0 lists Bowen Zuo as sole author. It remains unchanged and may be cited as it is. The manuscript prepared for journal submission lists Bowen Zuo and Xiaojuan Luo as authors and identifies Xiaojuan Luo as the corresponding author. Both authors are affiliated with East China University of Science and Technology.
