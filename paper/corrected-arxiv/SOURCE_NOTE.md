# The corrected edition

`dimred-corrected-arxiv.tex` is a corrected edition of *Dynamic dimensional reduction in the
Abelian sandpile*, starting from [arXiv v2](https://arxiv.org/abs/2009.05968v2), whose
unmodified source is [`../dimred-arxiv.tex`](../dimred-arxiv.tex). The abstract and the
statements of Theorem 1.1 and Corollary 1.1 are unchanged, except that the hitting time in
Theorem 1.1(ii) is defined with its quantifier made explicit. Every change is listed, with the
published text, the corrected text and the reason, in the section "Corrections to the published
version" at the end of the corrected edition, and in the repository README.

The Lean statements follow this edition, whose SHA-256 is recorded in `ledger/manifest.yaml`.
Line references in the comments of `DimRed/` are to this file.

The bibliography and the figures are included. Build from this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error dimred-corrected-arxiv.tex
```
