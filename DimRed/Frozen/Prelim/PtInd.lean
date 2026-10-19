/-
Lemma 2.1 of the corrected arXiv-format draft, frozen.
`dimred-corrected-arxiv.tex:291-297` (label `pt_ind_lemma`):

  "For each $x \in \mathcal{C}$ and all $t \geq 0$, v_{t+1}(x) =
   \max\left\{0,\left\lfloor \frac{s_0(x)+\sum_{y\sim
   x}v_t(y)}{2d}\right\rfloor\right\}."

The standing hypothesis of the subsection, `dimred-corrected-arxiv.tex:290`,
is "let $s_0 \leq 2 (2 d) - 1$ be an arbitrary initial sandpile on
$\mathcal{C}$ and $v_t$ its odometer", carried as `hs1`; the corrected
hypothesis has no lower bound on `s_0`, and none is carried. Integer division
on `ℤ` is floor division for a positive divisor, so `/ (2 * d)` is the paper's
`⌊·/2d⌋`, and the `max 0` of the statement is the outer `max {0, ·}` of the
corrected display.
-/
import DimRed.Support.SignedUpdateZero

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.pt_ind_lemma (d N : ℕ) (hd : 1 ≤ d) (s₀ : Site d → ℤ)
    (hs1 : ∀ y, inCube d N y → s₀ y ≤ 2 * (2 * (d : ℤ)) - 1)
    (t : ℕ) (x : Site d) (hx : inCube d N x) :
    odo d N s₀ (t + 1) x =
      max 0 ((s₀ x + nbrSum (odo d N s₀ t) x) / (2 * (d : ℤ)))
-- FROZEN-STATEMENT-END
:= odo_succ_eq_max_zero_quotient d N hd s₀ hs1 t x hx
