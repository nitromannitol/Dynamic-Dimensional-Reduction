/-
Lemma 2.1 of `dimred.tex`, frozen.  `dimred.tex:289-294` (label `pt_ind_lemma`):

  "For each $x \in \mathcal{C}$ and all $t \geq 0$,
   $v_{t+1}(x) = \lfloor \frac{ s_0(x) + \sum_{y \sim x} v_{t}(y) }{2 d} \rfloor$."

The standing hypothesis of the subsection, `dimred.tex:286-288`, is
"let $s_0 \leq 2 (2 d) - 1$ be an arbitrary initial sandpile on $\mathcal{C}$
and $v_t$ its odometer".  That a sandpile is a nonnegative number of chips is
implicit there and is carried as `hs0`; without it the identity is false, as
`s_0 ≡ -1` shows.  Integer division on `ℤ` is floor division for a positive
divisor, so `/ (2 * d)` is the paper's `⌊·/2d⌋`.
-/
import DimRed.Support.Recursion

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.pt_ind_lemma (d N : ℕ) (hd : 1 ≤ d) (s₀ : Site d → ℤ)
    (hs0 : ∀ y, 0 ≤ s₀ y) (hs1 : ∀ y, s₀ y ≤ 2 * (2 * (d : ℤ)) - 1)
    (t : ℕ) (x : Site d) (hx : inCube d N x) :
    odo d N s₀ (t + 1) x = (s₀ x + nbrSum (odo d N s₀ t) x) / (2 * (d : ℤ))
-- FROZEN-STATEMENT-END
:= by sorry
