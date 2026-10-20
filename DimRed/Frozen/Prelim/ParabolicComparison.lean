/-
Lemma 2.2 of the corrected edition.
`dimred-corrected-arxiv.tex:314-319` (label `parabolic_comparison`, display
`eq:parabolic_leastaction`):

  "v(t,x) = \min\{ u: \mathcal{G} \to \mathbb{Z}^+: \Delta^{\mathcal{G}}
   u(t,x) + s(t,x) \leq 2d-1 \mbox{ for all $x \in \mathcal{C}$ and $t \geq
   1$} \}"

Here `G = ℤ^+ × C`, `s(t,x) := s_0(x)`, `v(t,x) := v_t(x)`
(`dimred-corrected-arxiv.tex`, label `subsec:parabolic`) and `Δ^G f(t,x) = -2d f(t,x) + ∑_{y ∼
x} f(t-1,y)` for `t ≥ 1` (`dimred-corrected-arxiv.tex`, label `subsec:parabolic`), the sum being
over the neighbours of `x` in `C`, so a competitor `u` is a nonnegative
function on `ℤ^+ × C`, extended by zero off the hypercube. A minimum of a set
of functions is the pointwise minimum: `v` satisfies the constraint, and `v ≤
u` for every `u` that does. The time index is written `t + 1` so that `t ≥ 1`
needs no truncated subtraction.
-/
import DimRed.Support.SignedParabolic

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.parabolic_comparison (d N : ℕ) (hd : 1 ≤ d) (s₀ : Site d → ℤ)
    (hs1 : ∀ y, inCube d N y → s₀ y ≤ 2 * (2 * (d : ℤ)) - 1) :
    (∀ (t : ℕ) (x : Site d), inCube d N x →
        (-(2 * (d : ℤ)) * odo d N s₀ (t + 1) x + nbrSum (odo d N s₀ t) x) + s₀ x
          ≤ 2 * (d : ℤ) - 1) ∧
      ∀ u : ℕ → Site d → ℤ, (∀ t y, 0 ≤ u t y) → (∀ t y, ¬ inCube d N y → u t y = 0) →
        (∀ (t : ℕ) (y : Site d), inCube d N y →
            (-(2 * (d : ℤ)) * u (t + 1) y + nbrSum (u t) y) + s₀ y ≤ 2 * (d : ℤ) - 1) →
        ∀ (t : ℕ) (y : Site d), odo d N s₀ t y ≤ u t y
-- FROZEN-STATEMENT-END
:= signed_parabolic_least_action d N hd s₀ hs1
