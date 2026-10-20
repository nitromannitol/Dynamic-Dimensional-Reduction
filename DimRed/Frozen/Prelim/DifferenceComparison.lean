/-
Lemma 2.4 of the corrected edition.
`dimred-corrected-arxiv.tex:459-480` (label `general_difference_comparison`):

  "Let $\mathbf{w} := \{w_1, \ldots, w_n\}$ be a set of points in $\Z^d$ each
   equipped with a function $g_j: \mathcal{S} \to \Z$ which is superharmonic
   in the interior of $\mathcal{S}$. If \sup_{j} \left( D_{w_j} v_{t_0}(x) -
   g_j(x) \right) \leq 0 \mbox{\qquad for all $x \in \mathcal{S}$}

  and for all $t \geq t_0$ and $x \in \{\mathcal{B}_0 \cup
   \mathcal{B}_{\mathbf{w}}\} \mathcal{S}$, \sup_j &\left(\sum_{y\sim
   x}v_t(y)-\sum_{y'\sim(x+w_j)}v_t(y') -2d g_j(x)\right)\leq0 \quad\mbox{and
   $x+w_j\in\mathcal C_N^{(d)}$ for every $j$}\\ &\mbox{ \qquad or } \\
   \sup_{j} &( D_{w_j} v_{t+1}(x) - g_j(x) ) \leq 0

  then \sup_{j} \left( D_{w_j} v_{t+1}(x) - g_j(x) \right) \leq 0 for all $t
   \geq t_0$ and $x \in \mathcal{S}$."

`D_w v_t(x) = v_t(x) - v_t(x+w)` (`dimred-corrected-arxiv.tex`, label `subsec:derivative_comparison`) and the
three pieces of `B_w` are `dimred-corrected-arxiv.tex`, label `eq:dissipative_boundary`. A supremum
over the finite index set being at most zero is every term being at most zero.
The standing hypothesis of the subsection is that the initial sandpile is
constant (`dimred-corrected-arxiv.tex`, label `subsec:derivative_comparison`), carried here as the constant
`c`; the statement takes every integer `c`, so the bound of Section 2 is not
assumed here.
-/
import DimRed.Support.DifferenceComparisonFull

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.general_difference_comparison (d M : ℕ) (hd : 1 ≤ d) (c : ℤ)
    {n : ℕ} (w : Fin n → Site d) (g : Fin n → Site d → ℤ)
    (hg : ∀ k, SuperharmonicIn d M (g k)) (t₀ : ℕ)
    (hinit : ∀ x, inSimplex d M x → ∀ k,
      odo d (2 * M) (fun _ => c) t₀ x - odo d (2 * M) (fun _ => c) t₀ (x + w k) - g k x ≤ 0)
    (hbdry : ∀ t, t₀ ≤ t → ∀ x, inSimplex d M x → (bdry M 0 x ∨ ∃ k, bdry M (w k) x) →
      ((∀ k, inCube d (2 * M) (x + w k) ∧
          nbrSum (odo d (2 * M) (fun _ => c) t) x
          - nbrSum (odo d (2 * M) (fun _ => c) t) (x + w k) - 2 * (d : ℤ) * g k x ≤ 0) ∨
       (∀ k, odo d (2 * M) (fun _ => c) (t + 1) x
          - odo d (2 * M) (fun _ => c) (t + 1) (x + w k) - g k x ≤ 0))) :
    ∀ t, t₀ ≤ t → ∀ x, inSimplex d M x → ∀ k,
      odo d (2 * M) (fun _ => c) (t + 1) x
        - odo d (2 * M) (fun _ => c) (t + 1) (x + w k) - g k x ≤ 0
-- FROZEN-STATEMENT-END
:= DimRed.Corrected.general_difference_comparison d M hd c w g hg t₀ hinit hbdry
