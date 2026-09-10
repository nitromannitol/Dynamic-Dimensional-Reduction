/-
Corollary 2.1 of `dimred.tex`, frozen.  `dimred.tex:513-526`
(label `axis_monotonicity`, "Axis monotonicity"):

  "For all $t \geq 1$, $x \in \mathcal{S}$, and all sets of indices
   $\mathcal{I} = \{ i_1, \ldots, i_n : 1 \leq i_1 < \cdots < i_{n} \leq d \}$
   and $\mathcal{J} = \{ j_1, \ldots, j_m : i_n < j_1 < \cdots < j_{m} \leq d \}$
   where $n \geq 1$ and $m \geq 0$ we have
   $v_t(x) \geq v_t(x + e_{\mathcal{I}} - e_{\mathcal{J}})$ for
   $(x + e_{\mathcal{I}} - e_{\mathcal{J}}) \in \mathcal{S}$."

The condition on the two index sets is that every index of `J` exceeds every
index of `I`, which is what `i_n < j_1` says once both are listed in increasing
order.  The standing hypothesis of the subsection is that the initial sandpile
is constant (`dimred.tex:434-436`), carried here as `c`.
-/
import DimRed.Support.Recursion

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.axis_monotonicity (d M : ℕ) (hd : 1 ≤ d) (c : ℤ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 2 * (2 * (d : ℤ)) - 1)
    (t : ℕ) (ht : 1 ≤ t) (x : Site d) (hx : inSimplex d M x)
    (I J : Finset (Fin d)) (hI : I.Nonempty) (hIJ : ∀ i ∈ I, ∀ j ∈ J, i < j)
    (hmem : inSimplex d M (x + ∑ i ∈ I, unit i - ∑ j ∈ J, unit j)) :
    odo d (2 * M) (fun _ => c) t (x + ∑ i ∈ I, unit i - ∑ j ∈ J, unit j)
      ≤ odo d (2 * M) (fun _ => c) t x
-- FROZEN-STATEMENT-END
:= by sorry
