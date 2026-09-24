/-
Corollary 2.1 of `dimred.tex`, frozen.  `dimred.tex:513-527`
(label `axis_monotonicity`, "Axis monotonicity"), attributed to Babai and
Gorodezky:

  "For all $t \geq 1$, $x \in \mathcal{S}$, every index $1 \leq i \leq d$,
   and every set of indices $\mathcal{J}$ that is either empty or equal to
   $\{ j \}$ for an index $i < j \leq d$, we have
   $v_t(x) \geq v_t(x + e_{\mathcal{I}} - e_{\mathcal{J}})$ for
   $(x + e_{\mathcal{I}} - e_{\mathcal{J}}) \in \mathcal{S}$
   where $\mathcal{I} = \{ i \}$."

One index up and at most one index down is the statement of the source the
corollary cites. Babai and Gorodezky's Definition 5.2 calls `f` axis monotone
when `f(r) ≤ f(s)` for each pair of lattice points with `s - r` perpendicular to
one axis of symmetry of `f` and `s` closer to that axis than `r`: one step,
perpendicular to one axis. On `S_M^{(d)}` the axes of symmetry are the
reflections `x_i = 1/2`, whose perpendicular step is `e_i`, and the rotations
`x_i = x_j`, whose perpendicular step is `e_i - e_j` with `i < j`. Those are the
two moves below. The use in Section 5 of the paper (`dimred.tex:1467`) is a
chain of the moves frozen here.

The standing hypothesis of the subsection is that the initial sandpile is
constant (`dimred.tex:434-436`), carried here as `c`.  The paper's `t ≥ 1` is
carried too, although the proof does not need it: at `t = 0` both sides are
zero.
-/
import DimRed.Support.AxisStep

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.axis_monotonicity (d M : ℕ) (hd : 1 ≤ d) (c : ℤ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 2 * (2 * (d : ℤ)) - 1)
    (t : ℕ) (_ht : 1 ≤ t) (x : Site d) (hx : inSimplex d M x)
    (i : Fin d) (J : Finset (Fin d)) (hJ : J.card ≤ 1) (hiJ : ∀ j ∈ J, i < j)
    (hmem : inSimplex d M (x + unit i - ∑ j ∈ J, unit j)) :
    odo d (2 * M) (fun _ => c) t (x + unit i - ∑ j ∈ J, unit j)
      ≤ odo d (2 * M) (fun _ => c) t x
-- FROZEN-STATEMENT-END
:= by
  rcases Nat.lt_or_ge J.card 1 with h0 | h1
  · have hJ0 : J = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hJ0
    simp only [Finset.sum_empty, sub_zero]
    exact odo_axis_refl d M hd c hc0 hc1 t x i (hx.1 i).1
  · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (le_antisymm hJ h1)
    subst hj
    simp only [Finset.sum_singleton]
    exact odo_axis_rot d M hd c hc0 hc1 t x i j
      (hx.2 i j (le_of_lt (hiJ j (Finset.mem_singleton_self j))))
