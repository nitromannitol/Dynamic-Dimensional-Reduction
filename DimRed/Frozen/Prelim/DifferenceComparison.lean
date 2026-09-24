/-
Lemma 2.4 of `dimred.tex`, frozen.  `dimred.tex:473-492`
(label `general_difference_comparison`):

  "Let $\mathbf{w} := \{w_1, \ldots, w_n\}$ be a set of points in $\Z^d$ each
   equipped with a function $g_j: \mathcal{S} \to \Z$ which is superharmonic in
   the interior of $\mathcal{S}$.  If
   $\sup_j ( D_{w_j} v_{t_0}(x) - g_j(x) ) \leq 0$ for all $x \in \mathcal{S}$
   and for all $t \geq t_0$ and $x \in \{\mathcal{B}_0 \cup
   \mathcal{B}_{\mathbf{w}}\} \mathcal{S}$,
   $\sup_j ( \sum_{y \sim x} v_{t}(y) - \sum_{y' \sim (x + w_j)} v_{t}(y')
   - 2 d g_j(x) ) \leq 0$ and $x + w_j \in \mathcal{C}_N$ for all $j$, or $\sup_j ( D_{w_j} v_{t+1}(x) - g_j(x) ) \leq 0$,
   then $\sup_j ( D_{w_j} v_{t+1}(x) - g_j(x) ) \leq 0$ for all $t \geq t_0$ and
   $x \in \mathcal{S}$."

`D_w v_t(x) = v_t(x) - v_t(x+w)` (`dimred.tex:437-439`) and the three pieces of
`B_w` are `dimred.tex:453-467`.  A supremum over the finite index set being at
most zero is every term being at most zero.  The standing hypothesis of the
subsection is that the initial sandpile is constant (`dimred.tex:434-436`),
carried here as the constant `c` with the bound of Section 2.
-/
import DimRed.Support.DifferenceStep

set_option maxHeartbeats 1000000

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.general_difference_comparison (d M : ℕ) (hd : 1 ≤ d) (c : ℤ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 2 * (2 * (d : ℤ)) - 1)
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
:= by
  have hmain : ∀ t, t₀ ≤ t → ∀ x, inSimplex d M x → ∀ k,
      odo d (2 * M) (fun _ => c) t x - odo d (2 * M) (fun _ => c) t (x + w k) - g k x ≤ 0 := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => intro x hx k; exact hinit x hx k
    | succ n hn ih =>
      intro x hx k
      by_cases hb : bdry M 0 x ∨ ∃ k, bdry M (w k) x
      · rcases hbdry n hn x hx hb with h1 | h2
        · exact difference_boundary_step d M hd c hc0 hc1 (w k) (g k) n x hx (h1 k).1 (h1 k).2
        · exact h2 k
      · have hstrict : (∀ i : Fin d, x i < (M : ℤ)) ∧ (∀ i : Fin d, 1 < x i) ∧
            (∀ i j : Fin d, i < j → x j < x i) := by
          simpa [add_zero] using not_bdry_strict M 0 x (fun h0 => hb (Or.inl h0))
        have hstrictw : (∀ i : Fin d, (x + w k) i < (M : ℤ)) ∧
            (∀ i : Fin d, 1 < (x + w k) i) ∧
            (∀ i j : Fin d, i < j → (x + w k) j < (x + w k) i) :=
          not_bdry_strict M (w k) x (fun hw => hb (Or.inr ⟨k, hw⟩))
        have hx0 : ∀ i : Fin d, inSimplex d M (x + unit i) ∧ inSimplex d M (x - unit i) :=
          fun i => ⟨inSimplex_add_unit d M x hx hstrict.1 hstrict.2.1 hstrict.2.2 i,
                    inSimplex_sub_unit d M x hx hstrict.1 hstrict.2.1 hstrict.2.2 i⟩
        have hxwS : inSimplex d M (x + w k) :=
          inSimplex_of_strict M (x + w k) hstrictw.1 hstrictw.2.1 hstrictw.2.2
        have hxw : ∀ i : Fin d,
            inSimplex d M (x + w k + unit i) ∧ inSimplex d M (x + w k - unit i) :=
          fun i => ⟨inSimplex_add_unit d M (x + w k) hxwS
                      hstrictw.1 hstrictw.2.1 hstrictw.2.2 i,
                    inSimplex_sub_unit d M (x + w k) hxwS
                      hstrictw.1 hstrictw.2.1 hstrictw.2.2 i⟩
        exact difference_interior_step d M hd c hc0 hc1 (w k) (g k) (hg k) n x hx hx0 hxw
          (inSimplex_inCube d M (x + w k) hxwS)
          (fun y hy => ih y hy k)
  intro t ht x hx k
  exact hmain (t + 1) (by omega) x hx k
