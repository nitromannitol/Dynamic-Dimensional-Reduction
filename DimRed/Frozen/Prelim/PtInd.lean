/-
Lemma 2.1 of `dimred.tex`, frozen.  `dimred.tex:289-294` (label `pt_ind_lemma`):

  "For each $x \in \mathcal{C}$ and all $t \geq 0$,
   $v_{t+1}(x) = \lfloor \frac{ s_0(x) + \sum_{y \sim x} v_{t}(y) }{2 d} \rfloor$."

The standing hypothesis of the subsection, `dimred.tex:286-288`, is
"let $0 \leq s_0 \leq 2 (2 d) - 1$ be an arbitrary initial sandpile on
$\mathcal{C}$ and $v_t$ its odometer", carried as `hs0` and `hs1`.  Integer division on `ℤ` is floor division for a positive
divisor, so `/ (2 * d)` is the paper's `⌊·/2d⌋`.
-/
import DimRed.Support.Recursion

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.pt_ind_lemma (d N : ℕ) (hd : 1 ≤ d) (s₀ : Site d → ℤ)
    (hs0 : ∀ y, inCube d N y → 0 ≤ s₀ y)
    (hs1 : ∀ y, inCube d N y → s₀ y ≤ 2 * (2 * (d : ℤ)) - 1)
    (t : ℕ) (x : Site d) (hx : inCube d N x) :
    odo d N s₀ (t + 1) x = (s₀ x + nbrSum (odo d N s₀ t) x) / (2 * (d : ℤ))
-- FROZEN-STATEMENT-END
:= by
  have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  have hb := sandp_bounds d N s₀ hs0 hs1 t x hx
  have hsucc := odo_succ_eq d N s₀ t x hx
  have hsandp : sandp d N s₀ t x
      = s₀ x + nbrSum (odo d N s₀ t) x - 2 * (d : ℤ) * odo d N s₀ t x := by
    simp only [sandp, lap]; ring
  rw [hsucc]
  refine (ediv_unique hdpos ?_ ?_).symm
  · split
    · rename_i hcase; rw [hsandp] at hcase hb; linarith [hb.1, hb.2]
    · rename_i hcase; rw [not_le, hsandp] at hcase; rw [hsandp] at hb; linarith [hb.1, hb.2]
  · split
    · rename_i hcase; rw [hsandp] at hcase hb; linarith [hb.1, hb.2]
    · rename_i hcase; rw [not_le, hsandp] at hcase; rw [hsandp] at hb; linarith [hb.1, hb.2]
