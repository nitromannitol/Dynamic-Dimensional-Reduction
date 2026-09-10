/-
Proposition 3.2 of `dimred.tex`, frozen.  `dimred.tex:789-810`
(label `prop:base_case`):

  "For all $d \geq 1$, when $s_0^{(d)} = 2 d + (d-1)$, the radially
   reparameterized parallel toppling odometer has the following form.  For all
   $t \geq 1$,
   $v_t(x) = v_{t-1}(x)+1$ for $x \leq a_{t}$ and $v_t(x) = v_{t-1}(x)$ for
   $a_{t} < x \leq a_{t-1}$.
   And for each $t' < t$ and $a_{t'-1} \geq x > a_{t'}$,
   $v_{t}(x) = v_{t-1}(x-1)$."

The setting is `M = 2`, hence the hypercube `C_4^{(d)}` (`dimred.tex:722-723`
and `dimred.tex:428-431`), and `x` is the radial coordinate of
`dimred.tex:724-727`, so `v_t(x)` is the odometer at `radial d x`.  `a_t` is
`blockEdge`, `dimred.tex:784-790`.  Time is written `t + 1` so that `t ≥ 1` and
`t - 1` need no truncated subtraction, and the ripple's `t'` is written `s + 1`
for the same reason.
-/
import DimRed.Support.Recursion

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.base_case (d : ℕ) (hd : 1 ≤ d) (t : ℕ) :
    (∀ x : ℕ, x ≤ d →
        ((x : ℤ) ≤ blockEdge d (t + 1) →
          odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t + 1) (radial d x)
            = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) + 1) ∧
        (blockEdge d (t + 1) < (x : ℤ) → (x : ℤ) ≤ blockEdge d t →
          odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t + 1) (radial d x)
            = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x))) ∧
      ∀ s : ℕ, s + 1 ≤ t → ∀ x : ℕ, x ≤ d →
        (x : ℤ) ≤ blockEdge d s → blockEdge d (s + 1) < (x : ℤ) →
        odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t + 1) (radial d x)
          = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d (x - 1))
-- FROZEN-STATEMENT-END
:= by sorry
