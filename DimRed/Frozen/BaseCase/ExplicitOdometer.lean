/-
Proposition 3.2 of the corrected edition.
`dimred-corrected-arxiv.tex:699-723` (label `prop:base_case`):

  "For all $d \geq 1$, when $s_0^{(d)} = 2 d + (d-1)$, the radially
   reparameterized parallel toppling odometer has the following form. For all
   $t \geq 1$, v_t(x) = \begin{cases} v_{t-1}(x) + 1 &\mbox{ for $x \leq
   a_{t}$} \\ v_{t-1}(x) &\mbox{ for $a_{t} < x \leq a_{t-1}$}. \end{cases}
   And for each $1\leq t'<t\leq t'+x$ and $a_{t'-1}\geq x>a_{t'}$,
   v_t(x)=v_{t'}(x-(t-t'))."

The setting is `M = 2` (`dimred-corrected-arxiv.tex`, label `subsec:M2`), hence the
hypercube `C_4^{(d)}` since `N = 2M` (`dimred-corrected-arxiv.tex`, label `subsec:symmetry`),
and `x` is the radial coordinate of `dimred-corrected-arxiv.tex`, label `subsec:M2`, so
`v_t(x)` is the odometer at `radial d x`. `a_t` is `blockEdge`,
`dimred-corrected-arxiv.tex`, label `subsec:M2`. Time is written `t + 1` so that `t ≥ 1`
and `t - 1` need no truncated subtraction, and the ripple's `t'` is written `s
+ 1` for the same reason.

Outside the firing block the profile at time `t` is the profile at time `t'`
shifted outward by `t - t'`: for `t' = s + 1`, the ripple range `t' < t ≤ t' +
x` of the statement, with its time `t` written `t + 1`, is `s + 1 ≤ t` and `t
- s ≤ x`, and the odometer at `radial d x` at time `t + 1` equals the odometer
at `radial d (x - (t - s))` at time `s + 1`.
-/
import DimRed.Support.Recursion
import DimRed.Support.BaseInduction

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
      ∀ s : ℕ, s + 1 ≤ t → ∀ x : ℕ, t - s ≤ x → x ≤ d →
        (x : ℤ) ≤ blockEdge d s → blockEdge d (s + 1) < (x : ℤ) →
        odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t + 1) (radial d x)
          = odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (s + 1) (radial d (x - (t - s)))
-- FROZEN-STATEMENT-END
:= by
  constructor
  · intro x hx
    refine ⟨?_, ?_⟩
    · intro hxle
      have hT1 : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) (t + 1) (radial d x)
          = ((t + 1 : ℕ) : ℤ) := block_eq d hd (t + 1) x hx hxle
      have hT : odo d 4 (fun _ => 2 * (d : ℤ) + ((d : ℤ) - 1)) t (radial d x) = (t : ℤ) :=
        block_eq d hd t x hx (le_trans hxle (blockEdge_antitone d t))
      rw [hT1, hT]; push_cast; ring
    · intro hgt hle
      rcases Nat.eq_zero_or_pos t with ht0 | htpos
      · subst ht0
        simp only [Nat.zero_add] at hgt
        have hb1 : blockEdge d 1 = (d : ℤ) := rfl
        have hb0 : blockEdge d 0 = (d : ℤ) := rfl
        omega
      · exact beyond_block_eq d hd t x htpos hx hgt hle
  · intro s hst x hxb hxd hxs hxs1
    have hq := ripple_shift d hd (t - s) s x hxb hxd hxs1 hxs
    have heq : s + (t - s) + 1 = t + 1 := by omega
    rwa [heq] at hq
