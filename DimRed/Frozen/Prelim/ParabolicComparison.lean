/-
Lemma 2.2 of `dimred.tex`, frozen.  `dimred.tex:311-316`
(label `parabolic_comparison`, display `eq:parabolic_leastaction`):

  "$v(t,x) = \min\{ u: \mathcal{G} \to \Z^+: \Delta^{\mathcal{G}} u(t,x) +
   s(t,x) \leq 2d-1 \mbox{ for all $x \in \mathcal{C}$ and $t \geq 1$} \}$."

Here `G = ℤ^+ × C`, `s(t,x) := s_0(x)`, `v(t,x) := v_t(x)`
(`dimred.tex:303-305`) and
`Δ^G f(t,x) = -2d f(t,x) + ∑_{y ∼ x} f(t-1,y)` for `t ≥ 1`
(`dimred.tex:306-309`), the sum being over the neighbours of `x` in `C`, so a
competitor `u` is a nonnegative function on `ℤ^+ × C`, extended by zero off the
hypercube.  A minimum of a set of functions is the pointwise minimum: `v`
satisfies the constraint, and `v ≤ u` for every `u` that does.  The time index
is written `t + 1` so that `t ≥ 1` needs no truncated subtraction.
-/
import DimRed.Frozen.Prelim.PtInd

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.parabolic_comparison (d N : ℕ) (hd : 1 ≤ d) (s₀ : Site d → ℤ)
    (hs0 : ∀ y, inCube d N y → 0 ≤ s₀ y)
    (hs1 : ∀ y, inCube d N y → s₀ y ≤ 2 * (2 * (d : ℤ)) - 1) :
    (∀ (t : ℕ) (x : Site d), inCube d N x →
        (-(2 * (d : ℤ)) * odo d N s₀ (t + 1) x + nbrSum (odo d N s₀ t) x) + s₀ x
          ≤ 2 * (d : ℤ) - 1) ∧
      ∀ u : ℕ → Site d → ℤ, (∀ t y, 0 ≤ u t y) → (∀ t y, ¬ inCube d N y → u t y = 0) →
        (∀ (t : ℕ) (y : Site d), inCube d N y →
            (-(2 * (d : ℤ)) * u (t + 1) y + nbrSum (u t) y) + s₀ y ≤ 2 * (d : ℤ) - 1) →
        ∀ (t : ℕ) (y : Site d), odo d N s₀ t y ≤ u t y
-- FROZEN-STATEMENT-END
:= by
  have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  constructor
  · intro t x hx
    have h := Frozen.pt_ind_lemma d N hd s₀ hs0 hs1 t x hx
    set A : ℤ := s₀ x + nbrSum (odo d N s₀ t) x with hA
    have hmod : A % (2 * (d : ℤ)) = A - 2 * (d : ℤ) * (A / (2 * (d : ℤ))) := Int.emod_def A _
    have hlt : A % (2 * (d : ℤ)) < 2 * (d : ℤ) := Int.emod_lt_of_pos A hdpos
    rw [h]
    linarith
  · intro u hu0 hu1 hcon t
    induction t with
    | zero => intro y; simpa [odo] using hu0 0 y
    | succ n ih =>
      intro y
      by_cases hy : inCube d N y
      · have h := Frozen.pt_ind_lemma d N hd s₀ hs0 hs1 n y hy
        have hmono : nbrSum (odo d N s₀ n) y ≤ nbrSum (u n) y := nbrSum_mono ih y
        have hc := hcon n y hy
        have hstep : s₀ y + nbrSum (u n) y < (u (n + 1) y + 1) * (2 * (d : ℤ)) := by nlinarith
        have h1 : (s₀ y + nbrSum (odo d N s₀ n) y) / (2 * (d : ℤ))
            ≤ (s₀ y + nbrSum (u n) y) / (2 * (d : ℤ)) :=
          Int.ediv_le_ediv hdpos (by linarith)
        have h2 : (s₀ y + nbrSum (u n) y) / (2 * (d : ℤ)) < u (n + 1) y + 1 :=
          (Int.ediv_lt_iff_lt_mul hdpos).2 hstep
        rw [h]; omega
      · rw [odo_eq_zero_outside d N s₀ (n + 1) y hy]; exact hu0 (n + 1) y
