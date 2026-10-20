/-
Lemma 2.3 of the corrected edition.
`dimred-corrected-arxiv.tex:395-397` (label `symmetry_lemma`):

  "For each $t \geq 0$ and each $ \sigma \in
   \operatorname{Aut}_{\mathcal{C}_d}$, $ \sigma v_t = v_t$. Hence, $v_t =
   v_t^{\mathcal{S}}$ on $\mathcal{S}^{(d)}_M$."

`Aut_{C_d}` is the group of `(d × d)` matrices with exactly one `±1` in each
row and column, acting by matrix-vector multiplication followed by the
translation that preserves `C_N^{(d)}` (`dimred-corrected-arxiv.tex`, label `subsec:symmetry`);
that is a permutation of the coordinates followed by the reflections `x_i ↦
(lo + hi) - x_i`, which is `cubeSym`. The standing hypothesis is that the
initial sandpile is symmetric (`dimred-corrected-arxiv.tex`, label `subsec:symmetry`), carried as
`hsym` and read as `CubeSymmetric`. The second sentence is the identification
of `v_t` with the symmetrized odometer on the fundamental domain, which the
Lean statement carries as its second conjunct (`foldedOdo`,
`dimred-corrected-arxiv.tex`, label `subsec:symmetry`); the development works with `v_t` on
`S_M^{(d)}` throughout (`dimred-corrected-arxiv.tex`, label `subsec:symmetry`).
-/
import DimRed.Support.ReflectedThreshold

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.symmetry_lemma (d N : ℕ) (s₀ : Site d → ℤ)
    (hsym : Corrected.CubeSymmetric d N s₀) :
    (∀ (t : ℕ) (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (x : Site d),
      odo d N s₀ t (cubeSym d N π ε x) = odo d N s₀ t x) ∧
    (∀ (t : ℕ) (x : Corrected.SimplexSite d (sideHalf N)),
      odo d N s₀ t x.val = Corrected.foldedOdo d N s₀ t x)
-- FROZEN-STATEMENT-END
:= Corrected.symmetry_lemma d N s₀ hsym
