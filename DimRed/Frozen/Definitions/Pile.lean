/-
Finite-pile conservation of the corrected edition.
`dimred-corrected-arxiv.tex:93-98` (physical carrier at
`dimred-corrected-arxiv.tex:278-284`):

  "Our proof begins with the {\it odometer} $v_t$, which encodes the number of
   topples at each site over time. Let $v_0 : \mathcal{C}_N^{(d)} \to
   \mathbb{Z}^+$ be the initial odometer $v_0 \equiv 0$; then, recursively,

  v_{t+1} &= v_{t} + 1\{ s_{t} \geq 2 d \}, \\ s_{t+1} &= s_{t} + \Delta (
   v_{t+1} - v_{t} ) ,

  where $\Delta$ is the graph Laplacian on $\mathcal{C}_N^{(d)}$ with
   dissipating boundary conditions. Dependence on $d$ and $N$ is indicated by
   writing $v_t^{(d,N)}$ and $s_t^{(d,N)}$."

This unit records the finite-time pile as `s_t = s_0 + Δ v_t` on the physical
cube, the telescoped form of the recursion at lines 95-96 with `v_0 = 0`.
-/
import DimRed.Support.SourceCarriers

open LatticeProb DimRed

-- FROZEN-STATEMENT-BEGIN
theorem DimRed.Frozen.pile_definition (d N : ℕ) (s₀ : Site d → ℤ) (t : ℕ) (x : Corrected.CubeSite d N) :
    Corrected.pile d N s₀ t x = s₀ x.val + lap (odo d N s₀ t) x.val
-- FROZEN-STATEMENT-END
:= rfl
