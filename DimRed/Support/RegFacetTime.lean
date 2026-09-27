/-
The time comparison at a facet point that the paper's strong facet argument
uses (`dimred.tex:1293-1296`): if strong facet compatibility holds at time `t-1`,
then at a facet point `(y, 1, 1_j)` with a nonempty head the odometer one layer
in at time `t` is at least the odometer at the facet point at time `t-1`.

The proof is the dichotomy of the clause: either the facet gap is exactly one at
time `t-1`, in which case the toppling form gives equality, or it is not, in
which case the first-difference bound and monotonicity in time give the
inequality.
-/
import DimRed.Support.RegBridges

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DimRed

open LatticeProb

/-- The time comparison at a facet point with a nonempty head, from strong facet
compatibility at the previous time. -/
theorem odo_facet_two_ge_prev {i j M t : ℕ} (ht : 1 ≤ t) (hi : 1 ≤ i) (hM : 2 ≤ M)
    (hS : RegStrongFacet (i + 1 + j) M (t - 1))
    (y : Fin i → ℤ) (hy2 : ∀ a, 2 ≤ y a)
    (hys : inSimplex (i + 1 + j) M (facetPoint y 1 j)) :
    odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 1 j)
      ≤ odoUnif (i + 1 + j) (2 * M) t (facetPoint y 2 j) := by
  have hpos : inPos (i + 1 + j) M (facetPoint y 1 j) := hys.1
  have hmid : facetPoint y 1 j (Fin.castAdd j (Fin.last i)) = 1 := facetPoint_mid y 1
  have h2 : ∃ l, 2 ≤ facetPoint y 1 j l :=
    ⟨Fin.castAdd j (Fin.castSucc ⟨0, by omega⟩), by
      rw [facetPoint_head]
      exact hy2 ⟨0, by omega⟩⟩
  have hmid' : facetPoint y 1 j + unit (Fin.castAdd j (Fin.last i)) = facetPoint y 2 j := by
    rw [facetPoint_add_mid_point y 1]
    norm_num
  by_cases hgap : odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 1 j)
      = odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 2 j) + 1
  · have h' : odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 1 j)
        = odoUnif (i + 1 + j) (2 * M) (t - 1)
          (facetPoint y 1 j + unit (Fin.castAdd j (Fin.last i))) + 1 := by
      rw [hmid']
      exact hgap
    have htopple := strong_raw (i + 1 + j) M (t - 1) hS (facetPoint y 1 j) hpos
      (Fin.castAdd j (Fin.last i)) hmid h2 h'
    rw [hmid'] at htopple
    have ht1 : t - 1 + 1 = t := by omega
    rw [ht1] at htopple
    rw [htopple]
    linarith
  · have hfirst := odo_first_diff (i + 1 + j) M (by omega) (by omega) (t - 1)
      (Fin.castAdd j (Fin.last i)) (facetPoint y 1 j) (by rw [hmid])
    rw [hmid'] at hfirst
    have hle : odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 1 j)
        ≤ odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 2 j) := by
      by_contra hc
      push Not at hc
      exact hgap (by linarith)
    have hmono : odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 2 j)
        ≤ odoUnif (i + 1 + j) (2 * M) t (facetPoint y 2 j) :=
      odo_mono (i + 1 + j) (2 * M) (fun _ => 2 * ((i + 1 + j : ℕ) : ℤ))
        (by omega) (facetPoint y 2 j)
    linarith

end DimRed
