import DimRed.Support.RegBridges

/-!
# The time comparison at a facet point

The time comparison at a facet point that the paper's strong facet argument
uses (`dimred.tex:1293-1296`): if strong facet compatibility holds at time `t-1`,
then at a facet point `(y, 1, 1_j)` with a nonempty head the odometer one layer
in at time `t` is at least the odometer at the facet point at time `t-1`.

The proof is the dichotomy of the clause: either the facet gap is exactly one at
time `t-1`, in which case the toppling form gives equality, or it is not, in
which case the first-difference bound and monotonicity in time give the
inequality.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DimRed

open LatticeProb

/-- The time comparison at a facet point with a nonempty head, from strong facet
compatibility at the previous time. -/
theorem odo_facet_two_ge_prev {i j M t : ℕ} (ht : 1 ≤ t) (hi : 1 ≤ i) (hM : 2 ≤ M)
    (hS : RegStrongFacet (i + 1 + j) M (t - 1))
    (y : Fin i → ℤ) (hy2 : ∃ a, 2 ≤ y a)
    (hys : inSimplex (i + 1 + j) M (facetPoint y 1 j)) :
    odoUnif (i + 1 + j) (2 * M) (t - 1) (facetPoint y 1 j)
      ≤ odoUnif (i + 1 + j) (2 * M) t (facetPoint y 2 j) := by
  have hpos : inPos (i + 1 + j) M (facetPoint y 1 j) := hys.1
  have hmid : facetPoint y 1 j (Fin.castAdd j (Fin.last i)) = 1 := facetPoint_mid y 1
  obtain ⟨a, ha⟩ := hy2
  have h2 : ∃ l, 2 ≤ facetPoint y 1 j l :=
    ⟨Fin.castAdd j (Fin.castSucc a), by
      rw [facetPoint_head]
      exact ha⟩
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

/-- The time comparison at a facet point with a one-coordinate head whose
coordinate is exactly two, the `a = 1` case of Step 5 of the Case 2 proof: the
reflected neighbour is the point itself, so the first-difference bound and
monotonicity in time give the inequality. -/
theorem odo_facet_two_ge_prev_one {j M t : ℕ} (ht : 1 ≤ t) (hM : 2 ≤ M)
    (hS : RegStrongFacet (1 + 1 + j) M (t - 1))
    (c : ℤ) (hc : 2 ≤ c)
    (hys : inSimplex (1 + 1 + j) M (facetPoint (fun _ : Fin 1 => c) 1 j)) :
    odoUnif (1 + 1 + j) (2 * M) (t - 1) (facetPoint (fun _ : Fin 1 => c) 1 j)
      ≤ odoUnif (1 + 1 + j) (2 * M) t (facetPoint (fun _ : Fin 1 => c) 2 j) := by
  have hmid : facetPoint (fun _ : Fin 1 => c) 1 j (Fin.castAdd j (Fin.last 1)) = 1 :=
    facetPoint_mid _ 1
  have hmid' : facetPoint (fun _ : Fin 1 => c) 1 j + unit (Fin.castAdd j (Fin.last 1))
      = facetPoint (fun _ : Fin 1 => c) 2 j := by
    rw [facetPoint_add_mid_point]
    norm_num
  have hfirst := odo_first_diff (1 + 1 + j) M (by omega) (by omega) (t - 1)
    (Fin.castAdd j (Fin.last 1)) (facetPoint (fun _ : Fin 1 => c) 1 j) (by rw [hmid])
  rw [hmid'] at hfirst
  have hmono : odoUnif (1 + 1 + j) (2 * M) (t - 1) (facetPoint (fun _ : Fin 1 => c) 2 j)
      ≤ odoUnif (1 + 1 + j) (2 * M) t (facetPoint (fun _ : Fin 1 => c) 2 j) :=
    odo_mono (1 + 1 + j) (2 * M) (fun _ => 2 * ((1 + 1 + j : ℕ) : ℤ)) (by omega) _
  by_cases hgap : odoUnif (1 + 1 + j) (2 * M) (t - 1) (facetPoint (fun _ : Fin 1 => c) 1 j)
      = odoUnif (1 + 1 + j) (2 * M) (t - 1) (facetPoint (fun _ : Fin 1 => c) 2 j) + 1
  · have h' : odoUnif (1 + 1 + j) (2 * M) (t - 1) (facetPoint (fun _ : Fin 1 => c) 1 j)
        = odoUnif (1 + 1 + j) (2 * M) (t - 1)
          (facetPoint (fun _ : Fin 1 => c) 1 j + unit (Fin.castAdd j (Fin.last 1))) + 1 := by
      rw [hmid']
      exact hgap
    have htopple := strong_raw (1 + 1 + j) M (t - 1) hS (facetPoint (fun _ : Fin 1 => c) 1 j)
      hys.1 (Fin.castAdd j (Fin.last 1)) hmid
      (Exists.intro (Fin.castAdd j (Fin.castSucc 0)) (by
        rw [facetPoint_head]
        exact hc)) h'
    have ht1 : t - 1 + 1 = t := by omega
    rw [ht1] at htopple
    -- `htopple : v_t(x+e_k) = v_{t-1}(x+e_k) + 1` and
    -- `hgap : v_{t-1}(x) = v_{t-1}(x+e_k) + 1`, so the goal is an equality
    rw [hmid'] at htopple
    rw [htopple]
    exact le_of_eq hgap
  · have hle : odoUnif (1 + 1 + j) (2 * M) (t - 1) (facetPoint (fun _ : Fin 1 => c) 1 j)
        ≤ odoUnif (1 + 1 + j) (2 * M) (t - 1) (facetPoint (fun _ : Fin 1 => c) 2 j) := by
      by_contra hc
      push Not at hc
      exact hgap (by linarith [hfirst])
    linarith [hle, hmono]

/-- The swap identity behind the `a = 1` case of Step 5: when the head coordinate
is two, the point one layer in at the reflected head is the image of the facet
point under the coordinate swap of the head and mid indices. -/
theorem facetPoint_one_two_swap (j M t : ℕ) (c : ℤ) (hc : c = 2) :
    odoUnif (1 + 1 + j) (2 * M) t (facetPoint (fun _ : Fin 1 => c - 1) 2 j)
      = odoUnif (1 + 1 + j) (2 * M) t (facetPoint (fun _ : Fin 1 => c) 1 j) := by
  have h1 : facetPoint (fun _ : Fin 1 => c - 1) 2 j
      = fun k => facetPoint (fun _ : Fin 1 => c) 1 j
          (Equiv.swap 0 (Fin.castAdd j (Fin.last 1)) k) := by
    funext k
    rw [facetPoint, facetPoint]
    refine Fin.addCases ?_ (fun b => ?_) k
    · intro a
      refine Fin.lastCases ?_ (fun a' => ?_) a
      · rw [Fin.append_left, Fin.snoc_last]
        simp only [Equiv.swap_apply_def]
        rw [if_neg (by simp [Fin.ext_iff])]
        simp only [ite_true]
        rw [show (0 : Fin (1 + 1 + j)) = Fin.castAdd j (0 : Fin (1 + 1)) from rfl]
        rw [Fin.append_left]
        rw [show (0 : Fin (1 + 1)) = Fin.castSucc (0 : Fin 1) from rfl]
        rw [Fin.snoc_castSucc]
        omega
      · rw [Fin.append_left, Fin.snoc_castSucc]
        simp only [Equiv.swap_apply_def]
        rw [if_pos (by simp [Fin.ext_iff])]
        rw [Fin.append_left, Fin.snoc_last]
        omega
    · have hswap : (Equiv.swap 0 (Fin.castAdd j (Fin.last 1)))
          (Fin.natAdd (1 + 1) b) = Fin.natAdd (1 + 1) b := by
        rw [Equiv.swap_apply_def]
        rw [if_neg (by simp [Fin.ext_iff])]
        rw [if_neg (by
          intro h
          have h2 : ((Fin.natAdd (1 + 1) b : Fin (1 + 1 + j)) : ℕ)
              = ((Fin.castAdd j (Fin.last 1) : Fin (1 + 1 + j)) : ℕ) := by rw [h]
          simp at h2
          omega)]
      rw [hswap, Fin.append_right, Fin.append_right]
  rw [h1]
  exact odo_swap_coord (1 + 1 + j) M (2 * ((1 + 1 + j : ℕ) : ℤ)) t
    (facetPoint (fun _ : Fin 1 => c) 1 j) 0 (Fin.castAdd j (Fin.last 1))


/-- The reflection identity of the one-coordinate case: the point one layer in
at the head is the reflection of the facet point with the head coordinate two. -/
theorem facetPoint_one_two_refl (j M t : ℕ) :
    odoUnif (1 + 1 + j) (2 * M) t (facetPoint (fun _ : Fin 1 => (1 : ℤ)) 2 j)
      = odoUnif (1 + 1 + j) (2 * M) t (facetPoint (fun _ : Fin 1 => (2 : ℤ)) 1 j) := by
  have h1 : facetPoint (fun _ : Fin 1 => (1 : ℤ)) 2 j
      = fun k => facetPoint (fun _ : Fin 1 => (2 : ℤ)) 1 j
          (Equiv.swap 0 (Fin.castAdd j (Fin.last 1)) k) := by
    funext k
    rw [facetPoint, facetPoint]
    refine Fin.addCases ?_ (fun b => ?_) k
    · intro a
      refine Fin.lastCases ?_ (fun a' => ?_) a
      · rw [Fin.append_left, Fin.snoc_last]
        simp only [Equiv.swap_apply_def]
        rw [if_neg (by simp [Fin.ext_iff])]
        simp only [ite_true]
        rw [show (0 : Fin (1 + 1 + j)) = Fin.castAdd j (0 : Fin (1 + 1)) from rfl]
        rw [Fin.append_left]
        rw [show (0 : Fin (1 + 1)) = Fin.castSucc (0 : Fin 1) from rfl]
        rw [Fin.snoc_castSucc]
      · rw [Fin.append_left, Fin.snoc_castSucc]
        simp only [Equiv.swap_apply_def]
        rw [if_pos (by simp [Fin.ext_iff])]
        rw [Fin.append_left, Fin.snoc_last]
    · have hswap : (Equiv.swap 0 (Fin.castAdd j (Fin.last 1)))
          (Fin.natAdd (1 + 1) b) = Fin.natAdd (1 + 1) b := by
        rw [Equiv.swap_apply_def]
        rw [if_neg (by simp [Fin.ext_iff])]
        rw [if_neg (by
          intro h
          have h2 : ((Fin.natAdd (1 + 1) b : Fin (1 + 1 + j)) : ℕ)
              = ((Fin.castAdd j (Fin.last 1) : Fin (1 + 1 + j)) : ℕ) := by rw [h]
          simp at h2
          omega)]
      rw [hswap, Fin.append_right, Fin.append_right]
  rw [h1]
  exact odo_swap_coord (1 + 1 + j) M (2 * ((1 + 1 + j : ℕ) : ℤ)) t
    (facetPoint (fun _ : Fin 1 => (2 : ℤ)) 1 j) 0 (Fin.castAdd j (Fin.last 1))

end DimRed
