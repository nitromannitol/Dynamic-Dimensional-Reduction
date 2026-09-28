import DimRed.Support.OneDimConsistAll
import DimRed.Support.StrongDerivStep
import DimRed.Frozen.Prelim.AxisMonotonicity

open LatticeProb DimRed

namespace DimRed

/-- The time bound feeding `hprev` of `odo_one_consist_all`: a time below the
topple time of scale `j` is below the topple time of every larger scale. -/
theorem toppleTime_le_of_lt_of_le {j K M t t' : ℕ}
    (hmono : ∀ {a b : ℕ}, j ≤ a → a ≤ b → b < M → toppleTime 1 a ≤ toppleTime 1 b)
    (hjK : j < K) (hKM : K ≤ M) (hK2 : 2 ≤ K)
    (ht : (t : ℕ∞) ≤ toppleTime 1 j) (htt : t' < t) :
    (t' : ℕ∞) ≤ toppleTime 1 (K - 1) := by

  have h1 : (t' : ℕ∞) < (t : ℕ∞) := by exact_mod_cast htt
  have hjK1 : j ≤ K - 1 := by omega
  have hK1M : K - 1 < M := by omega
  have h2 : (t : ℕ∞) ≤ toppleTime 1 (K - 1) :=
    le_trans ht (hmono (a := j) (b := K - 1) le_rfl hjK1 hK1M)
  exact le_of_lt (lt_of_lt_of_le h1 h2)


/-- The `hfacet` regime of `odo_one_consist_all`: the hypothesis
`(s+1 : ℕ∞) < toppleTime 1 (K-1)` puts `s` below the topple time of scale `K`. -/
theorem toppleTime_lt_of_succ_lt {K M s : ℕ} (hKM : K < M) (hK2 : 2 ≤ K)
    (hmono : ∀ {a b : ℕ}, 1 ≤ a → a ≤ b → b < M → toppleTime 1 a ≤ toppleTime 1 b)
    (h : ((s + 1 : ℕ) : ℕ∞) < toppleTime 1 (K - 1)) :
    (s : ℕ∞) < toppleTime 1 K := by

  have hK1 : 1 ≤ K - 1 := by omega
  have hK1K : K - 1 ≤ K := by omega
  have h1 : ((s + 1 : ℕ) : ℕ∞) ≤ toppleTime 1 K :=
    le_trans (le_of_lt h) (hmono (a := K - 1) (b := K) hK1 hK1K hKM)
  have h2 : (s : ℕ∞) < ((s + 1 : ℕ) : ℕ∞) := by
    rw [Nat.cast_lt]
    omega
  exact lt_of_lt_of_le h2 h1


/-- The topple time of the scale-one cube is one. -/
theorem toppleTime_one_one : toppleTime 1 1 = 1 := by
  apply le_antisymm
  · rw [toppleTime_eq_corner 1 1 (by norm_num) (by omega)]
    apply sInf_le
    exact ⟨1, ⟨by norm_num, corner_one_le 1⟩, rfl⟩
  · exact one_le_toppleTime 1 1

/-- The facet point with an empty head is the constant vector with the middle
coordinate replaced by `c`. -/
theorem facetPoint_zero_head' (c c' : ℤ) (j : ℕ) :
    facetPoint (fun _ : Fin 0 => c') c j
      = fun k : Fin (0 + 1 + j) =>
          if k = (⟨0, by omega⟩ : Fin (0 + 1 + j)) then c else 1 := by
  have h : (fun _ : Fin 0 => c') = (fun _ : Fin 0 => (0 : ℤ)) := by
    funext a
    exact absurd a.2 (by omega)
  rw [h, facetPoint_zero_head]

/-- The half-side of the even box of side `2 * M` is `M`. -/
theorem sideHalf_two_mul (M : ℕ) : sideHalf (2 * M) = M := by
  rw [sideHalf]
  omega

/-- The corner point's coordinates: `M` at the first index, `1` elsewhere. -/
theorem cornerPoint_apply (d M : ℕ) (i : Fin d) :
    cornerPoint d M i = if (i : ℕ) = 0 then (M : ℤ) else 1 := rfl

/-- The corner point's first coordinate is `M`. -/
theorem cornerPoint_apply_zero (d M : ℕ) (hd : 1 ≤ d) :
    cornerPoint d M ⟨0, hd⟩ = (M : ℤ) := by
  rw [cornerPoint_apply]
  simp



/-- The corner of the side-`b` cube exceeds `b - a` in its first coordinate, for
`a < b`. -/
theorem cornerPoint_gt_sub (d a b : ℕ) (hd : 1 ≤ d) (ha : 1 ≤ a) (hab : a < b) :
    (b : ℤ) - (a : ℤ) < cornerPoint d b ⟨0, hd⟩ := by
  rw [cornerPoint_apply_zero d b hd]
  have hab' : (a : ℤ) < (b : ℤ) := by exact_mod_cast hab
  linarith




/-- The neighbour sum of the smaller cube's odometer, extended by zero off the
smaller cube, is at most the neighbour sum of the smaller odometer itself. -/
theorem nbrSum_extend_le (d m t : ℕ) (y : Site d) :
    nbrSum (fun z => if inCube d (2 * m) z then odoUnif d (2 * m) t z else 0) y
      ≤ nbrSum (odo d (2 * m) (fun _ => 2 * (d : ℤ)) t) y := by
  simp only [nbrSum]
  refine Finset.sum_le_sum ?_
  intro i _
  have h1 : (if inCube d (2 * m) (y + unit i) then odoUnif d (2 * m) t (y + unit i) else 0)
      ≤ odo d (2 * m) (fun _ => 2 * (d : ℤ)) t (y + unit i) := by
    by_cases hh : inCube d (2 * m) (y + unit i)
    · simp only [hh, if_true, odoUnif, le_refl]
    · simp only [hh, if_false]
      have hnn := odo_nonneg d (2 * m) (fun _ => 2 * (d : ℤ)) t (y + unit i)
      simpa [odoUnif] using hnn
  have h2 : (if inCube d (2 * m) (y - unit i) then odoUnif d (2 * m) t (y - unit i) else 0)
      ≤ odo d (2 * m) (fun _ => 2 * (d : ℤ)) t (y - unit i) := by
    by_cases hh : inCube d (2 * m) (y - unit i)
    · simp only [hh, if_true, odoUnif, le_refl]
    · simp only [hh, if_false]
      have hnn := odo_nonneg d (2 * m) (fun _ => 2 * (d : ℤ)) t (y - unit i)
      simpa [odoUnif] using hnn
  linarith



/-- The neighbour sum of the smaller cube's odometer, extended by zero off the
smaller cube, is nonnegative. -/
theorem nbrSum_extend_nonneg (d m t : ℕ) (y : Site d) :
    (0 : ℤ) ≤ nbrSum (fun z => if inCube d (2 * m) z then odoUnif d (2 * m) t z else 0) y := by
  simp only [nbrSum]
  refine Finset.sum_nonneg ?_
  intro i _
  have h1 : (0 : ℤ) ≤ (if inCube d (2 * m) (y + unit i) then odoUnif d (2 * m) t (y + unit i) else 0) := by
    by_cases hh : inCube d (2 * m) (y + unit i)
    · simp only [hh, if_true]
      have hnn := odo_nonneg d (2 * m) (fun _ => 2 * (d : ℤ)) t (y + unit i)
      simpa [odoUnif] using hnn
    · simp only [hh, if_false, le_refl]
  have h2 : (0 : ℤ) ≤ (if inCube d (2 * m) (y - unit i) then odoUnif d (2 * m) t (y - unit i) else 0) := by
    by_cases hh : inCube d (2 * m) (y - unit i)
    · simp only [hh, if_true]
      have hnn := odo_nonneg d (2 * m) (fun _ => 2 * (d : ℤ)) t (y - unit i)
      simpa [odoUnif] using hnn
    · simp only [hh, if_false, le_refl]
  linarith




/-- Shifting a point down by one commutes with adding a unit vector. -/
theorem sub_one_add_unit (d : ℕ) (y : Site d) (i : Fin d) :
    (fun k : Fin d => (y + unit i) k - 1) = (fun k : Fin d => y k - 1) + unit i := by
  funext k
  simp only [Pi.add_apply, unit]
  by_cases hk : k = i
  · subst hk
    simp
  · simp [hk]



/-- Shifting a point down by one commutes with subtracting a unit vector. -/
theorem sub_one_sub_unit (d : ℕ) (y : Site d) (i : Fin d) :
    (fun k : Fin d => (y - unit i) k - 1) = (fun k : Fin d => y k - 1) - unit i := by
  funext k
  simp only [Pi.sub_apply, unit]
  by_cases hk : k = i
  · subst hk
    simp
  · simp [hk]




/-- Folding commutes with shifting down by one, for points with all coordinates
above one. -/
theorem foldPoint_sub_one (d m : ℕ) (z : Site d) (hz : ∀ k : Fin d, 1 < z k) :
    foldPoint d (2 * (m - 1)) (fun k => z k - 1) = fun k => foldPoint d (2 * m) z k - 1 := by
  funext k
  rw [foldPoint_apply, foldPoint_apply]
  have hz1 : 1 ≤ z k := by have := hz k; omega
  rw [if_pos hz1]
  have hz1' : 1 ≤ z k - 1 := by have := hz k; omega
  rw [if_pos hz1']




/-- Sorting commutes with shifting down by one, for points with all coordinates
above one. -/
theorem toSimplexPoint_sub_one (d m : ℕ) (z : Site d) (hz : ∀ k : Fin d, 1 < z k) :
    toSimplexPoint d (m - 1) (fun k => z k - 1)
      = fun k => toSimplexPoint d m z k - 1 := by
  -- the sorting key is unchanged by the shift, so the permutation is the same
  have hkey : (fun i : Fin d => -(foldPoint d (2 * (m - 1)) (fun k => z k - 1) i))
      = (fun i : Fin d => -(foldPoint d (2 * m) z i) + 1) := by
    funext i
    rw [foldPoint_sub_one d m z hz]
    ring
  have hfold : foldPoint d (2 * (m - 1)) (fun k => z k - 1)
      = fun k => foldPoint d (2 * m) z k - 1 := foldPoint_sub_one d m z hz
  -- the two sort permutations agree, because the keys differ by a constant
  -- the two sorted tuples agree as functions, which is all the caller needs
  have hsort : (fun j : Fin d => foldPoint d (2 * (m - 1)) (fun k => z k - 1)
        (Tuple.sort (fun i : Fin d => -(foldPoint d (2 * (m - 1)) (fun k => z k - 1) i)) j))
      = fun j : Fin d => foldPoint d (2 * m) z
        (Tuple.sort (fun i : Fin d => -(foldPoint d (2 * m) z i)) j) - 1 := by
    -- `κ₁ = κ₂ + 1`, so `κ₁ ∘ σ₂ = (κ₂ ∘ σ₂) + 1` is monotone
    have hmono1 : Monotone ((fun i : Fin d => -(foldPoint d (2 * (m - 1)) (fun k => z k - 1) i))
        ∘ Tuple.sort (fun i : Fin d => -(foldPoint d (2 * m) z i))) := by
      intro a b hab
      have h := Tuple.monotone_sort (fun i : Fin d => -(foldPoint d (2 * m) z i)) hab
      have hka := congrFun hkey ((Tuple.sort fun i => -foldPoint d (2 * m) z i) a)
      have hkb := congrFun hkey ((Tuple.sort fun i => -foldPoint d (2 * m) z i) b)
      simp only [Function.comp_apply] at h ⊢
      linarith
    -- `κ₁ ∘ σ₂ = κ₁ ∘ σ₁` by uniqueness of the monotone permutation
    have h1 := Tuple.unique_monotone hmono1
      (Tuple.monotone_sort (fun i : Fin d => -(foldPoint d (2 * (m - 1)) (fun k => z k - 1) i)))
    funext j
    have h2 := congrFun h1 j
    simp only [Function.comp_apply] at h2
    -- `κ₁ (σ₂ j) = κ₁ (σ₁ j)`; unfold `κ₁` with `foldPoint_sub_one`
    have hka := congrFun hkey ((Tuple.sort fun i => -foldPoint d (2 * (m - 1)) (fun k => z k - 1) i) j)
    have hkb := congrFun hkey ((Tuple.sort fun i => -foldPoint d (2 * m) z i) j)
    rw [foldPoint_sub_one d m z hz] at hka
    simp only at hka hkb
    linarith
  change (fun j : Fin d => foldPoint d (2 * (m - 1)) (fun k => z k - 1)
      (Tuple.sort (fun i : Fin d => -(foldPoint d (2 * (m - 1)) (fun k => z k - 1) i)) j))
    = fun j : Fin d => foldPoint d (2 * m) z
      (Tuple.sort (fun i : Fin d => -(foldPoint d (2 * m) z i)) j) - 1
  exact hsort




/-- Adding a unit vector to a point of the sorted domain with all coordinates
above two keeps it in the cube of side `2m`. -/
theorem inCube_add_unit_of_gt_two (d m : ℕ) (y : Site d) (i : Fin d)
    (h1 : ∀ k : Fin d, (1 : ℤ) ≤ y k) (h2 : ∀ k : Fin d, y k ≤ (m : ℤ))
    (h3 : ∀ k : Fin d, (2 : ℤ) < y k) (hm : 2 ≤ m) (hi : y i < (m : ℤ)) :
    inCube d (2 * m) (y + unit i) := by
  intro k
  rw [loCoord_two_mul, hiCoord_two_mul]
  have h1k : (1 : ℤ) ≤ y k := h1 k
  have h2k : y k ≤ (m : ℤ) := h2 k
  have h3k : (2 : ℤ) < y k := h3 k
  simp only [Pi.add_apply, unit]
  by_cases hk : k = i
  · subst hk
    simp only [Pi.single_eq_same]
    constructor <;> omega
  · simp only [Pi.single_eq_of_ne hk]
    constructor <;> omega



/-- Adding a unit vector to a point with all coordinates above two keeps every
coordinate above one. -/
theorem gt_one_add_unit_of_gt_two (d : ℕ) (y : Site d) (i : Fin d)
    (h3 : ∀ k : Fin d, (2 : ℤ) < y k) :
    ∀ k : Fin d, (1 : ℤ) < (y + unit i) k := by
  intro k
  have h3k : (2 : ℤ) < y k := h3 k
  simp only [Pi.add_apply, unit]
  by_cases hk : k = i
  · subst hk
    simp only [Pi.single_eq_same]
    omega
  · simp only [Pi.single_eq_of_ne hk]
    omega




/-- The sorted representative of a point with all coordinates above two also has
all coordinates above two. -/
theorem gt_one_toSimplexPoint_of_gt_one (d m : ℕ) (z : Site d)
    (hz : ∀ k : Fin d, (1 : ℤ) < z k) :
    ∀ k : Fin d, (1 : ℤ) < toSimplexPoint d m z k := by
  intro k
  -- the sorted point's coordinates are a permutation of the original's
  have hperm : ∀ j : Fin d, ∃ i : Fin d, toSimplexPoint d m z j = foldPoint d (2 * m) z i := by
    intro j
    refine ⟨(Tuple.sort (fun i => -(foldPoint d (2 * m) z i))) j, ?_⟩
    rfl
  obtain ⟨i, hi⟩ := hperm k
  rw [hi]
  -- `foldPoint` of a point above two is the point itself
  rw [foldPoint_apply]
  have hzi : (1 : ℤ) ≤ z i := by have := hz i; omega
  rw [if_pos hzi]
  have := hz i
  omega




/-- Shifting a point of the sorted domain with all coordinates above one down by
one keeps it in the cube of side `2(m-1)`. -/
theorem inCube_sub_one_of_gt_one (d m : ℕ) (y : Site d) (hm : 2 ≤ m)
    (h1 : ∀ k : Fin d, (1 : ℤ) ≤ y k) (h2 : ∀ k : Fin d, y k ≤ (m : ℤ))
    (h3 : ∀ k : Fin d, (1 : ℤ) < y k) :
    inCube d (2 * (m - 1)) (fun k => y k - 1) := by
  intro k
  rw [loCoord_two_mul, hiCoord_two_mul]
  have h1k : (1 : ℤ) ≤ y k := h1 k
  have h2k : y k ≤ (m : ℤ) := h2 k
  have h3k : (1 : ℤ) < y k := h3 k
  have hcast : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  rw [hcast]
  show (1 : ℤ) - ((m : ℤ) - 1) ≤ y k - 1 ∧ y k - 1 ≤ (m : ℤ) - 1
  constructor <;> omega



/-- A point of the sorted domain with all coordinates above one lies in the cube
of side `2m`. -/
theorem inCube_of_inSimplex_gt_one (d m : ℕ) (y : Site d) (hm : 2 ≤ m)
    (hy : inSimplex d m y) (h3 : ∀ k : Fin d, (1 : ℤ) < y k) :
    inCube d (2 * m) y := by
  intro k
  rw [loCoord_two_mul, hiCoord_two_mul]
  have h1k : (1 : ℤ) ≤ y k := (hy.1 k).1
  have h2k : y k ≤ (m : ℤ) := (hy.1 k).2
  have h3k : (1 : ℤ) < y k := h3 k
  constructor <;> omega




/-- The head of a point of the sorted domain lies in the cube of side `2M`. -/
theorem inCube_castSucc (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) (x : Site d)
    (hx : inSimplex d M x) :
    inCube (d - 1) (2 * M) (fun k : Fin (d - 1) => x (Fin.cast (by omega : d - 1 + 1 = d) k.castSucc)) := by
  intro k
  rw [loCoord_two_mul, hiCoord_two_mul]
  have h := hx.1 (Fin.cast (by omega : d - 1 + 1 = d) k.castSucc)
  have hM1 : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
  constructor <;> linarith [h.1, h.2]



/-- The head of a point of the sorted domain has all coordinates at least one. -/
theorem one_le_castSucc (d M : ℕ) (hd : 1 ≤ d) (x : Site d)
    (hx : inSimplex d M x) :
    ∀ k : Fin (d - 1), (1 : ℤ) ≤ x (Fin.cast (by omega : d - 1 + 1 = d) k.castSucc) := by
  intro k
  exact (hx.1 (Fin.cast (by omega : d - 1 + 1 = d) k.castSucc)).1




/-- The terminal odometer is invariant under the dimensional reduction at every
time, lifted to the `iSup`. -/
theorem odoInfUnif_snoc_eq (e M : ℕ) (y : Site e)
    (hred : ∀ t : ℕ, odoUnif (e + 1) (2 * M) t (Fin.snoc y 1) = odoUnif e (2 * M) t y) :
    odoInfUnif (e + 1) (2 * M) (Fin.snoc y 1) = odoInfUnif e (2 * M) y := by
  have hall : ∀ t : ℕ,
      odo (e + 1) (2 * M) (fun _ => 2 * ((e + 1 : ℕ) : ℤ)) t (Fin.snoc y 1)
      = odo e (2 * M) (fun _ => 2 * (e : ℤ)) t y := by
    intro t
    have h := hred t
    simpa [odoUnif] using h
  simp only [odoInfUnif, odoInf]
  exact congrArg (fun f : ℕ → ℤ => ⨆ t : ℕ, ((f t).toNat : ℕ∞)) (funext hall)




/-- `Fin.snoc` is `Fin.lastCases` up to the dimension cast. -/
theorem snoc_eq_lastCases {n : ℕ} (x : Fin n → ℤ) (c : ℤ) :
    (Fin.snoc x c : Fin (n + 1) → ℤ)
      = fun k : Fin (n + 1) => Fin.lastCases c x k := by
  funext k
  refine Fin.lastCases ?_ (fun a => ?_) k
  · rw [Fin.snoc_last, Fin.lastCases_last]
  · rw [Fin.snoc_castSucc, Fin.lastCases_castSucc]


end DimRed
