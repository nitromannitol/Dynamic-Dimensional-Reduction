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




/-- The `Fin.lastCases` form of a point equals its `Fin.snoc` form. -/
theorem lastCases_eq_snoc {n : ℕ} (x : Fin n → ℤ) (c : ℤ) :
    (fun k : Fin (n + 1) => Fin.lastCases c x k) = (Fin.snoc x c : Fin (n + 1) → ℤ) := by
  exact (snoc_eq_lastCases x c).symm




/-- The terminal odometer at a `Fin.lastCases` point equals the one at its
`Fin.snoc` form. -/
theorem odoInfUnif_lastCases_eq_snoc (n M : ℕ) (x : Fin n → ℤ) (c : ℤ) :
    odoInfUnif (n + 1) (2 * M) (fun k : Fin (n + 1) => Fin.lastCases c x k)
      = odoInfUnif (n + 1) (2 * M) (Fin.snoc x c) := by
  rw [lastCases_eq_snoc]




/-- The `Fin.lastCases` at the last index is the value. -/
theorem lastCases_at_last {n : ℕ} (c : ℤ) (x : Fin n → ℤ) :
    (fun k : Fin (n + 1) => Fin.lastCases c x k) (Fin.last n) = c := by
  simp only [Fin.lastCases_last]



/-- The `Fin.lastCases` at a head index is the head value. -/
theorem lastCases_at_castSucc {n : ℕ} (c : ℤ) (x : Fin n → ℤ) (a : Fin n) :
    (fun k : Fin (n + 1) => Fin.lastCases c x k) a.castSucc = x a := by
  simp only [Fin.lastCases_castSucc]




/-- The `Fin 1` points are all equal. -/
theorem fin_one_subsingleton (a b : Fin 1) : a = b := by
  exact Subsingleton.elim a b




/-- The terminal odometer at a `Fin 1` point is independent of the point. -/
theorem odoInfUnif_fin_one_eq (M : ℕ) (a b : Fin 1) :
    odoInfUnif 1 (2 * M) (fun _ : Fin 1 => a) = odoInfUnif 1 (2 * M) (fun _ : Fin 1 => b) := by
  congr 1
  funext k
  rw [fin_one_subsingleton a b]



/-- The topple time is monotone in the side length at a fixed dimension `d ≥ 1`:
`τ_d a ≤ τ_d b` for `a ≤ b`.  Immediate from `τ_j = j² - j + 1`. -/
theorem toppleTime_mono_scale_dim (d a b : ℕ) (_hd : 1 ≤ d) (ha : 1 ≤ a) (hab : a ≤ b)
    (hsq : ∀ j : ℕ, 1 ≤ j → toppleTime d j = ((j * j - j + 1 : ℕ) : ℕ∞)) :
    toppleTime d a ≤ toppleTime d b := by
  have hb : 1 ≤ b := le_trans ha hab
  rw [hsq a ha, hsq b hb]
  have h1 : a * a ≤ b * b := Nat.mul_le_mul hab hab
  have h2 : a * a - a + 1 ≤ b * b - b + 1 := by
    have h3 : a * a - a = a * (a - 1) := by
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · subst ha0; simp
      · rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have h4 : b * b - b = b * (b - 1) := by
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · subst hb0; simp
      · rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [h3, h4]
    have h5 : a - 1 ≤ b - 1 := by omega
    have h6 : a * (a - 1) ≤ b * (b - 1) := Nat.mul_le_mul hab h5
    omega
  exact_mod_cast h2

/-- The corner odometer of the side-`b` cube is at most the corner odometer of
the side-`a` cube plus `b - a`, for `a ≤ b` and `n ≤ τ_a`, in every dimension. -/
theorem odo_corner_dominate_dim (d a b n : ℕ) (_hd : 1 ≤ d) (hab : a ≤ b) (_ha : 1 ≤ a)
    (htau : (n : ℕ∞) ≤ toppleTime d a)
    (hmono : ∀ {c e : ℕ}, a ≤ c → c ≤ e → toppleTime d c ≤ toppleTime d e)
    (hconsist : ∀ K : ℕ, a < K → K ≤ b → (n : ℕ∞) ≤ toppleTime d (K - 1) →
      odoUnif d (2 * K) n (cornerPoint d K) ≤
        odoUnif d (2 * (K - 1)) n (cornerPoint d (K - 1)) + 1) :
    odoUnif d (2 * b) n (cornerPoint d b) ≤
      odoUnif d (2 * a) n (cornerPoint d a) + ((b - a : ℕ) : ℤ) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    have h1 := hconsist (b + 1) (by omega) (by omega)
      (le_trans htau (hmono (by omega) (by omega)))
    rw [show b + 1 - 1 = b by omega] at h1
    have h2 : odoUnif d (2 * b) n (cornerPoint d b) ≤
        odoUnif d (2 * a) n (cornerPoint d a) + ((b - a : ℕ) : ℤ) :=
      ih (fun K hK hKb => hconsist K hK (by omega))
    have h3 : ((b + 1 - a : ℕ) : ℤ) = ((b - a : ℕ) : ℤ) + 1 := by
      have : b + 1 - a = (b - a) + 1 := by omega
      rw [this, Nat.cast_add, Nat.cast_one]
    rw [h3]
    linarith

/-- The topple time is monotone in the side length at a fixed dimension `d ≥ 1`:
`τ_d a ≤ τ_d b` for `a ≤ b`.  From the corner domination and the consistency
clause at the larger scale. -/
theorem toppleTime_mono_scale_dim2 (d a b : ℕ) (hd : 1 ≤ d) (ha : 1 ≤ a) (hab : a ≤ b)
    (hmono : ∀ {c e : ℕ}, a ≤ c → c ≤ e → toppleTime d c ≤ toppleTime d e)
    (hconsist : ∀ K : ℕ, a < K → K ≤ b → (n : ℕ) → (n : ℕ∞) ≤ toppleTime d (K - 1) →
      odoUnif d (2 * K) n (cornerPoint d K) ≤
        odoUnif d (2 * (K - 1)) n (cornerPoint d (K - 1)) + 1)
    (hhitb : ∃ n : ℕ, 1 ≤ n ∧ (b : ℤ) ≤ odoUnif d (2 * b) n (cornerPoint d b))
    (hhita : ∃ n : ℕ, 1 ≤ n ∧ (a : ℤ) ≤ odoUnif d (2 * a) n (cornerPoint d a)) :
    toppleTime d a ≤ toppleTime d b := by
  by_contra hcon
  push Not at hcon
  have hb1 : 1 ≤ b := le_trans ha hab
  have hne : toppleTime d b ≠ ⊤ := toppleTime_ne_top d b hd hb1 hhitb
  obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.mp hne
  have hTle : toppleTime d b ≤ (T : ℕ∞) := le_of_eq hT.symm
  have hTge : (T : ℕ∞) ≤ toppleTime d b := le_of_eq hT
  have hTlt : (T : ℕ∞) < toppleTime d a := lt_of_le_of_lt hTge hcon
  have hbT : (b : ℤ) ≤ odoUnif d (2 * b) T (cornerPoint d b) := by
    have h := (toppleTime_le_iff d b hd hb1 hhitb (T : ℕ∞)).mp hTle
    obtain ⟨n, hn, hn1, hnval⟩ := h
    have hnT : n ≤ T := ENat.coe_le_coe.mp hn
    have hmono' : odoUnif d (2 * b) n (cornerPoint d b)
        ≤ odoUnif d (2 * b) T (cornerPoint d b) :=
      odo_mono d (2 * b) (fun _ => 2 * (d : ℤ)) hnT _
    linarith
  have hdom := odo_corner_dominate_dim d a b T hd hab ha hTlt.le
    (fun hc he => hmono hc he)
    (fun K hK hKb hn => hconsist K hK hKb T hn)
  have haT : (a : ℤ) ≤ odoUnif d (2 * a) T (cornerPoint d a) := by
    have hbT' : (b : ℤ) ≤ odoUnif d (2 * a) T (cornerPoint d a) + ((b - a : ℕ) : ℤ) :=
      le_trans hbT hdom
    have hcast : ((b - a : ℕ) : ℤ) = (b : ℤ) - (a : ℤ) := by
      rw [Nat.cast_sub hab]
    have hbT'' : (b : ℤ) ≤ odoUnif d (2 * a) T (cornerPoint d a) + ((b : ℤ) - (a : ℤ)) := by
      rw [← hcast]
      exact hbT'
    linarith
  have hT1 : 1 ≤ T := by
    have h1 : (1 : ℕ∞) ≤ toppleTime d b := one_le_toppleTime d b
    have h2 : (1 : ℕ∞) ≤ (T : ℕ∞) := le_trans h1 hTle
    exact ENat.coe_le_coe.mp h2
  have hle := (toppleTime_le_iff d a hd ha hhita (T : ℕ∞)).mpr
  exact absurd (hle ⟨T, le_rfl, ⟨hT1, haT⟩⟩) (not_le.mpr hTlt)

/-- One step of the scale monotonicity of the topple time: `τ_d c ≤ τ_d (c+1)`.
The domination at `b = a + 1` is exactly the consistency clause, so no
monotonicity is assumed. -/
theorem toppleTime_mono_scale_succ (d c : ℕ) (hd : 1 ≤ d) (hc : 1 ≤ c)
    (hconsist : ∀ n : ℕ, (n : ℕ∞) ≤ toppleTime d c →
      odoUnif d (2 * (c + 1)) n (cornerPoint d (c + 1)) ≤
        odoUnif d (2 * c) n (cornerPoint d c) + 1)
    (hhitc : ∃ n : ℕ, 1 ≤ n ∧ (c : ℤ) ≤ odoUnif d (2 * c) n (cornerPoint d c))
    (hhitc1 : ∃ n : ℕ, 1 ≤ n ∧
      ((c + 1 : ℕ) : ℤ) ≤ odoUnif d (2 * (c + 1)) n (cornerPoint d (c + 1))) :
    toppleTime d c ≤ toppleTime d (c + 1) := by
  by_contra hcon
  push Not at hcon
  have hne : toppleTime d (c + 1) ≠ ⊤ := toppleTime_ne_top d (c + 1) hd (by omega) hhitc1
  obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.mp hne
  have hTle : toppleTime d (c + 1) ≤ (T : ℕ∞) := le_of_eq hT.symm
  have hTge : (T : ℕ∞) ≤ toppleTime d (c + 1) := le_of_eq hT
  have hTlt : (T : ℕ∞) < toppleTime d c := lt_of_le_of_lt hTge hcon
  have hbT : ((c + 1 : ℕ) : ℤ) ≤ odoUnif d (2 * (c + 1)) T (cornerPoint d (c + 1)) := by
    have h := (toppleTime_le_iff d (c + 1) hd (by omega) hhitc1 (T : ℕ∞)).mp hTle
    obtain ⟨n, hn, hn1, hnval⟩ := h
    have hnT : n ≤ T := ENat.coe_le_coe.mp hn
    have hmono' := odo_mono d (2 * (c + 1)) (fun _ => 2 * (d : ℤ)) hnT (cornerPoint d (c + 1))
    simp only [odoUnif] at hmono' hnval ⊢
    linarith
  have hdom := hconsist T hTlt.le
  have hcT : (c : ℤ) ≤ odoUnif d (2 * c) T (cornerPoint d c) := by
    have hcast : ((c + 1 : ℕ) : ℤ) = (c : ℤ) + 1 := by push_cast; ring
    rw [hcast] at hbT
    linarith
  have hT1 : 1 ≤ T := by
    have h1 : (1 : ℕ∞) ≤ toppleTime d (c + 1) := one_le_toppleTime d (c + 1)
    exact ENat.coe_le_coe.mp (le_trans h1 hTle)
  have hle := (toppleTime_le_iff d c hd hc hhitc (T : ℕ∞)).mpr
  exact absurd (hle ⟨T, le_rfl, ⟨hT1, hcT⟩⟩) (not_le.mpr hTlt)

/-- The topple time is monotone in the side length at a fixed dimension `d ≥ 1`,
with NO circularity: the one-step case is `toppleTime_mono_scale_succ` and the
chain is `Nat.le_induction`. -/
theorem toppleTime_mono_scale_dim' (d a b M : ℕ) (hd : 1 ≤ d) (ha : 1 ≤ a) (hab : a ≤ b)
    (hbM : b < M)
    (hconsist : ∀ c : ℕ, 1 ≤ c → c < M → ∀ n : ℕ, (n : ℕ∞) ≤ toppleTime d c →
      odoUnif d (2 * (c + 1)) n (cornerPoint d (c + 1)) ≤
        odoUnif d (2 * c) n (cornerPoint d c) + 1)
    (hhit : ∀ c : ℕ, 1 ≤ c → c < M →
      ∃ n : ℕ, 1 ≤ n ∧ (c : ℤ) ≤ odoUnif d (2 * c) n (cornerPoint d c)) :
    toppleTime d a ≤ toppleTime d b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ c hac ih =>
      exact le_trans (ih (by omega)) (toppleTime_mono_scale_succ d c hd (le_trans ha hac)
        (hconsist c (le_trans ha hac) (by omega)) (hhit c (le_trans ha hac) (by omega))
        (hhit (c + 1) (by omega) hbM))

/-- The one-step corner domination: at any time `n ≤ τ_c` the corner of the
`(c+1)`-cube is at most one above the corner of the `c`-cube.  This is
`odo_corner_dominate_dim` at `a = c`, `b = c + 1`, where `b - a = 1`. -/
theorem corner_dominate_succ (d c n : ℕ) (_hd : 1 ≤ d) (hc : 1 ≤ c)
    (hn : (n : ℕ∞) ≤ toppleTime d c)
    (hconsist : ∀ K : ℕ, c < K → K ≤ c + 1 → (n : ℕ∞) ≤ toppleTime d (K - 1) →
      odoUnif d (2 * K) n (cornerPoint d K) ≤
        odoUnif d (2 * (K - 1)) n (cornerPoint d (K - 1)) + 1) :
    odoUnif d (2 * (c + 1)) n (cornerPoint d (c + 1)) ≤
      odoUnif d (2 * c) n (cornerPoint d c) + 1 := by
  have h := hconsist (c + 1) (by omega) (by omega) (by
    rw [show c + 1 - 1 = c from by omega]
    exact hn)
  rwa [show c + 1 - 1 = c from by omega] at h

end DimRed
