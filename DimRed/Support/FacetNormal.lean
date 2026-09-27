import DimRed.Support.StrongDerivPure
import DimRed.Support.Downset
import DimRed.Support.FacetNbr
import DimRed.Support.Symmetry

/-!
# The sorting normal form of a facet point

The sorting normal form of a point of the positive orthant with a coordinate
equal to `1`: after sorting the coordinates with that coordinate first among the
ones, the point is `facetPoint z 1 j` and its neighbour in that direction is
`facetPoint z 2 j`.  This is the normal form that weak and strong facet
compatibility are stated for.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DimRed

open LatticeProb


/-- A facet point with a sorted head is antitone. -/
theorem facetPoint_antitone (i j : ℕ) (z : Fin i → ℤ) (hanti : Antitone z)
    (hz : ∀ a, 2 ≤ z a) :
    ∀ l m : Fin (i + 1 + j), l ≤ m → facetPoint z 1 j m ≤ facetPoint z 1 j l := by
  intro l m hlm
  have hle : (l : ℕ) ≤ (m : ℕ) := hlm
  have key : ∀ p q : Fin (i + 1 + j), (p : ℕ) ≤ (q : ℕ) →
      facetPoint z 1 j q ≤ facetPoint z 1 j p := by
    intro p q hpq
    by_cases hp : (p : ℕ) < i
    · by_cases hq : (q : ℕ) < i
      · have h1 : (⟨(p : ℕ), hp⟩ : Fin i) ≤ ⟨(q : ℕ), hq⟩ := by
          rw [Fin.le_def]; simp only; exact hpq
        have e1 : facetPoint z 1 j p = z ⟨(p : ℕ), hp⟩ := by
          have hpp : p = Fin.castAdd j (Fin.castSucc ⟨(p : ℕ), hp⟩) := Fin.ext rfl
          conv_lhs => rw [hpp]
          rw [facetPoint_head]
        have e2 : facetPoint z 1 j q = z ⟨(q : ℕ), hq⟩ := by
          have hqq : q = Fin.castAdd j (Fin.castSucc ⟨(q : ℕ), hq⟩) := Fin.ext rfl
          conv_lhs => rw [hqq]
          rw [facetPoint_head]
        rw [e1, e2]
        exact hanti h1
      · have hqi : i ≤ (q : ℕ) := le_of_not_gt hq
        have e1 : facetPoint z 1 j p = z ⟨(p : ℕ), hp⟩ := by
          have hpp : p = Fin.castAdd j (Fin.castSucc ⟨(p : ℕ), hp⟩) := Fin.ext rfl
          conv_lhs => rw [hpp]
          rw [facetPoint_head]
        have e2 : facetPoint z 1 j q = 1 := by
          rcases lt_or_eq_of_le hqi with hlt | heq
          · have hqq : q = Fin.natAdd (i + 1) ⟨(q : ℕ) - (i + 1), by omega⟩ := Fin.ext (by
              simp only [Fin.val_natAdd]; omega)
            conv_lhs => rw [hqq]
            rw [facetPoint_tail]
          · have hqq : q = Fin.castAdd j (Fin.last i) := Fin.ext (by
              simp only [Fin.val_castAdd, Fin.val_last]
              omega)
            conv_lhs => rw [hqq]
            rw [facetPoint_mid]
        rw [e1, e2]
        linarith [hz ⟨(p : ℕ), hp⟩]
    · have hpi : i ≤ (p : ℕ) := le_of_not_gt hp
      have hqi : i ≤ (q : ℕ) := le_trans hpi hpq
      have e2 : facetPoint z 1 j q = 1 := by
        rcases lt_or_eq_of_le hqi with hlt | heq
        · have hqq : q = Fin.natAdd (i + 1) ⟨(q : ℕ) - (i + 1), by omega⟩ := Fin.ext (by
            simp only [Fin.val_natAdd]; omega)
          conv_lhs => rw [hqq]
          rw [facetPoint_tail]
        · have hqq : q = Fin.castAdd j (Fin.last i) := Fin.ext (by
            simp only [Fin.val_castAdd, Fin.val_last]
            omega)
          conv_lhs => rw [hqq]
          rw [facetPoint_mid]
      have e1 : facetPoint z 1 j p = 1 := by
        rcases lt_or_eq_of_le hpi with hlt | heq
        · have hpp : p = Fin.natAdd (i + 1) ⟨(p : ℕ) - (i + 1), by omega⟩ := Fin.ext (by
            simp only [Fin.val_natAdd]; omega)
          conv_lhs => rw [hpp]
          rw [facetPoint_tail]
        · have hpp : p = Fin.castAdd j (Fin.last i) := Fin.ext (by
            simp only [Fin.val_castAdd, Fin.val_last]
            omega)
          conv_lhs => rw [hpp]
          rw [facetPoint_mid]
      rw [e1, e2]
  exact key l m hle

/-- The odometer is unchanged when the index type is transported along an
equality of dimensions. -/
theorem odoUnif_cast {d d' : ℕ} (h : d = d') (M t : ℕ) (f : Site d') :
    odoUnif d (2 * M) t (fun a => f (Fin.cast h a)) = odoUnif d' (2 * M) t f := by
  subst h
  rfl

/-- The sorting normal form of a point of the positive orthant with a coordinate
equal to `1`. -/
theorem facet_normal_form (d M : ℕ) (x : Site d) (hx : inPos d M x) (k : Fin d) (hk : x k = 1) :
    ∃ (i j : ℕ) (_ : i + 1 + j = d) (z : Fin i → ℤ), (∀ a, 2 ≤ z a) ∧
      inSimplex (i + 1 + j) M (facetPoint z 1 j) ∧ ((∃ l, 2 ≤ x l) → 1 ≤ i) ∧
      ∀ t, odoUnif d (2 * M) t x = odoUnif (i + 1 + j) (2 * M) t (facetPoint z 1 j) ∧
        odoUnif d (2 * M) t (x + unit k) = odoUnif (i + 1 + j) (2 * M) t (facetPoint z 2 j) := by
  classical
  set S : Finset (Fin d) := Finset.univ.filter (fun l => 2 ≤ x l) with hSdef
  set i : ℕ := S.card with hidef
  set j : ℕ := d - i - 1 with hjdef
  have hkS : k ∉ S := by
    rw [hSdef]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hcard : i < d := by
    have h := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ S, by
      intro hc
      exact hkS (hc ▸ Finset.mem_univ k)⟩)
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [hidef]
    exact h
  have hij : i + 1 + j = d := by
    rw [hjdef, Nat.sub_sub]
    exact Nat.add_sub_cancel' (by omega)
  let κ : Fin d → ℤ := fun l => -(2 * x l) + (if l = k then 0 else 1)
  let π : Equiv.Perm (Fin d) := Tuple.sort κ
  have hmono : Monotone (κ ∘ π) := Tuple.monotone_sort κ
  have hmemS : ∀ l : Fin d, l ∈ S ↔ 2 ≤ x l := by intro l; simp [hSdef]
  have hκbig : ∀ l : Fin d, 2 ≤ x l → κ l ≤ -3 := by
    intro l hl; dsimp [κ]; split_ifs <;> omega
  have hκone : ∀ l : Fin d, x l = 1 → κ l = -2 ∨ κ l = -1 := by
    intro l hl; dsimp [κ]; rw [hl]; split_ifs <;> omega
  set T : Finset (Fin d) := Finset.univ.filter (fun b => κ (π b) ≤ -3) with hTdef
  have hTdown : ∀ b b' : Fin d, b ∈ T → b' ≤ b → b' ∈ T := by
    intro b b' hb hbb
    rw [hTdef] at hb ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact le_trans (hmono hbb) hb
  have hTS : ∀ b : Fin d, b ∈ T → π b ∈ S := by
    intro b hb
    rw [hTdef] at hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact (hmemS (π b)).mpr (by
      by_contra hcon
      have h2 : x (π b) = 1 := by have := (hx (π b)).1; omega
      have h3 := hκone (π b) h2
      omega)
  have hST : ∀ b : Fin d, π b ∈ S → b ∈ T := by
    intro b hb
    rw [hTdef]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hκbig (π b) ((hmemS (π b)).mp hb)
  have hTcard : T.card = i := by
    have hbij : T.card = S.card := by
      refine Finset.card_bij (fun b _ => π b) (fun b hb => hTS b hb)
        (fun b1 _ b2 _ h => π.injective h)
        (fun c hc => ⟨π.symm c, hST _ (by rwa [π.apply_symm_apply]), π.apply_symm_apply c⟩)
    rw [hbij, hidef]
  have hTmem : ∀ b : Fin d, b ∈ T ↔ (b : ℕ) < i := by
    have hTeq := downset_eq_Iio d i hcard T hTdown hTcard
    intro b
    rw [hTeq]
    exact Finset.mem_Iio
  have hfirst : ∀ a : Fin d, (a : ℕ) < i → 2 ≤ x (π a) := by
    intro a ha
    exact (hmemS (π a)).mp (hTS a ((hTmem a).mpr ha))
  have hmid1 : x (π (Fin.cast hij (Fin.castAdd j (Fin.last i)))) = 1 := by
    have hidx : ((Fin.cast hij (Fin.castAdd j (Fin.last i)) : Fin d) : ℕ) = i := by
      simp [Fin.cast, Fin.castAdd]
    by_contra hcon
    have h2 : 2 ≤ x (π (Fin.cast hij (Fin.castAdd j (Fin.last i)))) := by
      have := (hx (π (Fin.cast hij (Fin.castAdd j (Fin.last i))))).1; omega
    have hmem : π (Fin.cast hij (Fin.castAdd j (Fin.last i))) ∈ S := (hmemS _).mpr h2
    have hT : Fin.cast hij (Fin.castAdd j (Fin.last i)) ∈ T := hST _ hmem
    have := (hTmem _).mp hT
    omega
  have hπi : π (Fin.cast hij (Fin.castAdd j (Fin.last i))) = k := by
    by_contra hne
    have hκi : κ (π (Fin.cast hij (Fin.castAdd j (Fin.last i)))) = -1 := by
      rcases hκone _ hmid1 with h | h
      · exfalso
        have hz : (if π (Fin.cast hij (Fin.castAdd j (Fin.last i))) = k
            then (0:ℤ) else 1) = 0 := by
          have hdef : κ (π (Fin.cast hij (Fin.castAdd j (Fin.last i))))
              = -(2 * x (π (Fin.cast hij (Fin.castAdd j (Fin.last i)))))
                + (if π (Fin.cast hij (Fin.castAdd j (Fin.last i))) = k then 0 else 1) := rfl
          rw [hdef, hmid1] at h; omega
        exact hne (by simpa using hz)
      · exact h
    let b : Fin d := π.symm k
    have hb : π b = k := π.apply_symm_apply k
    have hκb : κ (π b) = -2 := by
      have hdef : κ k = -(2 * x k) + (if k = k then (0:ℤ) else 1) := rfl
      rw [hb, hdef, hk]; norm_num
    have hlt : b < Fin.cast hij (Fin.castAdd j (Fin.last i)) := by
      by_contra hle
      have hle' : Fin.cast hij (Fin.castAdd j (Fin.last i)) ≤ b := le_of_not_gt hle
      have h1 : κ (π (Fin.cast hij (Fin.castAdd j (Fin.last i)))) ≤ κ (π b) := hmono hle'
      omega
    have hidx : ((Fin.cast hij (Fin.castAdd j (Fin.last i)) : Fin d) : ℕ) = i := by
      simp [Fin.cast, Fin.castAdd]
    have hb1 := hfirst b (by rw [Fin.lt_def] at hlt; rw [hidx] at hlt; exact hlt)
    rw [hb, hk] at hb1
    omega
  have htail1 : ∀ b : Fin j, x (π (Fin.cast hij (Fin.natAdd (i + 1) b))) = 1 := by
    intro b
    have hidx : ((Fin.cast hij (Fin.natAdd (i + 1) b) : Fin d) : ℕ) = i + 1 + (b : ℕ) := by
      simp [Fin.cast, Fin.natAdd]
    have hidx0 : ((Fin.cast hij (Fin.castAdd j (Fin.last i)) : Fin d) : ℕ) = i := by
      simp [Fin.cast, Fin.castAdd]
    have hge : (Fin.cast hij (Fin.castAdd j (Fin.last i)) : Fin d)
        ≤ Fin.cast hij (Fin.natAdd (i + 1) b) := by
      rw [Fin.le_def]
      rw [hidx0, hidx]
      omega
    have h1 : κ (π (Fin.cast hij (Fin.castAdd j (Fin.last i))))
        ≤ κ (π (Fin.cast hij (Fin.natAdd (i + 1) b))) := hmono hge
    rw [hπi] at h1
    have hκk : κ k = -2 := by
      have hdef : κ k = -(2 * x k) + (if k = k then (0:ℤ) else 1) := rfl
      rw [hdef, hk]; norm_num
    rw [hκk] at h1
    by_contra hcon
    have h2 : 2 ≤ x (π (Fin.cast hij (Fin.natAdd (i + 1) b))) := by
      have := (hx (π (Fin.cast hij (Fin.natAdd (i + 1) b)))).1; omega
    have h3 := hκbig _ h2
    omega
  have hanti : Antitone (fun a : Fin i => x (π (Fin.cast hij (Fin.castAdd j
      (Fin.castSucc a))))) := by
    intro a b hab
    have hle : (Fin.cast hij (Fin.castAdd j (Fin.castSucc a)) : Fin d)
        ≤ Fin.cast hij (Fin.castAdd j (Fin.castSucc b)) := by
      rw [Fin.le_def] at hab ⊢
      simp [Fin.cast, Fin.castAdd]
      omega
    have h1 : κ (π (Fin.cast hij (Fin.castAdd j (Fin.castSucc a))))
        ≤ κ (π (Fin.cast hij (Fin.castAdd j (Fin.castSucc b)))) := hmono hle
    have h2 : 2 ≤ x (π (Fin.cast hij (Fin.castAdd j (Fin.castSucc a)))) :=
      hfirst _ (by
        have hidx : ((Fin.cast hij (Fin.castAdd j (Fin.castSucc a)) : Fin d) : ℕ)
            = (a : ℕ) := by
          simp [Fin.cast, Fin.castAdd]
        rw [hidx]; exact a.isLt)
    have h3 : 2 ≤ x (π (Fin.cast hij (Fin.castAdd j (Fin.castSucc b)))) :=
      hfirst _ (by
        have hidx : ((Fin.cast hij (Fin.castAdd j (Fin.castSucc b)) : Fin d) : ℕ)
            = (b : ℕ) := by
          simp [Fin.cast, Fin.castAdd]
        rw [hidx]; exact b.isLt)
    have h4 := hκbig _ h2
    have h5 := hκbig _ h3
    have h6 : κ (π (Fin.cast hij (Fin.castAdd j (Fin.castSucc a))))
        = -(2 * x (π (Fin.cast hij (Fin.castAdd j (Fin.castSucc a)))))
          + (if π (Fin.cast hij (Fin.castAdd j (Fin.castSucc a))) = k then 0 else 1) := rfl
    have h7 : κ (π (Fin.cast hij (Fin.castAdd j (Fin.castSucc b))))
        = -(2 * x (π (Fin.cast hij (Fin.castAdd j (Fin.castSucc b)))))
          + (if π (Fin.cast hij (Fin.castAdd j (Fin.castSucc b))) = k then 0 else 1) := rfl
    rw [h6, h7] at h1
    by_cases ha : π (Fin.cast hij (Fin.castAdd j (Fin.castSucc a))) = k
    · exact absurd h2 (by rw [ha, hk]; omega)
    · by_cases hb : π (Fin.cast hij (Fin.castAdd j (Fin.castSucc b))) = k
      · rw [if_neg ha, if_pos hb] at h1
        have hb1 : x (π (Fin.cast hij (Fin.castAdd j (Fin.castSucc b)))) = 1 := by rw [hb, hk]
        omega
      · rw [if_neg ha, if_neg hb] at h1
        linarith [h4, h5]
  have hM1 : (1 : ℤ) ≤ (M : ℤ) := by
    have h1 : (1 : ℤ) ≤ x k := (hx k).1
    have h2 : x k ≤ (M : ℤ) := (hx k).2
    omega
  refine ⟨i, j, hij, fun a => x (π (Fin.cast hij (Fin.castAdd j (Fin.castSucc a)))),
    ?_, ?_, ?_, ?_⟩
  · intro a
    have hidx : ((Fin.cast hij (Fin.castAdd j (Fin.castSucc a)) : Fin d) : ℕ) = (a : ℕ) := by
      simp [Fin.cast, Fin.castAdd]
    exact hfirst _ (by rw [hidx]; exact a.isLt)
  · constructor
    · intro l
      refine Fin.addCases ?_ ?_ l
      · intro h
        refine Fin.lastCases ?_ (fun a => ?_) h
        · rw [facetPoint_mid]
          exact ⟨le_refl 1, hM1⟩
        · rw [facetPoint_head]
          have hidx : ((Fin.cast hij (Fin.castAdd j (Fin.castSucc a)) : Fin d) : ℕ)
            = (a : ℕ) := by
            simp [Fin.cast, Fin.castAdd]
          have h2 : 2 ≤ x (π (Fin.cast hij (Fin.castAdd j (Fin.castSucc a)))) :=
            hfirst _ (by rw [hidx]; exact a.isLt)
          exact ⟨by linarith, (hx _).2⟩
      · intro a
        rw [facetPoint_tail]
        exact ⟨le_refl 1, hM1⟩
    · exact facetPoint_antitone i j _ hanti (fun a => hfirst _ (by
        have hidx : ((Fin.cast hij (Fin.castAdd j (Fin.castSucc a)) : Fin d) : ℕ)
            = (a : ℕ) := by
          simp [Fin.cast, Fin.castAdd]
        rw [hidx]; exact a.isLt))
  · intro ⟨l, hl⟩
    have : 0 < i := by
      rw [hidef]
      exact Finset.card_pos.mpr ⟨l, (hmemS l).mpr hl⟩
    omega
  · intro t
    constructor
    · have hperm : (fun a : Fin d => x (π a))
          = fun a : Fin d => facetPoint (fun a => x (π (Fin.cast hij (Fin.castAdd j
              (Fin.castSucc a))))) 1 j
              (Fin.cast hij.symm a) := by
        funext l
        have hl : Fin.cast hij (Fin.cast hij.symm l) = l := by
          rw [Fin.cast_cast]
          rfl
        rw [← hl]
        refine Fin.addCases ?_ ?_ (Fin.cast hij.symm l)
        · intro h
          refine Fin.lastCases ?_ (fun b => ?_) h
          · rw [facetPoint_mid]; exact hmid1
          · rw [facetPoint_head]
        · intro a; rw [facetPoint_tail]; exact htail1 a
      have hsym := odo_cubeSym d (2 * M) (fun _ => 2 * (d : ℤ))
        (isSymmetricPile_const' d (2 * M) (2 * (d : ℤ))) t π (fun _ => true) x
      have he : cubeSym d (2 * M) π (fun _ => true) x = fun a => x (π a) := by
        funext a; simp [cubeSym]
      rw [he] at hsym
      rw [hperm] at hsym
      exact hsym.symm.trans (odoUnif_cast hij.symm M t
        (facetPoint (fun a => x (π (Fin.cast hij (Fin.castAdd j (Fin.castSucc a))))) 1 j))
    · have hperm : (fun a : Fin d => (x + unit k) (π a))
          = fun a : Fin d => facetPoint (fun a => x (π (Fin.cast hij (Fin.castAdd j
              (Fin.castSucc a))))) 2 j
              (Fin.cast hij.symm a) := by
        funext l
        have hl : Fin.cast hij (Fin.cast hij.symm l) = l := by
          rw [Fin.cast_cast]
          rfl
        rw [← hl]
        refine Fin.addCases ?_ ?_ (Fin.cast hij.symm l)
        · intro h
          refine Fin.lastCases ?_ (fun b => ?_) h
          · rw [facetPoint_mid, Pi.add_apply, hπi, hk]
            simp [unit]
          · rw [facetPoint_head, Pi.add_apply]
            have hne : π (Fin.cast hij (Fin.castAdd j (Fin.castSucc b))) ≠ k := by
              intro hc
              have h1 : Fin.cast hij (Fin.castAdd j (Fin.castSucc b))
                  = Fin.cast hij (Fin.castAdd j (Fin.last i)) := π.injective (by rw [hc, hπi])
              rw [Fin.ext_iff] at h1
              simp [Fin.cast, Fin.castAdd] at h1
              omega
            rw [unit_apply_ne hne, add_zero]
        · intro a
          rw [facetPoint_tail, Pi.add_apply, htail1 a]
          have hne2 : π (Fin.cast hij (Fin.natAdd (i + 1) a)) ≠ k := by
            intro hc
            rw [← hπi] at hc
            have h1 : Fin.cast hij (Fin.natAdd (i + 1) a)
                = Fin.cast hij (Fin.castAdd j (Fin.last i)) := π.injective hc
            rw [Fin.ext_iff] at h1
            simp [Fin.cast, Fin.castAdd, Fin.natAdd] at h1
            omega
          rw [unit_apply_ne hne2, add_zero]
      have hsym := odo_cubeSym d (2 * M) (fun _ => 2 * (d : ℤ))
        (isSymmetricPile_const' d (2 * M) (2 * (d : ℤ))) t π (fun _ => true) (x + unit k)
      have he : cubeSym d (2 * M) π (fun _ => true) (x + unit k)
          = fun a => (x + unit k) (π a) := by
        funext a; simp [cubeSym]
      rw [he] at hsym
      rw [hperm] at hsym
      exact hsym.symm.trans (odoUnif_cast hij.symm M t
        (facetPoint (fun a => x (π (Fin.cast hij (Fin.castAdd j (Fin.castSucc a))))) 2 j))

end DimRed
