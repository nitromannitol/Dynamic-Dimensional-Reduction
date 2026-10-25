module

public import DimRed.Support.AxisStep

@[expose] public section

/-
The two sandpile consequences of the odometer identities, the statement labelled `sandpile_corollary` in `dimred-corrected-arxiv.tex`.
The proofs expand the terminal or time-t odometer through the Laplacian and
cancel the corresponding neighbour terms.
-/

namespace DimRed

open LatticeProb

def snocPerm {d : ℕ} (π : Equiv.Perm (Fin d)) : Equiv.Perm (Fin (d + 1)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr π (Equiv.refl (Fin 1)))).trans finSumFinEquiv

def snocEps {d : ℕ} (ε : Fin d → Bool) : Fin (d + 1) → Bool :=
  Fin.snoc ε true

theorem odoInf_cubeSym_const (d N : ℕ) (c : ℤ) (π : Equiv.Perm (Fin d))
    (ε : Fin d → Bool) (x : Site d) :
    odoInf d N (fun _ => c) (cubeSym d N π ε x) = odoInf d N (fun _ => c) x := by
  simp only [odoInf]
  apply iSup_congr
  intro t
  have hsym : IsSymmetricPile d N (fun _ => c) := fun _ _ _ => rfl
  rw [odo_cubeSym d N (fun _ => c) hsym t π ε x]

theorem cubeSym_snoc (d N : ℕ) (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool)
    (x : Site d) (c : ℤ) :
    cubeSym (d + 1) N (snocPerm π) (snocEps ε) (Fin.snoc x c) =
      Fin.snoc (cubeSym d N π ε x) c := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp [cubeSym, snocPerm, snocEps]
    have hlast : Fin.natAdd d (0 : Fin 1) = Fin.last d := by rfl
    rw [hlast]
    simp
  · simp [cubeSym, snocPerm, snocEps]
    have hcast : Fin.castAdd 1 (π i) = (π i).castSucc := by rfl
    rw [hcast, Fin.snoc_castSucc]

theorem odoInf_snoc_cubeSym (d N : ℕ) (c₀ : ℤ) (π : Equiv.Perm (Fin d))
    (ε : Fin d → Bool) (x : Site d) (c : ℤ) :
    odoInf (d + 1) N (fun _ => c₀) (Fin.snoc (cubeSym d N π ε x) c) =
      odoInf (d + 1) N (fun _ => c₀) (Fin.snoc x c) := by
  rw [← cubeSym_snoc d N π ε x c]
  exact odoInf_cubeSym_const (d + 1) N c₀ (snocPerm π) (snocEps ε) (Fin.snoc x c)

def foldPointN (d N : ℕ) (x : Site d) : Site d :=
  cubeSym d N (Equiv.refl (Fin d)) (fun j => decide (1 ≤ x j)) x

noncomputable def toSimplexPointN (d N : ℕ) (x : Site d) : Site d :=
  fun j => foldPointN d N x (Tuple.sort (fun i => -(foldPointN d N x i)) j)

theorem foldPointN_mem (d N : ℕ) (x : Site d) (hx : inCube d N x) (j : Fin d) :
    1 ≤ foldPointN d N x j ∧ foldPointN d N x j ≤ (sideHalf N : ℤ) := by
  have hj := hx j
  have hsum : (1 : ℤ) ≤ loCoord N + hiCoord N := by
    have hdiv : N / 2 ≤ (N + 1) / 2 := by omega
    have hdivz : ((N / 2 : ℕ) : ℤ) ≤ (((N + 1) / 2 : ℕ) : ℤ) := by
      exact_mod_cast hdiv
    simp only [loCoord, hiCoord, sideHalf]
    omega
  rw [foldPointN, cubeSym]
  by_cases h1 : 1 ≤ x j
  · simp only [h1, decide_true, if_true]
    exact ⟨h1, hj.2⟩
  · have hx0 : x j ≤ 0 := by omega
    simp only [h1, decide_false]
    simp only [Equiv.refl_apply]
    change 1 ≤ loCoord N + hiCoord N - x j ∧
      loCoord N + hiCoord N - x j ≤ hiCoord N
    constructor
    · omega
    · omega

theorem inSimplex_toSimplexPointN (d N : ℕ) (x : Site d) (hx : inCube d N x) :
    inSimplex d (sideHalf N) (toSimplexPointN d N x) := by
  classical
  constructor
  · intro j
    exact foldPointN_mem d N x hx _
  · intro i j hij
    have hmono := Tuple.monotone_sort (fun i => -(foldPointN d N x i)) hij
    change foldPointN d N x (Tuple.sort (fun i => -(foldPointN d N x i)) j) ≤
      foldPointN d N x (Tuple.sort (fun i => -(foldPointN d N x i)) i)
    have hmono' : -foldPointN d N x (Tuple.sort (fun i => -(foldPointN d N x i)) i) ≤
        -foldPointN d N x (Tuple.sort (fun i => -(foldPointN d N x i)) j) := by
      simpa only [Function.comp_apply] using hmono
    linarith

theorem inCube_even_of_inCube (d N : ℕ) (x : Site d) (hx : inCube d N x) :
    inCube d (2 * sideHalf N) x := by
  intro i
  have hi := hx i
  simp only [loCoord, hiCoord, sideHalf] at hi ⊢
  omega

theorem cubeSym_toSimplexPointN (d N : ℕ) (x : Site d) :
    cubeSym d N (Tuple.sort (fun i => -(foldPointN d N x i))) (fun _ => true)
        (foldPointN d N x) = toSimplexPointN d N x := by
  funext j
  simp [cubeSym, toSimplexPointN]

theorem odoInfUnif_reduction_of_inCube (N d : ℕ)
    (hred : ∀ y : Site d, inSimplex d (sideHalf N) y →
      odoInfUnif (d + 1) N (Fin.snoc y 1) = odoInfUnif d N y)
    (y : Site d) (hy : inCube d N y) :
    odoInfUnif (d + 1) N (Fin.snoc y 1) = odoInfUnif d N y := by
  classical
  set z := toSimplexPointN d N y with hz
  have hzS : inSimplex d (sideHalf N) z := by
    exact inSimplex_toSimplexPointN d N y hy
  have hfold : odoInfUnif d N (foldPointN d N y) = odoInfUnif d N y := by
    simpa [odoInfUnif, foldPointN] using
      (odoInf_cubeSym_const d N (2 * (d : ℤ)) (Equiv.refl (Fin d))
        (fun j => decide (1 ≤ y j)) y)
  have hsort : odoInfUnif d N z = odoInfUnif d N (foldPointN d N y) := by
    rw [hz, ← cubeSym_toSimplexPointN d N y]
    exact odoInf_cubeSym_const d N (2 * (d : ℤ))
      (Tuple.sort (fun i => -(foldPointN d N y i))) (fun _ => true)
      (foldPointN d N y)
  have hfoldHigh :
      odoInfUnif (d + 1) N (Fin.snoc (foldPointN d N y) 1) =
        odoInfUnif (d + 1) N (Fin.snoc y 1) := by
    simpa [odoInfUnif, foldPointN] using
      (odoInf_snoc_cubeSym d N (2 * ((d + 1 : ℕ) : ℤ)) (Equiv.refl (Fin d))
        (fun j => decide (1 ≤ y j)) y 1)
  have hsortHigh :
      odoInfUnif (d + 1) N (Fin.snoc z 1) =
        odoInfUnif (d + 1) N (Fin.snoc (foldPointN d N y) 1) := by
    rw [hz, ← cubeSym_toSimplexPointN d N y]
    exact odoInf_snoc_cubeSym d N (2 * ((d + 1 : ℕ) : ℤ))
      (Tuple.sort (fun i => -(foldPointN d N y i))) (fun _ => true)
      (foldPointN d N y) 1
  calc
    odoInfUnif (d + 1) N (Fin.snoc y 1) =
        odoInfUnif (d + 1) N (Fin.snoc (foldPointN d N y) 1) := hfoldHigh.symm
    _ = odoInfUnif (d + 1) N (Fin.snoc z 1) := hsortHigh.symm
    _ = odoInfUnif d N z := hred z hzS
    _ = odoInfUnif d N y := hsort.trans hfold

theorem unit_castSucc_apply (d : ℕ) (i j : Fin d) :
    unit i.castSucc j.castSucc = unit i j := by
  by_cases h : j = i
  · subst j
    simp [unit]
  · have h' : j.castSucc ≠ i.castSucc := by
      intro h'
      exact h ((Fin.castSucc_injective d) h')
    simp [unit, h, h']

theorem nbrSum_snoc_local (d : ℕ) (u : Site (d + 1) → ℤ) (x : Site d) (c : ℤ) :
    nbrSum u (Fin.snoc x c) =
      (∑ i : Fin d,
        (u (Fin.snoc (x + unit i) c) + u (Fin.snoc (x - unit i) c))) +
        (u (Fin.snoc x (c + 1)) + u (Fin.snoc x (c - 1))) := by
  simp only [nbrSum, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    · have e : Fin.snoc x c + unit i.castSucc = Fin.snoc (x + unit i) c := by
        funext k
        refine Fin.lastCases ?_ (fun j => ?_) k
        · simp [Fin.snoc_last, unit]
        · simp only [Fin.snoc_castSucc, Pi.add_apply, unit_castSucc_apply]
      rw [e]
    · have e : Fin.snoc x c - unit i.castSucc = Fin.snoc (x - unit i) c := by
        funext k
        refine Fin.lastCases ?_ (fun j => ?_) k
        · simp [Fin.snoc_last, unit]
        · simp only [Fin.snoc_castSucc, Pi.sub_apply, unit_castSucc_apply]
      rw [e]
  · congr 1
    · have e : Fin.snoc x c + unit (Fin.last d) = Fin.snoc x (c + 1) := by
        funext k
        refine Fin.lastCases ?_ (fun j => ?_) k
        · simp [Fin.snoc_last, unit]
        · simp [Fin.snoc_castSucc, unit]
      rw [e]
    · have e : Fin.snoc x c - unit (Fin.last d) = Fin.snoc x (c - 1) := by
        funext k
        refine Fin.lastCases ?_ (fun j => ?_) k
        · simp [Fin.snoc_last, unit]
        · simp [Fin.snoc_castSucc, unit]
      rw [e]

theorem odoInf_eq_zero_outside (d N : ℕ) (s₀ : Site d → ℤ) (x : Site d)
    (hx : ¬ inCube d N x) : odoInf d N s₀ x = 0 := by
  apply le_antisymm
  · refine iSup_le fun t => ?_
    rw [odo_eq_zero_outside d N s₀ t x hx]
    exact le_refl 0
  · exact bot_le

theorem cubeSym_reflect_last (d N : ℕ) (x : Site d) (c : ℤ) :
    cubeSym (d + 1) N (Equiv.refl (Fin (d + 1)))
        (fun k => decide (k ≠ Fin.last d)) (Fin.snoc x c) =
      Fin.snoc x (loCoord N + hiCoord N - c) := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp [cubeSym]
  · simp [cubeSym]

theorem odoInfUnif_last_zero_of_odo (N d : ℕ) (_hN : 1 ≤ N)
    (hred : ∀ y : Site d, inSimplex d (sideHalf N) y →
      odoInfUnif (d + 1) N (Fin.snoc y 1) = odoInfUnif d N y)
    (hterm : ∀ y : Site d, inSimplex d (sideHalf N) y → (∀ i, 2 ≤ y i) →
      odoInfUnif (d + 1) N (Fin.snoc y 2) = odoInfUnif d N y)
    (x : Site d) (hx : inSimplex d (sideHalf N) x) (hx2 : ∀ i, 2 ≤ x i) :
    odoInfUnif (d + 1) N (Fin.snoc x 0) = odoInfUnif d N x := by
  have hsum_even : N % 2 = 0 → loCoord N + hiCoord N = 1 := by
    intro heven
    simp only [loCoord, hiCoord, sideHalf]
    omega
  have hsum_odd : N % 2 ≠ 0 → loCoord N + hiCoord N = 2 := by
    intro hodd
    simp only [loCoord, hiCoord, sideHalf]
    omega
  by_cases heven : N % 2 = 0
  · have hsum := hsum_even heven
    have hsym : odoInfUnif (d + 1) N (Fin.snoc x 0) =
        odoInfUnif (d + 1) N (Fin.snoc x 1) := by
      have h := odoInf_cubeSym_const (d + 1) N (2 * ((d + 1 : ℕ) : ℤ))
        (Equiv.refl (Fin (d + 1))) (fun k => decide (k ≠ Fin.last d))
        (Fin.snoc x 1)
      rw [cubeSym_reflect_last] at h
      simpa [odoInfUnif, hsum] using h
    exact hsym.trans (hred x hx)
  · have hsum := hsum_odd heven
    have hsym : odoInfUnif (d + 1) N (Fin.snoc x 0) =
        odoInfUnif (d + 1) N (Fin.snoc x 2) := by
      have h := odoInf_cubeSym_const (d + 1) N (2 * ((d + 1 : ℕ) : ℤ))
        (Equiv.refl (Fin (d + 1))) (fun k => decide (k ≠ Fin.last d))
        (Fin.snoc x 2)
      rw [cubeSym_reflect_last] at h
      simpa [odoInfUnif, hsum] using h
    exact hsym.trans (hterm x hx hx2)

theorem sandp_dimred_of_odo
    (N d : ℕ) (hN : 1 ≤ N) (_hd : 1 ≤ d) (x : Site d)
    (hx : inSimplex d (sideHalf N) x) (hx2 : ∀ i, 2 ≤ x i)
    (hred : ∀ y : Site d, inSimplex d (sideHalf N) y →
        odoInfUnif (d + 1) N (Fin.snoc y 1) = odoInfUnif d N y)
    (hterm : ∀ y : Site d, inSimplex d (sideHalf N) y → (∀ i, 2 ≤ y i) →
        odoInfUnif (d + 1) N (Fin.snoc y 2) = odoInfUnif d N y) :
      sandpInfUnif (d + 1) N (Fin.snoc x 1) = sandpInfUnif d N x + 2 := by
  have hred_all : ∀ y : Site d,
      odoInfUnif (d + 1) N (Fin.snoc y 1) = odoInfUnif d N y := by
    intro y
    by_cases hy : inCube d N y
    · exact odoInfUnif_reduction_of_inCube N d hred y hy
    · have hy' : ¬ inCube (d + 1) N (Fin.snoc y 1) := by
        intro hcube
        apply hy
        intro i
        simpa using hcube i.castSucc
      simp only [odoInfUnif]
      rw [odoInf_eq_zero_outside (d + 1) N (fun _ => 2 * ((d + 1 : ℕ) : ℤ))
          (Fin.snoc y 1) hy',
        odoInf_eq_zero_outside d N (fun _ => 2 * (d : ℤ)) y hy]
  have hzero : odoInfUnif (d + 1) N (Fin.snoc x 0) = odoInfUnif d N x :=
    odoInfUnif_last_zero_of_odo N d hN hred hterm x hx hx2
  have hmid :
      (∑ i : Fin d,
        (((odoInfUnif (d + 1) N (Fin.snoc (x + unit i) 1)).toNat : ℤ) +
          (odoInfUnif (d + 1) N (Fin.snoc (x - unit i) 1)).toNat)) =
      ∑ i : Fin d,
        (((odoInfUnif d N (x + unit i)).toNat : ℤ) +
          (odoInfUnif d N (x - unit i)).toNat) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := congrArg (fun q : ℕ∞ => (q.toNat : ℤ)) (hred_all (x + unit i))
    have h2 := congrArg (fun q : ℕ∞ => (q.toNat : ℤ)) (hred_all (x - unit i))
    simpa using congrArg₂ (· + ·) h1 h2
  have hterm' := congrArg (fun q : ℕ∞ => (q.toNat : ℤ)) (hterm x hx hx2)
  have hzero' := congrArg (fun q : ℕ∞ => (q.toNat : ℤ)) hzero
  have hcenter' := congrArg (fun q : ℕ∞ => (q.toNat : ℤ)) (hred_all x)
  norm_num at hterm' hzero'
  rw [sandpInfUnif, sandpInfUnif, lap, lap, nbrSum_snoc_local]
  norm_num
  rw [hmid, hterm', hzero', hcenter']
  simp only [nbrSum]
  ring

noncomputable def sortPointN (d : ℕ) (x : Site d) : Site d :=
  fun j => x (Tuple.sort (fun i => -x i) j)

theorem cubeSym_sortPointN (d N : ℕ) (x : Site d) :
    cubeSym d N (Tuple.sort (fun i => -x i)) (fun _ => true) x = sortPointN d x := by
  funext j
  simp [cubeSym, sortPointN]

theorem inSimplex_sortPointN (N d j : ℕ) (hj : j < sideHalf N) (x : Site d)
    (hx : inCube d N x)
    (hgt : ∀ i, (sideHalf N : ℤ) - (j : ℤ) < x i) :
    inSimplex d (sideHalf N) (sortPointN d x) := by
  classical
  have hA : (1 : ℤ) ≤ (sideHalf N : ℤ) - (j : ℤ) := by omega
  have hcoord : ∀ i : Fin d, 1 ≤ x i ∧ x i ≤ (sideHalf N : ℤ) := by
    intro i
    have hi := hx i
    constructor
    · have hxi : (1 : ℤ) ≤ x i := by linarith [hgt i, hA]
      exact hxi
    · exact hi.2
  constructor
  · intro i
    dsimp [sortPointN]
    exact hcoord _
  · intro i k hik
    have hmono := Tuple.monotone_sort (fun i => -x i) hik
    have hmono' : -x (Tuple.sort (fun i => -x i) i) ≤
        -x (Tuple.sort (fun i => -x i) k) := by
      simpa only [Function.comp_apply] using hmono
    dsimp [sortPointN]
    linarith

theorem odoUnif_selfsim_of_odo (N d j t : ℕ) (hj : j < sideHalf N)
    (hodo : ∀ y : Site d, inSimplex d (sideHalf N) y →
      (∀ i, (sideHalf N : ℤ) - (j : ℤ) < y i) →
      odoUnif d N t y = odoUnif d (2 * j) t
        (fun i => y i - ((sideHalf N : ℤ) - (j : ℤ))))
    (y : Site d) (hgt : ∀ i, (sideHalf N : ℤ) - (j : ℤ) < y i) :
    odoUnif d N t y = odoUnif d (2 * j) t
      (fun i => y i - ((sideHalf N : ℤ) - (j : ℤ))) := by
  classical
  let A : ℤ := (sideHalf N : ℤ) - (j : ℤ)
  have hA : (1 : ℤ) ≤ A := by
    dsimp [A]
    omega
  by_cases hy : inCube d N y
  · set z := sortPointN d y with hz
    have hzS : inSimplex d (sideHalf N) z := by
      exact inSimplex_sortPointN N d j hj y hy hgt
    have hzt : ∀ i, (sideHalf N : ℤ) - (j : ℤ) < z i := by
      intro i
      exact hgt _
    have hsymN : odoUnif d N t z = odoUnif d N t y := by
      have h := odo_cubeSym d N (fun _ => 2 * (d : ℤ))
        (isSymmetricPile_const' d N (2 * (d : ℤ))) t
        (Tuple.sort (fun i => -y i)) (fun _ => true) y
      rw [cubeSym_sortPointN] at h
      simpa [odoUnif, hz] using h
    have hsmall :
        odoUnif d (2 * j) t (fun i => z i - A) =
          odoUnif d (2 * j) t (fun i => y i - A) := by
      have h := odo_cubeSym d (2 * j) (fun _ => 2 * (d : ℤ))
        (isSymmetricPile_const' d (2 * j) (2 * (d : ℤ))) t
        (Tuple.sort (fun i => -y i)) (fun _ => true)
        (fun i => y i - A)
      have he : cubeSym d (2 * j) (Tuple.sort (fun i => -y i)) (fun _ => true)
          (fun i => y i - A) = (fun i => z i - A) := by
        funext i
        simp [cubeSym, hz, sortPointN]
      rw [he] at h
      simpa [odoUnif] using h
    calc
      odoUnif d N t y = odoUnif d N t z := hsymN.symm
      _ = odoUnif d (2 * j) t (fun i => z i - A) := by
        simpa [A] using hodo z hzS hzt
      _ = odoUnif d (2 * j) t (fun i => y i - A) := hsmall
  · have hzeroN : odoUnif d N t y = 0 := by
      exact odo_eq_zero_outside d N (fun _ => 2 * (d : ℤ)) t y hy
    have hySmall : ¬ inCube d (2 * j) (fun i => y i - A) := by
      intro hc
      apply hy
      have hlo : loCoord N ≤ (1 : ℤ) := by simp [loCoord]; omega
      intro i
      have hupper := (hc i).2
      have hyi : y i ≤ (sideHalf N : ℤ) := by
        simp only [hiCoord, sideHalf] at hupper
        dsimp [A] at hupper
        omega
      have hlow : (1 : ℤ) ≤ y i := by
        have hi := hgt i
        omega
      exact ⟨le_trans hlo hlow, hyi⟩
    have hzeroSmall : odoUnif d (2 * j) t (fun i => y i - A) = 0 := by
      exact odo_eq_zero_outside d (2 * j) (fun _ => 2 * (d : ℤ)) t _ hySmall
    rw [hzeroN, hzeroSmall]
 
theorem sandp_selfsim_of_odo
    (N d : ℕ) (hN : 1 ≤ N) (_hd : 2 ≤ d) (j t : ℕ) (hj : j < sideHalf N)
    (x : Site d) (_hx : inSimplex d (sideHalf N) x)
    (hxgt : ∀ i, (sideHalf N : ℤ) - (j : ℤ) + 1 < x i)
    (hodo : ∀ y : Site d, inSimplex d (sideHalf N) y →
      (∀ i, (sideHalf N : ℤ) - (j : ℤ) < y i) →
      odoUnif d N t y = odoUnif d (2 * j) t
        (fun i => y i - ((sideHalf N : ℤ) - (j : ℤ)))) :
      sandpUnif d N t x = sandpUnif d (2 * j) t
        (fun i => x i - ((sideHalf N : ℤ) - (j : ℤ))) := by
  have _hN' : 1 ≤ sideHalf N := by omega
  have _hNuse : 1 ≤ N := hN
  have hgt : ∀ y : Site d, (∀ i, (sideHalf N : ℤ) - (j : ℤ) < y i) →
      odoUnif d N t y = odoUnif d (2 * j) t
        (fun i => y i - ((sideHalf N : ℤ) - (j : ℤ))) := by
    intro y hy
    exact odoUnif_selfsim_of_odo N d j t hj hodo y hy
  have hcenter := hgt x (fun i => by
    have hi := hxgt i
    omega)
  have hplus := fun i => hgt (x + unit i) (fun k => by
    have := hxgt k
    rw [add_unit_apply]
    split <;> omega)
  have hminus := fun i => hgt (x - unit i) (fun k => by
    have := hxgt k
    rw [sub_unit_apply]
    split <;> omega)
  have hplus' : ∀ i : Fin d,
      odoUnif d N t (x + unit i) = odoUnif d (2 * j) t
        ((fun k => x k - ((sideHalf N : ℤ) - (j : ℤ))) + unit i) := by
    intro i
    rw [hplus i]
    congr 1
    funext k
    rw [add_unit_apply d x i k,
      add_unit_apply d (fun k => x k - ((sideHalf N : ℤ) - (j : ℤ))) i k]
    ring
  have hminus' : ∀ i : Fin d,
      odoUnif d N t (x - unit i) = odoUnif d (2 * j) t
        ((fun k => x k - ((sideHalf N : ℤ) - (j : ℤ))) - unit i) := by
    intro i
    rw [hminus i]
    congr 1
    funext k
    rw [sub_unit_apply d x i k,
      sub_unit_apply d (fun k => x k - ((sideHalf N : ℤ) - (j : ℤ))) i k]
    ring
  have hsum : nbrSum (odoUnif d N t) x =
      nbrSum (odoUnif d (2 * j) t)
        (fun i => x i - ((sideHalf N : ℤ) - (j : ℤ))) := by
    simp only [nbrSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hplus' i, hminus' i]
  simp only [sandpUnif, sandp]
  change 2 * (d : ℤ) + lap (fun y => odoUnif d N t y) x =
    2 * (d : ℤ) + lap (fun y => odoUnif d (2 * j) t y)
      (fun i => x i - ((sideHalf N : ℤ) - (j : ℤ)))
  simp only [lap]
  rw [hcenter, hsum]

end DimRed
