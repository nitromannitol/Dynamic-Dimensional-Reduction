module

public import DimRed.Support.DerivBound
public import DimRed.Support.Difference

@[expose] public section

/-!
The time step for dimensional reduction, following the subsection labelled `subsec:dim_reduction` in `dimred-corrected-arxiv.tex`.
The zero-gap and boundary-gap cases are formalized here; the remaining
interior facet case is exposed as an explicit induction hypothesis.
-/
namespace DimRed

open LatticeProb

def weak_facet_step (d M q : ℕ) : Prop :=
  ∀ (z : Site d) (k : Fin d), inSimplex d M z → z k = 1 →
    odoUnif d (2 * M) q z = odoUnif d (2 * M) q (z + unit k) + 1 →
    odoUnif d (2 * M) (q + 1) z = odoUnif d (2 * M) q z

def strong_facet_step (d M q : ℕ) : Prop :=
  ∀ (z : Site d) (k : Fin d), inSimplex d M z → z k = 1 →
    odoUnif d (2 * M) q z - odoUnif d (2 * M) q (z + unit k) ≤ 1

/-- The second conjunct of strong facet compatibility at a raw point: a site with
a coordinate equal to one that has just fired does not fire again, and its
neighbour in that direction does.  The clause of Proposition 4.1 carries this
only in the regime `t < τ_M ∨ 1 ≤ i`, which is why it is a separate predicate. -/
def strong_facet_step_topple (d M q : ℕ) : Prop :=
  ∀ (z : Site d) (k : Fin d), inSimplex d M z → z k = 1 → (∃ l, 2 ≤ z l) →
    odoUnif d (2 * M) q z = odoUnif d (2 * M) q (z + unit k) + 1 →
      odoUnif d (2 * M) (q + 1) z = odoUnif d (2 * M) q z ∧
        odoUnif d (2 * M) (q + 1) (z + unit k) =
          odoUnif d (2 * M) q (z + unit k) + 1

def strong_topple_control_step (d M : ℕ) : Prop :=
  ∀ (q : ℕ), toppleTime d (M - 1) ≤ (q : ℕ∞) →
    simplexMax d M (fun z => odoUnif d (2 * M) (q + 2) z -
      odoUnif d (2 * M) q z) ≤ 1

def self_similarity_step (d M : ℕ) : Prop :=
  ∀ (j : ℕ), 1 ≤ j → j ≤ M → ∀ (q : ℕ), (q : ℕ∞) ≤ toppleTime d j →
    ∀ z : Site d, inSimplex d M z →
      (∀ i : Fin d, (M : ℤ) - (j : ℤ) < z i) →
      odoUnif d (2 * M) q z =
        odoUnif d (2 * j) q (fun i => z i - ((M : ℤ) - (j : ℤ)))

theorem fin_snoc_add_unit {d : ℕ} (x : Site d) (c : ℤ) (i : Fin d) :
    Fin.snoc (x + unit i) c = Fin.snoc x c + unit (Fin.castSucc i) := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp [Fin.snoc, unit]
  · simp only [Fin.snoc_castSucc, Pi.add_apply, unit]
    by_cases hji : j = i
    · subst j
      simp
    · have hji' : j.castSucc ≠ i.castSucc := by
        intro h
        exact hji (Fin.castSucc_injective _ h)
      simp [Pi.single_eq_of_ne hji, Pi.single_eq_of_ne hji']

theorem fin_snoc_sub_unit {d : ℕ} (x : Site d) (c : ℤ) (i : Fin d) :
    Fin.snoc (x - unit i) c = Fin.snoc x c - unit (Fin.castSucc i) := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp [Fin.snoc, unit]
  · simp only [Fin.snoc_castSucc, Pi.sub_apply, unit]
    by_cases hji : j = i
    · subst j
      simp
    · have hji' : j.castSucc ≠ i.castSucc := by
        intro h
        exact hji (Fin.castSucc_injective _ h)
      simp [Pi.single_eq_of_ne hji, Pi.single_eq_of_ne hji']

theorem fin_snoc_add_last {d : ℕ} (x : Site d) (c : ℤ) :
    Fin.snoc x (c + 1) = Fin.snoc x c + unit (Fin.last d) := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp [Fin.snoc, unit]
  · simp [Fin.snoc, unit]

theorem fin_snoc_sub_last {d : ℕ} (x : Site d) (c : ℤ) :
    Fin.snoc x (c - 1) = Fin.snoc x c - unit (Fin.last d) := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp [Fin.snoc, unit]
  · simp [Fin.snoc, unit]

theorem inSimplex_snoc_one_local {d M : ℕ} (x : Site d) (hx : inSimplex d M x)
    (hM : 1 ≤ M) :
    inSimplex (d + 1) M (Fin.snoc x 1) := by
  constructor
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.snoc]
      omega
    · simpa [Fin.snoc] using hx.1 j
  · intro i j hij
    revert hij
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · refine Fin.lastCases ?_ (fun i' => ?_) i
      · intro _
        rfl
      · intro _
        simpa [Fin.snoc] using (hx.1 i').1
    · refine Fin.lastCases ?_ (fun i' => ?_) i
      · intro hij
        exfalso
        have hle : d ≤ (j' : ℕ) := by
          simpa [Fin.le_def] using hij
        omega
      · intro hij
        simpa [Fin.snoc] using hx.2 i' j' (Fin.le_def.mpr (Fin.le_def.mp hij))

theorem lap_snoc_eq_of_reduction {d M q : ℕ} (x : Site d)
    (hprev : ∀ z : Site d,
      odoUnif (d + 1) (2 * M) q (Fin.snoc z 1) = odoUnif d (2 * M) q z)
    (hgap : odoUnif (d + 1) (2 * M) q (Fin.snoc x 1 + unit (Fin.last d)) =
      odoUnif (d + 1) (2 * M) q (Fin.snoc x 1)) :
    lap (odoUnif (d + 1) (2 * M) q) (Fin.snoc x 1) =
      lap (odoUnif d (2 * M) q) x := by
  let u : Site (d + 1) → ℤ := odoUnif (d + 1) (2 * M) q
  let v : Site d → ℤ := odoUnif d (2 * M) q
  have hminus : u ((Fin.snoc x 1) - unit (Fin.last d)) = u (Fin.snoc x 1) := by
    have hpoint : (Fin.snoc x 1) - unit (Fin.last d) = Fin.snoc x (0 : ℤ) :=
      (fin_snoc_sub_last x 1).symm
    have h := odo_reflect_coord (d + 1) M (2 * ((d + 1 : ℕ) : ℤ)) q
      (Fin.snoc x (0 : ℤ)) (Fin.last d)
    have he : (fun k : Fin (d + 1) =>
        if k = Fin.last d then 1 -
            ((Fin.snoc x (0 : ℤ) : Site (d + 1)) (Fin.last d))
        else (Fin.snoc x (0 : ℤ) : Site (d + 1)) k) =
        (Fin.snoc x 1 : Site (d + 1)) := by
      funext k
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simp [Fin.snoc]
      · simp [Fin.snoc]
    rw [he] at h
    rw [hpoint]
    exact h.symm
  have hadd : u (Fin.snoc x 1 + unit (Fin.last d)) =
      u (Fin.snoc x 1) := hgap
  have hsum : nbrSum u (Fin.snoc x 1) = nbrSum v x +
      (u (Fin.snoc x 1 + unit (Fin.last d)) +
        u (Fin.snoc x 1 - unit (Fin.last d))) := by
    simp only [nbrSum]
    rw [Fin.sum_univ_add]
    rw [Fin.sum_univ_one]
    have hplus : ∀ i : Fin d,
        u (Fin.snoc x 1 + unit (Fin.castSucc i)) = v (x + unit i) := by
      intro i
      rw [← fin_snoc_add_unit x 1 i]
      simpa [u, v] using hprev (x + unit i)
    have hminus' : ∀ i : Fin d,
        u (Fin.snoc x 1 - unit (Fin.castSucc i)) = v (x - unit i) := by
      intro i
      rw [← fin_snoc_sub_unit x 1 i]
      simpa [u, v] using hprev (x - unit i)
    have hplus_sum :
        (∑ i : Fin d, (u (Fin.snoc x 1 + unit (Fin.castSucc i)) +
          u (Fin.snoc x 1 - unit (Fin.castSucc i)))) = nbrSum v x := by
      simp only [nbrSum]
      exact Finset.sum_congr rfl (fun i _ => by rw [hplus i, hminus' i])
    have hplus_sum' :
        (∑ i : Fin d, (u (Fin.snoc x 1 + unit (Fin.castAdd 1 i)) +
          u (Fin.snoc x 1 - unit (Fin.castAdd 1 i)))) = nbrSum v x := by
      calc
        _ = ∑ i : Fin d, (u (Fin.snoc x 1 + unit (Fin.castSucc i)) +
            u (Fin.snoc x 1 - unit (Fin.castSucc i))) := by
          apply Finset.sum_congr rfl
          intro i _
          congr 2
        _ = nbrSum v x := hplus_sum
    have hlast : Fin.natAdd d (0 : Fin 1) = Fin.last d := by rfl
    rw [hplus_sum', hlast]
    simp only [nbrSum]
  rw [lap, lap, hsum, hadd, hminus]
  dsimp [u, v] at *
  rw [hprev x]
  ring

theorem odo_dimred_step
    (d M t : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ M) (x : Site d) (hx : inSimplex d M x)
    (hprev : ∀ i : ℕ, 1 ≤ i → i ≤ d → ∀ z : Site i,
        odoUnif (i + 1) (2 * M) (t - 1) (Fin.snoc z 1) =
          odoUnif i (2 * M) (t - 1) z)
    (hweak : weak_facet_step (d + 1) M (t - 1) ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ d → weak_facet_step i M (t - 1))
    (hfacet : strong_facet_step (d + 1) M (t - 1) ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ d → strong_facet_step i M (t - 1))
    (htopple : ∀ i : ℕ, 1 ≤ i → i ≤ d + 1 →
      (toppleTime i (M - 1) ≤ ((t - 2 : ℕ) : ℕ∞) →
        simplexMax i M (fun w => odoUnif i (2 * M) t w
          - odoUnif i (2 * M) (t - 2) w) ≤ 1))
    (hconsist : ∀ (j : ℕ), 1 ≤ j → j ≤ M → ((t - 1 : ℕ) : ℕ∞) ≤ toppleTime (d + 1) j →
        ∀ z : Site (d + 1), inSimplex (d + 1) M z →
          (∀ i : Fin (d + 1), (M : ℤ) - (j : ℤ) < z i) →
          odoUnif (d + 1) (2 * M) (t - 1) z =
            odoUnif (d + 1) (2 * j) (t - 1) (fun i => z i - ((M : ℤ) - (j : ℤ))))
    (hcritical : ∀ (z : Site d), inSimplex d M z →
      (∀ k : Fin d, 1 < z k) →
      odoUnif (d + 1) (2 * M) (t - 1) (Fin.snoc z 1) =
        odoUnif (d + 1) (2 * M) (t - 1)
          (Fin.snoc z 1 + unit (Fin.last d)) + 1 →
      (∀ i : ℕ, 1 ≤ i → i ≤ d → ∀ w : Site i,
          odoUnif (i + 1) (2 * M) (t - 1) (Fin.snoc w 1) =
            odoUnif i (2 * M) (t - 1) w) →
      (weak_facet_step (d + 1) M (t - 1) ∧
        ∀ i : ℕ, 1 ≤ i → i ≤ d → weak_facet_step i M (t - 1)) →
      (strong_facet_step (d + 1) M (t - 1) ∧
        ∀ i : ℕ, 1 ≤ i → i ≤ d → strong_facet_step i M (t - 1)) →
      (∀ i : ℕ, 1 ≤ i → i ≤ d + 1 →
        (toppleTime i (M - 1) ≤ ((t - 2 : ℕ) : ℕ∞) →
          simplexMax i M (fun w => odoUnif i (2 * M) t w
            - odoUnif i (2 * M) (t - 2) w) ≤ 1)) →
      (∀ (j : ℕ), 1 ≤ j → j ≤ M → ((t - 1 : ℕ) : ℕ∞) ≤ toppleTime (d + 1) j →
        ∀ z : Site (d + 1), inSimplex (d + 1) M z →
          (∀ i : Fin (d + 1), (M : ℤ) - (j : ℤ) < z i) →
          odoUnif (d + 1) (2 * M) (t - 1) z =
            odoUnif (d + 1) (2 * j) (t - 1) (fun i => z i - ((M : ℤ) - (j : ℤ)))) →
      odoUnif (d + 1) (2 * M) t (Fin.snoc z 1) =
        odoUnif d (2 * M) t z) :
    odoUnif (d + 1) (2 * M) t (Fin.snoc x 1) = odoUnif d (2 * M) t x := by
  cases t with
  | zero => simp [odoUnif, odo]
  | succ q =>
    simp only [Nat.succ_sub_one] at hprev hweak hfacet hcritical
    have hprev_x := hprev d (by omega) (by omega) x
    have hcube_x := inSimplex_inCube d M x hx
    have hcube_X : inCube (d + 1) (2 * M) (Fin.snoc x 1) := by
      exact inSimplex_inCube (d + 1) M (Fin.snoc x 1)
        (inSimplex_snoc_one_local x hx (by omega))
    have hstep_full := odo_succ_eq (d + 1) (2 * M)
      (fun _ => 2 * ((d + 1 : ℕ) : ℤ)) q (Fin.snoc x 1) hcube_X
    have hstep_lower := odo_succ_eq d (2 * M)
      (fun _ => 2 * (d : ℤ)) q x hcube_x
    change odoUnif (d + 1) (2 * M) (q + 1) (Fin.snoc x 1) =
      odoUnif d (2 * M) (q + 1) x
    change odo (d + 1) (2 * M) (fun _ => 2 * ((d + 1 : ℕ) : ℤ))
        (q + 1) (Fin.snoc x 1) =
      odo d (2 * M) (fun _ => 2 * (d : ℤ)) (q + 1) x
    rw [hstep_full, hstep_lower]
    change odoUnif (d + 1) (2 * M) q (Fin.snoc x 1) +
        (if 2 * ((d + 1 : ℕ) : ℤ) ≤
          sandp (d + 1) (2 * M) (fun _ => 2 * ((d + 1 : ℕ) : ℤ)) q
            (Fin.snoc x 1) then 1 else 0) =
      odoUnif d (2 * M) q x +
        (if 2 * (d : ℤ) ≤ sandp d (2 * M) (fun _ => 2 * (d : ℤ)) q x
          then 1 else 0)
    have haxis := odo_axis_refl (d + 1) M (by omega)
      (2 * ((d + 1 : ℕ) : ℤ)) (by omega) (by omega) q
      (Fin.snoc x 1) (Fin.last d) (by simp [Fin.snoc])
    have haxis' : odoUnif (d + 1) (2 * M) q
        (Fin.snoc x 1 + unit (Fin.last d)) ≤
        odoUnif (d + 1) (2 * M) q (Fin.snoc x 1) := by
      simpa [odoUnif] using haxis
    have hX := inSimplex_snoc_one_local x hx (by omega)
    have hfacet_full := hfacet.1 (Fin.snoc x 1) (Fin.last d) hX
      (by simp [Fin.snoc])
    have hdiff : odoUnif (d + 1) (2 * M) q (Fin.snoc x 1) -
        odoUnif (d + 1) (2 * M) q
          (Fin.snoc x 1 + unit (Fin.last d)) ≤ 1 := hfacet_full
    have hnonneg : 0 ≤ odoUnif (d + 1) (2 * M) q (Fin.snoc x 1) -
        odoUnif (d + 1) (2 * M) q (Fin.snoc x 1 + unit (Fin.last d)) := by
      linarith [haxis']
    rcases eq_or_lt_of_le hdiff with hgap1 | hgap0
    · have hgap' : odoUnif (d + 1) (2 * M) q
          (Fin.snoc x 1 + unit (Fin.last d)) + 1 =
          odoUnif (d + 1) (2 * M) q (Fin.snoc x 1) := by linarith
      by_cases hinterior : ∀ k : Fin d, 1 < x k
      · have hcrit := hcritical x hx hinterior hgap'.symm hprev hweak hfacet htopple hconsist
        simpa [odoUnif, odo, hcube_X, hcube_x, sandp] using hcrit
      · simp only [not_forall] at hinterior
        obtain ⟨k, _hk⟩ := hinterior
        have hxk : x k = 1 := by
          have h := (hx.1 k).1
          omega
        have hX := inSimplex_snoc_one_local x hx (by omega)
        have hswap := odo_swap_add (d + 1) M
          (2 * ((d + 1 : ℕ) : ℤ)) q (Fin.snoc x 1) (Fin.castSucc k)
          (Fin.last d) (Fin.castSucc_ne_last k) (by simp [Fin.snoc, hxk])
        have hswap' : odoUnif (d + 1) (2 * M) q
            (Fin.snoc x 1 + unit (Fin.castSucc k)) =
            odoUnif (d + 1) (2 * M) q
              (Fin.snoc x 1 + unit (Fin.last d)) := by
          simpa [odoUnif] using hswap
        have heq_full : odoUnif (d + 1) (2 * M) q
            (Fin.snoc x 1) = odoUnif (d + 1) (2 * M) q
              (Fin.snoc x 1 + unit (Fin.castSucc k)) + 1 := by
          calc
            odoUnif (d + 1) (2 * M) q (Fin.snoc x 1) =
                odoUnif (d + 1) (2 * M) q
                  (Fin.snoc x 1 + unit (Fin.last d)) + 1 := hgap'.symm
            _ = odoUnif (d + 1) (2 * M) q
                  (Fin.snoc x 1 + unit (Fin.castSucc k)) + 1 := by rw [hswap']
        have hprev_step := hprev d (by omega) (by omega) (x + unit k)
        have hsnoc_step : Fin.snoc (x + unit k) 1 =
            Fin.snoc x 1 + unit (Fin.castSucc k) := fin_snoc_add_unit x 1 k
        rw [hsnoc_step] at hprev_step
        have hgap_lower : odoUnif d (2 * M) q x =
            odoUnif d (2 * M) q (x + unit k) + 1 := by
          rw [← hprev_x, ← hprev_step]
          exact heq_full
        have hweak_lower := hweak.2 d (by omega) (by omega)
        have hstay_lower := hweak_lower x k hx hxk hgap_lower
        have hweak_full := hweak.1
        have hstay_full := hweak_full (Fin.snoc x 1) (Fin.last d) hX
          (by simp [Fin.snoc]) hgap'.symm
        have hboundary := hstay_full.trans (hprev_x.trans hstay_lower.symm)
        simpa [odoUnif, odo, hcube_X, hcube_x, sandp] using hboundary
    · have hzero : odoUnif (d + 1) (2 * M) q
          (Fin.snoc x 1 + unit (Fin.last d)) =
          odoUnif (d + 1) (2 * M) q (Fin.snoc x 1) := by linarith
      have hlap := lap_snoc_eq_of_reduction x
        (fun z => hprev d (by omega) (by omega) z) hzero
      have hfull : (2 * ((d + 1 : ℕ) : ℤ) ≤
          sandp (d + 1) (2 * M) (fun _ => 2 * ((d + 1 : ℕ) : ℤ)) q
            (Fin.snoc x 1)) ↔
          0 ≤ lap (odoUnif (d + 1) (2 * M) q) (Fin.snoc x 1) := by
        change (2 * ((d + 1 : ℕ) : ℤ) ≤
          2 * ((d + 1 : ℕ) : ℤ) +
            lap (odoUnif (d + 1) (2 * M) q) (Fin.snoc x 1)) ↔ _
        constructor <;> intro h <;> linarith
      have hlower : (2 * (d : ℤ) ≤
          sandp d (2 * M) (fun _ => 2 * (d : ℤ)) q x) ↔
          0 ≤ lap (odoUnif d (2 * M) q) x := by
        change (2 * (d : ℤ) ≤ 2 * (d : ℤ) +
            lap (odoUnif d (2 * M) q) x) ↔ _
        constructor <;> intro h <;> linarith
      simp only [hfull, hlower]
      rw [hlap, hprev_x]

end DimRed
