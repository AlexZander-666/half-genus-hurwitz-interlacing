import HalfWords.Coordinates

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords
variable {V : Type*} [DecidableEq V]

private def after (r : Perm V) (a b : V) := rewire (oriented r) ((a,false),(b,true))
private abbrev linked (r : Perm V) (a b : V) (x y : V) :=
  Charge.Reach (oriented 1) (after r a b) (x,false) (y,false)

omit [DecidableEq V] in
private theorem vertical (M : Perm (V × Bool)) (x : V × Bool) :
    Charge.Reach (oriented 1) M (x.1,false) x := by
  rcases x with ⟨i,w⟩
  cases w
  · exact .refl _
  · exact .rel _ _ (Or.inl rfl)

private theorem edge_after (r : Perm V) (a b v : V) :
    linked r a b (if v=b then a else v) (if r v=a then b else r v) := by
  let σ := swap (a,false) (b,true)
  have hh : Charge.Reach (oriented 1) (after r a b) (σ (v,true)) (σ (r v,false)) := by
    apply Relation.EqvGen.rel
    right
    simp [after,rewire_apply,σ]
  have h := Relation.EqvGen.trans _ _ _ (vertical (after r a b) (σ (v,true)))
    (Relation.EqvGen.trans _ _ _ hh (Relation.EqvGen.symm _ _ (vertical _ (σ (r v,false)))))
  by_cases hv : v=b
  · subst v
    by_cases hw : r b=a <;> simpa [σ,swap_apply_def,hw] using h
  · by_cases hw : r v=a <;> simpa [σ,swap_apply_def,hv,hw] using h

private theorem anchor_after [Finite V] {r : Perm V} {a b : V} (h : r.SameCycle a b) :
    linked r a b a b := by
  by_contra no
  have close (v : V) (hv : linked r a b a v) : linked r a b a (r v) := by
    by_cases back : r v = a
    · rw [back]; exact .refl _
    have away : v ≠ b := fun e => no (e ▸ hv)
    exact .trans _ _ _ hv (by simpa [away,back] using edge_after r a b v)
  obtain ⟨i,hi⟩ := h.exists_nat_pow_eq
  have all (j : ℕ) : linked r a b a ((r^j) a) := by
    induction j with
    | zero => exact .refl _
    | succ j ih => simpa only [pow_succ',Perm.mul_apply] using close _ ih
  exact no (hi ▸ all i)

private theorem anchor_any [Finite V] (r : Perm V) (a b : V) : linked r a b a b := by
  by_cases same : r.SameCycle a b
  · exact anchor_after same
  have walk (i : ℕ) : linked r a b a ((r^i) a) := by
    induction i with
    | zero => exact .refl _
    | succ i ih =>
      rw [pow_succ',Perm.mul_apply]
      by_cases back : r ((r^i) a)=a
      · rw [back]; exact .refl _
      have away : (r^i) a ≠ b := fun e => same ⟨(i:ℤ),by simpa using e⟩
      exact .trans _ _ _ ih (by simpa [away,back] using edge_after r a b ((r^i) a))
  have prev : r.SameCycle a (r.symm a) := by simpa using (Perm.SameCycle.rfl (f:=r) (x:=a))
  obtain ⟨i,hi⟩ := prev.exists_nat_pow_eq
  have ne : r.symm a ≠ b := fun e => same (e ▸ prev)
  exact .trans _ _ _ (hi ▸ walk i) (by simpa [ne] using edge_after r a b (r.symm a))

private theorem old_step [Finite V] (r : Perm V) (a b v : V) :
    linked r a b v (r v) := by
  have ab := anchor_any r a b
  have e := edge_after r a b v
  by_cases hv : v=b
  · subst v
    by_cases hw : r b=a
    · rw [hw]; exact .symm _ _ ab
    · exact .trans _ _ _ (.symm _ _ ab) (by simpa [hw] using e)
  · by_cases hw : r v=a
    · rw [hw]; exact .trans _ _ _ (by simpa [hv,hw] using e) (.symm _ _ ab)
    · simpa [hv,hw] using e

/-- An opposite-color transposition cannot split an existing overlay component. The proof tracks the reachable set in the actual rewired matching. -/
theorem sameCycle_reach_after_flip [Finite V] {r : Perm V} {a b : V}
    {x y : V × Bool} (conn : r.SameCycle x.1 y.1) :
    Charge.Reach (oriented 1) (rewire (oriented r) ((a,false),(b,true))) x y := by
  obtain ⟨j,hj⟩ := conn.exists_nat_pow_eq
  have path (i : ℕ) : linked r a b x.1 ((r^i) x.1) := by
    induction i with
    | zero => exact .refl _
    | succ i ih =>
      rw [pow_succ', Perm.mul_apply]
      exact .trans _ _ _ ih (old_step r a b _)
  exact .trans _ _ _ (.symm _ _ (vertical _ x)) (.trans _ _ _ (hj ▸ path j) (vertical _ y))

private theorem projected_swap {r : Perm V} {a b : V} (h : r.SameCycle a b) (v : V × Bool) :
    r.SameCycle v.1 (swap (a,false) (b,true) v).1 := by
  by_cases ea : v = (a,false)
  · subst v; simpa using h
  by_cases eb : v = (b,true)
  · subst v; simpa using h.symm
  rw [swap_apply_of_ne_of_ne ea eb]

/-- Exactly the same alternating components survive the flip, including their
complete labeled supports. This covers the transposition of matched labels. -/
theorem component_iff_after_flip [Finite V] {r : Perm V} {a b : V}
    (h : r.SameCycle a b) (x y : V × Bool) :
    Charge.Reach (oriented 1) (rewire (oriented r) ((a,false),(b,true))) x y ↔
      Charge.Reach (oriented 1) (oriented r) x y := by
  rw [oriented_reach_iff]
  refine ⟨?_,sameCycle_reach_after_flip⟩
  intro conn
  induction conn with
  | rel x y he =>
    rcases he with he|he <;> subst y
    · rcases x with ⟨v,w⟩
      cases w <;> exact Perm.SameCycle.rfl
    · rw [rewire_apply]
      let u := swap (a,false) (b,true) x
      have hop : r.SameCycle u.1 (oriented r u).1 :=
        (oriented_reach_iff r u _).mp (.rel _ _ (Or.inr rfl))
      exact (projected_swap h x).trans (hop.trans (projected_swap h _))
  | refl => exact .rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ik => exact ih.trans ik

/-- The exact component partition after a cross-color swap is the equivalence
closure of the old cycles together with the identification of the two anchors.
It merges precisely the two old components when these were distinct. -/
theorem opposite_surgery [Finite V] (r : Perm V) (a b : V) (x y : V × Bool) :
    Charge.Reach (oriented 1) (rewire (oriented r) ((a,false),(b,true))) x y ↔
      Relation.EqvGen (fun i j => r.SameCycle i j ∨ i=a ∧ j=b) x.1 y.1 := by
  let R := Relation.EqvGen (fun i j => r.SameCycle i j ∨ i=a ∧ j=b)
  have swapRel (v : V × Bool) : R v.1 (swap (a,false) (b,true) v).1 := by
    have ab : R a b := .rel _ _ (Or.inr ⟨rfl,rfl⟩)
    by_cases ea : v=(a,false)
    · subst v; simpa using ab
    by_cases eb : v=(b,true)
    · subst v; simpa using (Relation.EqvGen.symm _ _ ab)
    rw [swap_apply_of_ne_of_ne ea eb]
    exact .refl _
  constructor
  · intro con
    induction con with
    | rel v w edge =>
      rcases edge with edge|edge <;> subst w
      · rcases v with ⟨i,c⟩; cases c <;> exact .refl _
      · rw [rewire_apply]
        let u := swap (a,false) (b,true) v
        have mid : R u.1 (oriented r u).1 := .rel _ _ (Or.inl
          ((oriented_reach_iff r _ _).mp (.rel _ _ (Or.inr rfl))))
        exact .trans _ _ _ (swapRel v) (.trans _ _ _ mid (swapRel _))
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih ij => exact .trans _ _ _ ih ij
  · intro con
    have lifts (i j : V) (conn : R i j) : linked r a b i j := by
      induction conn with
      | rel i j e =>
        rcases e with e|⟨rfl,rfl⟩
        · exact sameCycle_reach_after_flip (x:=(i,false)) (y:=(j,false)) e
        · exact anchor_any r _ _
      | refl => exact .refl _
      | symm _ _ _ ih => exact .symm _ _ ih
      | trans _ _ _ _ _ ih ij => exact .trans _ _ _ ih ij
    exact .trans _ _ _ (.symm _ _ (vertical _ x)) (.trans _ _ _ (lifts _ _ con) (vertical _ y))

#print axioms opposite_surgery
#print axioms component_iff_after_flip
#print axioms sameCycle_reach_after_flip
end HalfWords
