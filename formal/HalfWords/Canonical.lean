import HalfWords.Source

namespace HalfWords

open Equiv Hurwitz

abbrev PairVertex (m : ℕ) := Fin (m+1) × Bool

def standard (m : ℕ) : Perm (PairVertex m) where
  toFun v := (v.1,!v.2)
  invFun v := (v.1,!v.2)
  left_inv := by rintro ⟨i,b⟩; cases b <;> rfl
  right_inv := by rintro ⟨i,b⟩; cases b <;> rfl

/-- On each block, the right label is matched to the left label of the next
block cyclically, exactly the canonical coset type (m+1). -/
def cyclic (m : ℕ) : Perm (PairVertex m) :=
  let f : PairVertex m → PairVertex m := fun (i,b) =>
    if b then (finRotate (m+1) i,false) else ((finRotate (m+1)).symm i,true)
  have h : Function.Involutive f := by
    rintro ⟨i,b⟩
    cases b <;> simp [f]
  h.toPerm f

theorem cyclic_onePart (m : ℕ) : OnePart (standard m) (cyclic m) := by
  let reach := Charge.Reach (standard m) (cyclic m)
  have move_std (i : Fin (m+1)) : reach (i,false) (i,true) :=
    Relation.EqvGen.rel _ _ (Or.inl rfl)
  have move_cyc (i : Fin (m+1)) : reach (i,true) (finRotate (m+1) i,false) :=
    Relation.EqvGen.rel _ _ (Or.inr rfl)
  have to_left (i : Fin (m+1)) : reach (0,false) (i,false) := by
    induction i using Fin.induction with
    | zero => exact Relation.EqvGen.refl ..
    | succ i ih =>
      have step := (move_cyc i.castSucc)
      have f : finRotate (m+1) i.castSucc = i.succ := by
        exact finRotate_of_lt i.isLt
      rw [f] at step
      exact Relation.EqvGen.trans _ _ _ ih
        (Relation.EqvGen.trans _ _ _ (move_std i.castSucc) step)
  have all (v : PairVertex m) : reach (0,false) v := by
    rcases v with ⟨i,b⟩
    cases b
    · exact to_left i
    · exact Relation.EqvGen.trans _ _ _ (to_left i) (move_std i)
  intro x y
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (all x)) (all y)

theorem onePart_map {V W : Type*} (e : V ≃ W) {s m : Perm V} (h : OnePart s m) :
    OnePart (e.permCongrHom s) (e.permCongrHom m) := by
  have go {x y : V} (hxy : Charge.Reach s m x y) :
      Charge.Reach (e.permCongrHom s) (e.permCongrHom m) (e x) (e y) := by
    induction hxy with
    | rel a b he =>
      apply Relation.EqvGen.rel
      cases he with
      | inl hs => exact Or.inl (by subst b; simp)
      | inr hm => exact Or.inr (by subst b; simp)
    | refl => exact Relation.EqvGen.refl ..
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih ik => exact Relation.EqvGen.trans _ _ _ ih ik
  intro x y
  simpa using go (h (e.symm x) (e.symm y))

/-- In zero-based coordinates the labels in a block occur consecutively. -/
def index (m : ℕ) : PairVertex m ≃ Fin ((m+1)*2) :=
  ((Equiv.refl _).prodCongr finTwoEquiv.symm).trans finProdFinEquiv

theorem raw_cyclic_eq_dp {R : Type*} [CommSemiring R] (b t : R) (m r : ℕ) :
    let e := index m
    let s := e.permCongrHom (standard m)
    let a := e.permCongrHom (cyclic m)
    WordWeights.paperSum b t ((m+1)*2) s a r = Paths.dp b t s 0 r a none true :=
  onePart_raw_eq_dp b t (onePart_map (index m) (cyclic_onePart m)) r

#print axioms cyclic_onePart
#print axioms raw_cyclic_eq_dp
end HalfWords
