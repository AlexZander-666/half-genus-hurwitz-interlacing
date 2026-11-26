import HalfWords.ActualSurgery
import HalfWords.Distance

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords
variable {V W : Type*}

/-- Size multiset of all equivalence classes, including singletons. -/
noncomputable def sizes [Fintype V] (S : Setoid V) : Multiset ℕ := by
  classical
  let _ := Fintype.ofFinite (Quotient S)
  exact Finset.univ.val.map fun q : Quotient S => Nat.card {x : V // Quotient.mk S x=q}

theorem sizes_congr [Fintype V] [Fintype W] (S : Setoid V) (T : Setoid W) (e : V ≃ W)
    (H : ∀ x y, S.r x y ↔ T.r (e x) (e y)) : sizes S = sizes T := by
  classical
  let f := Quotient.congr e H
  have binder (q : Quotient S) : {x // Quotient.mk S x=q} ≃ {y // Quotient.mk T y=f q} :=
    e.subtypeEquiv fun x => by
      change (Quotient.mk S x=q) ↔ Quotient.mk T (e x)=f q
      exact f.injective.eq_iff.symm
  let _ := Fintype.ofFinite (Quotient S)
  let _ := Fintype.ofFinite (Quotient T)
  dsimp only [sizes]
  rw [← Finset.map_univ_equiv f,Finset.map_val,Multiset.map_map]
  apply Multiset.map_congr rfl
  intro q _
  exact Nat.card_congr (binder q)

/-- The original partition recorded in numbers of standard pairs. -/
noncomputable def profile [Fintype V] (s M : Perm V) :=
  (sizes (Relation.EqvGen.setoid (Charge.Edge s M))).map (·/2)

theorem profile_congr [Fintype V] [Fintype W] (s M : Perm V) (S N : Perm W) (e : V ≃ W)
    (H : ∀ x y, Charge.Reach s M x y ↔ Charge.Reach S N (e x) (e y)) :
    profile s M=profile S N := by
  exact congrArg _ (sizes_congr _ _ e H)

theorem same_profile_after_flip [Fintype V] [DecidableEq V] (r : Perm V) {a b : V}
    (h : r.SameCycle a b) :
    profile (oriented 1) (rewire (oriented r) ((a,false),(b,true))) =
      profile (oriented 1) (oriented r) := by
  exact profile_congr _ _ _ _ (Equiv.refl _) (component_iff_after_flip h)

theorem oriented_profile [Fintype V] (r : Perm V) :
    profile (oriented 1) (oriented r)=sizes (Perm.SameCycle.setoid r) := by
  classical
  let S := Relation.EqvGen.setoid (Charge.Edge (oriented 1) (oriented r))
  let T := Perm.SameCycle.setoid r
  let e : Quotient S ≃ Quotient T := {
    toFun := Quotient.lift (fun p => Quotient.mk T p.1)
      (fun i j h => Quotient.sound ((oriented_reach_iff r i j).mp h))
    invFun := Quotient.lift (fun x => Quotient.mk S (x,false))
      (fun i j h => Quotient.sound ((oriented_reach_iff r _ _).mpr h))
    left_inv := fun q => Quotient.inductionOn q (fun p => Quotient.sound
      ((oriented_reach_iff r _ _).mpr Perm.SameCycle.rfl))
    right_inv := fun q => Quotient.inductionOn q (fun _ => rfl) }
  have bind (q : Quotient S) :
      {v // Quotient.mk S v=q} ≃ {w // Quotient.mk T w=e q} × Bool := {
    toFun := fun v => (⟨v.val.1,by
      change e (Quotient.mk S v.val)=e q
      rw [v.property]⟩,v.val.2)
    invFun := fun w => ⟨(w.1.val,w.2),e.injective w.1.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  change (sizes S).map (·/2) = sizes T
  let _ := Fintype.ofFinite (Quotient S)
  let _ := Fintype.ofFinite (Quotient T)
  dsimp only [sizes]
  rw [Multiset.map_map,← Finset.map_univ_equiv e,Finset.map_val,Multiset.map_map]
  apply Multiset.map_congr rfl
  intro q _
  change Nat.card {x // Quotient.mk S x=q}/2 = Nat.card {v // Quotient.mk T v=e q}
  rw [Nat.card_congr (bind q),Nat.card_prod]
  simp

#print axioms oriented_profile
end HalfWords
