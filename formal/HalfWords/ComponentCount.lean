import Mathlib

namespace HalfWords
variable {V : Type*}

def merged (s : Setoid V) (a b : V) : Setoid V :=
  Relation.EqvGen.setoid (fun i j => s.r i j ∨ i=a ∧ j=b)

/-- Adding a single identification to an equivalence relation discards exactly
the second class when the two original classes are distinct. -/
noncomputable def mergedEquiv (s : Setoid V) (a b : V) (apart : ¬s.r a b) :
    Quotient (merged s a b) ≃ {q : Quotient s // q ≠ Quotient.mk s b} := by
  classical
  let π := Quotient.mk s
  have ab : π a ≠ π b := fun eq => apart (Quotient.exact eq)
  let f (x : V) : {q : Quotient s // q ≠ π b} :=
    if e : π x=π b then ⟨π a,ab⟩ else ⟨π x,e⟩
  have compatible : ∀ {x y}, (merged s a b).r x y → f x=f y := by
    intro x y h
    induction h with
    | rel x y e =>
      rcases e with e|⟨rfl,rfl⟩
      · have he : π x=π y := Quotient.sound e
        apply Subtype.ext
        by_cases h : π x=π b
        · simp [f,h,he.symm.trans h]
        · have hy : π y ≠ π b := fun e => h (he.trans e)
          simp [f,hy,he]
      · simp [f,ab]
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ l r => exact l.trans r
  let rep (x : V) := if π x=π b then a else x
  have relate (x : V) : (merged s a b).r x (rep x) := by
    by_cases hx : π x=π b
    · rw [show rep x=a from if_pos hx]
      exact .trans _ _ _ (.rel _ _ (Or.inl (Quotient.exact hx))) (.symm _ _ (.rel _ _ (Or.inr ⟨rfl,rfl⟩)))
    · rw [show rep x=x from if_neg hx]
  have choose (x : V) : (f x).val=π (rep x) := by
    by_cases hx : π x=π b <;> simp [f,rep,hx]
  have ker : merged s a b = Setoid.ker f := by
    ext x y
    refine ⟨compatible,fun e => ?_⟩
    have old : s.r (rep x) (rep y) := Quotient.exact
      ((choose x).symm.trans ((congrArg Subtype.val e).trans (choose y)))
    exact .trans _ _ _ (relate x) (.trans _ _ _ (.rel _ _ (Or.inl old)) (.symm _ _ (relate y)))
  have onto : Function.Surjective f := by
    rintro ⟨q,hq⟩
    obtain ⟨v,hv⟩ := Quotient.exists_rep q
    change π v=q at hv
    exact ⟨v,Subtype.ext (by simp [f,hv,hq])⟩
  rw [ker]
  exact Setoid.quotientKerEquivOfSurjective f onto

theorem merged_card [Finite V] (s : Setoid V) (a b : V) (apart : ¬s.r a b) :
    Nat.card (Quotient (merged s a b))+1=Nat.card (Quotient s) := by
  classical
  let _ := Fintype.ofFinite (Quotient s)
  have pos : 0<Fintype.card (Quotient s) := Fintype.card_pos_iff.mpr ⟨Quotient.mk s a⟩
  rw [Nat.card_congr (mergedEquiv s a b apart), Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun q => q = Quotient.mk s b)]
  simp
  omega

#print axioms merged_card
end HalfWords
