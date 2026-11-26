import HalfWords.Distance
import HalfWords.ActualSurgery

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords
variable {V W : Type*}

/-- Numeric change in component count, recorded with its graph and charge
witnesses. A join can have either charge cost. -/
inductive SurgeryCount (connected : Prop) (charge : ℕ) (before after : ℕ) : Prop where
  | cut : connected → charge=0 → after=before+1 → SurgeryCount connected charge before after
  | flip : connected → charge=1 → after=before → SurgeryCount connected charge before after
  | join : ¬connected → after+1=before → SurgeryCount connected charge before after

theorem coordinate_step [Fintype V] [DecidableEq V] (r : Perm V) (a b : V)
    (col : Bool) (ne : (a,false) ≠ (b,col)) :
    SurgeryCount (r.SameCycle a b) (if col then 1 else 0)
      (orbitCount r) (componentCount (oriented 1) (rewire (oriented r) ((a,false),(b,col)))) := by
  cases col
  · rw [rewire_same_color,oriented_count]
    by_cases con : r.SameCycle a b
    · exact .cut con rfl (orbitCount_cut _ (fun (e : a=b) => ne (congrArg (fun v => (v,false)) e)) con).symm
    · exact .join con (orbitCount_join _ con)
  · by_cases con : r.SameCycle a b
    · have st : Relation.EqvGen.setoid (Charge.Edge (oriented 1) (rewire (oriented r) ((a,false),(b,true)))) =
          Relation.EqvGen.setoid (Charge.Edge (oriented 1) (oriented r)) := by
        ext x y
        exact component_iff_after_flip con x y
      exact .flip con rfl ((congrArg (fun S => Nat.card (Quotient S)) st).trans (oriented_count r))
    · exact .join con ((opposite_join_count r con).trans (oriented_count r))

theorem count_map (e : V ≃ W) (s M : Perm V) :
    componentCount (e.permCongrHom s) (e.permCongrHom M) = componentCount s M :=
  (Nat.card_congr (Quotient.congr e (fun x y => (reach_map_iff e s M x y).symm))).symm

/-- The trichotomy for Definition 4.1 on an arbitrary ordered finite set of
actual labels and arbitrary perfect matchings, including loops of size one. -/
theorem actual_step [Fintype V] [LinearOrder V] (s M : Perm V)
    (hs : s⁻¹=s) (hm : M⁻¹=M) (ns : ∀x, s x ≠ x) (nm : ∀x, M x ≠ x)
    (a b : V) (ne : a ≠ b) :
    SurgeryCount (Charge.Reach s M a b) (Charge.flip s M a b)
      (componentCount s M) (componentCount s (rewire M (a,b))) := by
  classical
  let c := Charge.canonical s M
  let col (v : V) := Bool.xor (c v) (c a)
  have valid := Charge.canonical_valid s M hs hm ns nm
  have fs (v : V) : col (s v) = !col v := by
    change Bool.xor (Charge.canonical s M (s v)) _ = _
    rw [valid.first]
    cases hv : c v <;> cases ha : c a <;> simp_all [col,c]
  have fm (v : V) : col (M v) = !col v := by
    change Bool.xor (Charge.canonical s M (M v)) _ = _
    rw [valid.second]
    cases hv : c v <;> cases ha : c a <;> simp_all [col,c]
  have ss (v : V) : s (s v) = v :=
    (congrArg (fun q : Perm V => q (s v)) hs.symm).trans (s.symm_apply_apply v)
  have mm (v : V) : M (M v) = v :=
    (congrArg (fun q : Perm V => q (M v)) hm.symm).trans (M.symm_apply_apply v)
  let e := chargedCoordinates s col fs ss
  let r := successor s M col fs fm ss mm
  have mEq : e.permCongrHom (oriented r)=M := matching_coordinates ..
  have sEq : e.permCongrHom (oriented (1:Perm {v // col v=false}))=s := by
    apply Equiv.ext
    intro v
    obtain ⟨⟨i,d⟩,rfl⟩ := e.surjective v
    change e (oriented 1 (e.symm (e (i,d))))=s (e (i,d))
    rw [symm_apply_apply]
    cases d
    · rfl
    · exact (ss i).symm
  let i : {v // col v=false} := ⟨a,by simp [col]⟩
  have ia : e (i,false)=a := rfl
  obtain ⟨⟨j,d⟩,jb⟩ := e.surjective b
  have flipEq : Charge.flip s M a b = (if d then 1 else 0) := by
    have dj : col b=d := by
      rw [← jb]
      cases d
      · exact j.property
      · change col (s j)=true; rw [fs,j.property]; rfl
    change (if c a=c b then 0 else 1) = _
    change Bool.xor (c b) (c a)=d at dj
    cases x : c a <;> cases y : c b <;> simp_all
  have nc : (i,false) ≠ (j,d) := fun E => ne (ia.symm.trans ((congrArg e E).trans jb))
  have con := reach_map_iff e (oriented 1) (oriented r) (i,false) (j,d)
  rw [sEq,mEq,ia,jb,oriented_reach_iff] at con
  have before := count_map e (oriented 1) (oriented r)
  rw [sEq,mEq,oriented_count] at before
  have after := count_map e (oriented 1) (rewire (oriented r) ((i,false),(j,d)))
  rw [rewire_map,sEq,mEq,ia,jb] at after
  rw [propext con,flipEq,before,after]
  exact coordinate_step r i j d nc

#print axioms actual_step
end HalfWords
