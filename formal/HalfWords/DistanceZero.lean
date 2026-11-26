import HalfWords.PivotCoordinates

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords Hurwitz.WordWeights Hurwitz.Paths

private theorem ident_count {V : Type*} [Finite V] :
    orbitCount (1 : Perm V)=Nat.card V := by
  have id : Perm.SameCycle.setoid (1:Perm V)=Setoid.ker (@id V) := by
    ext x y
    change (1: Perm V).SameCycle x y ↔ x=y
    simp [Perm.SameCycle]
  unfold orbitCount
  rw [id]
  exact Nat.card_congr (Setoid.quotientKerEquivOfSurjective _ Function.surjective_id)

theorem distance_zero_iff {V : Type*} [Fintype V] [LinearOrder V] (s M : Perm V)
    (hs : s⁻¹=s) (hm : M⁻¹=M) (ns : ∀v,s v≠v) (nm : ∀v,M v≠v) :
    componentCount s M≤componentCount s s ∧
    (componentCount s M=componentCount s s ↔ M=s) := by
  classical
  obtain ⟨e,r,mEq,pair⟩ := canonical_matching_coordinates s M hs hm ns nm
  let V' := {v // Charge.canonical s M v=false}
  have sEq : e.permCongrHom (oriented (1:Perm V'))=s := by
    apply Equiv.ext
    intro v
    obtain ⟨⟨i,d⟩,rfl⟩ := e.surjective v
    change e (oriented 1 (e.symm (e (i,d))))=_
    rw [Equiv.symm_apply_apply]
    cases d
    · exact pair i false
    · exact pair i true
  have eqn : componentCount s M=orbitCount r := by
    have h := (count_map e (oriented 1) (oriented r)).trans (oriented_count r)
    rwa [sEq,mEq] at h
  have eqs : componentCount s s=Nat.card V' := by rw [←sEq,count_map,oriented_count,ident_count]
  rw [eqn,eqs]
  let S := Perm.SameCycle.setoid r
  let f : V' → Quotient S := Quotient.mk _
  have sur : Function.Surjective f := Quotient.exists_rep
  refine ⟨Nat.card_le_card_of_surjective f sur,⟨fun eq => ?_,?_⟩⟩
  · have inj := ((Nat.bijective_iff_surjective_and_card f).mpr ⟨sur,eq.symm⟩).1
    have id : r=1 := Equiv.ext (fun i => inj (Quotient.sound
      (show r.SameCycle (r i) i from (r.sameCycle_apply_right.mpr Perm.SameCycle.rfl).symm)))
    exact mEq.symm.trans ((congrArg (fun z => e.permCongrHom (oriented z)) id).trans sEq)
  · intro h
    rw [←eqn,←eqs,h]

theorem standard_core {V : Type*} [Fintype V] [LinearOrder V] (s : Perm V)
    (hs : s⁻¹=s) (ns : ∀v,s v≠v) : core s s=0 := by
  obtain ⟨e,_,_,pair⟩ := canonical_matching_coordinates s s hs hs ns ns
  let V' := {v // Charge.canonical s s v=false}
  have sEq : e.permCongrHom (oriented (1:Perm V'))=s := by
    apply Equiv.ext
    intro v
    obtain ⟨⟨i,d⟩,rfl⟩ := e.surjective v
    change e (oriented 1 (e.symm (e (i,d))))=_
    rw [Equiv.symm_apply_apply]
    cases d
    · exact pair i false
    · exact pair i true
  rw [←sEq,core_map,core,oriented_core]
  exact Perm.cycleType_one

theorem fresh_none_zero {R : Type*} [CommRing R] {n : ℕ} (b t : R)
    (s M : Perm (Fin n)) : fresh b t s M 0 none = if M=s then 1 else 0 := by
  classical
  have eq : fresh b t s M 0 none=pathSum b t s 0 0 M none true := by
    unfold fresh pathSum
    apply Fintype.sum_congr
    intro w
    have nil := List.length_eq_zero_iff.mp w.property.1
    simp [nil,executionFlips,hive,suffixWeight,hiveFrom]
  rw [eq,pathSum_zero]; simp

theorem standard_positive_empty {R : Type*} [CommRing R] {n : ℕ} (b t : R)
    (s : Perm (Fin n)) (hs : s⁻¹=s) (ns : ∀v,s v≠v)
    (std : ∀h : Fin n,h.val%2=0 → h<s h) :
    fresh b t s s 1 none = 0 := by
  classical
  let _ : IsEmpty (SuffixWords s 0 1 s none true) := ⟨fun w => by
    obtain ⟨q,hq⟩ := List.exists_mem_of_ne_nil (l:=w.val) (fun eq => by
      have len := w.property.1; rw [eq] at len; contradiction)
    exact hive_initially_active s s hs hs ns ns std none w (by omega) q hq rfl⟩
  simp [fresh]

#print axioms distance_zero_iff
#print axioms standard_positive_empty
end HalfWords
