import HalfWords.ActiveMaximum
import HalfWords.UnboundedRecurrence

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords
variable {n : ℕ}

/-- For a nonstandard exposed pair, its upper endpoint is the largest label
in its entire component. Consequently the lower pivot is canonically negative
and does not require an arbitrary sign choice. -/
theorem active_coordinates (s M : Perm (Fin n)) (hs : s⁻¹=s) (hm : M⁻¹=M)
    (ns : ∀v,s v≠v) (nm : ∀v,M v≠v) (h : Fin n) (active : M h≠s h)
    (closed : ∀v,s h < v → M v=s v) :
    let J := {v : Fin n // Charge.canonical s M v=false}
    ∃ (r : Perm J) (e : J×Bool ≃ Fin n) (a : J),
      e.permCongrHom (oriented 1)=s ∧ e.permCongrHom (oriented r)=M ∧
      e (a,false)=h ∧ e (a,true)=s h ∧ ∀v,Charge.Reach s M h v → v≤e (a,true) := by
  classical
  let col := Charge.canonical s M
  have valid := Charge.canonical_valid s M hs hm ns nm
  have ss (v : Fin n) : s (s v)=v :=
    (congrArg (fun p : Perm (Fin n) => p (s v)) hs.symm).trans (s.symm_apply_apply v)
  have mm (v : Fin n) : M (M v)=v :=
    (congrArg (fun p : Perm (Fin n) => p (M v)) hm.symm).trans (M.symm_apply_apply v)
  have cap (v : Fin n) (c : Charge.Reach s M h v) : v ≤ s h :=
    exposed_component_cap ss mm h active closed c
  have top : col (s h)=true := valid.maximum _ fun v c => cap _ (.trans _ _ _
    (.rel _ _ (Or.inl rfl)) c)
  have bottom : col h=false := by
    have eq := valid.first h
    change col (s h) = !col h at eq
    rw [top] at eq
    cases H : col h
    · rfl
    · rw [H] at eq; contradiction
  let a : {v // col v=false} := ⟨h,bottom⟩
  let e := chargedCoordinates s col valid.first ss
  let r := successor s M col valid.first valid.second ss mm
  refine ⟨r,e,a,?_,matching_coordinates ..,rfl,rfl,cap⟩
  apply Equiv.ext
  intro v
  obtain ⟨⟨i,d⟩,rfl⟩ := e.surjective v
  change e (oriented 1 (e.symm (e (i,d))))=s (e (i,d))
  rw [Equiv.symm_apply_apply]
  cases d
  · rfl
  · exact (ss i).symm

/-- The pivot component of an unmatched exposed pair is a nontrivial orbit. -/
theorem active_orbit {V W : Type*} [Fintype V] [DecidableEq V]
    (e : V×Bool ≃ W) (s M : Perm W) (r : Perm V)
    (hs : e.permCongrHom (oriented 1)=s) (hm : e.permCongrHom (oriented r)=M)
    (a : V) (active : M (e (a,false))≠s (e (a,false))) : a∈r.support := by
  apply Perm.mem_support.mpr
  intro fix
  apply active
  rw [←hs,←hm]
  change e (oriented r (e.symm (e (a,false))))=e (oriented 1 (e.symm (e (a,false))))
  simp only [Equiv.symm_apply_apply,oriented_left]
  have eq : r.symm a=a := (congrArg r.symm fix).symm.trans (r.symm_apply_apply a)
  rw [eq]; rfl

#print axioms active_coordinates
end HalfWords
