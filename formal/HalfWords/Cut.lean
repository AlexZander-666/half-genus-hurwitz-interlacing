import HalfWords.Surgery
import Mathlib.GroupTheory.Perm.Cycle.Concrete

namespace HalfWords
open Equiv Hurwitz.MatchingWords
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For arbitrary distinct points in the same component of the actual
permutation, split its canonically anchored list at the second point. -/
theorem cut_anchored_list (r : Perm V) {a b : V} (ne : a ≠ b) (same : r.SameCycle a b) :
    ∃ as bs : List V, r.toList a = (a::as)++(b::bs) ∧
      b ∉ a::as ∧
      swap a b * r =
        ((a::as).formPerm * (b::bs).formPerm) * ((r.cycleOf a)⁻¹*r) := by
  have ha : a ∈ r.support := Perm.mem_support.mpr fun eq => ne (same.eq_of_left eq)
  have hb : b ∈ r.toList a := Perm.mem_toList_iff.mpr ⟨same,ha⟩
  have initial := r.toList_getElem_zero a ha
  obtain ⟨head,tail,ht⟩ := List.exists_cons_of_ne_nil (fun e => Perm.toList_eq_nil_iff.mp e ha)
  rw [ht] at hb
  have ea : head=a := by simpa [ht] using initial
  subst head
  have mem : b ∈ tail := (List.mem_cons.mp hb).resolve_left ne.symm
  obtain ⟨as,bs,h⟩ := List.mem_iff_append.mp mem
  have full : r.toList a = (a::as)++(b::bs) := by simp [ht,h]
  have nd := r.nodup_toList a
  rw [full] at nd
  have fresh : b ∉ a::as := fun m => (List.disjoint_of_nodup_append nd)
    m (List.mem_cons_self ..)
  refine ⟨as,bs,full,fresh,?_⟩
  have cyc := Perm.formPerm_toList r a
  rw [full] at cyc
  calc swap a b * r = (swap a b * r.cycleOf a) * ((r.cycleOf a)⁻¹*r) := by group
       _ = _ := by rw [← cyc,cut_cycle a b as bs fresh]

#print axioms cut_anchored_list
end HalfWords
