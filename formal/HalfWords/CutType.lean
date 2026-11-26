import HalfWords.Cut
import HalfWords.CoreProfile

namespace HalfWords
open Equiv
variable {V : Type*} [Fintype V] [DecidableEq V]

def longPart (n : ℕ) : Multiset ℕ := if 2≤n then {n} else 0

theorem formPerm_type (A : List V) (nd : A.Nodup) : A.formPerm.cycleType=longPart A.length := by
  by_cases h : 2≤A.length
  · rw [longPart,if_pos h,(List.isCycle_formPerm nd h).cycleType,
      List.support_formPerm_of_nodup _ nd (fun v ev => by simp [ev] at h)]
    simp [List.card_toFinset,List.dedup_eq_self.mpr nd]
  · cases A with
    | nil => simp [longPart]
    | cons a A =>
      cases A with
      | nil => simp [longPart]
      | cons b B => simp at h

/-- Cutting at a fixed label with index i leaves the two circular segments
of lengths i and L−i and the same residual factors, also for i=1 or L−1. -/
theorem split_types (r : Perm V) {a b : V} (ne : a ≠ b) (same : r.SameCycle a b) :
    let L := (r.toList a).length
    let i := (r.toList a).idxOf b
    let rest := ((r.cycleOf a)⁻¹*r).cycleType
    r.cycleType = longPart L + rest ∧
    (swap a b*r).cycleType = (longPart i + longPart (L-i)) + rest := by
  obtain ⟨as,bs,full,absent,cut⟩ := cut_anchored_list r ne same
  let A := a::as
  let B := b::bs
  let rest := (r.cycleOf a)⁻¹*r
  have all : r.toList a = A ++ B := full
  have nd : (A++B).Nodup := all ▸ r.nodup_toList a
  have iEq : (r.toList a).idxOf b=A.length := by
    rw [all,List.idxOf_append_of_notMem absent]
    simp [A,B]
  have lEq : (r.toList a).length-(r.toList a).idxOf b=B.length := by rw [iEq,all,List.length_append]; omega
  have fixed {v : V} (inside : v ∈ A++B) : rest v=v := by
    have mem : v ∈ r.toList a := all ▸ inside
    change (r.cycleOf a).symm (r v)=v
    rw [← (Perm.mem_toList_iff.mp mem).1.cycleOf_apply]
    exact (r.cycleOf a).symm_apply_apply v
  have dis (C : List V) (sub : ∀v∈C,v∈A++B) : C.formPerm.Disjoint rest := by
    intro v
    by_cases mem : v ∈ C
    · exact Or.inr (fixed (sub v mem))
    · exact Or.inl (List.formPerm_apply_of_notMem mem)
  have dAB : A.formPerm.Disjoint B.formPerm := by
    intro v
    by_cases mem : v∈A
    · exact Or.inr (List.formPerm_apply_of_notMem (List.disjoint_of_nodup_append nd mem))
    · exact Or.inl (List.formPerm_apply_of_notMem mem)
  have ds : (A.formPerm*B.formPerm).Disjoint rest :=
    (dis A (fun _ hx => List.mem_append_left _ hx)).mul_left
      (dis B (fun _ hx => List.mem_append_right _ hx))
  have rc : r=(A++B).formPerm*rest := by
    rw [← all,Perm.formPerm_toList]
    dsimp [rest]
    group
  dsimp only
  constructor
  · conv_lhs => rw [rc]
    rw [(dis (A++B) (fun _ h => h)).cycleType_mul,formPerm_type _ nd,all]
  · rw [cut,ds.cycleType_mul,dAB.cycleType_mul,formPerm_type _ nd.of_append_left,
      formPerm_type _ nd.of_append_right,lEq,iEq]

/-- The nontrivial alternating lengths of the raw matching are exactly the
usual permutation cycle type in any oriented coordinates. -/
theorem oriented_core (r : Perm V) :
    (profile (oriented 1) (oriented r)).filter (1<·) = r.cycleType := by
  rw [oriented_profile,orbitSizes_filter]

#print axioms split_types
end HalfWords
