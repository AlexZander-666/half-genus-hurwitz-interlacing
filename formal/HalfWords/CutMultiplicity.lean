import HalfWords.CutType
import Mathlib.Data.List.NodupEquivFin

namespace HalfWords
open Equiv Hurwitz.MatchingWords
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The cut partners at a designated vertex, including both end cuts of an orbit. -/
noncomputable def cutPartners (r : Perm V) (a : V) : Finset V := by
  classical
  exact Finset.univ.filter fun b => a ≠ b ∧ r.SameCycle a b

theorem mem_cutPartners (r : Perm V) (a b : V) :
    b ∈ cutPartners r a ↔ a ≠ b ∧ r.SameCycle a b := by
  classical
  simp [cutPartners]

/-- Every ordered split of the selected orbit occurs once. In the singleton
case both ranges are empty (mathlib represents that orbit by an empty list). -/
noncomputable def cutIndex (r : Perm V) (a : V) :
    cutPartners r a ≃ Finset.Ico 1 (r.toList a).length := by
  classical
  let l := r.toList a
  have zero (b : V) (h : b ∈ l) : l.idxOf b=0 ↔ b=a := by
    obtain ⟨_,ha⟩ := Perm.mem_toList_iff.mp h
    have ix := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr h)
    constructor
    · intro he
      exact (show b = l[0]'(r.length_toList_pos_of_mem_support a ha) by simpa only [he] using ix.symm).trans (r.toList_getElem_zero a ha)
    · intro e
      let h0 := r.length_toList_pos_of_mem_support a ha
      have first : l[0]'h0 = b := (r.toList_getElem_zero a ha).trans e.symm
      rw [←first]
      exact (r.nodup_toList a).idxOf_getElem 0 h0
  refine {
    toFun := fun b => ⟨l.idxOf b.val,?_⟩
    invFun := fun i => ⟨l[i.val]'(Finset.mem_Ico.mp i.property).2,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · obtain ⟨ne,same⟩ := (mem_cutPartners r a b).mp b.property
    have ha : a ∈ r.support := Perm.mem_support.mpr (fun eq => ne (same.eq_of_left eq))
    have mem : b.val ∈ l := Perm.mem_toList_iff.mpr ⟨same,ha⟩
    exact Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr (fun h => ne ((zero _ mem).mp h).symm),
      List.idxOf_lt_length_iff.mpr mem⟩
  · obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp i.property
    have mem := List.getElem_mem (l:=l) hi
    have idx : l.idxOf l[i.val] = i.val := (r.nodup_toList a).idxOf_getElem _ hi
    exact (mem_cutPartners r a _).mpr ⟨fun eq => by
      have h := (zero _ mem).mpr eq.symm
      omega, (Perm.mem_toList_iff.mp mem).1⟩
  · intro b
    apply Subtype.ext
    exact List.getElem_idxOf _
  · intro i
    apply Subtype.ext
    exact (r.nodup_toList a).idxOf_getElem _ (Finset.mem_Ico.mp i.property).2

theorem cut_sum {R : Type*} [AddCommMonoid R] (r : Perm V) (a : V)
    (F : Multiset ℕ → R) :
    ∑ b ∈ cutPartners r a, F ((swap a b*r).cycleType) =
    ∑ i ∈ Finset.Ico 1 (r.toList a).length,
      F (longPart i + longPart ((r.toList a).length-i) + ((r.cycleOf a)⁻¹*r).cycleType) := by
  classical
  rw [←Finset.sum_attach,←Finset.sum_attach (s:=Finset.Ico 1 (r.toList a).length)]
  apply Finset.sum_equiv (cutIndex r a)
  · simp
  · intro b _
    obtain ⟨ne,same⟩ := (mem_cutPartners r a b).mp b.property
    exact congrArg F (split_types r ne same).2

#print axioms cut_sum
end HalfWords
