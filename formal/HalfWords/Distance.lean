import HalfWords.Cut
import HalfWords.Join
import HalfWords.Flip
import HalfWords.ComponentCount

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords
variable {V : Type*}

theorem separated_after_cut [Fintype V] [DecidableEq V] (r : Perm V) {a b : V}
    (ne : a ≠ b) (same : r.SameCycle a b) : ¬ (swap a b*r).SameCycle a b := by
  obtain ⟨as,bs,lt,absent,factor⟩ := cut_anchored_list r ne same
  have nd := r.nodup_toList a
  rw [lt] at nd
  have stable {v : V} (hv : v ∈ a::as) : (swap a b*r) v ∈ a::as := by
    have inside : v ∈ r.toList a := lt ▸ List.mem_append_left _ hv
    have fixed : ((r.cycleOf a)⁻¹*r) v=v := by
      change (r.cycleOf a).symm (r v)=v
      rw [← (Perm.mem_toList_iff.mp inside).1.cycleOf_apply]
      exact (r.cycleOf a).symm_apply_apply v
    rw [factor,Perm.mul_apply,fixed,Perm.mul_apply,
      List.formPerm_apply_of_notMem (List.disjoint_of_nodup_append nd hv)]
    exact List.formPerm_apply_mem_of_mem hv
  intro post
  obtain ⟨j,hj⟩ := post.exists_nat_pow_eq
  have iter (i : ℕ) : ((swap a b*r)^i) a ∈ a::as := by
    induction i with
    | zero => exact List.mem_cons_self ..
    | succ i ih => simpa only [pow_succ',Perm.mul_apply] using stable ih
  exact absent (hj ▸ iter j)

/-- The count includes cycles of length one. -/
noncomputable def orbitCount (r : Perm V) := Nat.card (Quotient (Perm.SameCycle.setoid r))

theorem orbitCount_join [Finite V] [DecidableEq V] (r : Perm V) {a b : V}
    (h : ¬r.SameCycle a b) : orbitCount (swap a b*r)+1=orbitCount r := by
  let eqv : Perm.SameCycle.setoid (swap a b*r) = merged (Perm.SameCycle.setoid r) a b := by
    ext x y
    exact same_color_join r h x y
  simpa only [orbitCount,eqv] using merged_card (Perm.SameCycle.setoid r) a b h

theorem orbitCount_cut [Fintype V] [DecidableEq V] (r : Perm V) {a b : V}
    (ne : a ≠ b) (h : r.SameCycle a b) : orbitCount r+1=orbitCount (swap a b*r) := by
  have rev := orbitCount_join (swap a b*r) (separated_after_cut r ne h)
  simpa [←mul_assoc] using rev

/-- All alternating components of a matching, including standard pairs. -/
noncomputable def componentCount (s M : Perm V) :=
  Nat.card (Quotient (Relation.EqvGen.setoid (Charge.Edge s M)))

private theorem pullbackCount {W : Type*} (s : Setoid W) (R : Setoid V)
    (f : V → W) (onto : Function.Surjective f)
    (relation : ∀x y, R.r x y ↔ s.r (f x) (f y)) :
    Nat.card (Quotient R)=Nat.card (Quotient s) := by
  let g (v : V) := Quotient.mk s (f v)
  have sur : Function.Surjective g := by
    intro q
    obtain ⟨w,rfl⟩ := Quotient.exists_rep q
    obtain ⟨v,rfl⟩ := onto w
    exact ⟨v,rfl⟩
  have E : R=Setoid.ker g := by
    ext x y
    exact (relation x y).trans Quotient.eq.symm
  rw [E]
  exact Nat.card_congr (Setoid.quotientKerEquivOfSurjective g sur)

theorem oriented_count [Finite V] (r : Perm V) : componentCount (oriented 1) (oriented r) =
    orbitCount r := pullbackCount _ _ Prod.fst (fun x => ⟨(x,false),rfl⟩) (oriented_reach_iff r)

theorem opposite_join_count [Finite V] [DecidableEq V] (r : Perm V) {a b : V}
    (h : ¬r.SameCycle a b) :
    componentCount (oriented 1) (rewire (oriented r) ((a,false),(b,true))) + 1 =
    componentCount (oriented 1) (oriented r) := by
  rw [oriented_count]
  have post := pullbackCount (merged (Perm.SameCycle.setoid r) a b)
    (Relation.EqvGen.setoid (Charge.Edge (oriented 1) (rewire (oriented r) ((a,false),(b,true)))))
    Prod.fst (fun x => ⟨(x,false),rfl⟩) (opposite_surgery r a b)
  exact (congrArg (·+1) post).trans (merged_card (Perm.SameCycle.setoid r) a b h)

#print axioms orbitCount_cut
#print axioms opposite_join_count
end HalfWords
