import HalfWords.Excess

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords Hurwitz.WordWeights

variable {V : Type*}
/-- A swap inside an existing component can only refine the old component
partition, independent of the charge and of any order on the labels. -/
theorem reach_before_internal [DecidableEq V] (s M : Perm V) {a b x y : V} (ab : Charge.Reach s M a b)
    (new : Charge.Reach s (rewire M (a,b)) x y) : Charge.Reach s M x y := by
  have sw (v : V) : Charge.Reach s M v (swap a b v) := by
    by_cases ea : v=a
    · subst v; simpa using ab
    by_cases eb : v=b
    · subst v; simpa using Relation.EqvGen.symm _ _ ab
    rw [swap_apply_of_ne_of_ne ea eb]
    exact .refl _
  induction new with
  | rel x y e =>
    rcases e with e|e <;> subst y
    · exact .rel _ _ (Or.inl rfl)
    · rw [rewire_apply]
      exact .trans _ _ _ (sw x) (.trans _ _ _ (.rel _ _ (Or.inr rfl)) (sw _))
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih ik => exact .trans _ _ _ ih ik

theorem no_foreign_swap [Fintype V] [LinearOrder V] (s M : Perm V) (hs : s⁻¹=s) (hm : M⁻¹=M)
    (ns : ∀v,s v≠v) (nm : ∀v,M v≠v)
    (xs : List (V×V)) (distinct : ∀q∈xs,q.1≠q.2)
    (cost : componentCount s M+xs.length ≤ componentCount s (execute M xs)+1) :
    ∀q∈xs, Charge.Reach s M q.1 q.2 := by
  induction xs generalizing M with
  | nil => simp
  | cons p xs ih =>
    rcases p with ⟨a,b⟩
    let q := (a,b)
    have mm (v : V) : M (M v) = v :=
      (congrArg (fun e : Perm V => e (M v)) hm.symm).trans (M.symm_apply_apply v)
    have new := rewire_preserves_matching M mm nm q
    have inv : (rewire M q)⁻¹=rewire M q := by
      apply Equiv.ext
      intro v
      apply (rewire M q).injective
      exact ((rewire M q).apply_symm_apply v).trans (new.1 v).symm
    have diff (v) (hv : v ∈ xs) := distinct v (List.mem_cons_of_mem q hv)
    have low := (word_excess s (rewire M q) hs inv ns new.2 xs diff).1
    change componentCount s M+(xs.length+1) ≤ componentCount s (execute (rewire M q) xs)+1 at cost
    have both : Charge.Reach s M a b ∧ componentCount s (rewire M q)+xs.length ≤
        componentCount s (execute (rewire M q) xs)+1 := by
      rcases actual_step s M hs hm ns nm a b (distinct q List.mem_cons_self) with
        ⟨cc,_,n⟩|⟨cc,_,n⟩|⟨_,n⟩
      · change componentCount s (rewire M q)=_ at n
        exact ⟨cc,by omega⟩
      · change componentCount s (rewire M q)=_ at n
        exact ⟨cc,by omega⟩
      · change componentCount s (rewire M q)+1=_ at n
        omega
    intro v hv
    rcases List.mem_cons.mp hv with rfl|tail
    · exact both.1
    · exact reach_before_internal s M both.1 (ih _ inv new.2 diff both.2 v tail)

#print axioms no_foreign_swap
end HalfWords
