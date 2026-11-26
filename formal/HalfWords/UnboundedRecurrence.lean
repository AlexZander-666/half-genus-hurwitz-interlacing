import HalfWords.InactiveBounds

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords Hurwitz.Paths Hurwitz.WordWeights

private theorem new_matching {V : Type*} [DecidableEq V] (M : Perm V) (hm : M⁻¹=M)
    (nm : ∀v,M v≠v) (a : V×V) :
    (rewire M a)⁻¹=rewire M a ∧ ∀v,rewire M a v≠v := by
  have mm (v : V) : M (M v)=v :=
    (congrArg (fun p : Perm V => p (M v)) hm.symm).trans (M.symm_apply_apply v)
  have H := rewire_preserves_matching M mm nm a
  refine ⟨?_,H.2⟩
  apply Equiv.ext
  intro v
  apply (rewire M a).injective
  exact ((rewire M a).apply_symm_apply v).trans (H.1 v).symm

/-- True unbounded rows at excess zero or one admit an unbounded recursion.
All children keep the original ambient labels. Upper paired components are
ignored because no permissible word can ever use their hives. -/
theorem unbounded_recurrence {R : Type*} [CommRing R] {n : ℕ} (t : R)
    (s M : Perm (Fin n)) (r : ℕ) (u h : Fin n) (gap : ∀v : Fin n, v<h ↔ v≤u)
    (hs : s⁻¹=s) (hm : M⁻¹=M) (ns : ∀v,s v≠v) (nm : ∀v,M v≠v)
    (std : ∀v : Fin n,v.val%2=0 → v<s v) (even : h.val%2=0)
    (cap : M (s h) ≤ s h) (adj : ∀z,z<s h → z≤h) (active : M h≠s h)
    (closed : ∀v : Fin n,h<v → v.val%2=0 → M v=s v)
    (budget : componentCount s M+(r+1)≤componentCount s s+1) :
    fresh 1 t s M (r+1) none =
    (∑ v ∈ internalLabels s M h, fresh 1 t s (rewire M (h,v)) r none)+
    (t-1)*fresh 1 t s (rewire M (h,M (s h))) r none := by
  classical
  have mm (v : Fin n) : M (M v)=v :=
    (congrArg (fun p : Perm (Fin n) => p (M v)) hm.symm).trans (M.symm_apply_apply v)
  have ord := std h even
  have low : M (s h)<h := lt_of_le_of_ne (adj _ (lt_of_le_of_ne cap (nm _)))
    (fun e => active ((congrArg M e).symm.trans (mm _)))
  have child_budget {v : Fin n} (lt : v<h) :
      componentCount s (rewire M (h,v))+r ≤ componentCount s s+1 := by
    rcases actual_step s M hs hm ns nm h v lt.ne.symm with ⟨_,_,eq⟩|⟨_,_,eq⟩|⟨_,eq⟩ <;> omega
  have preserves {v z : Fin n} (lt : v<h) (high : h<z) (ez : z.val%2=0) :
      rewire M (h,v) z=s z := by
    rw [rewire_apply,swap_apply_of_ne_of_ne high.ne.symm (lt.trans high).ne.symm,
      closed z high ez,swap_apply_of_ne_of_ne (high.trans (std z ez)).ne.symm
      ((lt.trans high).trans (std z ez)).ne.symm]
  rw [fresh_restrict 1 t s M hs hm ns nm std (r+1) h budget closed,
    active_recurrence t s M r u h gap hs hm ns nm even ord cap adj active budget]
  congr 1
  · apply Finset.sum_congr rfl
    intro v hv
    have lt : v<h := (Finset.mem_filter.mp hv).2.1
    exact (fresh_restrict 1 t s _ hs (new_matching M hm nm _).1 ns
      (new_matching M hm nm _).2 std r h (child_budget lt) (fun _ => preserves lt)).symm
  · apply congrArg ((t-1)*·)
    symm
    apply fresh_restrict 1 t s _ hs (new_matching M hm nm _).1 ns
      (new_matching M hm nm _).2 std r u (child_budget low)
    intro z hz ez
    by_cases eq : z=h
    · subst z
      exact (rewire_standard_iff M mm ord.ne.symm ((low.trans ord).ne.symm)).mpr rfl
    · apply preserves low _ ez
      exact lt_of_le_of_ne (le_of_not_gt (fun less => hz.not_ge ((gap _).mp less))) (fun e => eq e.symm)

#print axioms unbounded_recurrence
end HalfWords
