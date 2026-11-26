import HalfWords.ActualSurgery
import HalfWords.Skip

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords

/-- The single swap that makes an exposed standard pair removable is forced
by the current partner of its upper label. This uses the actual rewire map. -/
theorem rewire_standard_iff {V : Type*} [DecidableEq V] (M : Perm V)
    (mm : Function.Involutive M) {a z v : V} (va : v ≠ a) (vz : v ≠ z) :
    rewire M (a,z) a = v ↔ z = M v := by
  simp only [rewire_apply,swap_apply_left,swap_apply_eq_iff,swap_apply_of_ne_of_ne va vz]
  exact ⟨fun e => (mm z).symm.trans (congrArg M e), fun e => e ▸ mm v⟩

/-- This unique correction child has original flip weight zero and is in the
pivot component for every canonical-charge matching. The label inequalities
are exactly those of an exposed consecutive standard pair. -/
theorem unique_correction_child [Fintype V] [LinearOrder V] (s M : Perm V)
    (hs : s⁻¹=s) (hm : M⁻¹=M) (ns : ∀ x, s x ≠ x) (nm : ∀ x, M x ≠ x)
    (a : V) (ha : a < s a) (cap : M (s a) ≤ s a)
    (gap : ∀ z, z < s a → z ≤ a) (active : M a ≠ s a) :
    (∃! z, z < a ∧ rewire M (a,z) a = s a) ∧
    Charge.Reach s M a (M (s a)) ∧ Charge.flip s M a (M (s a)) = 0 := by
  have mm (v : V) : M (M v) = v :=
    (congrArg (fun q : Perm V => q (M v)) hm.symm).trans (M.symm_apply_apply v)
  have less : M (s a) < a := lt_of_le_of_ne (gap _ (lt_of_le_of_ne cap (nm _)))
    (fun e => active ((congrArg M e).symm.trans (mm _)))
  have valid := Charge.canonical_valid s M hs hm ns nm
  refine ⟨⟨M (s a),⟨less,?_⟩,?_⟩,.trans _ _ _ (.rel _ _ (Or.inl rfl))
    (.rel _ _ (Or.inr rfl)),?_⟩
  · exact (rewire_standard_iff M mm ha.ne.symm (nm _).symm).mpr rfl
  · intro z hz
    exact (rewire_standard_iff M mm ha.ne.symm ((hz.1.trans ha).ne.symm)).mp hz.2
  · simp [Charge.flip,valid.second,valid.first]

#print axioms unique_correction_child
end HalfWords
