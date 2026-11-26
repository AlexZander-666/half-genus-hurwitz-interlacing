import HalfWords.Fresh
import HalfWords.UniqueChild

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords Hurwitz.WordWeights Hurwitz.Paths

theorem rewire_comm {V : Type*} [DecidableEq V] (M : Perm V) (a b : V) :
    rewire M (a,b) = rewire M (b,a) := by simp only [rewire,swap_comm a b]
theorem flip_comm {V : Type*} [Fintype V] [LinearOrder V] (s M : Perm V) (a b : V) :
    Charge.flip s M a b = Charge.flip s M b a := by simp only [Charge.flip,eq_comm]

/-- The exact join/cut/flip recurrence before collecting word counts by their
length profile. For a nonstandard pivot the unique skip correction has
coefficient t−1 and flip exponent zero. -/
theorem unmatched_pivot {R : Type*} [CommRing R] {n : ℕ} (b t : R)
    (s M : Perm (Fin n)) (r : ℕ) (u h : Fin n) (gap : ∀ v : Fin n, v<h ↔ v≤u)
    (hs : s⁻¹=s) (hm : M⁻¹=M) (ns : ∀v, s v ≠ v) (nm : ∀v, M v ≠ v)
    (even : h.val % 2 = 0) (ord : h < s h) (cap : M (s h) ≤ s h)
    (adj : ∀z, z < s h → z ≤ h) (active : M h ≠ s h) :
    fresh b t s M (r+1) (some h) =
      (∑ a ∈ (nextSteps (some h)).filter (fun a => a.2=h),
        b ^ Charge.flip s M a.1 a.2 * fresh b t s (rewire M a) r (some h)) +
      (t-1)*fresh b t s (rewire M (M (s h),h)) r (some u) := by
  classical
  have mm (v : Fin n) : M (M v) = v :=
    (congrArg (fun q : Perm (Fin n) => q (M v)) hm.symm).trans (M.symm_apply_apply v)
  let z := M (s h)
  have low : z < h := lt_of_le_of_ne (adj _ (lt_of_le_of_ne cap (nm _)))
    (fun e => active ((congrArg M e).symm.trans (mm _)))
  have good := (unique_correction_child s M hs hm ns nm h ord cap adj active).2.2
  have zeroFlip : Charge.flip s M z h = 0 := (flip_comm _ _ _ _).trans good
  let steps := (nextSteps (some h)).filter (fun a => a.2=h)
  have present : (z,h) ∈ steps := Finset.mem_filter.mpr
    ⟨mem_nextSteps.mpr ⟨⟨low,even⟩,le_rfl⟩,rfl⟩
  rw [fresh_pivot b t s M r u h gap,lower_empty_of_unmatched b t s M (r+1) u h gap ord.le active,
    zero_add]
  simp_rw [mul_add,Finset.sum_add_distrib]
  apply congrArg (_ + ·)
  change ∑ a ∈ steps, _ = _
  rw [Finset.sum_eq_single (z,h)]
  · simp [zeroFlip,z] at *
  · intro a ha ne
    obtain ⟨v,w⟩ := a
    obtain ⟨mem,e⟩ := Finset.mem_filter.mp ha
    dsimp only at e
    subst w
    have small : v < h := (mem_nextSteps.mp mem).1.1
    have bad : rewire M (v,h) h ≠ s h := by
      rw [rewire_comm]
      intro paired
      apply ne
      exact Prod.ext ((rewire_standard_iff M mm ord.ne.symm ((small.trans ord).ne.symm)).mp paired) rfl
    rw [lower_empty_of_unmatched b t s _ r u h gap ord.le bad]
    simp
  · exact fun no => (no present).elim

#print axioms unmatched_pivot
end HalfWords
