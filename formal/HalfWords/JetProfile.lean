import HalfWords.JetRows
import HalfWords.PivotCoordinates

namespace HalfWords
open scoped DualNumber
open Equiv Hurwitz.MatchingWords TrivSqZeroExt
variable {R V W : Type*} [CommRing R] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Product rule with both budget columns for the actual children of any
nontrivial pivot. The nilpotent term selects exactly one flip across the
whole forest of alternating components. -/
theorem product_pivot (t : R) (e : V×Bool ≃ W) (s M : Perm W) (r : Perm V)
    (hs : e.permCongrHom (oriented 1)=s) (hm : e.permCongrHom (oriented r)=M)
    (a : V) (ha : a∈r.support) :
    profileProduct t (core s M) =
      (∑ b ∈ cutPartners r a, profileProduct t (core s (rewire M (e (a,false),e (b,false))))) +
      (∑ b ∈ cutPartners r a, ε*profileProduct t (core s (rewire M (e (a,false),e (b,true))))) +
      inl (t-1)*profileProduct t (core s (rewire M (e (a,false),M (s (e (a,false)))))) := by
  let L := (r.toList a).length
  have high : 2≤L := Perm.two_le_length_toList_iff_mem_support.mpr ha
  have eq0 : core s M=r.cycleType := by rw [←hs,←hm,core_map,core,oriented_core]
  have same : r.SameCycle a (r a) := (r.sameCycle_apply_right).mpr Perm.SameCycle.rfl
  have EQ := (split_types r (Perm.mem_support.mp ha).symm same).1
  let T := profileProduct t (((r.cycleOf a)⁻¹*r).cycleType)
  have total : profileProduct t (core s M)=jetRow t L*T := by
    rw [eq0,EQ,product_union,product_part _ (by omega : 1≤L)]
  have term (i : ℕ) (hi : i ∈ Finset.Ico 1 L) :
      profileProduct t (longPart i+longPart (L-i)+((r.cycleOf a)⁻¹*r).cycleType) =
      jetRow t i*jetRow t (L-i)*T := by
    obtain ⟨lo,up⟩ := Finset.mem_Ico.mp hi
    rw [product_union,product_union,product_part _ lo,product_part _ (by omega)]
  have cut := actual_cut_profile_sum e s M r hs hm a (profileProduct t)
  have flip := actual_flip_profile_sum e s M r hs hm a (fun p => (ε : DualNumber R)*profileProduct t p)
  rw [cut,flip,actual_correction_profile e s M r hs hm a ha,total]
  change jetRow t L*T =
    (∑ i ∈ Finset.Ico 1 L, _) + (L-1) • (ε * (jetRow t L*T)) + inl (t-1)*_
  rw [Finset.sum_congr rfl term,←Finset.sum_mul,product_union,product_part _ (by omega : 1≤L-1)]
  have rows := congrArg (· * T) (jet_recurrence t high)
  simpa only [add_mul,smul_mul_assoc,mul_assoc] using rows

#print axioms product_pivot
end HalfWords
