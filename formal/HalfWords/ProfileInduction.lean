import HalfWords.ChildBudget
import HalfWords.JetProfile
import HalfWords.DistanceZero

namespace HalfWords
open scoped DualNumber
open Equiv Hurwitz Hurwitz.MatchingWords Hurwitz.WordWeights Hurwitz.Paths TrivSqZeroExt

private theorem rewired_valid {V : Type*} [DecidableEq V] (M : Perm V) (hm : M⁻¹=M)
    (nm : ∀v,M v≠v) (x y : V) : (rewire M (x,y))⁻¹=rewire M (x,y) ∧ ∀v,rewire M (x,y) v≠v := by
  have mm (v : V) : M (M v)=v :=
    (congrArg (fun p : Perm V => p (M v)) hm.symm).trans (M.symm_apply_apply v)
  have H := rewire_preserves_matching M mm nm (x,y)
  exact ⟨Equiv.ext (fun v => (rewire M (x,y)).injective
    (((rewire M (x,y)).apply_symm_apply v).trans (H.1 v).symm)),H.2⟩

/-- The full unconnected endpoint-conditioned word polynomial at excess zero
and one is the corresponding column of the product over alternating parts.
The ambient matching and all numerical hive labels are retained. -/
theorem true_profile {R : Type*} [CommRing R] (t : R) (m len : ℕ)
    (M : Perm (Fin ((m+1)*2))) (hm : M⁻¹=M) (nm : ∀v,M v≠v) (d : ℕ) (hd : d≤1)
    (budget : componentCount (originalStandard m) M+len =
      componentCount (originalStandard m) (originalStandard m)+d) :
    fresh 1 t (originalStandard m) M len none =
      jetComponent d (profileProduct t (core (originalStandard m) M)) := by
  classical
  let s := originalStandard m
  have hs : s⁻¹=s := by
    change ((index m).permCongrHom (standard m))⁻¹ = (index m).permCongrHom (standard m)
    rw [←map_inv]; rfl
  have ss (v : Fin ((m+1)*2)) : s (s v)=v :=
    (congrArg (fun p : Perm _ => p (s v)) hs.symm).trans (s.symm_apply_apply v)
  have ns (v : Fin ((m+1)*2)) : s v≠v := by
    obtain ⟨⟨i,b⟩,rfl⟩ := (index m).surjective v
    intro eq
    change (index m) (standard m ((index m).symm ((index m) (i,b)))) = (index m) (i,b) at eq
    rw [Equiv.symm_apply_apply] at eq
    have flip := congrArg Prod.snd ((index m).injective eq)
    cases b <;> contradiction
  have std (v : Fin ((m+1)*2)) (ev : v.val%2=0) : v<s v :=
    show v.val < (originalStandard m v).val by rw [original_even_step _ ev]; omega
  change componentCount s M+len=componentCount s s+d at budget
  change fresh 1 t s M len none=jetComponent d (profileProduct t (core s M))
  induction len generalizing M d with
  | zero =>
    obtain ⟨le,iff⟩ := distance_zero_iff s M hs hm ns nm
    obtain rfl : M=s := iff.mp (by omega)
    obtain rfl : d=0 := by omega
    rw [fresh_none_zero,if_pos rfl,standard_core _ hs ns]
    rfl
  | succ len ih =>
    have mm (v : Fin ((m+1)*2)) : M (M v)=v :=
      (congrArg (fun p : Perm _ => p (M v)) hm.symm).trans (M.symm_apply_apply v)
    by_cases eq : M=s
    · subst M
      obtain rfl : len=0 := by omega
      obtain rfl : d=1 := by omega
      rw [standard_positive_empty 1 t s hs ns std,standard_core _ hs ns]
      rfl
    obtain ⟨h,even,active,pos,closed⟩ := active_max mm nm eq
    change M h≠s h at active
    change ∀v,s h<v → M v=s v at closed
    let u : Fin ((m+1)*2) := ⟨h.val-1,by have := h.isLt; omega⟩
    have gap (v : Fin ((m+1)*2)) : v<h ↔ v≤u := by change v.val<h.val ↔ v.val≤h.val-1; omega
    have order := std h even
    have adjacent := original_even_step h even
    change (s h).val=h.val+1 at adjacent
    have adj (v : Fin ((m+1)*2)) (less : v<s h) : v≤h := by
      have low : v.val<(s h).val := less; change v.val≤h.val; omega
    have bound : M (s h) ≤ s h := by
      by_contra! gt
      have good := closed _ gt
      rw [mm] at good
      have eqm : h=M (s h) := (ss h).symm.trans ((congrArg s good).trans (ss _))
      exact active ((congrArg M eqm).trans (mm _))
    have evenclosed (v : Fin ((m+1)*2)) (above : h<v) (ev : v.val%2=0) : M v=s v := by
      apply closed
      have gt : h.val<v.val := above
      change (s h).val<v.val; omega
    obtain ⟨r,e,a,es,em,ea,eb,cap⟩ := active_coordinates s M hs hm ns nm h active closed
    have support := active_orbit e s M r es em a (by simpa [ea] using active)
    let P (K : Perm _) := profileProduct t (core s K)
    let child (b) (col : Bool) := rewire M (e (a,false),e (b,col))
    let correction := rewire M (e (a,false),M (s (e (a,false))))
    have applyCut {K : Perm _} (inv : K⁻¹=K) (nf : ∀v,K v≠v)
        (count : componentCount s K=componentCount s M+1) :
        fresh 1 t s K len none=jetComponent d (P K) :=
      ih K inv nf d hd (by omega)
    have cuts (b) (hb : b∈cutPartners r a) : fresh 1 t s (child b false) len none =
        jetComponent d (P (child b false)) :=
      applyCut (rewired_valid M hm nm _ _).1 (rewired_valid M hm nm _ _).2
        (mapped_counts e s M r es em a b hb).1
    have flips (b) (hb : b∈cutPartners r a) : fresh 1 t s (child b true) len none =
        jetComponent d (ε*P (child b true)) := by
      have count : componentCount s (child b true)=componentCount s M := (mapped_counts e s M r es em a b hb).2
      rw [component_eps_mul]
      split_ifs with d0
      · exact fresh_below_distance 1 t s _ hs (rewired_valid M hm nm _ _).1 ns
          (rewired_valid M hm nm _ _).2 len none (show componentCount s (child b true)+len<componentCount s s by omega)
      · exact ih _ (rewired_valid M hm nm _ _).1 (rewired_valid M hm nm _ _).2 0 (by decide) (show componentCount s (child b true)+len=componentCount s s+0 by omega)
    have corr : fresh 1 t s correction len none=jetComponent d (P correction) :=
      applyCut (rewired_valid M hm nm _ _).1 (rewired_valid M hm nm _ _).2
        (mapped_correction_count e s M r es em a support)
    have labels := sum_internal_labels e s M r es em a (by simpa [ea,eb] using order)
      (by simpa [ea,eb] using adj) (by simpa [ea] using cap)
      (fun v => fresh 1 t s (rewire M (e (a,false),v)) len none)
    change fresh 1 t s M (len+1) none=jetComponent d (P M)
    rw [unbounded_recurrence t s M len u h gap hs hm ns nm std even bound adj active evenclosed (by omega)]
    rw [←ea,labels]
    change ((∑ b ∈ cutPartners r a, fresh 1 t s (child b false) len none)+
      ∑ b ∈ cutPartners r a, fresh 1 t s (child b true) len none)+
      (t-1)*fresh 1 t s correction len none=_
    rw [Finset.sum_congr rfl cuts,Finset.sum_congr rfl flips,corr]
    have jet := congrArg (jetComponent d) (product_pivot t e s M r es em a support)
    simpa only [map_add,map_sum,component_inl_mul] using jet.symm

#print axioms true_profile
end HalfWords
