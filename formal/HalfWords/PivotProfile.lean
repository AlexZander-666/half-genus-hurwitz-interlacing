import HalfWords.CutMultiplicity

namespace HalfWords
open Equiv Hurwitz.MatchingWords
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

noncomputable def core (s M : Perm W) := (profile s M).filter (1<·)

omit [DecidableEq V] [DecidableEq W] in
theorem core_map (e : V ≃ W) (s M : Perm V) :
    core (e.permCongrHom s) (e.permCongrHom M)=core s M :=
  congrArg _ (profile_congr _ _ _ _ e (fun x y => (reach_map_iff e s M x y).symm)).symm

/-- A physical rewire of the two selected labels, in arbitrary matching coordinates. -/
theorem child_core (e : (V×Bool) ≃ W) (s M : Perm W) (r : Perm V)
    (hs : e.permCongrHom (oriented 1)=s) (hm : e.permCongrHom (oriented r)=M)
    (a b : V) (d : Bool) :
    core s (rewire M (e (a,false),e (b,d))) =
    core (oriented 1) (rewire (oriented r) ((a,false),(b,d))) := by
  rw [←hs,←hm,←rewire_map]
  exact core_map ..

/-- The cut sum already uses the actual rewired matching on the left. -/
theorem actual_cut_profile_sum {R : Type*} [AddCommMonoid R]
    (e : (V×Bool) ≃ W) (s M : Perm W) (r : Perm V)
    (hs : e.permCongrHom (oriented 1)=s) (hm : e.permCongrHom (oriented r)=M)
    (a : V) (F : Multiset ℕ → R) :
    ∑ b ∈ cutPartners r a, F (core s (rewire M (e (a,false),e (b,false)))) =
    ∑ i ∈ Finset.Ico 1 (r.toList a).length,
      F (longPart i + longPart ((r.toList a).length-i) + ((r.cycleOf a)⁻¹*r).cycleType) := by
  simp_rw [child_core e s M r hs hm,rewire_same_color,core,oriented_core]
  exact cut_sum ..

/-- Every within-component opposite-colour swap, except the excluded standard
partner, retains the original profile. This includes a matching-edge swap. -/
theorem actual_flip_profile_sum {R : Type*} [AddCommMonoid R]
    (e : (V×Bool) ≃ W) (s M : Perm W) (r : Perm V)
    (hs : e.permCongrHom (oriented 1)=s) (hm : e.permCongrHom (oriented r)=M)
    (a : V) (F : Multiset ℕ → R) :
    ∑ b ∈ cutPartners r a, F (core s (rewire M (e (a,false),e (b,true)))) =
    ((r.toList a).length-1) • F (core s M) := by
  have eq0 : core s M = r.cycleType := by
    rw [←hs,←hm,core_map,core,oriented_core]
  have eq1 (b : V) (mem : b ∈ cutPartners r a) :
      core s (rewire M (e (a,false),e (b,true)))=core s M := by
    rw [child_core e s M r hs hm,eq0,core,same_profile_after_flip r
      ((mem_cutPartners r a b).mp mem).2,oriented_core]
  have card0 := Fintype.card_congr (cutIndex r a)
  simp only [Fintype.card_coe, Nat.card_Ico] at card0
  rw [←card0,←Finset.sum_const]
  exact Finset.sum_congr rfl (fun b hb => congrArg F (eq1 b hb))

/-- The unique correction uses index 1, including when L=2 and both children
are singletons. The standard pair is absent from the nontrivial profile. -/
theorem actual_correction_profile (e : (V×Bool) ≃ W) (s M : Perm W) (r : Perm V)
    (hs : e.permCongrHom (oriented 1)=s) (hm : e.permCongrHom (oriented r)=M)
    (a : V) (ha : a ∈ r.support) :
    core s (rewire M (e (a,false),M (s (e (a,false))))) =
    longPart ((r.toList a).length-1) + ((r.cycleOf a)⁻¹*r).cycleType := by
  have one : 1 < (r.toList a).length := Perm.two_le_length_toList_iff_mem_support.mpr ha
  have get : (r.toList a)[1]=r a := by simpa using r.getElem_toList a 1 one
  have ix : (r.toList a).idxOf (r a)=1 := by
    rw [←get]
    exact (r.nodup_toList a).idxOf_getElem 1 one
  have image : M (s (e (a,false)))=e (r a,false) := by simp [←hs,←hm]; rfl
  have same : r.SameCycle a (r a) := Perm.mem_toList_iff.mp (get ▸ List.getElem_mem one) |>.1
  rw [image,child_core e s M r hs hm,rewire_same_color,core,oriented_core,
    (split_types r (Perm.mem_support.mp ha).symm same).2,ix]
  simp [longPart]

#print axioms actual_cut_profile_sum
#print axioms actual_flip_profile_sum
#print axioms actual_correction_profile
end HalfWords
