import HalfWords.Flip

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords
variable {V W : Type*}

private theorem reach_map {s M : Perm V} (e : V ≃ W) {x y : V}
    (conn : Charge.Reach s M x y) :
    Charge.Reach (e.permCongrHom s) (e.permCongrHom M) (e x) (e y) := by
  induction conn with
  | rel x y h =>
    apply Relation.EqvGen.rel
    cases h with
    | inl f => exact Or.inl (by subst y; simp)
    | inr f => exact Or.inr (by subst y; simp)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih ik => exact .trans _ _ _ ih ik

theorem reach_map_iff (e : V ≃ W) (s M : Perm V) (x y : V) :
    Charge.Reach (e.permCongrHom s) (e.permCongrHom M) (e x) (e y) ↔
      Charge.Reach s M x y := by
  refine ⟨fun h => ?_,reach_map e⟩
  have inv (p : Perm V) : e.symm.permCongr (e.permCongr p) = p := by
    apply Equiv.ext
    intro v
    simp
  simpa [inv] using reach_map e.symm h

theorem rewire_map [DecidableEq V] [DecidableEq W] (e : V ≃ W) (M : Perm V) (a b : V) :
    e.permCongrHom (rewire M (a,b)) = rewire (e.permCongrHom M) (e a,e b) := by
  have h := swaps_relabel e [(a,b)]
  have sw : e.permCongrHom (swap a b) = swap (e a) (e b) := by
    simpa [Connectivity.swaps] using h.symm
  unfold rewire
  rw [map_mul,map_mul,map_inv,sw]

theorem canonical_flip_preserves_components [Fintype V] [LinearOrder V]
    (s M : Perm V) (hs : s⁻¹=s) (hm : M⁻¹=M)
    (ns : ∀x, s x ≠ x) (nm : ∀x, M x ≠ x) (a b : V)
    (ha : Charge.canonical s M a=false) (hb : Charge.canonical s M b=true)
    (conn : Charge.Reach s M a b) (x y : V) :
    Charge.flip s M a b = 1 ∧
    (Charge.Reach s (rewire M (a,b)) x y ↔ Charge.Reach s M x y) := by
  classical
  refine ⟨by simp [Charge.flip,ha,hb],?_⟩
  let col := Charge.canonical s M
  have valid := Charge.canonical_valid s M hs hm ns nm
  have ss (v : V) : s (s v) = v :=
    (congrArg (fun q : Perm V => q (s v)) hs.symm).trans (s.symm_apply_apply v)
  have mm (v : V) : M (M v) = v :=
    (congrArg (fun q : Perm V => q (M v)) hm.symm).trans (M.symm_apply_apply v)
  let e := chargedCoordinates s col valid.first ss
  let r := successor s M col valid.first valid.second ss mm
  have heM : e.permCongrHom (oriented r) = M := matching_coordinates ..
  have hes : e.permCongrHom (oriented (1: Perm {v // col v = false})) = s := by
    apply Equiv.ext
    intro v
    obtain ⟨⟨i,c⟩,rfl⟩ := e.surjective v
    change e (oriented 1 (e.symm (e (i,c)))) = s (e (i,c))
    rw [symm_apply_apply]
    cases c
    · rfl
    · exact (ss i).symm
  let ia : {v // col v=false} := ⟨a,ha⟩
  let ib : {v // col v=false} := ⟨s b,by simp [col,valid.first,hb]⟩
  have ea : e (ia,false) = a := rfl
  have eb : e (ib,true) = b := ss b
  have old (i j) := reach_map_iff e (oriented 1) (oriented r) i j
  simp only [hes,heM] at old
  have same : r.SameCycle ia ib := (oriented_reach_iff r (ia,false) (ib,true)).mp
    ((old _ _).mp (by simpa [ea,eb] using conn))
  obtain ⟨u,rfl⟩ := e.surjective x
  obtain ⟨v,rfl⟩ := e.surjective y
  have post := reach_map_iff e (oriented 1) (rewire (oriented r) ((ia,false),(ib,true))) u v
  rw [rewire_map,hes,heM,ea,eb] at post
  exact post.trans ((component_iff_after_flip same u v).trans (old _ _).symm)

#print axioms canonical_flip_preserves_components
end HalfWords
