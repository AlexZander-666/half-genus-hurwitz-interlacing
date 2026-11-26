import HalfWords.PivotCoordinates

namespace HalfWords
open Equiv Hurwitz.MatchingWords
variable {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]

theorem mapped_counts (e : V×Bool ≃ W) (s M : Perm W) (r : Perm V)
    (hs : e.permCongrHom (oriented 1)=s) (hm : e.permCongrHom (oriented r)=M)
    (a b : V) (mem : b∈cutPartners r a) :
    componentCount s (rewire M (e (a,false),e (b,false))) = componentCount s M+1 ∧
    componentCount s (rewire M (e (a,false),e (b,true))) = componentCount s M := by
  obtain ⟨ne,conn⟩ := (mem_cutPartners r a b).mp mem
  have init : componentCount s M=orbitCount r := by rw [←hs,←hm,count_map,oriented_count]
  have child (d : Bool) :
      componentCount s (rewire M (e (a,false),e (b,d)))=
      componentCount (oriented 1) (rewire (oriented r) ((a,false),(b,d))) := by
    rw [←hs,←hm,←rewire_map,count_map]
  rw [child,child,init,rewire_same_color,oriented_count]
  refine ⟨(orbitCount_cut r ne conn).symm,?_⟩
  rcases coordinate_step r a b true (by simp) with ⟨_,z,_⟩|⟨_,_,h⟩|⟨no,_⟩
  · contradiction
  · exact h
  · exact (no conn).elim

theorem mapped_correction_count (e : V×Bool ≃ W) (s M : Perm W) (r : Perm V)
    (hs : e.permCongrHom (oriented 1)=s) (hm : e.permCongrHom (oriented r)=M)
    (a : V) (ha : a∈r.support) :
    componentCount s (rewire M (e (a,false),M (s (e (a,false))))) = componentCount s M+1 := by
  have mem := (mem_cutPartners r a (r a)).mpr
    ⟨(Perm.mem_support.mp ha).symm,r.sameCycle_apply_right.mpr Perm.SameCycle.rfl⟩
  have eq : M (s (e (a,false)))=e (r a,false) := by simp [←hs,←hm]; rfl
  rw [eq]
  exact (mapped_counts e s M r hs hm a _ mem).1

#print axioms mapped_counts
end HalfWords
