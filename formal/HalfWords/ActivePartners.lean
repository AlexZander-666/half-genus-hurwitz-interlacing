import HalfWords.PivotProfile

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords
variable {V W : Type*}

/-- A standard matching edge is an entire component of the overlay. -/
theorem paired_iff_of_reach {s M : Perm W} (ss : Function.Involutive s)
    (mm : Function.Involutive M) {x y : W} (conn : Charge.Reach s M x y) :
    M x=s x ↔ M y=s y := by
  have along (z : W) : (M z=s z ↔ M (s z)=s (s z)) ∧
      (M z=s z ↔ M (M z)=s (M z)) := by
    constructor
    · rw [ss z]
      exact ⟨fun eq => eq ▸ mm z,fun eq => (mm (s z)).symm ▸ congrArg M eq.symm⟩
    · rw [mm z]
      exact ⟨fun eq => eq ▸ (ss z).symm,fun eq => (congrArg s eq).trans (ss _ ) |>.symm⟩
  induction conn with
  | rel x y h => rcases h with rfl|rfl; exact (along x).1; exact (along x).2
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih jk => exact ih.trans jk

theorem exposed_component_cap [LinearOrder W] {s M : Perm W} (ss : Function.Involutive s)
    (mm : Function.Involutive M) (h : W) (active : M h≠s h)
    (closed : ∀ y, s h < y → M y=s y) {v : W} (conn : Charge.Reach s M h v) :
    v ≤ s h := le_of_not_gt (fun gt => active ((paired_iff_of_reach ss mm conn).mpr (closed v gt)))

section
variable [Fintype V] [DecidableEq V] [Fintype W] [LinearOrder W]

omit [Fintype W] in
/-- The two colours indexed by proper cuts are exactly all lower labels in
the same component at an exposed adjacent pair. This identity is independent
of whether the orientation agrees with the numerical ordering of other labels. -/
theorem eligible_coordinates (e : V×Bool ≃ W) (s M : Perm W) (r : Perm V)
    (hs : e.permCongrHom (oriented 1)=s) (hm : e.permCongrHom (oriented r)=M)
    (a : V) (ord : e (a,false)<e (a,true))
    (adj : ∀v, v<e (a,true) → v≤e (a,false))
    (cap : ∀ v, Charge.Reach s M (e (a,false)) v → v≤e (a,true))
    (b : V) (d : Bool) :
    e (b,d)<e (a,false) ∧ Charge.Reach s M (e (a,false)) (e (b,d)) ↔
      b∈cutPartners r a := by
  have reach := reach_map_iff e (oriented 1) (oriented r) (a,false) (b,d)
  rw [hs,hm,oriented_reach_iff] at reach
  rw [mem_cutPartners,←reach]
  constructor
  · rintro ⟨less,conn⟩
    refine ⟨?_,conn⟩
    rintro rfl
    cases d
    · exact (lt_irrefl _) less
    · exact ord.not_gt less
  · rintro ⟨ne,conn⟩
    have diff (d' : Bool) : e (b,d) ≠ e (a,d') :=
      fun eq => ne (congrArg Prod.fst (e.injective eq)).symm
    exact ⟨lt_of_le_of_ne (adj _ (lt_of_le_of_ne (cap _ conn) (diff true))) (diff false),conn⟩

noncomputable def internalLabels (s M : Perm W) (h : W) : Finset W := by
  classical
  exact Finset.univ.filter fun v => v<h ∧ Charge.Reach s M h v

theorem sum_internal_labels {R : Type*} [AddCommMonoid R]
    (e : V×Bool ≃ W) (s M : Perm W) (r : Perm V)
    (hs : e.permCongrHom (oriented 1)=s) (hm : e.permCongrHom (oriented r)=M)
    (a : V) (ord : e (a,false)<e (a,true))
    (adj : ∀v, v<e (a,true) → v≤e (a,false))
    (cap : ∀ v, Charge.Reach s M (e (a,false)) v → v≤e (a,true))
    (F : W → R) :
    ∑ v ∈ internalLabels s M (e (a,false)), F v =
      (∑ b ∈ cutPartners r a, F (e (b,false))) + ∑ b ∈ cutPartners r a, F (e (b,true)) := by
  classical
  have id : internalLabels s M (e (a,false)) =
      ((cutPartners r a) ×ˢ (Finset.univ : Finset Bool)).map e.toEmbedding := by
    ext v
    obtain ⟨⟨b,d⟩,rfl⟩ := e.surjective v
    simpa [internalLabels] using eligible_coordinates e s M r hs hm a ord adj cap b d
  rw [id,Finset.sum_map,Finset.sum_product,←Finset.sum_add_distrib]
  simp [add_comm]
end

#print axioms sum_internal_labels
end HalfWords
