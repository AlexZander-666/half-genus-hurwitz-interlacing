import HalfWords.Profiles

namespace HalfWords
open Equiv
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def orbitFactor (r : Perm V) : Quotient (Perm.SameCycle.setoid r) → Perm V :=
  Quotient.lift (r.cycleOf ·) (fun _ _ h => h.cycleOf_eq)

theorem orbitSize_eq_one (r : Perm V) (q : Quotient (Perm.SameCycle.setoid r))
    (h : orbitFactor r q=1) : Nat.card {x // Quotient.mk _ x=q}=1 := by
  obtain ⟨v,rfl⟩ := Quotient.exists_rep q
  change r.cycleOf v=1 at h
  have fixed := (Perm.cycleOf_eq_one_iff r).mp h
  have uni (x : {x : V // Quotient.mk (Perm.SameCycle.setoid r) x=Quotient.mk _ v}) : x.val=v :=
    (show r.SameCycle x.val v from Quotient.exact x.property).eq_of_right fixed
  exact Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => Subtype.ext ((uni x).trans (uni y).symm)⟩,
    ⟨⟨v,rfl⟩⟩⟩

theorem orbitSize_eq_support (r : Perm V) (q : Quotient (Perm.SameCycle.setoid r))
    (h : orbitFactor r q≠1) :
    Nat.card {x // Quotient.mk _ x=q} = (orbitFactor r q).support.card := by
  obtain ⟨v,rfl⟩ := Quotient.exists_rep q
  change r.cycleOf v≠1 at h
  have fixed : r v ≠ v := fun e => h ((Perm.cycleOf_eq_one_iff r).mpr e)
  let eqv : {x : V // Quotient.mk (Perm.SameCycle.setoid r) x=Quotient.mk _ v} ≃
      (r.cycleOf v).support := Equiv.subtypeEquivRight (fun x => by
        rw [Quotient.eq]
        exact Perm.sameCycle_comm.trans (Perm.mem_support_cycleOf_iff' fixed).symm)
  have count : Nat.card (r.cycleOf v).support=(r.cycleOf v).support.card := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  exact (Nat.card_congr eqv).trans count

noncomputable def activeFactors (r : Perm V) :
    {q // orbitFactor r q ≠ 1} ≃ r.cycleFactorsFinset := by
  classical
  let f (q : {q // orbitFactor r q ≠ 1}) : r.cycleFactorsFinset :=
    ⟨orbitFactor r q.val,by
      obtain ⟨v,hv⟩ := Quotient.exists_rep q.val
      rw [← hv]
      apply Perm.cycleOf_ne_one_iff_mem_cycleFactorsFinset.mp
      change orbitFactor r (Quotient.mk _ v)≠1
      rw [hv]
      exact q.property⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨q,ha⟩ ⟨u,hb⟩ he
    obtain ⟨a,rfl⟩ := Quotient.exists_rep q
    obtain ⟨b,rfl⟩ := Quotient.exists_rep u
    have e : r.cycleOf a=r.cycleOf b := congrArg Subtype.val he
    apply Subtype.ext
    exact Quotient.sound ((Perm.sameCycle_iff_cycleOf_eq_of_mem_support
      (Perm.cycleOf_mem_cycleFactorsFinset_iff.mp (f ⟨_,ha⟩).property)
      (Perm.cycleOf_mem_cycleFactorsFinset_iff.mp (f ⟨_,hb⟩).property)).mpr e)
  · rintro ⟨g,hg⟩
    obtain ⟨v,hv⟩ := (Perm.mem_cycleFactorsFinset_iff.mp hg).1.nonempty_support
    have eq := Perm.cycle_is_cycleOf hv hg
    have ne : orbitFactor r (Quotient.mk _ v) ≠ 1 := by
      change r.cycleOf v ≠ 1
      rw [←eq]
      exact (Perm.mem_cycleFactorsFinset_iff.mp hg).1.ne_one
    exact ⟨⟨Quotient.mk _ v,ne⟩,Subtype.ext eq.symm⟩

theorem orbitSizes_filter (r : Perm V) :
    (sizes (Perm.SameCycle.setoid r)).filter (1<·) = r.cycleType := by
  classical
  let S := Perm.SameCycle.setoid r
  let _ := Fintype.ofFinite (Quotient S)
  let size (q : Quotient S) := Nat.card {x // Quotient.mk S x=q}
  have keep (q : Quotient S) : 1<size q ↔ orbitFactor r q≠1 := by
    by_cases h : orbitFactor r q=1
    · have eq : size q=1 := orbitSize_eq_one r q h
      rw [eq,h]; simp
    · have fac := (activeFactors r ⟨q,h⟩).property
      change orbitFactor r q ∈ r.cycleFactorsFinset at fac
      have eq : size q=(orbitFactor r q).support.card := orbitSize_eq_support r q h
      exact ⟨fun _ => h,fun _ => eq ▸ (Perm.mem_cycleFactorsFinset_iff.mp fac).1.two_le_card_support⟩
  change (sizes S).filter (1<·) = _
  dsimp only [sizes]
  rw [Multiset.filter_map]
  change Multiset.map size ((Finset.univ : Finset (Quotient S)).filter (fun q=>1<size q)).val = _
  have eqf : (Finset.univ : Finset (Quotient S)).filter (fun q=>1<size q) =
      Finset.univ.filter (fun q => orbitFactor r q≠1) := by ext; simp [keep]
  rw [eqf,← Finset.subtype_map, Finset.map_val,Multiset.map_map]
  rw [Perm.cycleType_def,← Finset.attach_map_val (s:=r.cycleFactorsFinset),Finset.map_val,Multiset.map_map]
  rw [← Finset.univ_eq_attach,← Finset.map_univ_equiv (activeFactors r),Finset.map_val,Multiset.map_map]
  apply Multiset.map_congr _ (fun q _ => orbitSize_eq_support r q.val q.property)
  simp

#print axioms orbitSizes_filter
end HalfWords
