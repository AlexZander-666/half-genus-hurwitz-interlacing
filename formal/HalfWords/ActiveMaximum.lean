import HalfWords.InactiveBounds

namespace HalfWords
open Equiv Hurwitz
variable {m : ℕ}

theorem original_even_step (v : Fin ((m+1)*2)) (hv : v.val%2=0) :
    (originalStandard m v).val=v.val+1 := by
  obtain ⟨⟨i,d⟩,rfl⟩ := (index m).surjective v
  cases d with
  | false =>
    change ((index m).permCongr (standard m) ((index m) (i,false))).val = _
    rw [Equiv.permCongr_apply,Equiv.symm_apply_apply]
    change 1+2*i.val=0+2*i.val+1
    omega
  | true =>
    change (1+2*i.val)%2=0 at hv
    omega

theorem original_odd_step (v : Fin ((m+1)*2)) (hv : v.val%2≠0) :
    v.val = (originalStandard m v).val+1 ∧ (originalStandard m v).val%2=0 := by
  obtain ⟨⟨i,d⟩,rfl⟩ := (index m).surjective v
  cases d with
  | true =>
    have dst : originalStandard m ((index m) (i,true))=(index m) (i,false) := by
      change ((index m).permCongr (standard m)) _ = _
      rw [Equiv.permCongr_apply,Equiv.symm_apply_apply]; rfl
    rw [dst]
    change 1+2*i.val=0+2*i.val+1 ∧ (0+2*i.val)%2=0
    omega
  | false => change (0+2*i.val)%2≠0 at hv; omega

/-- A nonstandard physical matching has a highest unmatched eligible pivot.
The entire suffix above its partner is already paired, and the pivot cannot
be the very first label: the exposed active component has at least two pairs. -/
theorem active_max {M : Perm (Fin ((m+1)*2))} (hm : Function.Involutive M)
    (nm : ∀v,M v≠v) (nonstd : M≠originalStandard m) :
    ∃h : Fin ((m+1)*2), h.val%2=0 ∧ M h≠originalStandard m h ∧ 0<h.val ∧
      ∀v : Fin ((m+1)*2), originalStandard m h<v → M v=originalStandard m v := by
  classical
  let s := originalStandard m
  have ss (v : Fin ((m+1)*2)) : s (s v)=v := by
    obtain ⟨⟨i,d⟩,rfl⟩ := (index m).surjective v
    cases d <;> simp [s,originalStandard,standard]
  let live := Finset.univ.filter fun v : Fin ((m+1)*2) => M v≠s v ∧ v.val%2=0
  have below (v : Fin ((m+1)*2)) (bad : M v≠s v) :
      ∃h∈live, v=h ∨ v=s h := by
    by_cases ev : v.val%2=0
    · exact ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,bad,ev⟩,Or.inl rfl⟩
    · have low := original_odd_step v ev
      have other : M (s v)≠s (s v) := by
        intro good
        rw [ss] at good
        exact bad ((congrArg M good).symm.trans (hm _))
      exact ⟨s v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,other,low.2⟩,Or.inr (ss v).symm⟩
  have existsBad : ∃v,M v≠s v := by
    by_contra! all
    exact nonstd (Equiv.ext all)
  obtain ⟨v,hv⟩ := existsBad
  obtain ⟨v,hv,_⟩ := below v hv
  let h := live.max' ⟨v,hv⟩
  obtain ⟨bad,even⟩ := (Finset.mem_filter.mp (live.max'_mem ⟨v,hv⟩)).2
  change M h≠s h at bad
  change h.val%2=0 at even
  have mx (z)(hz : z ∈ live) : z≤h := live.le_max' _ hz
  have paired (z : Fin ((m+1)*2)) (above : s h<z) : M z=s z := by
    by_contra un
    obtain ⟨w,hw,eq|eq⟩ := below z un
    all_goals have le := show w.val≤h.val from mx w hw
    · have hs0 := original_even_step h even
      change (s h).val = _ at hs0
      subst z
      change (s h).val<w.val at above
      omega
    · have hs0 := original_even_step h even
      have hw0 := original_even_step w (Finset.mem_filter.mp hw).2.2
      subst z
      change (s h).val<(s w).val at above
      change (s h).val = _ at hs0
      change (s w).val = _ at hw0
      omega
  refine ⟨h,even,bad,?_,paired⟩
  have cap : M (s h) ≤ s h := by
    by_contra! gt
    have good := paired _ gt
    rw [hm] at good
    have eq : h=M (s h) := (ss h).symm.trans ((congrArg s good).trans (ss _))
    exact bad ((congrArg M eq).trans (hm _))
  have no : M (s h)≠h := fun eq => bad ((congrArg M eq).symm.trans (hm _))
  have hi : (M (s h)).val < (s h).val := (show M (s h) < s h from lt_of_le_of_ne cap (nm _))
  have sep : (M (s h)).val ≠ h.val := fun eq => no (Fin.ext eq)
  have hs0 := original_even_step h even
  change (s h).val = _ at hs0
  omega

#print axioms active_max
end HalfWords
