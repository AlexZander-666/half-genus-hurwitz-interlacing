import HalfWords.Mobius

namespace HalfWords
open Polynomial Polynomial.Chebyshev Real HalfGenus

private theorem saturate {d : ℕ} (b : ℝ) (r : Fin d → ℝ)
    (anti : StrictAnti r) (neg : ∀i,r i<0)
    (eqs : ∀i,(hurwitzPolynomial b (d+1)).eval (r i)=0) (nz : hurwitzPolynomial b (d+1) ≠0) :
    let P := hurwitzPolynomial b (d+1)
    P.natDegree=d+1 ∧ P.Splits ∧ P.roots.Nodup ∧
    P.roots=(insert 0 (Finset.univ.image r)).val := by
  classical
  let P := hurwitzPolynomial b (d+1)
  let S := insert (0:ℝ) (Finset.univ.image r)
  have absent : (0:ℝ)∉Finset.univ.image r := by simpa using (fun i => (neg i).ne)
  have count : S.card=d+1 := by
    rw [show S=insert (0:ℝ) (Finset.univ.image r) from rfl,Finset.card_insert_of_notMem absent,
      Finset.card_image_of_injective _ anti.injective,Finset.card_univ,Fintype.card_fin]
  have incl : S.val ≤ P.roots := by
    apply Finset.val_le_iff_val_subset.mpr
    intro z hz
    apply (Polynomial.mem_roots nz).mpr
    rcases Finset.mem_insert.mp (show z∈insert 0 (Finset.univ.image r) from hz) with h|h
    · exact h ▸ zero_hurwitz b _
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
      exact eqs i
  have hd : P.natDegree ≤ d+1 := degree_hurwitz b _
  have eq := Multiset.eq_of_le_of_card_le incl ((Polynomial.card_roots' _).trans (hd.trans_eq count.symm))
  have deg : P.natDegree=d+1 := hd.antisymm (count ▸ (show S.card≤P.natDegree from
    ((congrArg Multiset.card eq).trans_le (Polynomial.card_roots' _))))
  exact ⟨deg,Polynomial.splits_iff_card_roots.mpr (eq ▸ count.trans deg.symm),
    eq ▸ S.nodup,eq.symm⟩

private theorem true_nonzero {b : ℝ} (hb : b≠0) (d : ℕ) : hurwitzPolynomial b (d+1) ≠ 0 := by
  let x := node (d+2) 1
  have inside : x∈Set.Ioo (-1:ℝ) 1 := by
    constructor
    · simpa only [x,node_eq_neg_one (by omega : d+2≠0)] using
        (node_lt (n:=d+2) (i:=1) (j:=d+2) (by omega) (by omega))
    · simpa only [x,node_eq_one] using
        (node_lt (n:=d+2) (i:=0) (j:=1) (by omega) (by omega))
  intro no
  have zero := (pullback_zero hb inside (d+1)).mp (by rw [no,eval_zero])
  have sign := difference_node_sign (m:=d+2) (i:=1) (by norm_num : (0:ℝ)<1/2) (by omega) (by omega)
  change (difference (1/2) (d+2)).eval x=0 at zero
  change 0<(-1:ℝ)^1*(difference (1/2) (d+2)).eval x at sign
  rw [zero,mul_zero] at sign
  exact lt_irrefl _ sign

/-- Genuine genus-one-half Coulter–Do one-part polynomials of degrees d+2
and d+3, for every nonzero real b. The displayed lists contain every negative
root in decreasing order. Each polynomial also has one simple root at zero.
This includes d=0, when the shorter list of negative roots is empty. -/
theorem hurwitz_consecutive {b : ℝ} (hb : b≠0) (d : ℕ) :
    let P := hurwitzPolynomial b (d+1)
    let Q := hurwitzPolynomial b (d+2)
    ∃ (r : Fin d → ℝ) (s : Fin (d+1) → ℝ),
      (∀i,r i<0) ∧ (∀j,s j<0) ∧ StrictAnti r ∧ StrictAnti s ∧
      (∀i,s i.succ<r i ∧ r i<s i.castSucc) ∧
      P.natDegree=d+1 ∧ P.Splits ∧ P.roots.Nodup ∧ P.roots=(insert 0 (Finset.univ.image r)).val ∧
      Q.natDegree=d+2 ∧ Q.Splits ∧ Q.roots.Nodup ∧ Q.roots=(insert 0 (Finset.univ.image s)).val := by
  classical
  obtain ⟨r,s,_,_,_,_,loc,roots,other⟩ := consecutive_differences (by norm_num : (0:ℝ)<1/2) d
  have inside (i : Fin d) : r i∈Set.Ioo (-1:ℝ) 1 := by
    constructor
    · exact (show -1 < node (d+2) (i.val+2) by
        simpa only [node_eq_neg_one (by omega : d+2≠0)] using
          (node_lt (n:=d+2) (i:=i.val+2) (j:=d+2) (by omega) (by omega))).trans (loc i).1
    · exact (loc i).2.trans (by simpa only [node_eq_one] using
        (node_lt (n:=d+2) (i:=0) (j:=i.val+1) (by omega) (by omega)))
  have alt (i : Fin d) : s i.succ<r i ∧ r i<s i.castSucc := by
    exact ⟨by simpa only [Fin.cons_succ] using (other i.succ).2.2,
      by simpa only [Fin.snoc_castSucc] using (other i.castSucc).2.1⟩
  have si (j : Fin (d+1)) : s j∈Set.Ioo (-1:ℝ) 1 := by
    constructor
    · refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [Fin.snoc_last] using (other (Fin.last d)).2.1
      · exact (inside i).1.trans (alt i).2
    · refine Fin.cases ?_ (fun i => ?_) j
      · simpa only [Fin.cons_zero] using (other 0).2.2
      · exact (alt i).1.trans (inside i).2
  let R (i : Fin d) := pull (r i)
  let S (j : Fin (d+1)) := pull (s j)
  have ar (i : Fin d) : S i.succ<R i ∧ R i<S i.castSucc :=
    ⟨pull_lt (si _).1 (inside _).1 (alt i).1,pull_lt (inside _).1 (si _).1 (alt i).2⟩
  have antiS : StrictAnti S := Fin.strictAnti_iff_succ_lt.mpr (fun i => (ar i).1.trans (ar i).2)
  have antiR : StrictAnti R := by
    intro i j lt
    have le : i.succ≤j.castSucc := by change i.val+1≤j.val; exact lt
    exact (ar j).2.trans (lt_of_le_of_lt (antiS.antitone le) (ar i).1)
  have rz (i : Fin d) : (hurwitzPolynomial b (d+1)).eval (R i)=0 := by
    apply (pullback_zero hb (inside i) _).mpr
    apply isRoot_of_mem_roots
    rw [roots]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem r (Finset.mem_univ _)))
  have sz (j : Fin (d+1)) : (hurwitzPolynomial b (d+2)).eval (S j)=0 :=
    (pullback_zero hb (si j) _).mpr (other j).1
  have rn (i) : R i<0 := pull_negative (inside i)
  have sn (j) : S j<0 := pull_negative (si j)
  obtain ⟨de,sp,nd,rs⟩ := saturate b R antiR rn rz (true_nonzero hb d)
  exact ⟨R,S,rn,sn,antiR,antiS,ar,de,sp,nd,rs,saturate b S antiS sn sz (true_nonzero hb (d+1))⟩

#print axioms hurwitz_consecutive
end HalfWords
