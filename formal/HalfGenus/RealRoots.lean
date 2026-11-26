import HalfGenus.Mesh
import Mathlib.Algebra.Polynomial.Splits

namespace HalfGenus

open Polynomial Polynomial.Chebyshev

/-- Complete multiset of simple roots, with one interior root per consecutive
pair of non-endpoint Chebyshev extrema. The cases m=2,3 are included. -/
theorem complete_mesh {lam : ℝ} (hlam : 0 < lam) (d : ℕ) :
    ∃ r : Fin d → ℝ,
      (∀ i, r i ∈ Set.Ioo (node (d+2) (i.val+2)) (node (d+2) (i.val+1))) ∧
      (difference lam (d+2)).Splits ∧
      (difference lam (d+2)).roots.Nodup ∧
      (difference lam (d+2)).roots =
        (insert (-1) (insert 1 (Finset.univ.image r))).val := by
  classical
  have choice (i : Fin d) := interval_contains_root (m:=d+2) (i:=i.val+1)
    hlam (by omega) (by omega)
  choose r loc zero using choice
  refine ⟨r,loc,?_⟩
  let D := difference lam (d+2)
  let S := insert (-1:ℝ) (insert 1 (Finset.univ.image r))
  have lt_node (i : Fin d) : r i < 1 :=
    (loc i).2.trans (by simpa only [node_eq_one] using
      (node_lt (n:=d+2) (i:=0) (j:=i.val+1) (by omega) (by omega)))
  have gt_node (i : Fin d) : -1 < r i :=
    lt_trans (by simpa only [node_eq_neg_one (show d+2 ≠ 0 by omega)] using
      (node_lt (n:=d+2) (i:=i.val+2) (j:=d+2) (by omega) (by omega))) (loc i).1
  have anti : StrictAnti r := by
    intro i j hij
    have h : i.val+2 ≤ j.val+1 := by change i.val < j.val at hij; omega
    have b : node (d+2) (j.val+1) ≤ node (d+2) (i.val+2) := by
      rcases eq_or_lt_of_le h with e | e
      · rw [e]
      · exact (node_lt (by omega) e).le
    exact (loc j).2.trans (b.trans_lt (loc i).1)
  have menu : (1:ℝ) ∉ Finset.univ.image r := by
    simpa using (fun i => (lt_node i).ne)
  have menv : (-1:ℝ) ∉ Finset.univ.image r := by
    simpa using (fun i => (gt_node i).ne')
  have cs : S.card = d+2 := by
    have mt : (-1:ℝ) ∉ insert 1 (Finset.univ.image r) := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨by norm_num,menv⟩
    dsimp only [S]
    rw [Finset.card_insert_of_notMem mt,Finset.card_insert_of_notMem menu,
      Finset.card_image_of_injective _ anti.injective,Finset.card_univ,Fintype.card_fin]
  have nzero : D ≠ 0 := by
    intro h
    have hsign := difference_node_sign (m:=d+2) (i:=1) hlam (by omega) (by omega)
    change 0 < (-1:ℝ)^1 * D.eval _ at hsign
    simp [h] at hsign
  have incl : S.val ≤ D.roots := by
    apply Finset.val_le_iff_val_subset.mpr
    intro x hx
    apply (Polynomial.mem_roots nzero).mpr
    change D.eval x = 0
    obtain hx | hx | hx : x = -1 ∨ x = 1 ∨ x ∈ Finset.univ.image r := by
      simpa only [S, Finset.mem_val, Finset.mem_insert] using hx
    · exact hx ▸ (difference_endpoints hlam (d+2)).1
    · exact hx ▸ (difference_endpoints hlam (d+2)).2
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact zero i
  have hd : D.natDegree ≤ d+2 := by
    apply (natDegree_sub_le ..).trans
    apply max_le _ (normalized_natDegree_le ..)
    rw [natDegree_T]
    exact le_rfl
  have eq : S.val = D.roots := Multiset.eq_of_le_of_card_le incl
    ((Polynomial.card_roots' _).trans (hd.trans_eq cs.symm))
  have hs : D.Splits := Polynomial.splits_iff_card_roots.mpr (le_antisymm
    (Polynomial.card_roots' _) (hd.trans_eq (cs.symm.trans (congrArg Multiset.card eq))))
  exact ⟨hs,eq ▸ S.nodup, eq.symm⟩

#print axioms complete_mesh

end HalfGenus
