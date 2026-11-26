import HalfGenus.Interlacing

namespace HalfGenus

open Polynomial Polynomial.Chebyshev

/-- Every adjacent pair has a strictly alternating string of all non-endpoint
zeros. Polynomials also split and are squarefree, including their endpoints. -/
theorem consecutive_differences {lam : ℝ} (hlam : 0 < lam) (d : ℕ) :
    ∃ (r : Fin d → ℝ) (s : Fin (d+1) → ℝ),
      (difference lam (d+2)).Splits ∧ (difference lam (d+3)).Splits ∧
      (difference lam (d+2)).roots.Nodup ∧ (difference lam (d+3)).roots.Nodup ∧
      (∀ i, r i ∈ Set.Ioo (node (d+2) (i.val+2)) (node (d+2) (i.val+1))) ∧
      (difference lam (d+2)).roots = (insert (-1) (insert 1 (Finset.univ.image r))).val ∧
      (∀ j, (difference lam (d+3)).eval (s j) = 0 ∧
        s j ∈ Set.Ioo (Fin.snoc (α:=fun _ => ℝ) r (-1) j) (Fin.cons (α:=fun _ => ℝ) 1 r j)) := by
  classical
  obtain ⟨r, loc, split, nodup, roots⟩ := complete_mesh hlam d
  obtain ⟨_, _, upper, simple, _⟩ := complete_mesh hlam (d+1)
  have zero (i : Fin d) : (difference lam (d+2)).eval (r i) = 0 := by
    apply (Polynomial.isRoot_of_mem_roots ?_)
    rw [roots]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem r (Finset.mem_univ i)))
  have gaps (j : Fin (d+1)) :
      ∃ z ∈ Set.Ioo (Fin.snoc (α:=fun _ => ℝ) r (-1) j) (Fin.cons (α:=fun _ => ℝ) 1 r j), (difference lam (d+3)).eval z = 0 := by
    cases d with
    | zero =>
      have H := interval_contains_root (m:=3) (i:=1) hlam (by omega) (by omega)
      obtain ⟨z,l,e⟩ := H
      have jz : j = 0 := Fin.ext (by omega)
      subst j
      refine ⟨z,?_,e⟩
      rw [show (0 : Fin 1) = Fin.last 0 from rfl, Fin.snoc_last]
      simpa using (show z ∈ Set.Ioo (-1:ℝ) 1 from
        ⟨(node_mem_Icc (n:=3) (i:=2)).1.trans_lt l.1,l.2.trans_le (node_mem_Icc (n:=3) (i:=1)).2⟩)
    | succ d =>
      by_cases h0 : j.val=0
      · have : j=0 := Fin.ext h0
        subst j
        simpa using first_gap (m:=d+3) hlam (by omega) (loc 0) (zero 0)
      · by_cases last : j.val=d+1
        · have : j=Fin.last (d+1) := Fin.ext last
          subst j
          have eq : Fin.last (d+1) = (Fin.last d).succ := rfl
          rw [Fin.snoc_last,eq,Fin.cons_succ]
          exact last_gap hlam d (loc (Fin.last d)) (zero (Fin.last d))
        · let i : Fin (d+1) := ⟨j.val-1,by omega⟩
          let a : Fin (d+1) := ⟨j.val,by omega⟩
          have eq₁ : j=a.castSucc := Fin.ext rfl
          have eq₂ : j=i.succ := Fin.ext (by dsimp [i]; omega)
          rw [eq₁,Fin.snoc_castSucc,← eq₁,eq₂,Fin.cons_succ]
          have h : a.val=i.val+1 := by dsimp [a,i]; omega
          have l := loc a
          simp only [h] at l
          exact middle_gap (i:=i.val+1) hlam (by omega) (by dsimp [i]; omega)
            l (loc i) (zero a) (zero i)
  choose s sl se using gaps
  exact ⟨r,s,split,upper,nodup,simple,loc,roots,fun j => ⟨se j,sl j⟩⟩

#print axioms consecutive_differences
end HalfGenus
