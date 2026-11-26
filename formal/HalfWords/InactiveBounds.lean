import HalfWords.ActiveRecurrence
import HalfWords.Locality

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords Hurwitz.Paths Hurwitz.WordWeights

theorem reachable_from_paired {V : Type*} (s M : Perm V)
    (ss : Function.Involutive s) (mm : Function.Involutive M)
    {h v : V} (paired : M h=s h) (reach : Charge.Reach s M h v) :
    v=h ∨ v=s h := by
  let P (x : V) := x=h ∨ x=s h
  have preserved (f : Perm V) (inv : Function.Involutive f) (start : f h=s h)
      (x : V) : P x ↔ P (f x) := by
    have forward (z : V) : P z → P (f z) := by
      rintro (rfl|eq)
      · exact Or.inr start
      · rw [eq,← start]; exact Or.inl (inv h)
    exact ⟨forward x,fun e => inv x ▸ forward (f x) e⟩
  have along {x y : V} (conn : Charge.Reach s M x y) : P x ↔ P y := by
    induction conn with
    | rel x y edge => rcases edge with rfl|rfl; exact preserved s ss rfl x; exact preserved M mm paired x
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih jk => exact ih.trans jk
  exact (along reach).mp (Or.inl rfl)

/-- Every larger endpoint that actually appears was already unmatched in the
initial overlay. It suffices for every eligible pivot to be smaller than its
standard mate, as in the original adjacent-pair indexing. -/
theorem hive_initially_active {n d : ℕ} (s M : Perm (Fin n)) (hs : s⁻¹=s)
    (hm : M⁻¹=M) (ns : ∀v,s v≠v) (nm : ∀v,M v≠v)
    (std : ∀h : Fin n, h.val % 2=0 → h<s h)
    (bound : Option (Fin n)) (w : SuffixWords s 0 d M bound true)
    (budget : componentCount s M+d≤componentCount s s+1) :
    ∀ q ∈ w.val, M q.2 ≠ s q.2 := by
  obtain ⟨_,allow,fin,_⟩ := (fits_iff ..).mp w.property.2
  have cost : componentCount s M+w.val.length ≤ componentCount s (execute M w.val)+1 := by
    rw [fin,w.property.1]; exact budget
  have all := no_foreign_swap s M hs hm ns nm w.val
    (fun q h => (show q.1<q.2 from (allow q h).1.1).ne) cost
  have ss (v : Fin n) : s (s v) = v :=
    (congrArg (fun p : Perm (Fin n) => p (s v)) hs.symm).trans (s.symm_apply_apply v)
  have mm (v : Fin n) : M (M v) = v :=
    (congrArg (fun p : Perm (Fin n) => p (M v)) hm.symm).trans (M.symm_apply_apply v)
  intro q h paired
  have low : q.1<q.2 := (allow q h).1.1
  rcases reachable_from_paired s M ss mm paired (.symm _ _ (all q h)) with eq|eq
  · exact low.ne eq
  · exact (low.trans (std q.2 (allow q h).1.2)).ne eq

/-- All inactive higher hives may be suppressed simultaneously at excess at
most one without relabeling the state or changing any word weight. -/
theorem fresh_restrict {R : Type*} [CommSemiring R] {n : ℕ} (b t : R)
    (s M : Perm (Fin n)) (hs : s⁻¹=s) (hm : M⁻¹=M) (ns : ∀v,s v≠v) (nm : ∀v,M v≠v)
    (std : ∀h : Fin n, h.val % 2=0 → h<s h) (d : ℕ) (cap : Fin n)
    (budget : componentCount s M+d≤componentCount s s+1)
    (closed : ∀v : Fin n, cap<v → v.val%2=0 → M v=s v) :
    fresh b t s M d none = fresh b t s M d (some cap) := by
  let eqv : SuffixWords s 0 d M none true ≃ SuffixWords s 0 d M (some cap) true := {
    toFun w := ⟨w.val,w.property.1,by
      obtain ⟨ord,ok,fin,endp⟩ := (fits_iff ..).mp w.property.2
      refine (fits_iff ..).mpr ⟨ord,?_,fin,endp⟩
      intro q h
      exact ⟨(ok q h).1,le_of_not_gt fun gt =>
        hive_initially_active s M hs hm ns nm std none w budget q h (closed q.2 gt (ok q h).1.2)⟩⟩
    invFun w := ⟨w.val,w.property.1,by
      obtain ⟨ord,ok,fin,endp⟩ := (fits_iff ..).mp w.property.2
      exact (fits_iff ..).mpr ⟨ord,fun q h => ⟨(ok q h).1,trivial⟩,fin,endp⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact Fintype.sum_equiv eqv _ _ (fun _ => rfl)

#print axioms hive_initially_active
#print axioms fresh_restrict
end HalfWords
