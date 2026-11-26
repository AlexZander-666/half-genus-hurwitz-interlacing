import HalfWords.Homogeneity
import HalfWords.Pivot

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords Hurwitz.WordWeights Hurwitz.Paths

theorem fresh_below_distance {R : Type*} [CommSemiring R] {n : ℕ} (b t : R)
    (s M : Perm (Fin n)) (hs : s⁻¹=s) (hm : M⁻¹=M) (ns : ∀v, s v≠v)
    (nm : ∀v, M v≠v) (r : ℕ) (bound : Option (Fin n))
    (small : componentCount s M+r < componentCount s s) : fresh b t s M r bound = 0 := by
  classical
  let _ : IsEmpty (SuffixWords s 0 r M bound true) := ⟨fun w => by
    obtain ⟨_,legal,fin,_⟩ := (fits_iff ..).mp w.property.2
    have h := (word_excess s M hs hm ns nm w.val (fun q hq =>
      (show q.1 < q.2 from (legal q hq).1.1).ne)).1
    rw [fin,w.property.1] at h
    omega⟩
  simp [fresh]

theorem fresh_at_budget {R : Type*} [CommSemiring R] {n : ℕ} (b t : R)
    (s M : Perm (Fin n)) (hs : s⁻¹=s) (hm : M⁻¹=M) (ns : ∀v, s v≠v)
    (nm : ∀v, M v≠v) (r d : ℕ) (bound : Option (Fin n)) (hd : d≤1)
    (time : componentCount s M+r = componentCount s s+d) :
    fresh b t s M r bound = b^d * fresh 1 t s M r bound := by
  classical
  rw [fresh,fresh,Finset.mul_sum]
  apply Fintype.sum_congr
  intro w
  obtain ⟨_,legal,fin,_⟩ := (fits_iff ..).mp w.property.2
  have budget := (word_excess s M hs hm ns nm w.val (fun q hq =>
    (show q.1 < q.2 from (legal q hq).1.1).ne)).2
  rw [fin,w.property.1] at budget
  have charge : executionFlips s M w.val=d := by have e := budget (by omega); omega
  simp [charge]

/-- In genus zero or one half, an actual join at the first step cannot give
any complete continuation, even if the earlier hive has already been used. -/
theorem join_has_no_suffix {R : Type*} [CommSemiring R] {n : ℕ} (b t : R)
    (s M : Perm (Fin n)) (hs : s⁻¹=s) (hm : M⁻¹=M) (ns : ∀v, s v≠v)
    (nm : ∀v, M v≠v) (a z : Fin n) (az : a≠z) (separate : ¬Charge.Reach s M a z)
    (r : ℕ) (bound : Option (Fin n)) (budget : componentCount s M+(r+1)≤componentCount s s+1) :
    fresh b t s (rewire M (a,z)) r bound = 0 := by
  have mm (v : Fin n) : M (M v) = v :=
    (congrArg (fun p : Perm (Fin n) => p (M v)) hm.symm).trans (M.symm_apply_apply v)
  have new := rewire_preserves_matching M mm nm (a,z)
  have inv : (rewire M (a,z))⁻¹=rewire M (a,z) := by
    apply Equiv.ext
    intro v
    apply (rewire M (a,z)).injective
    exact ((rewire M (a,z)).apply_symm_apply v).trans (new.1 v).symm
  apply fresh_below_distance b t s _ hs inv ns new.2
  rcases actual_step s M hs hm ns nm a z az with ⟨c,_,_⟩|⟨c,_,_⟩|⟨_,count⟩
  · exact (separate c).elim
  · exact (separate c).elim
  · omega

#print axioms join_has_no_suffix
#print axioms fresh_at_budget
end HalfWords
