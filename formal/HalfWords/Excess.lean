import HalfWords.StepCount
import HalfWords.Canonical

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords Hurwitz.WordWeights Hurwitz.Paths
variable {V : Type*} [Fintype V] [LinearOrder V]

omit [Fintype V] [LinearOrder V] in
private theorem inv_is_self {m : Perm V} (h : Function.Involutive m) : m⁻¹ = m := by
  ext x
  apply m.injective
  exact (m.apply_symm_apply x).trans (h x).symm

/-- An arbitrary word has nonnegative excess. At excess zero or one its
actual total Definition 4.1 charge is exactly that excess. -/
theorem word_excess (s M : Perm V) (hs : s⁻¹=s) (hm : M⁻¹=M)
    (ns : ∀x, s x ≠ x) (nm : ∀x, M x ≠ x)
    (xs : List (V×V)) (distinct : ∀ q ∈ xs, q.1 ≠ q.2) :
    let finish := componentCount s (execute M xs)
    let available := componentCount s M + xs.length
    finish ≤ available ∧ (available ≤ finish+1 → executionFlips s M xs + finish = available) := by
  induction xs generalizing M with
  | nil => simp [execute,executionFlips]
  | cons q xs ih =>
    rcases q with ⟨i,j⟩
    let q := (i,j)
    have mm (v : V) : M (M v) = v :=
      (congrArg (fun p : Perm V => p (M v)) hm.symm).trans (M.symm_apply_apply v)
    have good := rewire_preserves_matching M mm nm q
    have tail := ih (rewire M q) (inv_is_self good.1) good.2
      (fun p hp => distinct p (List.mem_cons_of_mem _ hp))
    have step := actual_step s M hs hm ns nm q.1 q.2 (distinct q List.mem_cons_self)
    dsimp only at tail ⊢
    change _ ≤ componentCount s M + (xs.length+1) ∧
      (_ → (Charge.flip s M q.1 q.2 + executionFlips s (rewire M q) xs) + _ = _)
    change componentCount s (execute (rewire M q) xs) ≤ _ ∧
      (componentCount s M + (xs.length+1) ≤ componentCount s (execute (rewire M q) xs)+1 →
      (Charge.flip s M q.1 q.2 + executionFlips s (rewire M q) xs) +
      componentCount s (execute (rewire M q) xs) = componentCount s M+(xs.length+1))
    rcases tail with ⟨bound,close⟩
    rcases step with ⟨_,charge,count⟩ | ⟨_,charge,count⟩ | ⟨_,count⟩
    · change componentCount s (rewire M q) = componentCount s M+1 at count
      exact ⟨by omega,fun h => by have e := close (by omega); omega⟩
    · change componentCount s (rewire M q) = componentCount s M at count
      exact ⟨by omega,fun h => by have e := close (by omega); omega⟩
    · change componentCount s (rewire M q) + 1 = componentCount s M at count
      exact ⟨by omega,fun h => by omega⟩

omit [Fintype V] [LinearOrder V] in
theorem onePart_count [Nonempty V] {s M : Perm V} (h : OnePart s M) : componentCount s M=1 := by
  let S := Relation.EqvGen.setoid (Charge.Edge s M)
  have sub : Subsingleton (Quotient S) := ⟨fun i j => Quotient.inductionOn₂ i j
    (fun a b => Quotient.sound (h a b))⟩
  let _ := sub
  exact Nat.card_eq_one_iff_unique.mpr ⟨sub,⟨Quotient.mk S (Classical.choice ‹Nonempty V›)⟩⟩

theorem standard_count (m : ℕ) : componentCount (standard m) (standard m)=m+1 := by
  let e : Quotient (Perm.SameCycle.setoid (1 : Perm (Fin (m+1)))) ≃ Fin (m+1) := by
    have S : Perm.SameCycle.setoid (1 : Perm (Fin (m+1))) = Setoid.ker id := by
      ext x y
      change (1: Perm (Fin (m+1))).SameCycle x y ↔ x=y
      simp [Perm.SameCycle]
    rw [S]
    exact Setoid.quotientKerEquivOfSurjective id Function.surjective_id
  have std : standard m=oriented (1 : Perm (Fin (m+1))) := by
    apply Equiv.ext
    rintro ⟨i,w⟩
    cases w <;> rfl
  rw [std, oriented_count]
  exact (Nat.card_congr e).trans (by simp)

#print axioms word_excess
#print axioms standard_count
end HalfWords
