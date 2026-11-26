import Hurwitz.Paths

namespace HalfWords

open Equiv Hurwitz Hurwitz.MatchingWords Hurwitz.WordWeights Hurwitz.Paths

/-- One exact weight relation on actual bounded legal chronological words. -/
theorem used_hive_word {R : Type*} [CommRing R] {n : ℕ} (b t : R)
    (s m : Perm (Fin n)) (h : Fin n) (xs : List (Fin n × Fin n))
    (sorted : Descending xs) (bound : ∀ a ∈ xs, Below (some h) a) :
    t * suffixWeight b t s m (some h) xs =
      b ^ executionFlips s m xs * t ^ hive xs +
      (t-1) * (if h ∈ largerEndpoints xs then 0 else b ^ executionFlips s m xs * t ^ hive xs) := by
  rw [suffixWeight,hiveFrom_eq_card (some h) xs sorted bound]
  simp only [seen,Finset.sdiff_singleton_eq_erase]
  change t * (b ^ executionFlips s m xs * t ^ ((largerEndpoints xs).erase h).card) =
    b ^ executionFlips s m xs * t ^ (largerEndpoints xs).card +
    (t-1) * (if h ∈ largerEndpoints xs then 0 else b ^ executionFlips s m xs * t ^ (largerEndpoints xs).card)
  by_cases mem : h ∈ largerEndpoints xs
  · rw [if_pos mem,← Finset.card_erase_add_one mem,pow_succ]
    ring
  · rw [if_neg mem,Finset.erase_eq_of_notMem mem]
    ring

/-- The residual-word formula holds at any current maximum h, including at t=0.
The rightmost sum counts words which skip that hive. -/
theorem used_hive_sum {R : Type*} [CommRing R] {n : ℕ} (b t : R)
    (s m : Perm (Fin n)) (h : Fin n) (r : ℕ) :
    t * dp b t s 0 r m (some h) true =
      (∑ w : SuffixWords s 0 r m (some h) true, b ^ executionFlips s m w.val * t ^ hive w.val) +
      (t-1) * ∑ w : SuffixWords s 0 r m (some h) true,
        if h ∈ largerEndpoints w.val then 0 else b ^ executionFlips s m w.val * t ^ hive w.val := by
  rw [← pathSum_eq_dp, pathSum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro w
  obtain ⟨sorted,leg,_⟩ := (fits_iff ..).mp w.property.2
  exact used_hive_word b t s m h w.val sorted (fun a ha => (leg a ha).2)

#print axioms used_hive_word
#print axioms used_hive_sum

end HalfWords
