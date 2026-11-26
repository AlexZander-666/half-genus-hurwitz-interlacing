import HalfWords.Hive

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords Hurwitz.WordWeights Hurwitz.Paths

/-- A chronological word which avoids two vertices preserves the indicator
that they are matched. Its other edges can be arbitrary. -/
theorem avoided_pair {V : Type*} [DecidableEq V] (M : Perm V) (x y : V)
    (xs : List (V × V)) (miss : ∀ a ∈ xs, x ≠ a.1 ∧ x ≠ a.2 ∧ y ≠ a.1 ∧ y ≠ a.2) :
    execute M xs x = y ↔ M x = y := by
  induction xs generalizing M with
  | nil => rfl
  | cons v vs ih =>
    have hv := miss v List.mem_cons_self
    change execute (rewire M v) vs x = y ↔ M x=y
    rw [ih _ (fun a ha => miss a (List.mem_cons_of_mem _ ha)),rewire_apply,
      Equiv.swap_apply_of_ne_of_ne hv.1 hv.2.1, Equiv.swap_apply_eq_iff,
      Equiv.swap_apply_of_ne_of_ne hv.2.2.1 hv.2.2.2]

/-- On the original suffix-word space, a missing upper hive leaves its
standard pair already matched before the word starts. -/
theorem skipped_pair {n r : ℕ} {s M : Perm (Fin n)} (h : Fin n) (hs : h ≤ s h)
    (w : SuffixWords s 0 r M (some h) true) (skip : h ∉ largerEndpoints w.val) :
    M h = s h := by
  obtain ⟨_,allowed,endpoint,_⟩ := (fits_iff ..).mp w.property.2
  have avoid : ∀ a ∈ w.val, h ≠ a.1 ∧ h ≠ a.2 ∧ s h ≠ a.1 ∧ s h ≠ a.2 := by
    intro a ha
    have lower : a.1 < a.2 := (allowed a ha).1.1
    have top : a.2 ≤ h := (allowed a ha).2
    have no : a.2 ≠ h := fun he => skip (by
      apply List.mem_toFinset.mpr
      exact List.mem_map.mpr ⟨a,ha,he⟩)
    have le := lt_of_le_of_ne top no
    exact ⟨(lower.trans le).ne.symm, le.ne.symm,
      ((lower.trans le).trans_le hs).ne.symm,(le.trans_le hs).ne.symm⟩
  exact (avoided_pair M h (s h) w.val avoid).mp (by rw [endpoint])

theorem no_skip_correction {R : Type*} [CommRing R] {n r : ℕ} (b t : R)
    (s M : Perm (Fin n)) (h : Fin n) (hs : h ≤ s h) (different : M h ≠ s h) :
    t * dp b t s 0 r M (some h) true =
      ∑ w : SuffixWords s 0 r M (some h) true, b ^ executionFlips s M w.val * t ^ hive w.val := by
  rw [used_hive_sum]
  have z (w : SuffixWords s 0 r M (some h) true) : h ∈ largerEndpoints w.val :=
    by_contra fun miss => different (skipped_pair h hs w miss)
  simp [z]

#print axioms skipped_pair
#print axioms no_skip_correction
end HalfWords
