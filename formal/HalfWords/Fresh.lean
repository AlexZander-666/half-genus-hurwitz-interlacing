import HalfWords.Hive
import HalfWords.Canonical
import HalfWords.Skip

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords Hurwitz.WordWeights Hurwitz.Paths

private theorem not_top_iff {n : ℕ} (h : Fin n) (xs : List (Fin n × Fin n)) :
     h ∉ largerEndpoints xs ↔ ∀ a ∈ xs, a.2 ≠ h := by
  constructor
  · intro no a ha e
    exact no (List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,e⟩))
  · intro ok mem
    obtain ⟨a,ha,e⟩ := List.mem_map.mp (List.mem_toFinset.mp mem)
    exact ok a ha e

theorem reduced_bound {n : ℕ} (u h : Fin n) (gap : ∀ v : Fin n, v<h ↔ v≤u)
    (s M : Perm (Fin n)) (xs : List (Fin n × Fin n)) :
    Fits s 0 M (some u) true xs ↔ Fits s 0 M (some h) true xs ∧ h ∉ largerEndpoints xs := by
  rw [not_top_iff,fits_iff,fits_iff]
  constructor
  · rintro ⟨sorted,allow,last,joined⟩
    have below (a) (ha : a ∈ xs) := (gap a.2).mpr (allow a ha).2
    exact ⟨⟨sorted,fun a ha => ⟨(allow a ha).1,(below a ha).le⟩,last,joined⟩,
      fun a ha => (below a ha).ne⟩
  · rintro ⟨⟨sorted,allow,last,joined⟩,skip⟩
    exact ⟨sorted,fun a ha => ⟨(allow a ha).1,(gap a.2).mp
      (lt_of_le_of_ne (allow a ha).2 (skip a ha))⟩,last,joined⟩

def lowerBoundEquiv {n : ℕ} (u h : Fin n) (gap : ∀ v : Fin n, v<h ↔ v≤u)
    (s M : Perm (Fin n)) (r : ℕ) :
    SuffixWords s 0 r M (some u) true ≃
    {w : SuffixWords s 0 r M (some h) true // h ∉ largerEndpoints w.1} where
  toFun w := ⟨⟨w.val,w.property.1,((reduced_bound u h gap s M w.val).mp w.property.2).1⟩,
    ((reduced_bound u h gap s M w.val).mp w.property.2).2⟩
  invFun w := ⟨w.val.val,w.val.property.1,(reduced_bound u h gap s M w.val.val).mpr
    ⟨w.val.property.2,w.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A fresh upper endpoint contributes its hive weight on its first use. -/
noncomputable def fresh {R : Type*} [CommSemiring R] {n : ℕ} (b t : R)
    (s M : Perm (Fin n)) (r : ℕ) (h : Option (Fin n)) : R :=
  ∑ w : SuffixWords s 0 r M h true, b ^ executionFlips s M w.val * t ^ hive w.val

/-- Moving the bound to the preceding label identifies the skipped terms
exactly, including every zero-weight specialization. -/
theorem used_hive_lower {R : Type*} [CommRing R] {n : ℕ} (b t : R)
    (s M : Perm (Fin n)) (r : ℕ) (u h : Fin n) (gap : ∀ v : Fin n, v<h ↔ v≤u) :
    t * dp b t s 0 r M (some h) true =
      fresh b t s M r (some h) + (t-1)*fresh b t s M r (some u) := by
  classical
  rw [used_hive_sum]
  congr 2
  let f (w : SuffixWords s 0 r M (some h) true) := b ^ executionFlips s M w.val * t ^ hive w.val
  let p (w : SuffixWords s 0 r M (some h) true) := h ∉ largerEndpoints w.val
  let e := lowerBoundEquiv u h gap s M r
  change (∑ w, if h ∈ largerEndpoints w.val then 0 else f w) = _
  calc
    _ = ∑ w ∈ Finset.univ.filter p, f w := by rw [Finset.sum_filter]; simp [ite_not]
    _ = ∑ w : {w // p w}, f w.val := by
      rw [← Finset.sum_subtype_eq_sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext
      simp
    _ = fresh b t s M r (some u) := by
      unfold fresh
      exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

/-- First swap expansion of the actual fresh-endpoint sum. -/
theorem fresh_succ {R : Type*} [CommSemiring R] {n : ℕ} (b t : R)
    (s M : Perm (Fin n)) (r : ℕ) (last : Option (Fin n)) :
    fresh b t s M (r+1) last =
      ∑ a ∈ nextSteps last, (b ^ Charge.flip s M a.1 a.2 * t) *
        dp b t s 0 r (rewire M a) (some a.2) true := by
  classical
  conv_lhs => rw [fresh, ← (firstSplit s 0 r M last true).symm.sum_comp, Fintype.sum_sigma]
  conv_rhs => rw [← Finset.sum_coe_sort (nextSteps last)]
  apply Fintype.sum_congr
  intro a
  rw [← pathSum_eq_dp,pathSum,Finset.mul_sum]
  apply Fintype.sum_congr
  intro w
  change b ^ executionFlips s M (a.val :: w.val) * t ^ hive (a.val :: w.val) = _
  have sorted : Descending (a.val :: w.val) := ((fits_iff ..).mp
    (show Fits s 0 M last true (a.val :: w.val) from ⟨mem_nextSteps.mp a.property,w.property.2⟩)).1
  rw [← hiveFrom_none _ sorted]
  change suffixWeight b t s M none (a.val :: w.val) = _
  exact suffixWeight_cons b t s M none a.val w.val

/-- Original maximum-pivot recurrence before quotienting by alternating
component lengths. No division by t or choice of a numeric specialization. -/
theorem fresh_pivot {R : Type*} [CommRing R] {n : ℕ} (b t : R)
    (s M : Perm (Fin n)) (r : ℕ) (u h : Fin n) (gap : ∀ v : Fin n, v<h ↔ v≤u) :
    fresh b t s M (r+1) (some h) = fresh b t s M (r+1) (some u) +
      ∑ a ∈ (nextSteps (some h)).filter (fun a => a.2=h),
        b ^ Charge.flip s M a.1 a.2 *
          (fresh b t s (rewire M a) r (some h) + (t-1)*fresh b t s (rewire M a) r (some u)) := by
  classical
  rw [fresh_succ,fresh_succ]
  have split : nextSteps (some u) = (nextSteps (some h)).filter (fun a => a.2≠h) := by
    ext a
    simp only [Finset.mem_filter,mem_nextSteps]
    change (executionStep a ∧ a.2 ≤ u) ↔ (executionStep a ∧ a.2 ≤ h) ∧ a.2≠h
    rw [← gap]
    exact ⟨fun H => ⟨⟨H.1,H.2.le⟩,H.2.ne⟩, fun H => ⟨H.1.1,lt_of_le_of_ne H.1.2 H.2⟩⟩
  rw [split]
  let f (a : Fin n × Fin n) := (b ^ Charge.flip s M a.1 a.2 * t) *
        dp b t s 0 r (rewire M a) (some a.2) true
  have eq := Finset.sum_filter_add_sum_filter_not (nextSteps (some h)) (fun a => a.2=h) f
  rw [← eq,add_comm]
  apply congrArg (_ + ·)
  apply Finset.sum_congr rfl
  intro a ha
  have e := (Finset.mem_filter.mp ha).2
  change (b ^ Charge.flip s M a.1 a.2*t) * _ = _
  rw [mul_assoc]
  conv_lhs => arg 2; rw [e,used_hive_lower b t s (rewire M a) r u h gap]

theorem lower_empty_of_unmatched {R : Type*} [CommSemiring R] {n : ℕ} (b t : R)
    (s M : Perm (Fin n)) (r : ℕ) (u h : Fin n) (gap : ∀ v : Fin n, v<h ↔ v≤u)
    (ordered : h ≤ s h) (unmatched : M h ≠ s h) : fresh b t s M r (some u) = 0 := by
  classical
  let _ : IsEmpty (SuffixWords s 0 r M (some u) true) := ⟨fun w => by
    let v := lowerBoundEquiv u h gap s M r w
    exact unmatched (skipped_pair h ordered v.val v.property)⟩
  simp [fresh]

theorem raw_cyclic_eq_fresh {R : Type*} [CommSemiring R] (b t : R) (m r : ℕ) :
    let e := index m
    let s := e.permCongrHom (standard m)
    let a := e.permCongrHom (cyclic m)
    paperSum b t ((m+1)*2) s a r = fresh b t s a r none := by
  dsimp only
  rw [raw_cyclic_eq_dp, ← pathSum_eq_dp, pathSum, fresh]
  apply Fintype.sum_congr
  intro w
  exact congrArg (fun e : ℕ => b ^ executionFlips _ _ w.val * t ^ e)
    (hiveFrom_none _ ((fits_iff ..).mp w.property.2).1)

#print axioms raw_cyclic_eq_fresh
#print axioms lower_empty_of_unmatched
#print axioms fresh_pivot

#print axioms used_hive_lower
end HalfWords
