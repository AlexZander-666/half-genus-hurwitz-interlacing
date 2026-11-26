import Hurwitz.WordWeights

/-! A first-step recurrence for the weighted sum over bounded execution words. -/

namespace Hurwitz.Paths

open Equiv MatchingWords WordWeights
open scoped BigOperators

variable {n : ℕ}

/-- The previous larger endpoint is an inclusive upper bound. An empty
prefix has no bound and no previously counted endpoint. -/
def Below (last : Option (Fin n)) (a : Fin n × Fin n) : Prop :=
  last.elim True (fun j ↦ a.2 ≤ j)

def Allowed (last : Option (Fin n)) (a : Fin n × Fin n) : Prop :=
  executionStep a ∧ Below last a

instance (last : Option (Fin n)) : DecidablePred (Allowed last) := fun a ↦ by
  cases last with
  | none => exact inferInstanceAs (Decidable ((a.1.val < a.2.val ∧ a.2.val % 2 = 0) ∧ True))
  | some j => exact inferInstanceAs (Decidable ((a.1.val < a.2.val ∧ a.2.val % 2 = 0) ∧ a.2 ≤ j))

def nextSteps (last : Option (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (Allowed last)

@[simp] theorem mem_nextSteps {last : Option (Fin n)} {a : Fin n × Fin n} :
    a ∈ nextSteps last ↔ Allowed last a := by
  simp [nextSteps]

def crossing (cutoff : ℕ) (a : Fin n × Fin n) : Bool :=
  decide (a.1.val < cutoff) != decide (a.2.val < cutoff)

theorem crosses_cons (cutoff : ℕ) (a : Fin n × Fin n) (xs : List (Fin n × Fin n)) :
    crosses cutoff (a :: xs) ↔ crossing cutoff a = true ∨ crosses cutoff xs := by
  constructor
  · rintro ⟨z,hz,hcross⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · exact Or.inl (by simpa [crossing] using hcross)
    · exact Or.inr ⟨z,hz,hcross⟩
  · rintro (ha | ⟨z,hz,hcross⟩)
    · exact ⟨a,List.mem_cons_self,by simpa [crossing] using ha⟩
    · exact ⟨z,List.mem_cons_of_mem _ hz,hcross⟩

/-- Acceptance of a suffix from the specified current matching and prefix data. -/
def Fits (s : Perm (Fin n)) (cutoff : ℕ) :
    Perm (Fin n) → Option (Fin n) → Bool → List (Fin n × Fin n) → Prop
  | m, _, joined, [] => m = s ∧ joined = true
  | m, last, joined, a :: xs =>
      Allowed last a ∧ Fits s cutoff (rewire m a) (some a.2) (joined || crossing cutoff a) xs

def Descending (xs : List (Fin n × Fin n)) : Prop :=
  xs.Pairwise (fun a b ↦ b.2 ≤ a.2)

theorem fits_iff (s : Perm (Fin n)) (cutoff : ℕ) (m : Perm (Fin n)) (last : Option (Fin n))
    (joined : Bool) (xs : List (Fin n × Fin n)) :
    Fits s cutoff m last joined xs ↔
      Descending xs ∧ (∀ a ∈ xs, Allowed last a) ∧ execute m xs = s ∧
        (joined = true ∨ crosses cutoff xs) := by
  induction xs generalizing m last joined with
  | nil => simp [Fits, Descending, execute, crosses]
  | cons a xs ih =>
    rw [Fits, ih, crosses_cons]
    simp only [Descending, List.pairwise_cons, Bool.or_eq_true]
    change Allowed last a ∧
      (xs.Pairwise (fun a b ↦ b.2 ≤ a.2) ∧ (∀ z ∈ xs, Allowed (some a.2) z) ∧
        execute (rewire m a) xs = s ∧
        ((joined = true ∨ crossing cutoff a = true) ∨ crosses cutoff xs)) ↔ _
    constructor
    · rintro ⟨ha,hm,ht,he,hj⟩
      have hb (z) (hz : z ∈ xs) : z.2 ≤ a.2 := (ht z hz).2
      refine ⟨⟨hb,hm⟩,?_,he,or_assoc.mp hj⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ha
      · refine ⟨(ht z hz).1,?_⟩
        cases last with
        | none => trivial
        | some j => exact (hb z hz).trans ha.2
    · rintro ⟨⟨hb,hm⟩,ha,he,hj⟩
      refine ⟨ha a List.mem_cons_self,hm,?_,he,or_assoc.mpr hj⟩
      intro z hz
      exact ⟨(ha z (List.mem_cons_of_mem _ hz)).1,hb z hz⟩

theorem executionAccepts_iff_fits (s m : Perm (Fin n)) (cutoff r : ℕ)
    (xs : List (Fin n × Fin n)) :
    ExecutionAccepts s m cutoff r xs ↔ xs.length = r ∧ Fits s cutoff m none false xs := by
  rw [fits_iff]
  simp [ExecutionAccepts, Descending, Allowed, Below]

/-- Count the changes of larger endpoint in the suffix, including its first
endpoint exactly when it differs from the previous one. -/
def hiveFrom : Option (Fin n) → List (Fin n × Fin n) → ℕ
  | _, [] => 0
  | last, a :: xs => (if last = some a.2 then 0 else 1) + hiveFrom (some a.2) xs

def largerEndpoints (xs : List (Fin n × Fin n)) : Finset (Fin n) :=
  (xs.map Prod.snd).toFinset

def seen : Option (Fin n) → Finset (Fin n)
  | none => ∅
  | some j => {j}

theorem hiveFrom_eq_card (last : Option (Fin n)) (xs : List (Fin n × Fin n))
    (hmono : Descending xs) (hbound : ∀ a ∈ xs, Below last a) :
    hiveFrom last xs = (largerEndpoints xs \ seen last).card := by
  induction xs generalizing last with
  | nil => simp [hiveFrom, largerEndpoints]
  | cons a xs ih =>
    obtain ⟨hb,hm⟩ := List.pairwise_cons.mp hmono
    have hea : a.2 ∈ insert a.2 (largerEndpoints xs) := Finset.mem_insert_self _ _
    have hcard := Finset.card_erase_add_one hea
    rw [Finset.erase_insert_eq_erase] at hcard
    rw [hiveFrom, ih (some a.2) hm (fun z hz ↦ hb z hz)]
    have he : largerEndpoints (a :: xs) = insert a.2 (largerEndpoints xs) := by
      simp [largerEndpoints]
    rw [he]
    cases last with
    | none =>
      simpa [seen, Finset.sdiff_singleton_eq_erase, Nat.add_comm] using hcard
    | some j =>
      by_cases hj : j = a.2
      · subst j
        simp [seen, Finset.sdiff_singleton_eq_erase, Finset.erase_insert_eq_erase]
      · have haj : a.2 < j := lt_of_le_of_ne (hbound a List.mem_cons_self) (Ne.symm hj)
        have hnot : j ∉ insert a.2 (largerEndpoints xs) := by
          intro hjm
          rcases Finset.mem_insert.mp hjm with h | hjm
          · exact hj h
          · obtain ⟨z,hz,hzj⟩ := List.mem_map.mp (List.mem_toFinset.mp hjm)
            exact (not_lt_of_ge (hzj ▸ hb z hz)) haj
        have herase : (insert a.2 (largerEndpoints xs)).erase j =
            insert a.2 (largerEndpoints xs) := Finset.erase_eq_of_notMem hnot
        simpa [hj, seen, Finset.sdiff_singleton_eq_erase, herase, Nat.add_comm] using hcard

theorem hiveFrom_none (xs : List (Fin n × Fin n)) (h : Descending xs) :
    hiveFrom none xs = hive xs := by
  rw [hiveFrom_eq_card none xs h (fun _ _ ↦ trivial)]
  simp [hive, largerEndpoints, seen]

abbrev SuffixWords (s : Perm (Fin n)) (cutoff r : ℕ) (m : Perm (Fin n))
    (last : Option (Fin n)) (joined : Bool) :=
  {xs : List (Fin n × Fin n) // xs.length = r ∧ Fits s cutoff m last joined xs}

noncomputable instance (s : Perm (Fin n)) (cutoff r : ℕ) (m : Perm (Fin n))
    (last : Option (Fin n)) (joined : Bool) : Fintype (SuffixWords s cutoff r m last joined) := by
  let code (w : SuffixWords s cutoff r m last joined) : List.Vector (Fin n × Fin n) r :=
    ⟨w.val, w.property.1⟩
  letI : Finite (SuffixWords s cutoff r m last joined) :=
    Finite.of_injective code
      (fun _ _ h ↦ Subtype.ext (congrArg (fun v : List.Vector (Fin n × Fin n) r ↦ v.val) h))
  exact Fintype.ofFinite _

/-- Splitting an accepted nonempty suffix by its first swap has an explicit
inverse given by prepending that same swap. -/
def firstSplit (s : Perm (Fin n)) (cutoff r : ℕ) (m : Perm (Fin n))
    (last : Option (Fin n)) (joined : Bool) :
    SuffixWords s cutoff (r+1) m last joined ≃
      Σ a : nextSteps last, SuffixWords s cutoff r (rewire m a.val)
        (some a.val.2) (joined || crossing cutoff a.val) where
  toFun w := by
    obtain ⟨xs,hl,hf⟩ := w
    cases xs with
    | nil => simp at hl
    | cons a xs =>
      exact ⟨⟨a,mem_nextSteps.mpr hf.1⟩,⟨xs,Nat.succ.inj hl,hf.2⟩⟩
  invFun w :=
    ⟨w.1.val :: w.2.val, by simp [w.2.property.1],
      ⟨mem_nextSteps.mp w.1.property,w.2.property.2⟩⟩
  left_inv w := by
    obtain ⟨xs,hl,hf⟩ := w
    cases xs with
    | nil => simp at hl
    | cons a xs => rfl
  right_inv w := by
    obtain ⟨⟨a,ha⟩,⟨xs,hl,hf⟩⟩ := w
    rfl

section Weighted

variable {R : Type*} [CommSemiring R]

def stepWeight (b u : R) (s m : Perm (Fin n)) (last : Option (Fin n)) (a : Fin n × Fin n) : R :=
  b ^ Charge.flip s m a.1 a.2 * (if last = some a.2 then 1 else u)

def suffixWeight (b u : R) (s m : Perm (Fin n)) (last : Option (Fin n)) (xs : List (Fin n × Fin n)) : R :=
  b ^ executionFlips s m xs * u ^ hiveFrom last xs

theorem suffixWeight_cons (b u : R) (s m : Perm (Fin n)) (last : Option (Fin n))
    (a : Fin n × Fin n) (xs : List (Fin n × Fin n)) :
    suffixWeight b u s m last (a :: xs) =
      stepWeight b u s m last a * suffixWeight b u s (rewire m a) (some a.2) xs := by
  by_cases ha : last = some a.2 <;>
    simp [suffixWeight, stepWeight, executionFlips, hiveFrom, ha, pow_add,
      mul_assoc, mul_left_comm, mul_comm]

/-- The recurrence on a fixed vertex set. Its state is the remaining length,
current matching, previous upper endpoint and whether a crossing has occurred. -/
def dp (b u : R) (s : Perm (Fin n)) (cutoff : ℕ) :
    ℕ → Perm (Fin n) → Option (Fin n) → Bool → R
  | 0, m, _, joined => if m = s ∧ joined = true then 1 else 0
  | r+1, m, last, joined =>
      ∑ a ∈ nextSteps last, stepWeight b u s m last a *
        dp b u s cutoff r (rewire m a) (some a.2) (joined || crossing cutoff a)

theorem dp_zero (b u : R) (s m : Perm (Fin n)) (cutoff : ℕ)
    (last : Option (Fin n)) (joined : Bool) :
    dp b u s cutoff 0 m last joined = (if m = s ∧ joined = true then 1 else 0) := rfl

theorem dp_succ (b u : R) (s m : Perm (Fin n)) (cutoff r : ℕ)
    (last : Option (Fin n)) (joined : Bool) :
    dp b u s cutoff (r+1) m last joined =
      ∑ a ∈ nextSteps last, stepWeight b u s m last a *
        dp b u s cutoff r (rewire m a) (some a.2) (joined || crossing cutoff a) := rfl

noncomputable def pathSum (b u : R) (s : Perm (Fin n)) (cutoff r : ℕ) (m : Perm (Fin n))
    (last : Option (Fin n)) (joined : Bool) : R :=
  ∑ w : SuffixWords s cutoff r m last joined, suffixWeight b u s m last w.val

theorem pathSum_zero (b u : R) (s m : Perm (Fin n)) (cutoff : ℕ)
    (last : Option (Fin n)) (joined : Bool) :
    pathSum b u s cutoff 0 m last joined = (if m = s ∧ joined = true then 1 else 0) := by
  classical
  by_cases ht : m = s ∧ joined = true
  · let w : SuffixWords s cutoff 0 m last joined := ⟨[],rfl,ht⟩
    rw [pathSum, if_pos ht, Finset.sum_eq_single w]
    · simp [w, suffixWeight, executionFlips, hiveFrom]
    · intro v _ hv
      have hnil : v.val = [] := List.length_eq_zero_iff.mp v.property.1
      exact (hv (Subtype.ext hnil)).elim
    · simp
  · have hempty : IsEmpty (SuffixWords s cutoff 0 m last joined) := ⟨fun w ↦ by
      have hnil : w.val = [] := List.length_eq_zero_iff.mp w.property.1
      exact ht (by simpa only [hnil, Fits] using w.property.2)⟩
    simp [pathSum, ht]

theorem pathSum_succ (b u : R) (s m : Perm (Fin n)) (cutoff r : ℕ)
    (last : Option (Fin n)) (joined : Bool) :
    pathSum b u s cutoff (r+1) m last joined =
      ∑ a ∈ nextSteps last, stepWeight b u s m last a *
        pathSum b u s cutoff r (rewire m a) (some a.2) (joined || crossing cutoff a) := by
  conv_lhs =>
    rw [pathSum, ← (firstSplit s cutoff r m last joined).symm.sum_comp, Fintype.sum_sigma]
  conv_rhs => rw [← Finset.sum_coe_sort (nextSteps last)]
  apply Fintype.sum_congr
  intro a
  rw [pathSum, Finset.mul_sum]
  apply Fintype.sum_congr
  intro w
  exact suffixWeight_cons b u s m last a.val w.val

/-- All accepted suffixes, with their prefix-adjusted hive weights, are counted
exactly once by the recurrence. -/
theorem pathSum_eq_dp (b u : R) (s : Perm (Fin n)) (cutoff r : ℕ) (m : Perm (Fin n))
    (last : Option (Fin n)) (joined : Bool) :
    pathSum b u s cutoff r m last joined = dp b u s cutoff r m last joined := by
  induction r generalizing m last joined with
  | zero => rw [pathSum_zero, dp_zero]
  | succ r ih =>
    rw [pathSum_succ, dp_succ]
    exact Finset.sum_congr rfl fun a _ ↦ congrArg (stepWeight b u s m last a * ·) (ih _ _ _)

theorem execSum_eq_dp (b u : R) (n : ℕ) (s m : Perm (Fin n)) (cutoff r : ℕ) :
    execSum b u n s m cutoff r = dp b u s cutoff r m none false := by
  let e : ExecWords n s m cutoff r ≃ SuffixWords s cutoff r m none false :=
    Equiv.subtypeEquivRight (executionAccepts_iff_fits s m cutoff r)
  rw [← pathSum_eq_dp]
  unfold execSum pathSum
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hm : Descending w.val := w.property.2.1
  change _ = suffixWeight b u s m none w.val
  rw [suffixWeight, hiveFrom_none _ hm]

theorem raw32_eq_dp (b u : R) :
    paperSum b u 10 Connectivity.std5 Connectivity.mat5 9 =
      dp b u Connectivity.std5 6 9 Connectivity.mat5 none false :=
  (raw32_eq_exec b u).trans (execSum_eq_dp b u 10 _ _ 6 9)

theorem raw42_eq_dp (b u : R) :
    paperSum b u 12 Connectivity.std6 Connectivity.mat6 10 =
      dp b u Connectivity.std6 8 10 Connectivity.mat6 none false :=
  (raw42_eq_exec b u).trans (execSum_eq_dp b u 12 _ _ 8 10)

end Weighted

end Hurwitz.Paths
