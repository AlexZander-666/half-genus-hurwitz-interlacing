import HalfWords.ActivePartners
import HalfWords.ZeroBudget

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords Hurwitz.WordWeights Hurwitz.Paths

theorem top_sum {R : Type*} [AddCommMonoid R] {n : ℕ} (h : Fin n)
    (even : h.val % 2=0) (F : Fin n × Fin n → R) :
    ∑ a ∈ (nextSteps (some h)).filter (fun a => a.2=h), F a =
    ∑ v ∈ Finset.Iio h, F (v,h) := by
  apply Finset.sum_nbij' Prod.fst (fun v => (v,h))
  · intro a ha
    obtain ⟨allow,e⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_Iio.mpr (e ▸ (mem_nextSteps.mp allow).1.1)
  · intro v hv
    exact Finset.mem_filter.mpr ⟨mem_nextSteps.mpr ⟨⟨(show v<h from Finset.mem_Iio.mp hv),even⟩,le_rfl⟩,rfl⟩
  · intro a ha
    exact Prod.ext rfl (Finset.mem_filter.mp ha).2.symm
  · intros; rfl
  · intro a ha
    exact congrArg F (Prod.ext rfl (Finset.mem_filter.mp ha).2)

/-- The true chronological word recursion at b=1, discarding every external
join by the one-half genus budget. Its correction never divides by t. -/
theorem active_recurrence {R : Type*} [CommRing R] {n : ℕ} (t : R)
    (s M : Perm (Fin n)) (r : ℕ) (u h : Fin n) (gap : ∀v : Fin n, v<h ↔ v≤u)
    (hs : s⁻¹=s) (hm : M⁻¹=M) (ns : ∀v,s v≠v) (nm : ∀v,M v≠v)
    (even : h.val%2=0) (ord : h<s h) (cap : M (s h) ≤ s h)
    (adj : ∀z,z<s h → z≤h) (active : M h≠s h)
    (budget : componentCount s M+(r+1)≤componentCount s s+1) :
    fresh 1 t s M (r+1) (some h) =
    (∑ v ∈ internalLabels s M h, fresh 1 t s (rewire M (h,v)) r (some h))+
    (t-1)*fresh 1 t s (rewire M (h,M (s h))) r (some u) := by
  classical
  rw [unmatched_pivot 1 t s M r u h gap hs hm ns nm even ord cap adj active,
    top_sum h even,rewire_comm M (M (s h)) h]
  congr 1
  simp only [one_pow,one_mul]
  conv_lhs => enter [2,v]; rw [rewire_comm M v h]
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro v hv
    simp [internalLabels] at hv
    exact Finset.mem_Iio.mpr hv.1
  · intro v hv
    obtain ⟨low,no⟩ := Finset.mem_sdiff.mp hv
    have lt := Finset.mem_Iio.mp low
    have conn : ¬ Charge.Reach s M h v := by simpa [internalLabels,lt] using no
    exact join_has_no_suffix 1 t s M hs hm ns nm h v lt.ne.symm conn r (some h) budget
  · intros; rfl

#print axioms active_recurrence
end HalfWords
