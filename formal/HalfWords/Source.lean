import Hurwitz.Paths

namespace HalfWords

open Equiv Hurwitz Hurwitz.Connectivity Hurwitz.MatchingWords Hurwitz.WordWeights Hurwitz.Paths

/-- A one-part overlay has exactly one orbit under its two colored edges. -/
def OnePart {V : Type*} (s m : Perm V) : Prop :=
  ∀ x y, Charge.Reach s m x y

/-- For a one-part input, the connectedness test follows from the terminal
condition for the actual word, at every word length. -/
theorem endpoint_connected {V : Type*} [DecidableEq V] {s m : Perm V}
    (connected : OnePart s m) {xs : List (V × V)} (endpt : execute m xs = s) :
    MulAction.IsPretransitive (generated s xs) V := by
  let H := generated s xs
  have hs : s ∈ H := Subgroup.subset_closure (List.mem_cons_self ..)
  let g := (swaps xs.reverse).prod
  have hg : g ∈ H := by
    apply H.list_prod_mem
    intro q hq
    apply Subgroup.subset_closure
    apply List.mem_cons_of_mem
    simpa [swaps] using hq
  have hm : m ∈ H := by
    have he : g*m*g⁻¹ = s := (execute_eq_conj m xs).symm.trans endpt
    have h := H.mul_mem (H.mul_mem (H.inv_mem hg) hs) hg
    rw [← he] at h
    simpa [mul_assoc] using h
  have move {x y : V} (reach : Charge.Reach s m x y) : CanMove H x y := by
    induction reach with
    | rel a b edge =>
      rcases edge with eq | eq
      · exact ⟨s,hs,eq⟩
      · exact ⟨m,hm,eq⟩
    | refl a => exact ⟨1,H.one_mem,rfl⟩
    | symm _ _ _ ih =>
      obtain ⟨p,hp,rfl⟩ := ih
      exact ⟨p⁻¹,H.inv_mem hp,p.symm_apply_apply _⟩
    | trans _ _ _ _ _ ih ik =>
      obtain ⟨p,hp,rfl⟩ := ih
      obtain ⟨q,hq,rfl⟩ := ik
      exact ⟨q*p,H.mul_mem hq hp,rfl⟩
  constructor
  intro x y
  obtain ⟨p,hp,hy⟩ := move (connected x y)
  exact ⟨⟨p,hp⟩,hy⟩

theorem onePart_accepts {n : ℕ} {s m : Perm (Fin n)} (h : OnePart s m)
    (r : ℕ) (xs : List (Fin n × Fin n)) :
    PaperAccepts ((paperLabelEquiv n).permCongrHom s) ((paperLabelEquiv n).permCongrHom m)
      r (paperOrder n xs) ↔ xs.length = r ∧ Fits s 0 m none true xs := by
  rw [PaperAccepts,paperOrder_length,paperOrder_pairwise_iff,paperOrder_steps_iff,
    paperOrder_endpoint_iff,paperOrder_connected_iff,fits_iff]
  simp only [Allowed, Below, Option.elim_none, and_true, true_or, Descending]
  exact ⟨fun H => ⟨H.1,H.2.1,H.2.2.1,H.2.2.2.1⟩,
    fun H => ⟨H.1,H.2.1,H.2.2.1,H.2.2.2,endpoint_connected h H.2.2.2⟩⟩

/-- At any one-part input this is the genuine connected Proposition 4.18
sum, read as a recurrence over all endpoint-valid chronological words. -/
theorem onePart_raw_eq_dp {R : Type*} [CommSemiring R] (b t : R)
    {n : ℕ} {s m : Perm (Fin n)} (h : OnePart s m) (r : ℕ) :
    paperSum b t n s m r = dp b t s 0 r m none true := by
  let e : SuffixWords s 0 r m none true ≃
      PaperWords n ((paperLabelEquiv n).permCongrHom s) ((paperLabelEquiv n).permCongrHom m) r :=
    (paperOrder n).subtypeEquiv fun xs => (onePart_accepts h r xs).symm
  rw [← pathSum_eq_dp]
  unfold paperSum pathSum
  rw [← e.sum_comp]
  apply Fintype.sum_congr
  intro w
  change _ ^ paperFlips _ _ (paperOrder n w.val) * t ^ hive (paperOrder n w.val) = _
  rw [paperOrder_weight, suffixWeight, hiveFrom_none w.val ((fits_iff ..).mp w.property.2).1]

#print axioms endpoint_connected
#print axioms onePart_raw_eq_dp
end HalfWords
