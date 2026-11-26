import HalfWords.OriginalCorollary

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords Hurwitz.WordWeights Hurwitz.Paths Polynomial

/-- Connected genus-one-half raw hive polynomial for the length m+1 profile.
The original Hurwitz row divides the raw word sum by m+1. -/
noncomputable def rawPolynomial (b : ℝ) (m : ℕ) : ℝ[X] :=
  paperSum (C b) X ((m+1)*2) (originalStandard m) (originalInput m) (m+1)

noncomputable def hurwitzPolynomial (b : ℝ) (m : ℕ) : ℝ[X] :=
  C (((m:ℝ)+1)⁻¹)*rawPolynomial b m

theorem eval_raw (b x : ℝ) (m : ℕ) :
    (rawPolynomial b m).eval x =
      paperSum b x ((m+1)*2) (originalStandard m) (originalInput m) (m+1) := by
  simp [rawPolynomial,paperSum,eval_finsetSum]

theorem eval_hurwitz (b x : ℝ) (m : ℕ) :
    (hurwitzPolynomial b m).eval x = b/((m:ℝ)+1)*(jetRow x (m+1)).snd := by
  rw [hurwitzPolynomial,eval_mul,eval_C,eval_raw,original_half]; ring

theorem hive_bound {m : ℕ} (xs : List (Fin ((m+1)*2) × Fin ((m+1)*2)))
    (legal : ∀q∈xs,executionStep q) : hive xs ≤ m := by
  let End := (xs.map Prod.snd).toFinset
  have prop (v : Fin ((m+1)*2)) (hv : v∈End) : v.val%2=0 ∧ 0<v.val := by
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    have H := legal q hq
    exact ⟨H.2,lt_of_le_of_lt (Nat.zero_le q.1.val) H.1⟩
  have inj : Set.InjOn (fun v : Fin ((m+1)*2) => v.val/2-1) End := by
    intro v hv w hw eq
    have h := prop v hv
    have j := prop w hw
    apply Fin.ext
    change v.val/2-1=w.val/2-1 at eq
    omega
  have into : Set.MapsTo (fun v : Fin ((m+1)*2) => v.val/2-1) End (Finset.range m) := by
    intro v hv
    have h := prop v hv
    have top := v.isLt
    apply Finset.mem_range.mpr; change v.val/2-1 < m; omega
  have q := Finset.card_le_card_of_injOn _ into inj
  simpa only [hive,End,Finset.card_range] using q

theorem degree_raw (b : ℝ) (m : ℕ) : (rawPolynomial b m).natDegree ≤ m := by
  rw [rawPolynomial,raw_cyclic_eq_fresh,fresh]
  apply natDegree_sum_le_of_forall_le
  intro w _
  have legal := ((fits_iff ..).mp w.property.2).2.1
  calc _ ≤ ((C b)^executionFlips (originalStandard m) (originalInput m) w.val).natDegree+
          (X^hive w.val : ℝ[X]).natDegree := natDegree_mul_le
       _ ≤ m := by rw [←C_pow,natDegree_C,natDegree_X_pow,zero_add]; exact hive_bound _ (fun q h => (legal q h).1)

theorem degree_hurwitz (b : ℝ) (m : ℕ) : (hurwitzPolynomial b m).natDegree ≤ m := by
  exact (natDegree_C_mul_le _ _).trans (degree_raw b m)

theorem zero_hurwitz (b : ℝ) (m : ℕ) : (hurwitzPolynomial b m).eval 0=0 := by
  rw [hurwitzPolynomial,eval_mul,eval_C,eval_raw,raw_cyclic_eq_fresh,fresh]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro w _
  have nz : hive w.val ≠0 := by
    intro z
    have nil : w.val=[] := by
      simpa [hive] using z
    have len := w.property.1
    rw [nil] at len
    contradiction
  simp [zero_pow nz]

#print axioms degree_hurwitz
#print axioms eval_hurwitz
end HalfWords
