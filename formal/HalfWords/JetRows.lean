import HalfWords.CutMultiplicity
import Mathlib.Algebra.DualNumber

namespace HalfWords
open scoped DualNumber
open TrivSqZeroExt
variable {R : Type*} [CommRing R]

/-- The degree-zero and degree-one columns together. Solving for the term
involving the current first column uses only ε²=0. -/
noncomputable def jetRow (t : R) : ℕ → DualNumber R
  | 0 => 1
  | 1 => 1
  | n+2 => (1+(n+1) • (ε : DualNumber R)) *
      ((∑ i : Fin (n+1), jetRow t (i.val+1) * jetRow t (n+1-i.val)) +
        inl (t-1)*jetRow t (n+1))
termination_by n => n
decreasing_by all_goals omega

theorem jet_one (t : R) : jetRow t 1 = 1 := by rw [jetRow]

def jetComponent (d : ℕ) : DualNumber R →+ R :=
  if d=0 then {toFun := fst,map_zero' := rfl,map_add' := fun _ _ => rfl} else {toFun := snd,map_zero' := rfl,map_add' := fun _ _ => rfl}

theorem component_inl_mul (t : R) (d : ℕ) (B : DualNumber R) :
    jetComponent d (inl t*B)=t*jetComponent d B := by
  cases d with
  | zero => rfl
  | succ d =>
    change (inl t * B : DualNumber R).snd = t*B.snd
    simp

theorem component_eps_mul (d : ℕ) (B : DualNumber R) :
    jetComponent d ((ε : DualNumber R)*B)=if d=0 then 0 else jetComponent 0 B := by
  cases d with
  | zero =>
    change ((ε : DualNumber R)*B).fst = 0
    simp
  | succ d =>
    change ((ε : DualNumber R)*B).snd = B.fst
    simp

theorem jet_recurrence (t : R) {L : ℕ} (hL : 2≤L) :
    jetRow t L = (∑ i ∈ Finset.Ico 1 L, jetRow t i*jetRow t (L-i)) +
      (L-1) • ((ε : DualNumber R)*jetRow t L) + inl (t-1)*jetRow t (L-1) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' hL
  have eqsum : (∑ i ∈ Finset.Ico 1 (n+2), jetRow t i * jetRow t (n+2-i)) =
      ∑ i : Fin (n+1), jetRow t (i.val+1) * jetRow t (n+1-i.val) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => jetRow t (i+1)*jetRow t (n+1-i))]
    apply Finset.sum_nbij' (fun j : ℕ => j-1) (fun j : ℕ => j+1)
    · intro j h; simp only [Finset.mem_Ico,Finset.mem_range] at *; omega
    · intro j h; simp only [Finset.mem_Ico,Finset.mem_range] at *; omega
    · intro j h; simp only [Finset.mem_Ico] at h; omega
    · intro j _; omega
    · intro j h
      obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp h
      congr 2 <;> omega
  rw [eqsum]
  have Lm : n+2-1=n+1 := by omega
  rw [Lm]
  set S := (∑ i : Fin (n+1), jetRow t (i.val+1) * jetRow t (n+1-i.val))
  have row : jetRow t (n+2) = (1 + (n+1) • (ε : DualNumber R))*(S+inl (t-1)*jetRow t (n+1)) := by rw [jetRow]
  rw [row]
  have vanish : (ε : DualNumber R)*((n+1) • ε)=0 := by
    rw [mul_smul_comm]; simp
  have cancel (A : DualNumber R) : ε*((1+(n+1) • ε)*A)=ε*A := by
    rw [←mul_assoc,mul_add,mul_one,vanish,add_zero]
  rw [cancel,add_mul,one_mul,smul_mul_assoc]
  abel

noncomputable def profileProduct (t : R) (p : Multiset ℕ) : DualNumber R := (p.map (jetRow t)).prod

theorem product_union (t : R) (p q : Multiset ℕ) :
    profileProduct t (p+q)=profileProduct t p * profileProduct t q := by
  simp [profileProduct]

theorem product_part (t : R) {n : ℕ} (hn : 1≤n) : profileProduct t (longPart n)=jetRow t n := by
  rcases hn.eq_or_lt with eq|hi
  · subst n; simp [profileProduct,longPart,jet_one]
  · simp [profileProduct,longPart,(show 2≤n by omega)]

#print axioms jet_recurrence
end HalfWords
