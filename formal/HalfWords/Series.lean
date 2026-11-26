import HalfWords.OriginalCorollary
import Mathlib.RingTheory.PowerSeries.Derivative

namespace HalfWords
open scoped DualNumber
open PowerSeries TrivSqZeroExt
variable {R : Type*} [CommRing R]

noncomputable def jetSeries (t : R) : PowerSeries (DualNumber R) :=
  mk fun j => if j=0 then 0 else jetRow t j

@[simp] theorem coeff_jet (t : R) (j : ℕ) : coeff j (jetSeries t)=if j=0 then 0 else jetRow t j :=
  coeff_mk ..

theorem coeff_shift {S : Type*} [CommRing S] (B : PowerSeries S) (j : ℕ) :
    coeff (j+1) (X*B)=coeff j B := by simpa only [pow_one] using coeff_X_pow_mul B 1 j

theorem coeff_convolution (t : R) (n : ℕ) :
    coeff n (jetSeries t * jetSeries t) =
      ∑ i ∈ Finset.Ico 1 n, jetRow t i * jetRow t (n-i) := by
  classical
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (jetSeries t)*coeff j (jetSeries t))]
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro i hi; simp only [Finset.mem_Ico,Finset.mem_range] at *; omega
  · intro i hi
    simp only [Finset.mem_sdiff,Finset.mem_range,Finset.mem_Ico] at hi
    by_cases zero : i=0
    · simp [zero]
    · have eq : n-i=0 := by omega
      simp [eq]
  · intro i hi
    obtain ⟨lo,up⟩ := Finset.mem_Ico.mp hi
    simp [show i≠0 by omega,show n-i≠0 by omega]

/-- All genus-zero and genus-one-half one-part word recurrences simultaneously,
as one identity in formal power series over the ring of dual numbers. -/
theorem jet_series_equation (t : R) :
    let J := jetSeries t
    J=X + J*J + C (inl (t-1))*(X*J) + C (ε : DualNumber R)*
      (X*(derivative (DualNumber R) J)-J) := by
  dsimp only
  ext n : 1
  simp only [map_add,coeff_C_mul,map_sub,coeff_convolution,coeff_jet,coeff_X]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_shift,coeff_shift,coeff_derivative,coeff_jet,coeff_jet]
    cases n with
    | zero => simp [jet_one]
    | succ n =>
      simp only [Nat.succ_ne_zero,if_false,
        show n+1≠0 by omega,show n+1+1≠1 by omega,zero_add]
      have H := jet_recurrence t (by omega : 2≤n+2)
      have mm : n+2-1=n+1 := by omega
      rw [mm] at H
      convert H using 1
      rw [nsmul_eq_mul]
      push_cast
      ring
#print axioms jet_series_equation
end HalfWords
