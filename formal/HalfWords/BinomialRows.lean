import HalfWords.CoefficientRecurrence
import Mathlib.Data.Nat.Choose.Basic

namespace HalfWords
open Polynomial

noncomputable def finiteRow (n : ℕ) (f : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range (n+1), C (f j)*X^j

noncomputable def evenBinom (n : ℕ) := finiteRow n (fun j => ((2*n).choose (2*j) : ℝ))
noncomputable def squareBinom (n : ℕ) := finiteRow n (fun j => (n.choose j : ℝ)^2)

theorem finiteRow_coeff (n : ℕ) (f : ℕ→ℝ) (support : ∀ j, n<j → f j=0) (j : ℕ) :
    (finiteRow n f).coeff j=f j := by
  rw [finiteRow,finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases h : j≤n
  · simp [Finset.mem_range.mpr (show j<n+1 by omega)]
  · simp [show j∉Finset.range (n+1) by simp; omega,support j (by omega)]

theorem even_coeff (n j : ℕ) : (evenBinom n).coeff j=((2*n).choose (2*j) : ℝ) :=
  finiteRow_coeff n _ (fun i hi => by rw [Nat.choose_eq_zero_of_lt (by omega : 2*n<2*i)]; simp) j

theorem square_coeff (n j : ℕ) : (squareBinom n).coeff j=(n.choose j : ℝ)^2 :=
  finiteRow_coeff n _ (fun i hi => by simp [Nat.choose_eq_zero_of_lt hi]) j

/-- Signed adjacency identity for the extended-by-zero binomial row. -/
theorem neighboring_choose (n j : ℕ) :
    ((j:ℝ)+1)*(n.choose (j+1):ℝ)=((n:ℝ)-j)*(n.choose j:ℝ) := by
  by_cases hj : j≤n
  · have h := congrArg (fun v : ℕ => (v:ℝ)) (Nat.choose_succ_right_eq n j)
    push_cast [Nat.cast_sub hj] at h
    linarith
  · rw [Nat.choose_eq_zero_of_lt (by omega : n<j+1),Nat.choose_eq_zero_of_lt (by omega : n<j)]
    simp

theorem choose_square_local (n j : ℕ) :
    ((n:ℝ)+2)*((n+2).choose (j+2):ℝ)^2 =
      (2*n+3)*(((n+1).choose (j+2):ℝ)^2+((n+1).choose (j+1):ℝ)^2)-
      (n+1)*((n.choose (j+2):ℝ)^2-2*(n.choose (j+1):ℝ)^2+(n.choose j:ℝ)^2) := by
  let A : ℝ := n.choose j
  let B : ℝ := n.choose (j+1)
  let D : ℝ := n.choose (j+2)
  have f : ((j:ℝ)+1)*B=((n:ℝ)-j)*A := neighboring_choose n j
  have g : ((j:ℝ)+2)*D=((n:ℝ)-j-1)*B := by
    have h := neighboring_choose n (j+1)
    push_cast at h
    change _*D=_*B at h
    linarith
  simp only [Nat.choose_succ_succ',Nat.cast_add]
  change ((n:ℝ)+2)*(A+B+(B+D))^2=(2*n+3)*((B+D)^2+(A+B)^2)-(n+1)*(D^2-2*B^2+A^2)
  linear_combination -2*(D+B)*f+2*(A+B)*g

/-- Form of the Legendre recurrence convenient for coefficient extraction. -/
theorem square_binomial_recurrence (n : ℕ) :
    C ((n:ℝ)+2)*squareBinom (n+2)=
    C (2*(n:ℝ)+3)*(squareBinom (n+1)+X*squareBinom (n+1))-
    C ((n:ℝ)+1)*(squareBinom n-C 2*(X*squareBinom n)+X*(X*squareBinom n)) := by
  ext j
  simp only [coeff_C_mul,coeff_sub,coeff_add]
  cases j with
  | zero => simp [square_coeff]; ring
  | succ j =>
    simp only [coeff_X_mul]
    cases j with
    | zero =>
      simp [square_coeff,Nat.choose_one_right]; ring
    | succ j =>
      simp only [coeff_X_mul,square_coeff]
      exact choose_square_local n j

/-- The reciprocal quadratic for the even binomial endpoint moments:
multiplying by (1±sqrt t)^4 advances the row by two. Pascal's identity
alone suffices for every polynomial coefficient including the boundary. -/
theorem even_binomial_recurrence (n : ℕ) :
    evenBinom (n+2)=
    C 2*(evenBinom (n+1)+X*evenBinom (n+1))-
    (evenBinom n-C 2*(X*evenBinom n)+X*(X*evenBinom n)) := by
  ext j
  simp only [coeff_C_mul,coeff_sub,coeff_add]
  cases j with
  | zero => norm_num [even_coeff]
  | succ j =>
    simp only [coeff_X_mul]
    cases j with
    | zero =>
      simp only [coeff_X_mul_zero,even_coeff,two_mul,zero_add,add_zero]
      simp only [show n+2+(n+2)=2*n+4 by omega,show n+1+(n+1)=2*n+2 by omega]
      simp [Nat.choose_succ_succ',Nat.choose_one_right,two_mul]
      ring
    | succ j =>
      simp only [coeff_X_mul,even_coeff]
      simp only [show 2*(j+1+1)=2*j+4 by omega,show 2*(j+1)=2*j+2 by omega,
        show 2*(n+2)=2*n+4 by omega,show 2*(n+1)=2*n+2 by omega]
      simp only [Nat.choose_succ_succ',Nat.cast_add]
      ring

#print axioms square_binomial_recurrence
#print axioms even_binomial_recurrence
end HalfWords
