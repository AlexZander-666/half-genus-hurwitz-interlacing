import HalfWords.BinomialRows
import HalfWords.HurwitzVerified

namespace HalfWords
open Polynomial
private theorem even_initial (x : ℝ) : (evenBinom 0).eval x=1 ∧ (evenBinom 1).eval x=1+x := by
  norm_num [evenBinom,finiteRow,Finset.sum_range_succ,eval_add,eval_mul]
private theorem square_initial (x : ℝ) : (squareBinom 0).eval x=1 ∧ (squareBinom 1).eval x=1+x := by
  norm_num [squareBinom,finiteRow,Finset.sum_range_succ,eval_add,eval_mul]

theorem endpoint_binomial (t : ℝ) (n : ℕ) :
    PowerSeries.coeff n (endpointSeries t)=(evenBinom n).eval t := by
  obtain ⟨h0,h1,rec⟩ := endpoint_coeffs t
  induction n using Nat.twoStepInduction with
  | zero => exact h0.trans (even_initial t).1.symm
  | one => exact h1.trans (even_initial t).2.symm
  | more n ih1 ih2 =>
    rw [rec,ih1,ih2,even_binomial_recurrence]
    simp only [eval_mul,eval_add,eval_sub,eval_C,eval_X]
    ring

theorem arcsine_binomial (t : ℝ) (n : ℕ) :
    PowerSeries.coeff n (arcsineSeries t)=(squareBinom n).eval t := by
  obtain ⟨h0,h1,rec⟩ := arcsine_coeffs t
  induction n using Nat.twoStepInduction with
  | zero => exact h0.trans (square_initial t).1.symm
  | one => exact h1.trans (square_initial t).2.symm
  | more n ih1 ih2 =>
    have eq := congrArg (eval t) (square_binomial_recurrence n)
    simp only [eval_mul,eval_add,eval_sub,eval_C,eval_X] at eq
    apply (mul_right_inj' (show (n:ℝ)+2≠0 by positivity)).mp
    rw [rec,ih1,ih2]
    linear_combination -eq

/-- The polynomial from the original connected permutation matching words.
Every degree, every real b and every power of the hive variable are included.
Here m is zero-based, so the part size in the paper is m+1. -/
theorem hurwitz_binomial_polynomial (b : ℝ) (m : ℕ) :
    hurwitzPolynomial b m =
    C (b/(2*((m:ℝ)+1)))*(evenBinom (m+1)-squareBinom (m+1)) := by
  apply Polynomial.funext
  intro t
  rw [eval_hurwitz,eval_mul,eval_C,eval_sub]
  have gf := congrArg (PowerSeries.coeff (m+1)) (exact_generating_function t)
  have h2 (A : PowerSeries ℝ) : PowerSeries.coeff (m+1) (2*A)=2*PowerSeries.coeff (m+1) A := by
    rw [two_mul,map_add,two_mul]
  rw [h2,map_sub,endpoint_binomial,arcsine_binomial] at gf
  have hcol : PowerSeries.coeff (m+1) (halfGenus t)=(jetRow t (m+1)).snd := by
    simp [halfGenus,coeff_col,coeff_jet,snd_jet]
  rw [hcol] at gf
  field_simp
  linear_combination b*gf

theorem hurwitz_coefficient (b : ℝ) (m j : ℕ) :
    (hurwitzPolynomial b m).coeff j =
    b/(2*((m:ℝ)+1))*(((2*(m+1)).choose (2*j):ℝ)-((m+1).choose j:ℝ)^2) := by
  rw [hurwitz_binomial_polynomial,coeff_C_mul,coeff_sub,even_coeff,square_coeff]

#print axioms hurwitz_binomial_polynomial
#print axioms hurwitz_coefficient
end HalfWords
