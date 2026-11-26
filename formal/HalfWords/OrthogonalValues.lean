import HalfWords.CoefficientRecurrence
import HalfGenus.Verified

namespace HalfWords
open Polynomial HalfGenus

noncomputable abbrev leg (n : ℕ) := normalized (1/2) n

private theorem leg_raise (n : ℕ) (x : ℝ) :
    ((n:ℝ)+1)*(leg (n+1)).eval x =
    ((n:ℝ)+1)*x*(leg n).eval x-(1-x^2)*(derivative (leg n)).eval x := by
  have ne : (n:ℝ)+1≠0 := by positivity
  change ((n:ℝ)+1)*(normalized (1/2) (n+1)).eval x=_
  rw [normalized]
  simp only [raiseNumerator,eval_mul,eval_sub,eval_C,eval_X,eval_one,eval_pow]
  norm_num
  field_simp

private theorem leg_diff (n : ℕ) (x : ℝ) :
    (derivative (leg (n+1))).eval x =
    ((n:ℝ)+1)*(leg n).eval x+x*(derivative (leg n)).eval x := by
  change (derivative (normalized (1/2) (n+1))).eval x=_
  rw [normalized,derivative_C_mul,derivative_raiseNumerator (normalized_equation (1/2) n)]
  simp only [eval_mul,eval_add,eval_C,eval_X]
  norm_num
  field_simp

theorem leg_three (n : ℕ) (x : ℝ) :
    ((n:ℝ)+2)*(leg (n+2)).eval x =
    (2*n+3)*x*(leg (n+1)).eval x-((n:ℝ)+1)*(leg n).eval x := by
  have h := leg_raise (n+1) x
  rw [leg_diff] at h
  push_cast at h
  linear_combination h-x*leg_raise n x

private theorem leg_initial (x : ℝ) : (leg 0).eval x=1 ∧ (leg 1).eval x=x := by
  norm_num [leg,normalized,raiseNumerator]

theorem endpoint_value (t x c : ℝ) (ca : c*x=1+t) (cb : c^2=(1-t)^2) (n : ℕ) :
    PowerSeries.coeff n (endpointSeries t)=c^n*(Chebyshev.T ℝ (n:ℤ)).eval x := by
  obtain ⟨h0,h1,rec⟩ := endpoint_coeffs t
  induction n using Nat.twoStepInduction with
  | zero => simpa using h0
  | one => simpa [ca] using h1
  | more n ih1 ih2 =>
    rw [rec,ih1,ih2]
    push_cast
    rw [Chebyshev.T_add_two]
    simp only [eval_sub,eval_mul,eval_X,eval_ofNat]
    rw [←ca,←cb,pow_succ,pow_succ]
    ring

theorem arcsine_value (t x c : ℝ) (ca : c*x=1+t) (cb : c^2=(1-t)^2) (n : ℕ) :
    PowerSeries.coeff n (arcsineSeries t)=c^n*(leg n).eval x := by
  obtain ⟨h0,h1,rec⟩ := arcsine_coeffs t
  induction n using Nat.twoStepInduction with
  | zero => simpa [(leg_initial x).1] using h0
  | one => simpa [(leg_initial x).2,ca] using h1
  | more n ih1 ih2 =>
    have ne : (n:ℝ)+2≠0 := by positivity
    apply (mul_right_inj' ne).mp
    rw [rec,ih1,ih2,←ca,←cb,pow_succ,pow_succ]
    linear_combination -(c^n*c^2)*leg_three n x

#print axioms arcsine_value
end HalfWords
