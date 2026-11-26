import HalfWords.ClassicalSeries

namespace HalfWords
open PowerSeries
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem denominator_times (t : K) (S : PowerSeries K) :
    denominator t*S = S - C (2*(1+t))*(X*S) + C ((1-t)^2)*(X*(X*S)) := by
  rw [denominator_form]; simp only [map_mul,map_ofNat]; ring

omit [CharZero K] in
theorem endpoint_coeffs (t : K) :
    coeff 0 (endpointSeries t)=1 ∧ coeff 1 (endpointSeries t)=1+t ∧
    ∀ n : ℕ, coeff (n+2) (endpointSeries t) =
      2*(1+t)*coeff (n+1) (endpointSeries t)-(1-t)^2*coeff n (endpointSeries t) := by
  have eq := endpoints_characterized t
  rw [denominator_times] at eq
  have first := congrArg (coeff 0) eq
  simp only [map_add,map_sub,coeff_C_mul,coeff_zero_eq_constantCoeff,map_mul,constantCoeff_X,
    zero_mul,constantCoeff_C,map_one,mul_zero,add_zero,sub_zero] at first
  have H0 : coeff 0 (endpointSeries t)=1 := by rwa [coeff_zero_eq_constantCoeff]
  have one := congrArg (coeff 1) eq
  simp only [map_add,map_sub,coeff_C_mul,coeff_shift,H0,mul_one] at one
  have H1 : coeff 1 (endpointSeries t)=1+t := by
    simp at one
    linear_combination one
  refine ⟨H0,H1,?_⟩
  intro n
  have h := congrArg (coeff (n+2)) eq
  simp only [map_add,map_sub,coeff_C_mul,coeff_shift] at h
  simp at h
  linear_combination h

theorem arcsine_coeffs (t : K) :
    coeff 0 (arcsineSeries t)=1 ∧ coeff 1 (arcsineSeries t)=1+t ∧
    ∀ n : ℕ, (n+2 : K)*coeff (n+2) (arcsineSeries t) =
      (2*n+3)*(1+t)*coeff (n+1) (arcsineSeries t)-
      (n+1)*(1-t)^2*coeff n (arcsineSeries t) := by
  let B := arcsineSeries t
  have H0 : coeff 0 B=1 := by rw [coeff_zero_eq_constantCoeff]; exact (arcsine_characterized t).1
  have eq := arcsine_equation t
  change denominator t*derivative K B=(C (1+t)-C ((1-t)^2)*X)*B at eq
  rw [denominator_times,sub_mul,mul_assoc] at eq
  have first := congrArg (coeff 0) eq
  simp only [map_add,map_sub,coeff_C_mul,coeff_derivative,Nat.cast_zero,zero_add,mul_one,
    coeff_zero_eq_constantCoeff,map_mul,constantCoeff_X,zero_mul,mul_zero,sub_zero,add_zero] at first
  have c0 : constantCoeff B=1 := (arcsine_characterized t).1
  simp [c0] at first
  refine ⟨H0,first,?_⟩
  intro n
  have eq1 := congrArg (coeff (n+1)) eq
  simp only [map_add,map_sub,coeff_C_mul,coeff_shift,coeff_derivative,Nat.cast_succ] at eq1
  have weightedPrevious : coeff n (X*derivative K B)=(n:K)*coeff n B := by
    cases n with
    | zero => simp
    | succ n => rw [coeff_shift,coeff_derivative]; push_cast; ring
  rw [weightedPrevious,←map_add (C (R:=K)) 1 t,coeff_C_mul] at eq1
  linear_combination eq1

#print axioms arcsine_coeffs
end HalfWords
