import HalfWords.Discriminant
import Mathlib.RingTheory.PowerSeries.Inverse

namespace HalfWords
open PowerSeries
variable {K : Type*} [Field K]

noncomputable def endpointSeries (t : K) : PowerSeries K := (1-C (1+t)*X)*(denominator t)⁻¹
noncomputable def arcsineSeries (t : K) : PowerSeries K := (regularRoot t)⁻¹

theorem denominator_form (t : K) :
    denominator t=1-2*C (1+t)*X+C ((1-t)^2)*X^2 := by
  simp only [denominator,map_add,map_sub,map_pow,map_one]; ring

theorem denominator_regular (t : K) : constantCoeff (denominator t)=1 := by simp [denominator]

theorem endpoints_characterized (t : K) :
    denominator t*endpointSeries t=1-C (1+t)*X := by
  rw [endpointSeries,mul_left_comm,PowerSeries.mul_inv_cancel _ (by rw [denominator_regular]; exact one_ne_zero),mul_one]

theorem arcsine_characterized (t : K) :
    constantCoeff (arcsineSeries t)=1 ∧ regularRoot t*arcsineSeries t=1 ∧
    denominator t*arcsineSeries t=regularRoot t := by
  have c := (source_discriminant t).1
  have h : regularRoot t*arcsineSeries t=1 := PowerSeries.mul_inv_cancel _ (c ▸ one_ne_zero)
  refine ⟨?_,h,?_⟩
  · simp [arcsineSeries,c]
  · rw [←(source_discriminant t).2.1,pow_two,mul_assoc,h,mul_one]

/-- The physical second column equals half the difference of the endpoint
and arcsine moment generating series. The square-root branch is fixed by
constant coefficient one. The denominator clears over all characteristic. -/
theorem exact_generating_function (t : K) :
    2*halfGenus t = endpointSeries t-arcsineSeries t := by
  have unitD := (isUnit_iff_constantCoeff.mpr (by rw [denominator_regular]; exact isUnit_one) :
    IsUnit (denominator t))
  apply unitD.mul_right_inj.mp
  rw [mul_sub,endpoints_characterized,(arcsine_characterized t).2.2]
  simpa only [mul_left_comm,mul_assoc] using cleared_generating_function t

theorem arcsine_equation (t : K) [CharZero K] :
    denominator t*derivative K (arcsineSeries t)=
      (C (1+t)-C ((1-t)^2)*X)*arcsineSeries t := by
  let Y := regularRoot t
  let B := arcsineSeries t
  let D := denominator t
  obtain ⟨_,id,prod⟩ := arcsine_characterized t
  change Y*B=1 at id
  change D*B=Y at prod
  have sq : Y^2=D := (source_discriminant t).2.1
  let δ := derivative K
  have ds := congrArg δ sq
  have dp := congrArg δ prod
  change δ (Y^2)=δ D at ds
  change δ (D*B)=δ Y at dp
  simp only [δ,Derivation.leibniz,smul_eq_mul,Derivation.leibniz_pow] at ds dp
  change D*derivative K B = _*B
  have dy : derivative K D = -2*C (1+t)+2*C ((1-t)^2)*X := by
    change derivative K (denominator t)=_
    rw [denominator_form]
    have two : derivative K (2 : PowerSeries K)=0 := (derivative K).map_natCast 2
    simp [Derivation.leibniz,pow_two,two]; ring
  have sd : 2*Y*derivative K Y = derivative K D := by simpa [nsmul_eq_mul,mul_assoc] using ds
  have cancel : 2*derivative K Y = derivative K D*B := by
    calc 2*derivative K Y = 2*derivative K Y*(Y*B) := by rw [id,mul_one]
         _ = (2*Y*derivative K Y)*B := by ring
         _ = _ := by rw [sd]
  have z : (2 : PowerSeries K) ≠ 0 := by
    intro eq
    have h := congrArg (constantCoeff (R:=K)) eq
    rw [←one_add_one_eq_two, map_add, map_one, map_zero] at h
    rw [one_add_one_eq_two] at h
    exact (two_ne_zero : (2:K)≠0) h
  apply (mul_right_inj' z).mp
  rw [dy] at dp cancel
  linear_combination 2*dp+cancel

#print axioms exact_generating_function
#print axioms arcsine_equation
end HalfWords
