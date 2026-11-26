import HalfWords.ScalarSeries

namespace HalfWords
open PowerSeries
variable {R : Type*} [CommRing R]

noncomputable def genusZero (t : R) := col 0 (jetSeries t)
noncomputable def halfGenus (t : R) := col 1 (jetSeries t)
noncomputable def denominator (t : R) : PowerSeries R := (1-C (t-1)*X)^2-4*X
noncomputable def regularRoot (t : R) : PowerSeries R := 1-2*genusZero t-C (t-1)*X

theorem source_discriminant (t : R) :
    constantCoeff (regularRoot t)=1 ∧ (regularRoot t)^2=denominator t ∧
    regularRoot t * derivative R (genusZero t)=1+C (t-1)*genusZero t ∧
    denominator t * halfGenus t=genusZero t-X := by
  let F := genusZero t
  let G := halfGenus t
  let a : PowerSeries R := C (t-1)
  obtain ⟨f,g⟩ := scalar_equations t
  change F=X+F^2+a*X*F at f
  change (1-2*F-a*X)*G=X*derivative R F-F at g
  have dz := congrArg (derivative R) f
  simp only [map_add,Derivation.leibniz,PowerSeries.derivative_X,
    Derivation.leibniz_pow,smul_eq_mul,show derivative R a=0 from derivative_C,
    mul_one] at dz
  have diff : (1-2*F-a*X)*derivative R F=1+a*F := by linear_combination dz
  have sq : (1-2*F-a*X)^2=(1-a*X)^2-4*X := by linear_combination -4*f
  have raw : ((1-a*X)^2-4*X)*G=F-X := by
    rw [←sq,pow_two,mul_assoc,g]
    linear_combination X*diff-2*f
  refine ⟨?_,sq,diff,raw⟩
  have cf : constantCoeff F=0 := by
    rw [←coeff_zero_eq_constantCoeff]
    change coeff 0 (col 0 (jetSeries t))=0
    simp
  change constantCoeff (1-2*F-a*X)=1
  simp [cf]

/-- Denominator-cleared form of the infinitesimal Wishart generating function
obtained from the physical word sums. It uses no division or convergence. -/
theorem cleared_generating_function (t : R) :
    2*denominator t*halfGenus t = 1-C (1+t)*X-regularRoot t := by
  rw [mul_assoc,(source_discriminant t).2.2.2,regularRoot]
  simp only [map_add,map_sub,map_one]
  ring

#print axioms cleared_generating_function
end HalfWords
