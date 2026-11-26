import HalfWords.Series

namespace HalfWords
open scoped DualNumber
open PowerSeries TrivSqZeroExt
variable {R : Type*} [CommRing R]

noncomputable def col (d : ℕ) (J : PowerSeries (DualNumber R)) : PowerSeries R :=
  mk fun n => jetComponent d (coeff n J)

@[simp] theorem coeff_col (d : ℕ) (J : PowerSeries (DualNumber R)) (n : ℕ) :
    coeff n (col d J)=jetComponent d (coeff n J) := coeff_mk ..

theorem col_add (d : ℕ) (A B : PowerSeries (DualNumber R)) : col d (A+B)=col d A+col d B := by
  ext n : 1; simp
theorem col_sub (d : ℕ) (A B : PowerSeries (DualNumber R)) : col d (A-B)=col d A-col d B := by
  ext n : 1; simp

theorem col_inl (d : ℕ) (t : R) (A : PowerSeries (DualNumber R)) :
    col d (C (inl t)*A)=C t*col d A := by ext n : 1; simp [coeff_C_mul,component_inl_mul]

theorem col_shift (d : ℕ) (A : PowerSeries (DualNumber R)) : col d (X*A)=X*col d A := by
  ext n : 1
  cases n with
  | zero => simp
  | succ n => simp

theorem col_derivative (d : ℕ) (A : PowerSeries (DualNumber R)) :
    col d (derivative _ A)=derivative _ (col d A) := by
  ext n : 1
  simp only [coeff_col,coeff_derivative]
  simpa only [nsmul_eq_mul,Nat.cast_add,Nat.cast_one,mul_comm] using
    (jetComponent (R:=R) d).map_nsmul (n+1) (coeff (n+1) A)

theorem fst_jet (B : DualNumber R) : jetComponent 0 B=B.fst := rfl
theorem snd_jet (B : DualNumber R) : jetComponent 1 B=B.snd := rfl

theorem first_mul (A B : PowerSeries (DualNumber R)) : col 0 (A*B)=col 0 A*col 0 B := by
  ext n : 1
  simp only [coeff_col,coeff_mul,map_sum,fst_jet,fst_mul]

theorem second_mul (A B : PowerSeries (DualNumber R)) :
    col 1 (A*B)=col 0 A*col 1 B+col 1 A*col 0 B := by
  ext n : 1
  simp only [coeff_col,coeff_mul,map_add,map_sum,fst_jet,snd_jet,DualNumber.snd_mul,Finset.sum_add_distrib]

theorem first_eps (A : PowerSeries (DualNumber R)) : col 0 (C ε*A)=0 := by
  ext n : 1; simp [coeff_C_mul,component_eps_mul]

theorem second_eps (A : PowerSeries (DualNumber R)) : col 1 (C ε*A)=col 0 A := by
  ext n : 1; simp [coeff_C_mul,component_eps_mul]

theorem fst_X : col 0 (X : PowerSeries (DualNumber R))=X := by
  ext n : 1; simp only [coeff_col,coeff_X]; split <;> rfl

theorem snd_X : col 1 (X : PowerSeries (DualNumber R))=0 := by
  ext n : 1; simp only [coeff_col,coeff_X,map_zero]; split <;> rfl

/-- The two scalar generating functions of the original word counts satisfy
the independently derived Corollary 4.16 equations. -/
theorem scalar_equations (t : R) :
    let F := col 0 (jetSeries t)
    let G := col 1 (jetSeries t)
    F = X+F^2+C (t-1)*X*F ∧
    (1-2*F-C (t-1)*X)*G=X*(derivative _ F)-F := by
  dsimp only
  constructor
  · have h := congrArg (col 0) (jet_series_equation t)
    simp only [col_add,first_eps,add_zero,col_inl,col_shift,fst_X] at h
    simpa only [first_mul,pow_two,mul_assoc] using h
  · have h := congrArg (col 1) (jet_series_equation t)
    simp only [col_add,second_eps,col_inl,col_shift,snd_X,zero_add,col_sub,col_derivative] at h
    rw [second_mul] at h
    linear_combination h

#print axioms scalar_equations
end HalfWords
