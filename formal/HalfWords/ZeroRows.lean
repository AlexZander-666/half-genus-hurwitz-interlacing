import HalfWords.HurwitzVerified

namespace HalfWords
open Polynomial

theorem zero_mark_row (m : ℕ) : hurwitzPolynomial 0 m=0 := by
  unfold hurwitzPolynomial rawPolynomial
  rw [map_zero,original_zero_parameter,mul_zero]

theorem degree_one_row (b : ℝ) : hurwitzPolynomial b 0=0 := by
  unfold hurwitzPolynomial rawPolynomial
  rw [original_degree_one,mul_zero]

#print axioms zero_mark_row
#print axioms degree_one_row
end HalfWords
