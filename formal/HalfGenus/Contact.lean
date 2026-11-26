import HalfGenus.Gegenbauer
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

namespace HalfGenus

open Polynomial Real

private theorem sign_from_squares {A u v : ℝ} (hA : 0 < A) (h : v^2 < (A*u)^2) :
    0 < (A*u-v)*u := by
  by_contra! H
  have hmul := mul_nonpos_of_nonneg_of_nonpos hA.le H
  nlinarith [sq_nonneg (A*u-v)]

/-- At every interior root of the Chebyshev-minus-normalized-Gegenbauer
row, the *actual next difference* has the sign opposite to sin(m θ). -/
theorem next_at_contact {lam : ℝ} (hlam : 0 < lam) {m : ℕ} (hm : 1 ≤ m)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 π)
    (contact : (Chebyshev.T ℝ (m:ℤ)).eval (cos θ) = (normalized lam m).eval (cos θ)) :
    ((Chebyshev.T ℝ ((m:ℤ)+1)).eval (cos θ) - (normalized lam (m+1)).eval (cos θ)) *
      sin ((m:ℝ)*θ) < 0 := by
  let A : ℝ := m+2*lam
  have hA : 0 < A := by dsimp [A]; positivity
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hx : cos θ ∈ Set.Ioo (-1:ℝ) 1 := by
    have hr := Real.sin_sq_add_cos_sq θ
    have hpos := sq_pos_of_pos hs
    constructor <;> nlinarith
  rw [Chebyshev.T_real_cos] at contact
  push_cast at contact
  let v := (derivative (normalized lam m)).eval (cos θ)
  have e := normalized_energy_lt hlam hm hx
  simp only [energy, eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_one, eval_X] at e
  rw [← contact] at e
  have hcos : 1-(cos θ)^2 = (sin θ)^2 := by linarith [sin_sq_add_cos_sq θ]
  rw [hcos] at e
  have strict : (sin θ*v)^2 < ((m:ℝ)*A) * (sin ((m:ℝ)*θ))^2 := by
    dsimp [v, A] at *
    have id := congrArg (fun a : ℝ => (m:ℝ)*(m+2*lam)*a) (sin_sq_add_cos_sq ((m:ℝ)*θ))
    nlinarith only [id,e]
  have larger : (m:ℝ)*A ≤ A^2 := by dsimp [A] at *; nlinarith [mul_pos hA hlam]
  have comp : (sin θ*v)^2 < (A*sin ((m:ℝ)*θ))^2 := by
    nlinarith [mul_le_mul_of_nonneg_right larger (sq_nonneg (sin ((m:ℝ)*θ)))]
  have sgn := sign_from_squares hA comp
  rw [Chebyshev.T_real_cos, normalized]
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, eval_mul, eval_C,
    raiseNumerator, eval_sub, eval_X, eval_one, eval_pow]
  rw [add_mul, one_mul, cos_add, ← contact, hcos]
  change (cos ((m:ℝ)*θ) * cos θ - sin ((m:ℝ)*θ)*sin θ -
    A⁻¹*(A*cos θ*cos ((m:ℝ)*θ) - (sin θ)^2*v)) * sin ((m:ℝ)*θ) < 0
  field_simp
  nlinarith [mul_pos hs sgn]

#print axioms next_at_contact

end HalfGenus
