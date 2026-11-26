import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

namespace HalfGenus

open Polynomial

/-- The denominator-free energy for the normalized ultraspherical equation. -/
noncomputable def energy (M : ℝ) (Z : ℝ[X]) : ℝ[X] :=
  C M * Z^2 + (1 - X^2) * (derivative Z)^2

theorem energy_derivative {M lam : ℝ} {Z : ℝ[X]}
    (ode : (1 - X^2) * derivative (derivative Z) -
      C (2*lam+1) * X * derivative Z + C M * Z = 0) :
    derivative (energy M Z) = C (4*lam) * X * (derivative Z)^2 := by
  simp only [energy, derivative_mul, derivative_C, derivative_sub,
    derivative_one, derivative_X, derivative_pow, Nat.cast_ofNat, zero_mul,
    zero_sub, zero_add, mul_one, map_mul, map_add, map_one, map_ofNat] at *
  linear_combination 2 * derivative Z * ode

private theorem ordered_energy {M lam : ℝ} {Z : ℝ[X]} (hlam : 0 ≤ lam)
    (h : derivative (energy M Z) = C (4*lam) * X * (derivative Z)^2) :
    AntitoneOn (energy M Z).eval (Set.Iic 0) ∧
    MonotoneOn (energy M Z).eval (Set.Ici 0) := by
  have d (u : ℝ) : deriv (energy M Z).eval u = 4 * lam * u * ((derivative Z).eval u)^2 := by
    rw [Polynomial.deriv, h]
    simp
  constructor
  · apply antitoneOn_of_deriv_nonpos (convex_Iic 0) (energy M Z).continuous.continuousOn
      (energy M Z).differentiable.differentiableOn
    intro u hu
    have hu' : u ≤ 0 := (show u ∈ Set.Iic (0 : ℝ) from interior_subset hu)
    rw [d]
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hu')
      (sq_nonneg _)
  · apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (energy M Z).continuous.continuousOn
      (energy M Z).differentiable.differentiableOn
    intro u hu
    have hu' : 0 ≤ u := (show u ∈ Set.Ici (0 : ℝ) from interior_subset hu)
    rw [d]
    positivity

/-- The normalized energy is strictly smaller at every interior point. -/
theorem energy_lt_endpoints {M lam : ℝ} {Z : ℝ[X]} (hlam : 0 < lam)
    (nonconstant : derivative Z ≠ 0)
    (ode : (1 - X^2) * derivative (derivative Z) -
      C (2*lam+1) * X * derivative Z + C M * Z = 0)
    (left : (Z.eval (-1))^2 = 1) (right : (Z.eval 1)^2 = 1)
    {u : ℝ} (hu : u ∈ Set.Ioo (-1) 1) : (energy M Z).eval u < M := by
  have d := energy_derivative ode
  obtain ⟨neg, pos⟩ := ordered_energy hlam.le d
  have hf : (energy M Z).eval (-1) = M := by simp [energy, left]
  have hg : (energy M Z).eval 1 = M := by simp [energy, right]
  have nonflat : energy M Z ≠ C M := by
    intro eq
    rw [eq, derivative_C] at d
    have coef : C (4 * lam) ≠ (0 : ℝ[X]) := by simp [hlam.ne']
    exact (mul_ne_zero (mul_ne_zero coef X_ne_zero) (pow_ne_zero _ nonconstant)) d.symm
  by_contra! h
  apply nonflat
  apply Polynomial.eq_of_infinite_eval_eq
  rcases le_total u 0 with hu0 | hu0
  · apply (Set.Ioo_infinite hu.1).mono
    intro a ha
    change (energy M Z).eval a = (C M).eval a
    rw [eval_C]
    exact le_antisymm ((neg (by norm_num) (show a ≤ 0 from ha.2.le.trans hu0) ha.1.le).trans_eq hf)
      (h.trans (neg (show a ≤ 0 from ha.2.le.trans hu0) hu0 ha.2.le))
  · apply (Set.Ioo_infinite hu.2).mono
    intro a ha
    change (energy M Z).eval a = (C M).eval a
    rw [eval_C]
    exact le_antisymm ((pos (show 0 ≤ a from hu0.trans ha.1.le) (by norm_num) ha.2.le).trans_eq hg)
      (h.trans (pos hu0 (show 0 ≤ a from hu0.trans ha.1.le) ha.1.le))

#print axioms energy_lt_endpoints
#print axioms energy_derivative

end HalfGenus
