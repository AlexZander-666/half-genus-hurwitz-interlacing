import HalfGenus.Energy

namespace HalfGenus

open Polynomial

/-- Normalized ultraspherical raising map, without its constant divisor. -/
noncomputable def raiseNumerator (a : ℝ) (Z : ℝ[X]) : ℝ[X] :=
  C a * X * Z - (1-X^2) * derivative Z

noncomputable def equation (m lam : ℝ) (Z : ℝ[X]) : ℝ[X] :=
  (1-X^2) * derivative (derivative Z) - C (2*lam+1) * X * derivative Z +
    C (m*(m+2*lam)) * Z

theorem derivative_raiseNumerator {m lam : ℝ} {Z : ℝ[X]} (h : equation m lam Z = 0) :
    derivative (raiseNumerator (m+2*lam) Z) =
      C (m+1) * (C (m+2*lam) * Z + X * derivative Z) := by
  simp [raiseNumerator, equation, derivative_mul, derivative_pow, map_ofNat] at *
  linear_combination -h

theorem equation_raiseNumerator {m lam : ℝ} {Z : ℝ[X]} (h : equation m lam Z = 0) :
    equation (m+1) lam (raiseNumerator (m+2*lam) Z) = 0 := by
  unfold equation
  rw [derivative_raiseNumerator h]
  simp [raiseNumerator, equation, derivative_mul, map_ofNat] at *
  linear_combination (C m + 1) * X * h

theorem equation_const_mul (m lam a : ℝ) (Z : ℝ[X]) :
    equation m lam (C a * Z) = C a * equation m lam Z := by
  simp [equation, derivative_mul]
  ring

/-- The raising recurrence with Z₀=1 and Zₘ(1)=1. -/
noncomputable def normalized (lam : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | m+1 => C (((m:ℝ)+2*lam)⁻¹) * raiseNumerator ((m:ℝ)+2*lam) (normalized lam m)

theorem normalized_equation (lam : ℝ) (m : ℕ) : equation m lam (normalized lam m) = 0 := by
  induction m with
  | zero => simp [normalized, equation]
  | succ j ih =>
    rw [normalized, equation_const_mul, Nat.cast_succ, equation_raiseNumerator ih, mul_zero]

theorem normalized_endpoints {lam : ℝ} (hlam : 0 < lam) (m : ℕ) :
    (normalized lam m).eval 1 = 1 ∧ (normalized lam m).eval (-1) = (-1 : ℝ)^m := by
  induction m with
  | zero => simp [normalized]
  | succ j ih =>
    have h : (j:ℝ)+2*lam ≠ 0 := ne_of_gt (by positivity)
    constructor
    · simp [normalized, raiseNumerator, ih.1, h]
    · simp [normalized, raiseNumerator, ih.2, pow_succ]
      field_simp
      ring

theorem normalized_energy_lt {lam : ℝ} (hlam : 0 < lam) {m : ℕ} (hm : 1 ≤ m)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    (energy (m*(m+2*lam)) (normalized lam m)).eval x < m*(m+2*lam) := by
  have de := normalized_equation lam m
  have hm' : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m from hm)
  have hg := normalized_endpoints hlam m
  have hn : derivative (normalized lam m) ≠ 0 := by
    intro hz
    unfold equation at de
    rw [hz] at de
    have pt := congrArg (Polynomial.eval 1) de
    simp [hg.1] at pt
    rcases pt with h | h
    · exact (Nat.ne_of_gt hm) h
    · linarith
  apply energy_lt_endpoints hlam hn de _ _ hx
  · rw [hg.2, ← pow_mul, mul_comm, pow_mul]
    simp
  · simp [hg.1]

#print axioms normalized_energy_lt
#print axioms normalized_endpoints
#print axioms normalized_equation
#print axioms equation_raiseNumerator
#print axioms derivative_raiseNumerator

end HalfGenus
