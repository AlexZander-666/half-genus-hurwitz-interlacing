import HalfGenus.Contact
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal

namespace HalfGenus

open Polynomial Polynomial.Chebyshev Real

noncomputable def difference (lam : ℝ) (m : ℕ) : ℝ[X] :=
  T ℝ m - normalized lam m

theorem abs_normalized_lt {lam : ℝ} (hlam : 0 < lam) {m : ℕ} (hm : 1 ≤ m)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1:ℝ) 1) : |(normalized lam m).eval x| < 1 := by
  have e := normalized_energy_lt hlam hm hx
  simp only [energy, eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_one, eval_X] at e
  have pos : 0 < (m:ℝ)*(m+2*lam) := by
    have : 0 < (m:ℝ) := by exact_mod_cast hm
    positivity
  have hsq : 0 ≤ 1-x^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx.2.le) (show 0 ≤ 1+x by linarith [hx.1])]
  have htt : ((normalized lam m).eval x)^2 < 1 := by
    by_contra! hh
    nlinarith [mul_nonneg hsq (sq_nonneg ((derivative (normalized lam m)).eval x)),
      mul_le_mul_of_nonneg_left hh pos.le]
  exact abs_lt.mpr ⟨by nlinarith, by nlinarith⟩

theorem difference_node_sign {lam : ℝ} (hlam : 0 < lam) {m i : ℕ} (hi : 0 < i) (him : i < m) :
    0 < (-1:ℝ)^i * (difference lam m).eval (node m i) := by
  have hx : node m i ∈ Set.Ioo (-1:ℝ) 1 := by
    constructor
    · simpa only [node_eq_neg_one (show m ≠ 0 by omega)] using (node_lt (le_refl m) him)
    · simpa only [node_eq_one] using (node_lt him.le hi)
  have h := abs_normalized_lt hlam (by omega : 1 ≤ m) hx
  rw [difference,eval_sub, eval_T_real_node (Finset.mem_Iic.mpr him.le)]
  have hn : ((-1:ℝ)^i)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have bound : (-1:ℝ)^i * (normalized lam m).eval (node m i) < 1 :=
    (le_abs_self _).trans_lt (by simpa [abs_mul] using h)
  nlinarith

theorem interval_contains_root {lam : ℝ} (hlam : 0 < lam) {m i : ℕ} (hi : 0 < i)
    (him : i+1 < m) : ∃ x ∈ Set.Ioo (node m (i+1)) (node m i), (difference lam m).eval x = 0 := by
  have upper := difference_node_sign hlam hi (show i < m by omega)
  have lower := difference_node_sign hlam (Nat.zero_lt_succ i) him
  rw [pow_succ] at lower
  have horder := (node_lt him.le (Nat.lt_succ_self i)).le
  rcases lt_or_gt_of_ne (pow_ne_zero i (neg_ne_zero.mpr (one_ne_zero : (1:ℝ)≠0))) with h | h
  · apply intermediate_value_Ioo' horder (difference lam m).continuous.continuousOn
    constructor
    · exact neg_of_mul_pos_right upper h.le
    · apply pos_of_mul_pos_right lower
      nlinarith
  · apply intermediate_value_Ioo horder (difference lam m).continuous.continuousOn
    constructor
    · exact neg_of_mul_pos_right lower (by nlinarith)
    · exact pos_of_mul_pos_right upper h.le

theorem normalized_natDegree_le (lam : ℝ) (m : ℕ) : (normalized lam m).natDegree ≤ m := by
  induction m with
  | zero => simp [normalized]
  | succ j ih =>
    rw [normalized, raiseNumerator]
    apply (natDegree_C_mul_le ..).trans
    apply (natDegree_sub_le ..).trans
    apply max_le
    · apply natDegree_mul_le.trans
      have h := natDegree_C_mul_le ((j:ℝ)+2*lam) (X : ℝ[X])
      simp only [natDegree_X] at h
      omega
    · cases j with
      | zero => simp [normalized]
      | succ a =>
        apply natDegree_mul_le.trans
        have h : ((1 : ℝ[X])-X^2).natDegree ≤ 2 := by
          apply (natDegree_sub_le ..).trans
          simp
        have b := (natDegree_derivative_le (normalized lam (a+1))).trans
          (Nat.sub_le_sub_right ih 1)
        omega

theorem difference_endpoints {lam : ℝ} (hlam : 0 < lam) (m : ℕ) :
    (difference lam m).eval (-1) = 0 ∧ (difference lam m).eval 1 = 0 := by
  have hg := normalized_endpoints hlam m
  simp [difference, T_eval_one, hg.1, hg.2]

#print axioms difference_endpoints
#print axioms normalized_natDegree_le
#print axioms difference_node_sign
#print axioms interval_contains_root

end HalfGenus
