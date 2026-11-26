import HalfGenus.RealRoots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace HalfGenus

open Real Polynomial Polynomial.Chebyshev

private theorem node_angle {m i : ℕ} (hm : 0 < m) (hi : i ≤ m) :
    arccos (node m i) = i*π/m := by
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  apply arccos_cos (by positivity)
  apply (div_le_iff₀ hm').mpr
  calc
    (i:ℝ)*π ≤ (m:ℝ)*π := mul_le_mul_of_nonneg_right (by exact_mod_cast hi) pi_pos.le
    _ = π*(m:ℝ) := mul_comm _ _

/-- Signed upper-row evaluation at any zero in the indexed lower-row gap. -/
theorem contact_in_gap {lam : ℝ} (hlam : 0 < lam) {m i : ℕ} (hi : 0 < i) (him : i+1 < m)
    {z : ℝ} (hz : z ∈ Set.Ioo (node m (i+1)) (node m i)) (zero : (difference lam m).eval z = 0) :
    0 < (-1:ℝ)^(i+1) * (difference lam (m+1)).eval z := by
  have hm : 0 < m := by omega
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have lo : -1 < z := (node_mem_Icc (n:=m) (i:=i+1)).1.trans_lt hz.1
  have hi' : z < 1 := hz.2.trans_le (node_mem_Icc (n:=m) (i:=i)).2
  have θlo := arccos_lt_arccos lo.le hz.2 (node_mem_Icc (n:=m) (i:=i)).2
  have θhi := arccos_lt_arccos (node_mem_Icc (n:=m) (i:=i+1)).1 hz.1 hi'.le
  rw [node_angle hm (by omega)] at θlo θhi
  have low : 0 < (m:ℝ)*arccos z - (i:ℝ)*π := by nlinarith [(div_lt_iff₀ hm').mp θlo]
  have high : (m:ℝ)*arccos z - (i:ℝ)*π < π := by
    push_cast at θhi
    nlinarith [(lt_div_iff₀ hm').mp θhi]
  have sinpos := sin_pos_of_pos_of_lt_pi low high
  have θpos : 0 < arccos z := by exact (arccos_pos.mpr hi')
  have θlt : arccos z < π := arccos_lt_pi.mpr lo
  have eq := sub_eq_zero.mp (show (T ℝ m).eval z - (normalized lam m).eval z = 0 by simpa [difference] using zero)
  have zcos := cos_arccos lo.le hi'.le
  have val := next_at_contact hlam hm ⟨θpos, θlt⟩ (by rw [zcos]; exact eq)
  rw [zcos] at val
  have trig := sin_add_nat_mul_pi ((m:ℝ)*arccos z-(i:ℝ)*π) i
  rw [sub_add_cancel] at trig
  rw [trig] at val
  suffices (T ℝ (↑m+1)).eval z - (normalized lam (m+1)).eval z = (difference lam (m+1)).eval z by
    rw [this] at val
    rw [pow_succ]
    by_contra! h
    nlinarith [mul_nonneg (show 0 ≤ (-1:ℝ)^i * (difference lam (m+1)).eval z by nlinarith) sinpos.le]
  simp only [difference,Nat.cast_succ,eval_sub]

private theorem root_of_opposite {p : ℝ[X]} {a b w : ℝ} (hab : a ≤ b)
    (ha : 0 < -w * p.eval a) (hb : 0 < w * p.eval b) :
    ∃ z ∈ Set.Ioo a b, p.eval z = 0 := by
  rcases lt_trichotomy w 0 with hw | hw | hw
  · exact intermediate_value_Ioo' hab p.continuous.continuousOn
      ⟨neg_of_mul_pos_right hb hw.le, pos_of_mul_pos_right ha (by linarith)⟩
  · simp [hw] at ha
  · exact intermediate_value_Ioo hab p.continuous.continuousOn
      ⟨neg_of_mul_pos_right ha (by linarith), pos_of_mul_pos_right hb hw.le⟩

/-- The two mesh estimates at the outer edges raise the degree. -/
private theorem outer_mesh (m : ℕ) (hm : 2 ≤ m) :
    node m 1 < node (m+1) 1 ∧ node (m+1) m < node m (m-1) := by
  have h : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have h1 : 1 ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have h2 : 0 < (m:ℝ)+1 := by positivity
  simp only [node,Nat.cast_one,Nat.cast_add,one_mul,Nat.cast_sub (show 1 ≤ m by omega)]
  constructor
  · apply strictAntiOn_cos
    · exact ⟨by positivity,(div_le_iff₀ h2).mpr (by nlinarith [mul_pos pi_pos h])⟩
    · exact ⟨by positivity,(div_le_iff₀ h).mpr (by nlinarith [mul_le_mul_of_nonneg_left h1 pi_pos.le])⟩
    · exact (div_lt_div_iff₀ h2 h).mpr (by nlinarith [pi_pos])
  · apply strictAntiOn_cos
    · exact ⟨div_nonneg (mul_nonneg (by linarith) pi_pos.le) h.le,
        (div_le_iff₀ h).mpr (by nlinarith [pi_pos])⟩
    · exact ⟨by positivity,(div_le_iff₀ h2).mpr (by nlinarith [pi_pos])⟩
    · exact (div_lt_div_iff₀ h h2).mpr (by nlinarith [pi_pos])

/-- The new row has a root in the gap near +1 before the first lower root. -/
theorem first_gap {lam : ℝ} (hlam : 0 < lam) {m : ℕ} (hm : 3 ≤ m)
    {z : ℝ} (loc : z ∈ Set.Ioo (node m 2) (node m 1)) (zero : (difference lam m).eval z = 0) :
    ∃ t ∈ Set.Ioo z 1, (difference lam (m+1)).eval t = 0 := by
  have low := contact_in_gap (i:=1) hlam (by omega) (by omega) loc zero
  have high := difference_node_sign (m:=m+1) (i:=1) hlam (by omega) (by omega)
  have order := loc.2.trans (outer_mesh m (by omega)).1
  obtain ⟨t,l,r⟩ := root_of_opposite (w:=-1) order.le (by simpa using low) (by simpa using high)
  exact ⟨t,⟨l.1,l.2.trans_le (node_mem_Icc ..).2⟩,r⟩

/-- The new row separates consecutive lower roots in interior mesh cells. -/
theorem middle_gap {lam : ℝ} (hlam : 0 < lam) {m i : ℕ} (hi : 0 < i) (him : i+2 < m)
    {a b : ℝ} (ha : a ∈ Set.Ioo (node m (i+2)) (node m (i+1)))
    (hb : b ∈ Set.Ioo (node m (i+1)) (node m i))
    (za : (difference lam m).eval a = 0) (zb : (difference lam m).eval b = 0) :
    ∃ t ∈ Set.Ioo a b, (difference lam (m+1)).eval t = 0 := by
  have low := contact_in_gap (i:=i+1) hlam (by omega) him ha za
  have high := contact_in_gap hlam hi (by omega) hb zb
  exact root_of_opposite (ha.2.trans hb.1).le (by simpa only [pow_succ, mul_neg_one] using low) high

/-- The new row has a root beyond the last lower root near −1. -/
theorem last_gap {lam : ℝ} (hlam : 0 < lam) (j : ℕ) {z : ℝ}
    (loc : z ∈ Set.Ioo (node (j+3) (j+2)) (node (j+3) (j+1)))
    (zero : (difference lam (j+3)).eval z = 0) :
    ∃ t ∈ Set.Ioo (-1) z, (difference lam (j+4)).eval t = 0 := by
  have high := contact_in_gap (m:=j+3) (i:=j+1) hlam (by omega) (by omega) loc zero
  have low := difference_node_sign (m:=j+4) (i:=j+3) hlam (by omega) (by omega)
  have order := (outer_mesh (j+3) (by omega)).2.trans loc.1
  obtain ⟨t,l,r⟩ := root_of_opposite (w:=(-1)^(j+2)) order.le
    (by simpa only [pow_succ,mul_neg_one] using low) high
  exact ⟨t,⟨lt_of_le_of_lt (node_mem_Icc ..).1 l.1,l.2⟩,r⟩

#print axioms first_gap
#print axioms middle_gap
#print axioms last_gap
#print axioms contact_in_gap

end HalfGenus
