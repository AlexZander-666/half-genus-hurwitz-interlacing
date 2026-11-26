import HalfWords.PhysicalPolynomial
import HalfWords.OrthogonalValues

namespace HalfWords
open Polynomial HalfGenus
noncomputable def pull (x : ℝ) := (x-1)/(x+1)

theorem pull_negative {x : ℝ} (h : x∈Set.Ioo (-1:ℝ) 1) : pull x<0 :=
  div_neg_of_neg_of_pos (by linarith [h.2]) (by linarith [h.1])

theorem pull_lt {x y : ℝ} (hx : -1<x) (_hy : -1<y) (h : x<y) : pull x<pull y := by
  apply (div_lt_div_iff₀ (show 0<x+1 by linarith) (show 0<y+1 by linarith)).mpr
  nlinarith

/-- The actual Coulter–Do connected word polynomial under the fractional
linear change. All constant factors and the m+1 normalization are present. -/
theorem pullback (b x : ℝ) (hx : -1<x) (m : ℕ) :
    (hurwitzPolynomial b m).eval (pull x) =
      b / (2*((m:ℝ)+1))*(1-pull x)^(m+1)*(difference (1/2) (m+1)).eval x := by
  let t := pull x
  let c := 1-t
  have ca : c*x=1+t := by dsimp [c,t,pull]; field_simp [show x+1≠0 by linarith]; ring
  have cb : c^2=(1-t)^2 := rfl
  have gf := congrArg (PowerSeries.coeff (m+1)) (exact_generating_function t)
  have coeff2 (B : PowerSeries ℝ) : PowerSeries.coeff (m+1) (2*B)=2*PowerSeries.coeff (m+1) B := by
    rw [two_mul,map_add,two_mul]
  rw [coeff2,map_sub,endpoint_value t x c ca cb,arcsine_value t x c ca cb] at gf
  have hg : PowerSeries.coeff (m+1) (halfGenus t)=(jetRow t (m+1)).snd := by
    simp [halfGenus,coeff_col,coeff_jet,snd_jet]
  rw [hg] at gf
  rw [eval_hurwitz,difference,eval_sub]
  change b/((m:ℝ)+1)*(jetRow t (m+1)).snd =
    b/(2*((m:ℝ)+1))*c^(m+1)*(_-_)
  have k0 : (m:ℝ)+1≠0 := by positivity
  field_simp
  linear_combination b*gf

theorem pullback_zero {b x : ℝ} (hb : b≠0) (hx : x∈Set.Ioo (-1:ℝ) 1) (m : ℕ) :
    (hurwitzPolynomial b m).eval (pull x)=0 ↔ (difference (1/2) (m+1)).eval x=0 := by
  rw [pullback b x hx.1]
  have nb : b/(2*((m:ℝ)+1))≠0 := div_ne_zero hb (by positivity)
  have pos : 0<1-pull x := by linarith [pull_negative hx]
  exact mul_eq_zero.trans (or_iff_right (mul_ne_zero nb (pow_ne_zero _ pos.ne')))

#print axioms pullback
end HalfWords
