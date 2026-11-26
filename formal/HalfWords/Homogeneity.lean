import HalfWords.Excess
import HalfWords.Fresh

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords Hurwitz.WordWeights Hurwitz.Paths
abbrev originalStandard (m : ℕ) := (index m).permCongrHom (standard m)
abbrev originalInput (m : ℕ) := (index m).permCongrHom (cyclic m)

private theorem nofixed_map {V W : Type*} (e : V ≃ W) (r : Perm V) (h : ∀v, r v ≠ v) :
    ∀w, e.permCongrHom r w ≠ w := by
  intro w
  obtain ⟨v,rfl⟩ := e.surjective w
  simpa using h v

/-- At genus 0 or 1/2 the original connected one-part word has exactly
zero or one flips, respectively. The degree is m+1. -/
theorem cyclic_flips (m d : ℕ) (hd : d ≤ 1)
    (w : SuffixWords (originalStandard m) 0 (m+d) (originalInput m) none true) :
    executionFlips (originalStandard m) (originalInput m) w.val = d := by
  let s := originalStandard m
  let M := originalInput m
  have hs : s⁻¹=s := by
    change ((index m).permCongrHom (standard m))⁻¹ = (index m).permCongrHom (standard m)
    rw [← map_inv]; rfl
  have hm : M⁻¹=M := by
    change ((index m).permCongrHom (cyclic m))⁻¹ = (index m).permCongrHom (cyclic m)
    rw [← map_inv]; rfl
  have ns : ∀v, s v ≠ v := nofixed_map _ _ (by
    rintro ⟨i,j⟩ e; have bit := congrArg Prod.snd e
    cases j <;> contradiction)
  have nm : ∀v, M v ≠ v := nofixed_map _ _ (by
    rintro ⟨i,j⟩ e; have bit := congrArg Prod.snd e
    cases j <;> contradiction)
  have start : componentCount s M=1 := by
    rw [show componentCount s M=componentCount (standard m) (cyclic m) from count_map ..]
    exact onePart_count (cyclic_onePart m)
  have finish : componentCount s s=m+1 := (count_map ..).trans (standard_count m)
  obtain ⟨_,good,final,_⟩ := (fits_iff ..).mp w.property.2
  have bounds := word_excess s M hs hm ns nm w.val
    (fun q hq => (show q.1 < q.2 from (good q hq).1.1).ne)
  dsimp only at bounds
  change execute M w.val = s at final
  rw [final,finish,start,w.property.1] at bounds
  have exactCount := bounds.2 (by omega)
  change executionFlips s M w.val=d
  omega

/-- The genuine Proposition 4.18 raw polynomial at one part of length m+1
is homogeneous of b-degree d at both d=0 and d=1, over arbitrary semirings. -/
theorem original_word_homogeneous {R : Type*} [CommSemiring R] (b t : R)
    (m d : ℕ) (hd : d ≤ 1) :
    paperSum b t ((m+1)*2) (originalStandard m) (originalInput m) (m+d) =
    b^d * paperSum 1 t ((m+1)*2) (originalStandard m) (originalInput m) (m+d) := by
  rw [raw_cyclic_eq_fresh,raw_cyclic_eq_fresh,fresh,fresh,Finset.mul_sum]
  apply Fintype.sum_congr
  intro w
  rw [cyclic_flips m d hd w]
  simp

theorem original_zero_parameter {R : Type*} [CommSemiring R] (t : R) (m : ℕ) :
    paperSum 0 t ((m+1)*2) (originalStandard m) (originalInput m) (m+1) = 0 := by
  simpa using original_word_homogeneous (0:R) t m 1 (by decide)

theorem original_degree_one {R : Type*} [CommSemiring R] (b t : R) :
    paperSum b t 2 (originalStandard 0) (originalInput 0) 1 = 0 := by
  change paperSum b t ((0+1)*2) (originalStandard 0) (originalInput 0) 1 = _
  rw [raw_cyclic_eq_dp,dp_succ]
  have nil : nextSteps (n:=2) none = ∅ := by
    ext p
    simp only [mem_nextSteps,Finset.notMem_empty,iff_false]
    rintro ⟨⟨small,even⟩,_⟩
    have upper := p.2.isLt
    omega
  rw [nil,Finset.sum_empty]

#print axioms original_zero_parameter
#print axioms original_degree_one
#print axioms cyclic_flips
#print axioms original_word_homogeneous
end HalfWords
