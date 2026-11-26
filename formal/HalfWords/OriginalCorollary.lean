import HalfWords.ProfileInduction

namespace HalfWords
open scoped DualNumber
open Equiv Hurwitz Hurwitz.MatchingWords Hurwitz.WordWeights TrivSqZeroExt

theorem input_core (m : ℕ) :
    core (originalStandard m) (originalInput m)=longPart (m+1) := by
  have std : standard m=oriented (1 : Perm (Fin (m+1))) := by
    apply Equiv.ext
    rintro ⟨i,d⟩
    cases d <;> rfl
  have row : cyclic m=oriented (finRotate (m+1)) := by
    apply Equiv.ext
    rintro ⟨i,d⟩
    cases d <;> rfl
  change core ((index m).permCongrHom _) ((index m).permCongrHom _)=_
  rw [core_map,std,row,core,oriented_core]
  cases m with
  | zero =>
    rw [show finRotate (0+1)=1 from (show finRotate 1 = 1 by apply Equiv.ext; intro i; exact Subsingleton.elim _ _),Perm.cycleType_one]; rfl
  | succ m =>
    rw [cycleType_finRotate,longPart,if_pos (by omega)]

theorem original_word_jet {R : Type*} [CommRing R] (b t : R) (m d : ℕ) (hd : d≤1) :
    paperSum b t ((m+1)*2) (originalStandard m) (originalInput m) (m+d) =
      b^d * jetComponent d (jetRow t (m+1)) := by
  rw [original_word_homogeneous b t m d hd,raw_cyclic_eq_fresh]
  apply congrArg (b^d * ·)
  have hm : (originalInput m)⁻¹=originalInput m := by
    change ((index m).permCongrHom (cyclic m))⁻¹ = (index m).permCongrHom (cyclic m)
    rw [←map_inv]; rfl
  have nm (v) : originalInput m v≠v := by
    obtain ⟨⟨i,c⟩,rfl⟩ := (index m).surjective v
    intro eq
    change index m (cyclic m ((index m).symm (index m (i,c))))=index m (i,c) at eq
    rw [Equiv.symm_apply_apply] at eq
    have b := congrArg Prod.snd ((index m).injective eq)
    cases c <;> contradiction
  have start : componentCount (originalStandard m) (originalInput m)=1 :=
    (count_map ..).trans (onePart_count (cyclic_onePart m))
  have finish : componentCount (originalStandard m) (originalStandard m)=m+1 :=
    (count_map ..).trans (standard_count m)
  rw [true_profile t m (m+d) (originalInput m) hm nm d hd (by omega),input_core,product_part _ (by omega)]

/-- Exact two-column first-one-part recurrence from original matching words.
The degree m+1 rows have word lengths m and m+1, respectively. -/
theorem original_half {R : Type*} [CommRing R] (b t : R) (m : ℕ) :
    paperSum b t ((m+1)*2) (originalStandard m) (originalInput m) (m+1) =
      b * (jetRow t (m+1)).snd := by
  rw [original_word_jet b t m 1 (by decide),pow_one]; rfl

#print axioms true_profile
#print axioms original_word_jet
#print axioms original_half
end HalfWords
