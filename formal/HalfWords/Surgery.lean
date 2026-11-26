import Hurwitz.MatchingWords
import Mathlib.GroupTheory.Perm.List

namespace HalfWords

open Equiv Hurwitz.MatchingWords
variable {α : Type*}

/-- The matching with black-to-white attachments given by a permutation r.
The standard partner at every label is the opposite Boolean copy. -/
def oriented (r : Perm α) : Perm (α × Bool) :=
  let f : α × Bool → α × Bool := fun (i,b) => if b then (r i,false) else (r.symm i,true)
  have h : Function.Involutive f := by
    rintro ⟨i,b⟩
    cases b <;> simp [f]
  h.toPerm f

@[simp] theorem oriented_right (r : Perm α) (i : α) : oriented r (i,true) = (r i,false) := rfl
@[simp] theorem oriented_left (r : Perm α) (i : α) : oriented r (i,false) = (r.symm i,true) := rfl

variable [DecidableEq α]

private theorem swap_left_white (a b i : α) : swap (a,false) (b,false) (i,false) = (swap a b i,false) := by
  by_cases ha : i=a <;> by_cases hb : i=b <;> simp_all [swap_apply_def]

private theorem swap_left_black (a b i : α) : swap (a,false) (b,false) (i,true) = (i,true) := by
  apply swap_apply_of_ne_of_ne <;> simp

/-- Exact rewire on the actual two-copy matching for a same-color swap. -/
theorem rewire_same_color (r : Perm α) (a b : α) :
    rewire (oriented r) ((a,false),(b,false)) = oriented (swap a b*r) := by
  apply Equiv.ext
  rintro ⟨i,w⟩
  cases w <;> simp only [rewire_apply,swap_left_white,swap_left_black,oriented_left,
    oriented_right,Perm.mul_apply]
  rfl

private theorem append_cycle (a b : α) (as bs : List α) :
    ((a::as)++(b::bs)).formPerm =
      ((a::as).formPerm * swap ((a::as).getLast (by simp)) b) * (b::bs).formPerm := by
  induction as generalizing a with
  | nil => simp
  | cons x xs ih =>
    change (swap a x)*((x::xs)++(b::bs)).formPerm = _
    rw [ih]
    simp [mul_assoc]

/-- Cutting the oriented cycle at a and b gives precisely its two consecutive
sublists; in particular the pivot piece has the first prescribed length. -/
theorem cut_cycle (a b : α) (as bs : List α) (h : b ∉ a::as) :
    swap a b * ((a::as)++(b::bs)).formPerm = (a::as).formPerm * (b::bs).formPerm := by
  rw [append_cycle, Equiv.mul_swap_eq_swap_mul, List.formPerm_apply_getLast,
    List.formPerm_apply_of_notMem h]
  simp [← mul_assoc]

theorem rewire_cut (a b : α) (as bs : List α) (h : b ∉ a::as) :
    rewire (oriented (((a::as)++(b::bs)).formPerm)) ((a,false),(b,false)) =
      oriented ((a::as).formPerm * (b::bs).formPerm) := by
  rw [rewire_same_color, cut_cycle a b as bs h]

#print axioms rewire_cut
end HalfWords
