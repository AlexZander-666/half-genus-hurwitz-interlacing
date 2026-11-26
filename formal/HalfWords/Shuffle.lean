import Mathlib

namespace HalfWords
variable {A I : Type*} [LinearOrder I]

def weave (key : A→I) (xs ys : List A) :=
  List.merge xs ys (fun a b => decide (key b ≤ key a))

theorem weave_sorted (key : A→I) {xs ys : List A}
    (hx : xs.Pairwise (fun a b => key b ≤ key a)) (hy : ys.Pairwise (fun a b => key b ≤ key a)) :
    (weave key xs ys).Pairwise (fun a b => key b ≤ key a) := by
  simpa [weave] using List.pairwise_merge (le := fun a b => decide (key b ≤ key a))
    (fun a b c => by simpa using (fun h g => le_trans g h : key b≤key a → key c≤key b → key c≤key a))
    (fun a b => by simpa using le_total (key b) (key a)) xs ys (by simpa using hx) (by simpa using hy)

theorem weave_filters (key : A→I) (side : I→Bool) (xs ys : List A)
    (hx : ∀x∈xs,side (key x)=true) (hy : ∀y∈ys,side (key y)=false) :
    (weave key xs ys).filter (fun x => side (key x)) = xs ∧
    (weave key xs ys).filter (fun x => !(side (key x))) = ys := by
  induction xs generalizing ys with
  | nil => simpa [weave,List.filter_eq_nil_iff] using hy
  | cons x xs ih =>
    induction ys with
    | nil => simpa [weave,List.filter_eq_nil_iff,List.filter_eq_self] using hx
    | cons y ys jy =>
      have xh := hx x List.mem_cons_self
      have yh := hy y List.mem_cons_self
      by_cases cmp : key y ≤ key x
      · have step := ih (y::ys) (fun a ha => hx a (List.mem_cons_of_mem _ ha)) hy
        simpa [weave,List.merge,cmp,xh] using step
      · have step := jy (fun a ha => hy a (List.mem_cons_of_mem _ ha))
        simpa [weave,List.merge,cmp,yh] using step

/-- Within each component equal hives retain the original chronology.
Distinct sides cannot tie because the side is determined by the hive. -/
theorem weave_recover (key : A→I) (side : I→Bool) {xs : List A}
    (sorted : xs.Pairwise (fun a b => key b≤key a)) :
    weave key (xs.filter (fun x => side (key x))) (xs.filter (fun x => !(side (key x)))) = xs := by
  induction xs with
  | nil => simp [weave]
  | cons a xs ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp sorted
    have rest := ih tail
    cases bit : side (key a) with
    | true =>
      simp only [List.filter_cons,bit,Bool.not_true,Bool.false_eq_true,if_false,if_true]
      cases eq : xs.filter (fun x => !(side (key x))) with
      | nil => simpa [weave,eq] using congrArg (List.cons a) rest
      | cons c cs =>
        have cMem : c ∈ xs := (List.mem_filter.mp (eq ▸ List.mem_cons_self)).1
        simpa [weave,eq,List.merge,head c cMem] using congrArg (List.cons a) rest
    | false =>
      simp only [List.filter_cons,bit,Bool.not_false,Bool.false_eq_true,if_false,if_true]
      cases eq : xs.filter (fun x => side (key x)) with
      | nil => simpa [weave,eq] using congrArg (List.cons a) rest
      | cons c cs =>
        have cm := List.mem_filter.mp (show c ∈ xs.filter (fun x => side (key x)) from eq ▸ List.mem_cons_self)
        have diff : key a ≠ key c := fun he => by simpa [← he,bit] using cm.2
        have lt := lt_of_le_of_ne (head c cm.1) diff.symm
        simpa [weave,eq,List.merge,not_le.mpr lt] using congrArg (List.cons a) rest

#print axioms weave_recover
end HalfWords
