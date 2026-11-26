import Mathlib

/-! The connectedness filter in the two-part computation, from Definition 3.8.
Labels in the concrete inputs start at zero. -/
namespace Hurwitz.Connectivity
open Equiv
variable {V : Type*} [DecidableEq V]

def swaps (xs : List (V × V)) : List (Perm V) := xs.map (fun z ↦ swap z.1 z.2)

def generated (std : Perm V) (xs : List (V × V)) : Subgroup (Perm V) :=
  Subgroup.closure {p | p ∈ std :: swaps xs}

def CanMove (H : Subgroup (Perm V)) (x y : V) : Prop := ∃ p ∈ H, p x = y

omit [DecidableEq V] in
private theorem chain {H : Subgroup (Perm V)} {x y z : V} :
    CanMove H x y → CanMove H y z → CanMove H x z := by
  rintro ⟨p,hp,rfl⟩ ⟨q,hq,rfl⟩
  exact ⟨q*p,H.mul_mem hq hp,rfl⟩

omit [DecidableEq V] in
private theorem reverse {H : Subgroup (Perm V)} {x y : V} :
    CanMove H x y → CanMove H y x := by
  rintro ⟨p,hp,rfl⟩
  exact ⟨p⁻¹,H.inv_mem hp,p.symm_apply_apply _⟩

private def stabilizer (c : V → Bool) : Subgroup (Perm V) where
  carrier := {p | ∀ i, c (p i) = c i}
  one_mem' _ := rfl
  mul_mem' hp hq i := (hp _).trans (hq i)
  inv_mem' {p} hp i := (by simpa using (hp (p.symm i)).symm)

private theorem swap_stabilizes {c : V → Bool} {x y : V} (h : c x = c y) :
    swap x y ∈ stabilizer c := by
  intro i
  by_cases hx : i = x
  · simpa [hx] using h.symm
  by_cases hy : i = y
  · simpa [hy] using h
  simp [swap_apply_def,hx,hy]

private theorem std_mem (std : Perm V) (xs : List (V × V)) :
    std ∈ generated std xs := Subgroup.subset_closure (List.mem_cons_self ..)

private theorem swap_mem (std : Perm V) {xs : List (V × V)} {a : V × V} (ha : a ∈ xs) :
    swap a.1 a.2 ∈ generated std xs := by
  apply Subgroup.subset_closure
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a,ha,rfl⟩)

private theorem matching_mem (std m : Perm V) (xs : List (V × V))
    (he : (swaps xs).prod * m * (swaps xs).prod⁻¹ = std) : m ∈ generated std xs := by
  let H := generated std xs
  have hp : (swaps xs).prod ∈ H := by
    apply H.list_prod_mem
    intro p h
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    exact swap_mem std ha
  have h : (swaps xs).prod⁻¹ * std * (swaps xs).prod ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem hp) (std_mem std xs)) hp
  rw [← he] at h
  simpa [mul_assoc] using h

private theorem bool_other {a b c : Bool} (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Every endpoint-valid word has the original matching in its generated group.
If the overlay has two connected sides, a crossing is necessary and sufficient
for transitivity, even when a word repeats a transposition. -/
theorem transitive_iff_crossing (std m : Perm V) (side : V → Bool)
    (hs : ∀ i, side (std i) = side i) (hne : ∃ i j, side i ≠ side j)
    (within : ∀ H : Subgroup (Perm V), std ∈ H → m ∈ H →
      ∀ i j, side i = side j → CanMove H i j)
    (xs : List (V × V)) (he : (swaps xs).prod * m * (swaps xs).prod⁻¹ = std) :
    MulAction.IsPretransitive (generated std xs) V ↔ ∃ a ∈ xs, side a.1 ≠ side a.2 := by
  let H := generated std xs
  constructor
  · intro ht
    by_contra! hn
    have hle : H ≤ stabilizer side := by
      apply (Subgroup.closure_le (K := stabilizer side)).mpr
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hs
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
        exact swap_stabilizes (hn a ha)
    obtain ⟨x,y,hxy⟩ := hne
    obtain ⟨p,hp⟩ := ht.exists_smul_eq x y
    have hm := hle p.property x
    change p.val x = y at hp
    exact hxy ((congrArg side hp) ▸ hm.symm)
  · rintro ⟨a,ha,hab⟩
    have conn := within H (std_mem std xs) (matching_mem std m xs he)
    have cross : CanMove H a.1 a.2 := ⟨_,swap_mem std ha,swap_apply_left _ _⟩
    constructor
    intro x y
    suffices h : CanMove H x y by
      obtain ⟨p,hp,hy⟩ := h
      exact ⟨⟨p,hp⟩,hy⟩
    by_cases hxy : side x = side y
    · exact conn x y hxy
    by_cases hx : side x = side a.1
    · exact chain (chain (conn _ _ hx) cross) (conn _ _ (bool_other hab (hx ▸ hxy)))
    · have hb := bool_other (Ne.symm hx) hab
      exact chain (chain (conn _ _ hb) (reverse cross)) (conn _ _ (bool_other hx hxy))

def std5 : Perm (Fin 10) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9
def mat5 : Perm (Fin 10) := swap 1 2 * swap 3 4 * swap 5 0 * swap 7 8 * swap 9 6
def std6 : Perm (Fin 12) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9 * swap 10 11
def mat6 : Perm (Fin 12) := swap 1 2 * swap 3 4 * swap 5 6 * swap 7 0 * swap 9 10 * swap 11 8

omit [DecidableEq V] in
private theorem within_of_paths (std m : Perm V) (side : V → Bool) (r : ℕ)
    (h : ∀ i j, side i = side j → ∃ k : Fin r, ∃ b : Bool,
      (((std*m)^k.val) * (if b then std else 1)) i = j)
    (H : Subgroup (Perm V)) (hs : std ∈ H) (hm : m ∈ H) :
    ∀ i j, side i = side j → CanMove H i j := by
  intro i j hside
  obtain ⟨k,b,he⟩ := h i j hside
  refine ⟨_,H.mul_mem (H.pow_mem (H.mul_mem hs hm) _) ?_,he⟩
  cases b
  · exact H.one_mem
  · exact hs

set_option maxRecDepth 12000 in
theorem transitive_32 (xs : List (Fin 10 × Fin 10))
    (he : (swaps xs).prod * mat5 * (swaps xs).prod⁻¹ = std5) :
    MulAction.IsPretransitive (generated std5 xs) (Fin 10) ↔
      ∃ a ∈ xs, decide (a.1.val < 6) ≠ decide (a.2.val < 6) := by
  apply transitive_iff_crossing std5 mat5 (fun i ↦ decide (i.val < 6))
    (by decide) ⟨0,6,by decide⟩ _ xs he
  exact within_of_paths _ _ _ 3 (by decide)

set_option maxRecDepth 12000 in
theorem transitive_42 (xs : List (Fin 12 × Fin 12))
    (he : (swaps xs).prod * mat6 * (swaps xs).prod⁻¹ = std6) :
    MulAction.IsPretransitive (generated std6 xs) (Fin 12) ↔
      ∃ a ∈ xs, decide (a.1.val < 8) ≠ decide (a.2.val < 8) := by
  apply transitive_iff_crossing std6 mat6 (fun i ↦ decide (i.val < 8))
    (by decide) ⟨0,8,by decide⟩ _ xs he
  exact within_of_paths _ _ _ 4 (by decide)

#print axioms transitive_32
#print axioms transitive_42
end Hurwitz.Connectivity
