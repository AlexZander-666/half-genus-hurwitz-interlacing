import HalfWords.Surgery
import Hurwitz.Charge

namespace HalfWords
open Equiv
variable {V : Type*}

/-- Coordinates by the negative standard partner and the charge bit. -/
def chargedCoordinates (s : Perm V) (col : V → Bool) (flip : ∀ x, col (s x) = !col x)
    (ss : Function.Involutive s) : {v // col v = false} × Bool ≃ V where
  toFun := fun (w,b) => if b then s w.val else w.val
  invFun := fun x => if hx : col x then (⟨s x,by simp [flip,hx]⟩,true)
    else (⟨x,by simpa using hx⟩,false)
  left_inv := by
    rintro ⟨⟨v,hv⟩,b⟩
    cases b <;> simp [hv,flip,ss v]
  right_inv := by
    intro x
    by_cases h : col x <;> simp [h,ss x]

def successor (s M : Perm V) (col : V → Bool)
    (fs : ∀ x, col (s x) = !col x) (fm : ∀ x, col (M x) = !col x)
    (ss : Function.Involutive s) (mm : Function.Involutive M) : Perm {v // col v = false} where
  toFun := fun i => ⟨M (s i),by simp [fm,fs,i.property]⟩
  invFun := fun i => ⟨s (M i),by simp [fs,fm,i.property]⟩
  left_inv i := Subtype.ext ((congrArg s (mm (s i))).trans (ss i))
  right_inv i := Subtype.ext ((congrArg M (ss (M i))).trans (mm i))

/-- The original matching is the two-color matching with permutation
successor, on a set defined directly from either valid charge assignment. -/
theorem matching_coordinates (s M : Perm V) (col : V → Bool)
    (fs : ∀ x, col (s x) = !col x) (fm : ∀ x, col (M x) = !col x)
    (ss : Function.Involutive s) (mm : Function.Involutive M) :
    (chargedCoordinates s col fs ss).permCongrHom
      (oriented (successor s M col fs fm ss mm)) = M := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,b⟩,rfl⟩ := (chargedCoordinates s col fs ss).surjective x
  change (chargedCoordinates s col fs ss) (oriented _ ((chargedCoordinates s col fs ss).symm
    ((chargedCoordinates s col fs ss) (i,b)))) = _
  rw [symm_apply_apply]
  cases b
  · exact ss (M i)
  · rfl

/-- Any pair of actual fixed-point-free involutions has these coordinates
using the canonical charge of Definition 4.1, with no cycle-type assumption. -/
theorem canonical_matching_coordinates [Fintype V] [LinearOrder V] (s M : Perm V)
    (hs : s⁻¹ = s) (hm : M⁻¹ = M) (ns : ∀v, s v ≠ v) (nm : ∀v, M v ≠ v) :
    ∃ e : {v // Hurwitz.Charge.canonical s M v = false} × Bool ≃ V,
    ∃ r : Perm {v // Hurwitz.Charge.canonical s M v = false}, e.permCongrHom (oriented r) = M ∧
      ∀ i b, e (i,!b) = s (e (i,b)) := by
  let col := Hurwitz.Charge.canonical s M
  have valid := Hurwitz.Charge.canonical_valid s M hs hm ns nm
  have ss (x : V) : s (s x) = x := by
    conv_lhs => lhs; rw [← hs]
    exact s.symm_apply_apply x
  have mm (x : V) : M (M x) = x := by
    conv_lhs => lhs; rw [← hm]
    exact M.symm_apply_apply x
  refine ⟨chargedCoordinates s col valid.first ss,successor s M col valid.first valid.second ss mm,
    matching_coordinates ..,?_⟩
  intro i b
  cases b <;> simp [chargedCoordinates,ss]

/-- The alternating components, including standard pairs, are precisely the
permutation cycles on the canonical negative representatives. -/
theorem oriented_reach_iff [Finite V] (r : Perm V) (x y : V × Bool) :
    Hurwitz.Charge.Reach (oriented 1) (oriented r) x y ↔ r.SameCycle x.1 y.1 := by
  constructor
  · intro h
    induction h with
    | rel x y h =>
      rcases x with ⟨a,b⟩
      rcases h with h | h <;> subst y
      · cases b <;> exact Perm.SameCycle.rfl
      · cases b <;> simpa using (Perm.SameCycle.rfl (f:=r) (x:=a))
    | refl => exact .rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ik => exact ih.trans ik
  · rintro h
    rcases x with ⟨a,ba⟩
    rcases y with ⟨b,bb⟩
    obtain ⟨j,ej⟩ := h.exists_nat_pow_eq
    change (r^j) a = b at ej
    subst b
    let R := Hurwitz.Charge.Reach (oriented (1 : Perm V)) (oriented r)
    have pair (v : V) : R (v,false) (v,true) := .rel _ _ (Or.inl rfl)
    have step (v : V) : R (v,false) (r v,false) :=
      .trans _ _ _ (pair v) (.rel _ _ (Or.inr rfl))
    have forward : R (a,false) ((r^j) a,false) := by
      clear h
      induction j with
      | zero => exact .refl _
      | succ j ih =>
        rw [pow_succ',Perm.mul_apply]
        exact .trans _ _ _ ih (step _)
    have init : R (a,ba) (a,false) := by
      cases ba
      · exact .refl _
      · exact .symm _ _ (pair a)
    have finish : R ((r^j) a,false) ((r^j) a,bb) := by
      cases bb
      · exact .refl _
      · exact pair _
    exact .trans _ _ _ init (.trans _ _ _ forward finish)

#print axioms oriented_reach_iff
#print axioms canonical_matching_coordinates
end HalfWords
