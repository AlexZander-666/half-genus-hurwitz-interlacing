import HalfWords.Coordinates

namespace HalfWords
open Equiv Hurwitz Hurwitz.MatchingWords
variable {V : Type*} [DecidableEq V] [Finite V]

/-- Joining the left attachments of two distinct cycles identifies their
old equivalence classes. All other classes, including singletons, persist. -/
theorem same_color_join (r : Perm V) {a b : V} (h : ¬r.SameCycle a b) (x y : V) :
    (swap a b*r).SameCycle x y ↔
      Relation.EqvGen (fun i j => r.SameCycle i j ∨ i=a ∧ j=b) x y := by
  let R := swap a b*r
  let J := Relation.EqvGen (fun i j => r.SameCycle i j ∨ i=a ∧ j=b)
  have jswap (v : V) : J v (swap a b v) := by
    have ab : J a b := .rel _ _ (Or.inr ⟨rfl,rfl⟩)
    by_cases ea : v=a
    · subst v; simpa using ab
    by_cases eb : v=b
    · subst v; simpa using Relation.EqvGen.symm _ _ ab
    rw [swap_apply_of_ne_of_ne ea eb]
    exact .refl _
  have back (i : ℕ) : R.SameCycle a ((r^i) a) := by
    induction i with
    | zero => exact .rfl
    | succ i ih =>
      rw [pow_succ',Perm.mul_apply]
      by_cases ha : r ((r ^ i) a) = a
      · rw [ha]
      have hb : r ((r ^ i) a) ≠ b := fun e =>
        h ⟨((i+1:ℕ):ℤ),by rw [zpow_natCast,pow_succ',Perm.mul_apply]; exact e⟩
      have m := ih.apply_right
      simpa [R,Perm.mul_apply,swap_apply_of_ne_of_ne ha hb] using m
  have prev : r.SameCycle a (r.symm a) := by simpa using (Perm.SameCycle.rfl (f:=r) (x:=a))
  obtain ⟨i,hi⟩ := prev.exists_nat_pow_eq
  have first : R.SameCycle a (r.symm a) := hi ▸ back i
  have hab : R.SameCycle a b := by simpa [R,Perm.mul_apply] using first.apply_right
  have rswap (v : V) : R.SameCycle v (swap a b v) := by
    by_cases ea : v=a
    · subst v; simpa using hab
    by_cases eb : v=b
    · subst v; simpa using hab.symm
    rw [swap_apply_of_ne_of_ne ea eb]
  constructor
  · intro conn
    obtain ⟨j,hj⟩ := conn.exists_nat_pow_eq
    have walk (i : ℕ) : J x ((R^i) x) := by
      induction i with
      | zero => exact .refl _
      | succ i ih =>
        rw [pow_succ',Perm.mul_apply]
        let v := (R^i) x
        have step : J v (r v) := .rel _ _ (Or.inl Perm.SameCycle.rfl.apply_right)
        exact .trans _ _ _ ih (.trans _ _ _ step (jswap _))
    exact hj ▸ walk j
  · intro conn
    induction conn with
    | rel u v edge =>
      rcases edge with orig|⟨rfl,rfl⟩
      · obtain ⟨j,hj⟩ := orig.exists_nat_pow_eq
        have walk (i : ℕ) : R.SameCycle u ((r^i) u) := by
          induction i with
          | zero => exact .rfl
          | succ i ih =>
            rw [pow_succ', Perm.mul_apply]
            exact ih.apply_right.trans (rswap _).symm
        exact hj ▸ walk j
      · exact hab
    | refl => exact .rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ij => exact ih.trans ij

theorem same_color_join_components (r : Perm V) {a b : V} (h : ¬r.SameCycle a b)
    (x y : V × Bool) :
    Charge.Reach (oriented 1) (rewire (oriented r) ((a,false),(b,false))) x y ↔
      Relation.EqvGen (fun i j => r.SameCycle i j ∨ i=a ∧ j=b) x.1 y.1 := by
  rw [rewire_same_color,oriented_reach_iff,same_color_join r h]

#print axioms same_color_join_components
end HalfWords
