import Mathlib

/-! The normalized signs on the overlay of two perfect matchings (Definition 4.1). -/
namespace Hurwitz.Charge
open Equiv Equiv.Perm

variable {V : Type*} (s t : Perm V)

def Edge (x y : V) : Prop := s x = y ∨ t x = y
abbrev Reach := Relation.EqvGen (Edge s t)

structure Valid [LE V] (color : V → Bool) : Prop where
  first (x) : color (s x) = !(color x)
  second (x) : color (t x) = !(color x)
  maximum (x) : (∀ y, Reach s t x y → y ≤ x) → color x = true

theorem unique [Fintype V] [LinearOrder V] {c d : V → Bool}
    (hc : Valid s t c) (hd : Valid s t d) : c = d := by
  classical
  have propagate {x y} (h : Reach s t x y) : (c x = d x ↔ c y = d y) := by
    induction h with
    | rel a b h =>
      rcases h with h | h <;> subst b
      · simp [hc.first, hd.first]
      · simp [hc.second, hd.second]
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ik => exact ih.trans ik
  funext x
  let C := Finset.univ.filter (Reach s t x)
  have hx : x ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl _⟩
  let m := C.max' ⟨x,hx⟩
  have hm : Reach s t x m := (Finset.mem_filter.mp (C.max'_mem ⟨x,hx⟩)).2
  have biggest (y) (hy : Reach s t m y) : y ≤ m :=
    C.le_max' _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, .trans _ _ _ hm hy⟩)
  exact (propagate hm).mpr ((hc.maximum m biggest).trans (hd.maximum m biggest).symm)

variable (hs : s⁻¹ = s) (ht : t⁻¹ = t)

include hs ht in
private theorem first_reflect (j : ℤ) : s * (s*t)^j = (s*t)^(-j) * s := by
  have he : s * (s*t) * s⁻¹ = (s*t)⁻¹ := by
    rw [mul_inv_rev, ht, hs]
    have hss : s * s = 1 := by calc s * s = s * s⁻¹ := by rw [hs]
                                  _ = 1 := mul_inv_cancel s
    rw [← mul_assoc s s t,hss,one_mul]
  have h := congrArg (fun a : Perm V => a ^ j) he
  rw [conj_zpow, inv_zpow, ← zpow_neg] at h
  calc
    _ = (s * (s*t)^j * s⁻¹) * s := by group
    _ = _ := by rw [h]

include hs ht in
theorem separate (fs : ∀ x, s x ≠ x) (ft : ∀ x, t x ≠ x) (x : V) :
    ¬ (s*t).SameCycle x (s x) := by
  rintro ⟨i,hi⟩
  let r := s*t
  change (r^i) x = s x at hi
  have reflect (j : ℤ) : s ((r^j) x) = (r^(i-j)) x := by
    have h := DFunLike.congr_fun (first_reflect s t hs ht j) x
    simp only [Perm.mul_apply] at h
    change s ((r ^ j) x) = (r ^ (-j)) (s x) at h
    rw [h, ← hi, ← Perm.mul_apply, ← zpow_add]
    congr 2
    omega
  let j := i / 2
  by_cases he : i = j+j
  · apply fs ((r^j) x)
    simpa only [show i-j=j by omega] using reflect j
  · apply ft ((r^j) x)
    have hsr : s*r=t := by
      change s*(s*t)=t
      calc s * (s*t) = (s⁻¹*s)*t := by rw [hs, mul_assoc]
           _ = t := by simp
    have h : t ((r^j) x) = s ((r^(j+1)) x) := by
      rw [← hsr, Perm.mul_apply, add_comm j 1, zpow_one_add, Perm.mul_apply]
      rfl
    rw [h, reflect, show i-(j+1)=j by dsimp [j] at *; omega]

section Finite
variable [Fintype V] [LinearOrder V]

def orbit (r : Perm V) (x : V) := Finset.univ.filter (r.SameCycle x)

private theorem mem_orbit (r : Perm V) {x y : V} : y ∈ orbit r x ↔ r.SameCycle x y := by simp [orbit]

def peak (r : Perm V) (x : V) : V := (orbit r x).max' ⟨x,(mem_orbit r).mpr .rfl⟩

theorem peak_mem (r : Perm V) (x : V) : r.SameCycle x (peak r x) :=
  (mem_orbit r).mp (Finset.max'_mem _ _)

private theorem le_peak (r : Perm V) (x : V) : x ≤ peak r x :=
  Finset.le_max' _ _ ((mem_orbit r).mpr .rfl)

theorem peak_eq_of_same {r : Perm V} {x y : V} (h : r.SameCycle x y) :
    peak r x = peak r y := by
  have e : orbit r x = orbit r y := by
    ext z
    rw [mem_orbit, mem_orbit]
    exact ⟨h.symm.trans, h.trans⟩
  unfold peak
  congr 1

def canonical (x : V) : Bool := decide (peak (s*t) (s x) < peak (s*t) x)

omit [LinearOrder V] in
private theorem reach_same {x y : V} (h : (s*t).SameCycle x y) : Reach s t x y := by
  obtain ⟨i,rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction i with
  | zero => simpa using Relation.EqvGen.refl (r := Edge s t) x
  | succ j ih =>
    rw [pow_succ', Perm.mul_apply, Perm.mul_apply]
    exact .trans _ _ _ ih (.trans _ _ _ (.rel _ _ (Or.inr rfl)) (.rel _ _ (Or.inl rfl)))

include hs ht in
theorem canonical_valid (fs : ∀ x, s x ≠ x) (ft : ∀ x, t x ≠ x) :
    Valid s t (canonical s t) := by
  let r := s*t
  have ss (x : V) : s (s x) = x := by
    exact (congrArg (fun u : Perm V => u (s x)) hs.symm).trans (s.symm_apply_apply x)
  have tt (x : V) : t (t x) = x := by
    exact (congrArg (fun u : Perm V => u (t x)) ht.symm).trans (t.symm_apply_apply x)
  have ne (x : V) : peak r x ≠ peak r (s x) := by
    intro eq
    apply separate s t hs ht fs ft x
    exact (peak_mem r x).trans (eq ▸ (peak_mem r (s x)).symm)
  have inv (x : V) : decide (peak r x < peak r (s x)) = !decide (peak r (s x) < peak r x) := by
    rcases lt_or_gt_of_ne (ne x) with h|h
    · simp [h, not_lt.mpr h.le]
    · simp [h, not_lt.mpr h.le]
  constructor
  · intro x
    unfold canonical
    rw [ss]
    exact inv x
  · intro x
    have a : peak r (s (t x)) = peak r x :=
      peak_eq_of_same (r := r) (x := r x) (y := x) (sameCycle_apply_left.mpr .rfl)
    have b : peak r (t x) = peak r (s x) := by
      apply peak_eq_of_same
      have h : r.SameCycle (t x) (r (t x)) := sameCycle_apply_right.mpr .rfl
      simpa [r, Perm.mul_apply, tt] using h
    change decide (peak r (s (t x)) < peak r (t x)) = _
    rw [a,b]
    exact inv x
  · intro x hx
    apply decide_eq_true
    apply lt_of_le_of_ne
    · exact (hx _ (.trans _ _ _ (.rel _ _ (Or.inl rfl))
        (reach_same s t (peak_mem r (s x))))).trans (le_peak r x)
    · exact (ne x).symm

theorem existsUnique_valid (hs : s⁻¹ = s) (ht : t⁻¹ = t)
    (fs : ∀ x, s x ≠ x) (ft : ∀ x, t x ≠ x) : ∃! c, Valid s t c :=
  ⟨canonical s t, canonical_valid s t hs ht fs ft, fun _ hc =>
    unique s t hc (canonical_valid s t hs ht fs ft)⟩

/-- The exponent of b in Definition 4.1 for the selected transposition. -/
def flip (x y : V) : ℕ := if canonical s t x = canonical s t y then 0 else 1

theorem flip_of_valid {c : V → Bool} (hc : Valid s t c)
    (hs : s⁻¹ = s) (ht : t⁻¹ = t) (fs : ∀ x, s x ≠ x) (ft : ∀ x, t x ≠ x)
    (x y : V) : flip s t x y = if c x = c y then 0 else 1 := by
  rw [flip, unique s t (canonical_valid s t hs ht fs ft) hc]

theorem flip_at_top_partner [OrderTop V] (c : V → Bool) (hc : Valid s t c)
    (hs : s⁻¹ = s) (ht : t⁻¹ = t) (fs : ∀ x, s x ≠ x) (ft : ∀ x, t x ≠ x)
    (i : V) : flip s t i (s ⊤) = if c i then 1 else 0 := by
  have h : c (⊤ : V) = true := hc.maximum _ (fun _ _ => le_top)
  rw [flip_of_valid s t hc hs ht fs ft, hc.first, h]
  cases c i <;> rfl

end Finite

section Embedding

variable {W : Type*} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]

omit [Fintype V] [Fintype W] in
private theorem powers_map (r : Perm V) (r' : Perm W) (e : V ↪o W)
    (comm : ∀ x, r' (e x) = e (r x)) (j : ℕ) (x : V) :
    (r'^j) (e x) = e ((r^j) x) := by
  induction j with
  | zero => simp
  | succ k ih => simp only [pow_succ', Perm.mul_apply, ih, comm]

theorem peak_map (r : Perm V) (r' : Perm W) (e : V ↪o W)
    (comm : ∀ x, r' (e x) = e (r x)) (x : V) :
    peak r' (e x) = e (peak r x) := by
  apply le_antisymm
  · obtain ⟨j,hj⟩ := (peak_mem r' (e x)).exists_nat_pow_eq
    rw [← hj, powers_map r r' e comm]
    exact e.monotone (Finset.le_max' _ _ ((mem_orbit r).mpr (SameCycle.rfl.pow_right)))
  · obtain ⟨j,hj⟩ := (peak_mem r x).exists_nat_pow_eq
    apply Finset.le_max' (orbit r' (e x))
    apply (mem_orbit r').mpr
    rw [← hj, ← powers_map r r' e comm]
    exact SameCycle.rfl.pow_right

/-- Reindexing labels, or deleting a disjoint component while keeping their
relative order, preserves every retained charge. -/
theorem canonical_map (s' t' : Perm W) (e : V ↪o W)
    (he : ∀ x, s' (e x) = e (s x)) (hf : ∀ x, t' (e x) = e (t x)) (x : V) :
    canonical s' t' (e x) = canonical s t x := by
  have comm (v : V) : (s'*t') (e v) = e ((s*t) v) := by simp [Perm.mul_apply, he, hf]
  simp only [canonical, he, peak_map (s*t) (s'*t') e comm, e.lt_iff_lt]

theorem flip_map (s' t' : Perm W) (e : V ↪o W) (he : ∀ x, s' (e x) = e (s x))
    (hf : ∀ x, t' (e x) = e (t x)) (x y : V) :
    flip s' t' (e x) (e y) = flip s t x y := by
  simp only [flip, canonical_map s t s' t' e he hf]

end Embedding

#print axioms existsUnique_valid
#print axioms canonical_valid
#print axioms flip_at_top_partner
#print axioms flip_map
end Hurwitz.Charge
