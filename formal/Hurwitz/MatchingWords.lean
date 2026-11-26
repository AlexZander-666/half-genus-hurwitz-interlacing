import Hurwitz.Connectivity

/-! From one-based connected monotone factorizations to chronological words on
the actual partner tuples for the two profiles. -/

namespace Hurwitz.MatchingWords

open Equiv Connectivity

abbrev PaperLabel (n : ℕ) := {i : ℕ // 1 ≤ i ∧ i ≤ n}

/-- The paper numbers the same vertices from one instead of from zero. -/
def paperLabelEquiv (n : ℕ) : Fin n ≃ PaperLabel n where
  toFun i := ⟨i.val + 1, by omega, by have := i.isLt; omega⟩
  invFun i := ⟨i.val - 1, by have := i.property; omega⟩
  left_inv i := by apply Fin.ext; simp
  right_inv i := by apply Subtype.ext; exact Nat.sub_add_cancel i.property.1

instance (n : ℕ) : Fintype (PaperLabel n) :=
  Fintype.ofEquiv (Fin n) (paperLabelEquiv n)

@[simp] theorem paperLabelEquiv_val (n : ℕ) (i : Fin n) :
    (paperLabelEquiv n i).val = i.val + 1 := rfl

/-- Swap the labels of a matching, retaining all its pairs. -/
def rewire {V : Type*} [DecidableEq V] (m : Perm V) (a : V × V) : Perm V :=
  swap a.1 a.2 * m * (swap a.1 a.2)⁻¹

theorem rewire_apply {V : Type*} [DecidableEq V] (m : Perm V) (a : V × V) (v : V) :
    rewire m a v = swap a.1 a.2 (m (swap a.1 a.2 v)) := rfl

theorem rewire_preserves_matching {V : Type*} [DecidableEq V] (m : Perm V)
    (hm : Function.Involutive m) (hf : ∀ v, m v ≠ v) (a : V × V) :
    Function.Involutive (rewire m a) ∧ ∀ v, rewire m a v ≠ v := by
  constructor
  · intro v
    simp only [rewire_apply, Equiv.swap_apply_self]
    rw [hm (swap a.1 a.2 v), Equiv.swap_apply_self]
  · intro v hv
    rw [rewire_apply, Equiv.swap_apply_eq_iff] at hv
    exact hf _ hv

/-- The partner-entry update on a raw vector. Swapping the members of a
pair leaves the vector unchanged. Otherwise only four entries can change. -/
def updatePartners {V : Type*} [DecidableEq V] (m : V → V) (a : V × V) (v : V) : V :=
  if m a.1 = a.2 then m v
  else if v = a.1 then m a.2
  else if v = a.2 then m a.1
  else if v = m a.1 then a.2
  else if v = m a.2 then a.1
  else m v

theorem rewire_eq_updatePartners {V : Type*} [DecidableEq V] (m : Perm V)
    (hm : Function.Involutive m) (hf : ∀ v, m v ≠ v) (a : V × V) (v : V) :
    rewire m a v = updatePartners m a v := by
  rw [rewire_apply]
  unfold updatePartners
  by_cases hpair : m a.1 = a.2
  · rw [if_pos hpair]
    have hrev : m a.2 = a.1 := by simpa only [hpair] using hm a.1
    by_cases hv₁ : v = a.1
    · rw [hv₁, Equiv.swap_apply_left, hrev, Equiv.swap_apply_left, hpair]
    by_cases hv₂ : v = a.2
    · rw [hv₂, Equiv.swap_apply_right, hpair, Equiv.swap_apply_right, hrev]
    have hm₁ : m v ≠ a.1 := fun he ↦ hv₂ (m.injective (he.trans hrev.symm))
    have hm₂ : m v ≠ a.2 := fun he ↦ hv₁ (m.injective (he.trans hpair.symm))
    rw [Equiv.swap_apply_of_ne_of_ne hv₁ hv₂, Equiv.swap_apply_of_ne_of_ne hm₁ hm₂]
  · rw [if_neg hpair]
    have hrev : m a.2 ≠ a.1 := by
      intro he
      exact hpair (he ▸ hm a.2)
    by_cases hv₁ : v = a.1
    · rw [if_pos hv₁, hv₁, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hrev (hf _)]
    rw [if_neg hv₁]
    by_cases hv₂ : v = a.2
    · rw [if_pos hv₂, hv₂, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (hf _) hpair]
    rw [if_neg hv₂, Equiv.swap_apply_of_ne_of_ne hv₁ hv₂]
    by_cases hp₁ : v = m a.1
    · rw [if_pos hp₁, hp₁, hm a.1, Equiv.swap_apply_left]
    rw [if_neg hp₁]
    by_cases hp₂ : v = m a.2
    · rw [if_pos hp₂, hp₂, hm a.2, Equiv.swap_apply_right]
    rw [if_neg hp₂]
    have hm₁ : m v ≠ a.1 := fun he ↦ hp₁ (m.injective (he.trans (hm a.1).symm))
    have hm₂ : m v ≠ a.2 := fun he ↦ hp₂ (m.injective (he.trans (hm a.2).symm))
    exact Equiv.swap_apply_of_ne_of_ne hm₁ hm₂

/-- Execute the given swaps in their chronological order. -/
def execute {V : Type*} [DecidableEq V] (m : Perm V) (xs : List (V × V)) : Perm V :=
  xs.foldl rewire m

theorem execute_eq_conj {V : Type*} [DecidableEq V] (m : Perm V) (xs : List (V × V)) :
    execute m xs = (swaps xs.reverse).prod * m * (swaps xs.reverse).prod⁻¹ := by
  induction xs generalizing m with
  | nil => simp [execute, swaps]
  | cons a xs ih =>
    change execute (rewire m a) xs = _
    rw [ih]
    simp only [rewire, swaps, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    group

section Relabel

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

private theorem permCongr_swap (e : V ≃ W) (a b : V) :
    e.permCongrHom (swap a b) = swap (e a) (e b) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  by_cases ha : x = a <;> by_cases hb : x = b <;>
    simp_all [Equiv.swap_apply_def]

theorem swaps_relabel (e : V ≃ W) (xs : List (V × V)) :
    swaps (xs.map (e.prodCongr e)) = (swaps xs).map e.permCongrHom := by
  simp only [swaps, List.map_map]
  congr 1
  funext a
  exact (permCongr_swap e a.1 a.2).symm

theorem generated_relabel (e : V ≃ W) (std : Perm V) (xs : List (V × V)) :
    (generated std xs).map e.permCongrHom.toMonoidHom =
      generated (e.permCongrHom std) (xs.map (e.prodCongr e)) := by
  rw [generated, MonoidHom.map_closure, generated, swaps_relabel]
  congr 1
  ext p
  simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom, ← List.map_cons, List.mem_map]

theorem generated_reverse (std : Perm V) (xs : List (V × V)) :
    generated std xs.reverse = generated std xs := by
  unfold generated swaps
  congr 1
  ext p
  simp

omit [DecidableEq V] [DecidableEq W] in
private theorem pretransitive_relabel (e : V ≃ W) (H : Subgroup (Perm V)) :
    MulAction.IsPretransitive (H.map e.permCongrHom.toMonoidHom) W ↔
      MulAction.IsPretransitive H V := by
  constructor
  · intro h
    constructor
    intro x y
    obtain ⟨p, hp⟩ := h.exists_smul_eq (e x) (e y)
    obtain ⟨q, hq, hrel⟩ := Subgroup.mem_map.mp p.property
    refine ⟨⟨q, hq⟩, ?_⟩
    change (p.val : Perm W) (e x) = e y at hp
    change q x = y
    rw [← hrel] at hp
    exact e.injective (by simpa using hp)
  · intro h
    constructor
    intro x y
    obtain ⟨p, hp⟩ := h.exists_smul_eq (e.symm x) (e.symm y)
    refine ⟨⟨e.permCongrHom p.val, Subgroup.mem_map.mpr ⟨p.val, p.property, rfl⟩⟩, ?_⟩
    change p.val (e.symm x) = e.symm y at hp
    change e.permCongrHom p.val x = y
    simpa using congrArg e hp

theorem generated_pretransitive_relabel_iff (e : V ≃ W) (std : Perm V) (xs : List (V × V)) :
    MulAction.IsPretransitive (generated (e.permCongrHom std) (xs.map (e.prodCongr e))) W ↔
      MulAction.IsPretransitive (generated std xs) V := by
  rw [← generated_relabel]
  exact pretransitive_relabel e _

theorem endpoint_relabel_iff (e : V ≃ W) (std m : Perm V) (xs : List (V × V)) :
    (swaps (xs.map (e.prodCongr e))).prod * e.permCongrHom m *
        (swaps (xs.map (e.prodCongr e))).prod⁻¹ = e.permCongrHom std ↔
      (swaps xs).prod * m * (swaps xs).prod⁻¹ = std := by
  rw [swaps_relabel, ← map_list_prod e.permCongrHom, ← map_inv, ← map_mul, ← map_mul,
    e.permCongrHom.injective.eq_iff]

end Relabel

/-- These are the raw partner vectors used in the two starts and the two
terminal standard pairings. An entry gives the other end of a pair. -/
def initial32 : Fin 10 → Fin 10 := ![5, 2, 1, 4, 3, 0, 9, 8, 7, 6]
def initial42 : Fin 12 → Fin 12 := ![7, 2, 1, 4, 3, 6, 5, 0, 11, 10, 9, 8]
def standard32 : Fin 10 → Fin 10 := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8]
def standard42 : Fin 12 → Fin 12 := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10]

theorem tuple32_agrees : (∀ i, initial32 i = mat5 i) ∧ (∀ i, standard32 i = std5 i) := by
  decide +kernel

theorem tuple42_agrees : (∀ i, initial42 i = mat6 i) ∧ (∀ i, standard42 i = std6 i) := by
  decide +kernel

/-- All four raw partner vectors are fixed-point-free involutions. -/
theorem tuple32_matching :
    (∀ i, initial32 (initial32 i) = i ∧ initial32 i ≠ i) ∧
      (∀ i, standard32 (standard32 i) = i ∧ standard32 i ≠ i) := by
  decide +kernel

theorem tuple42_matching :
    (∀ i, initial42 (initial42 i) = i ∧ initial42 i ≠ i) ∧
      (∀ i, standard42 (standard42 i) = i ∧ standard42 i ≠ i) := by
  decide +kernel

theorem tuple32_edges_distinct : ∀ i, standard32 i ≠ initial32 i := by decide +kernel

theorem tuple42_edges_distinct : ∀ i, standard42 i ≠ initial42 i := by decide +kernel

/-- Reachability by the two edges of the raw overlay, allowing a double edge
when a pair is shared. -/
inductive OverlayReach {V : Type*} (std m : V → V) (x : V) : V → Prop
  | refl : OverlayReach std m x x
  | standard {y : V} : OverlayReach std m x y → OverlayReach std m x (std y)
  | matching {y : V} : OverlayReach std m x y → OverlayReach std m x (m y)

private theorem overlay_pair_powers {V : Type*} {std m : Perm V} {x y : V}
    (h : OverlayReach std m x y) (k : ℕ) :
    OverlayReach std m x (((std * m) ^ k) y) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.matching.standard

private theorem overlay_eq_side {V : Type*} (std m : Perm V) (side : V → Bool) (r : ℕ)
    (hs : ∀ i, side (std i) = side i) (hm : ∀ i, side (m i) = side i)
    (hreach : ∀ i j, side i = side j → ∃ k : Fin r, ∃ b : Bool,
      (((std * m)^k.val) * (if b then std else 1)) i = j) (x y : V) :
    OverlayReach std m x y ↔ side x = side y := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | standard _ ih => exact ih.trans (hs _).symm
    | matching _ ih => exact ih.trans (hm _).symm
  · intro h
    obtain ⟨k, b, hb⟩ := hreach x y h
    rw [← hb, Equiv.Perm.mul_apply]
    apply overlay_pair_powers
    cases b
    · exact OverlayReach.refl
    · exact OverlayReach.refl.standard

theorem overlay32_components (x y : Fin 10) :
    OverlayReach standard32 initial32 x y ↔ decide (x.val < 6) = decide (y.val < 6) := by
  rw [show standard32 = (std5 : Fin 10 → Fin 10) from funext tuple32_agrees.2,
    show initial32 = (mat5 : Fin 10 → Fin 10) from funext tuple32_agrees.1]
  exact overlay_eq_side std5 mat5 (fun i ↦ decide (i.val < 6)) 3 (by decide) (by decide)
    (by decide) x y

theorem overlay42_components (x y : Fin 12) :
    OverlayReach standard42 initial42 x y ↔ decide (x.val < 8) = decide (y.val < 8) := by
  rw [show standard42 = (std6 : Fin 12 → Fin 12) from funext tuple42_agrees.2,
    show initial42 = (mat6 : Fin 12 → Fin 12) from funext tuple42_agrees.1]
  exact overlay_eq_side std6 mat6 (fun i ↦ decide (i.val < 8)) 4 (by decide) (by decide)
    (by decide) x y

theorem overlay32_side_cardinalities :
    Fintype.card {i : Fin 10 // i.val < 6} = 6 ∧
      Fintype.card {i : Fin 10 // 6 ≤ i.val} = 4 := by decide +kernel

theorem overlay42_side_cardinalities :
    Fintype.card {i : Fin 12 // i.val < 8} = 8 ∧
      Fintype.card {i : Fin 12 // 8 ≤ i.val} = 4 := by decide +kernel

/-- A pair of labels untouched by the remaining swaps is present at the
terminal state exactly when it is present before that suffix. -/
theorem execute_pair_iff_of_avoids {V : Type*} [DecidableEq V] (m : Perm V)
    (xs : List (V × V)) (i j : V)
    (h : ∀ a ∈ xs, i ≠ a.1 ∧ i ≠ a.2 ∧ j ≠ a.1 ∧ j ≠ a.2) :
    execute m xs i = j ↔ m i = j := by
  induction xs generalizing m with
  | nil => rfl
  | cons a xs ih =>
    have ht := h a List.mem_cons_self
    have hi : swap a.1 a.2 i = i := Equiv.swap_apply_of_ne_of_ne ht.1 ht.2.1
    have hj : swap a.1 a.2 j = j := Equiv.swap_apply_of_ne_of_ne ht.2.2.1 ht.2.2.2
    change execute (rewire m a) xs i = j ↔ m i = j
    rw [ih (rewire m a) (fun b hb ↦ h b (List.mem_cons_of_mem _ hb))]
    change swap a.1 a.2 (m ((swap a.1 a.2).symm i)) = j ↔ _
    rw [Equiv.symm_swap, hi]
    calc
      _ ↔ swap a.1 a.2 (m i) = swap a.1 a.2 j := by rw [hj]
      _ ↔ _ := (swap a.1 a.2).injective.eq_iff

/-- Paper order composes rightmost first. The execution model processes those
swaps first, so the word is reversed as well as relabelled. -/
def paperOrder (n : ℕ) : List (Fin n × Fin n) ≃ List (PaperLabel n × PaperLabel n) where
  toFun xs := xs.reverse.map ((paperLabelEquiv n).prodCongr (paperLabelEquiv n))
  invFun ys := ys.reverse.map ((paperLabelEquiv n).symm.prodCongr (paperLabelEquiv n).symm)
  left_inv xs := by
    simp only [← List.map_reverse, List.reverse_reverse, List.map_map]
    conv_rhs => rw [← List.map_id xs]
    refine List.map_congr_left fun a _ ↦ ?_
    exact ((paperLabelEquiv n).prodCongr (paperLabelEquiv n)).symm_apply_apply a
  right_inv ys := by
    simp only [← List.map_reverse, List.reverse_reverse, List.map_map]
    conv_rhs => rw [← List.map_id ys]
    refine List.map_congr_left fun a _ ↦ ?_
    exact ((paperLabelEquiv n).prodCongr (paperLabelEquiv n)).apply_symm_apply a

@[simp] theorem paperOrder_length (n : ℕ) (xs : List (Fin n × Fin n)) :
    (paperOrder n xs).length = xs.length := by
  simp [paperOrder]

def paperStep {n : ℕ} (a : PaperLabel n × PaperLabel n) : Prop :=
  a.1.val < a.2.val ∧ a.2.val % 2 = 1

def executionStep {n : ℕ} (a : Fin n × Fin n) : Prop :=
  a.1.val < a.2.val ∧ a.2.val % 2 = 0

/-- Increasingly ordered endpoints are uniquely recoverable from their
actual transposition. -/
theorem paperStep_swap_injective {n : ℕ} {a b : PaperLabel n × PaperLabel n}
    (ha : paperStep a) (hb : paperStep b)
    (he : swap a.1 a.2 = swap b.1 b.2) : a = b := by
  have ha' : a.1 ≠ a.2 := fun e ↦ (ne_of_lt ha.1) (congrArg Subtype.val e)
  have hb' : b.1 ≠ b.2 := fun e ↦ (ne_of_lt hb.1) (congrArg Subtype.val e)
  have hs : ({a.1, a.2} : Finset (PaperLabel n)) = {b.1, b.2} := by
    simpa only [Equiv.Perm.support_swap ha', Equiv.Perm.support_swap hb'] using
      congrArg Equiv.Perm.support he
  have h₁ : a.1 = b.1 ∨ a.1 = b.2 := by
    have h : a.1 ∈ ({b.1, b.2} : Finset (PaperLabel n)) := hs ▸ (by simp)
    simpa using h
  have h₂ : a.2 = b.1 ∨ a.2 = b.2 := by
    have h : a.2 ∈ ({b.1, b.2} : Finset (PaperLabel n)) := hs ▸ (by simp)
    simpa using h
  rcases h₁ with h₁₁ | h₁₂ <;> rcases h₂ with h₂₁ | h₂₂
  · exact (ha' (h₁₁.trans h₂₁.symm)).elim
  · exact Prod.ext h₁₁ h₂₂
  · have hleft := congrArg Subtype.val h₁₂
    have hright := congrArg Subtype.val h₂₁
    have hap := ha.1
    have hbp := hb.1
    omega
  · exact (ha' (h₁₂.trans h₂₂.symm)).elim

theorem paper_word_swaps_injective {n : ℕ} {ys zs : List (PaperLabel n × PaperLabel n)}
    (hy : ∀ a ∈ ys, paperStep a) (hz : ∀ a ∈ zs, paperStep a)
    (he : swaps ys = swaps zs) : ys = zs := by
  induction ys generalizing zs with
  | nil => simpa [swaps] using he
  | cons a ys ih =>
    cases zs with
    | nil => simp [swaps] at he
    | cons b zs =>
      simp only [swaps, List.map_cons, List.cons.injEq] at he
      have hab := paperStep_swap_injective (hy a List.mem_cons_self)
        (hz b List.mem_cons_self) he.1
      have hl := ih (fun p hp ↦ hy p (List.mem_cons_of_mem a hp))
        (fun p hp ↦ hz p (List.mem_cons_of_mem b hp)) he.2
      rw [hab, hl]

/-- Both descriptions use weak monotonicity, so repeated labels and repeated
transpositions are retained. -/
theorem paperOrder_pairwise_iff (n : ℕ) (xs : List (Fin n × Fin n)) :
    (paperOrder n xs).Pairwise (fun a b ↦ a.2.val ≤ b.2.val) ↔
      xs.Pairwise (fun a b ↦ b.2.val ≤ a.2.val) := by
  change (xs.reverse.map ((paperLabelEquiv n).prodCongr (paperLabelEquiv n))).Pairwise _ ↔ _
  rw [List.pairwise_map, List.pairwise_reverse]
  change xs.Pairwise (fun a b ↦ b.2.val + 1 ≤ a.2.val + 1) ↔ _
  simp only [Nat.add_le_add_iff_right]

theorem paperOrder_steps_iff (n : ℕ) (xs : List (Fin n × Fin n)) :
    (∀ a ∈ paperOrder n xs, paperStep a) ↔ ∀ a ∈ xs, executionStep a := by
  have legal (a : Fin n × Fin n) :
      paperStep ((paperLabelEquiv n).prodCongr (paperLabelEquiv n) a) ↔ executionStep a := by
    change (a.1.val + 1 < a.2.val + 1 ∧ (a.2.val + 1) % 2 = 1) ↔
      (a.1.val < a.2.val ∧ a.2.val % 2 = 0)
    omega
  change (∀ a ∈ xs.reverse.map _, paperStep a) ↔ _
  simp only [List.forall_mem_map, legal, List.mem_reverse]

theorem paperOrder_endpoint_iff (n : ℕ) (std m : Perm (Fin n)) (xs : List (Fin n × Fin n)) :
    (swaps (paperOrder n xs)).prod * (paperLabelEquiv n).permCongrHom m *
        (swaps (paperOrder n xs)).prod⁻¹ = (paperLabelEquiv n).permCongrHom std ↔
      execute m xs = std := by
  rw [execute_eq_conj]
  exact endpoint_relabel_iff (paperLabelEquiv n) std m xs.reverse

theorem paperOrder_connected_iff (n : ℕ) (std : Perm (Fin n)) (xs : List (Fin n × Fin n)) :
    MulAction.IsPretransitive
        (generated ((paperLabelEquiv n).permCongrHom std) (paperOrder n xs)) (PaperLabel n) ↔
      MulAction.IsPretransitive (generated std xs) (Fin n) := by
  apply (generated_pretransitive_relabel_iff (paperLabelEquiv n) std xs.reverse).trans
  exact Iff.of_eq (congrArg (fun H : Subgroup (Perm (Fin n)) ↦ MulAction.IsPretransitive H (Fin n))
    (generated_reverse std xs))

/-- The number of distinct larger endpoints is unchanged by relabelling and reversal. -/
def hive {V : Type*} [DecidableEq V] (xs : List (V × V)) : ℕ :=
  (xs.map Prod.snd).toFinset.card

theorem paperOrder_hive (n : ℕ) (xs : List (Fin n × Fin n)) :
    hive (paperOrder n xs) = hive xs := by
  have hlist :
      (paperOrder n xs).map Prod.snd = (xs.reverse.map Prod.snd).map (paperLabelEquiv n) := by
    change ((xs.reverse.map ((paperLabelEquiv n).prodCongr (paperLabelEquiv n))).map Prod.snd) = _
    rw [List.map_map, List.map_map]
    rfl
  have hmap :
      ((paperOrder n xs).map Prod.snd).toFinset =
        ((xs.reverse.map Prod.snd).toFinset).image (paperLabelEquiv n) := by
    rw [hlist]
    exact Multiset.toFinset_map (paperLabelEquiv n) (xs.reverse.map Prod.snd)
  rw [hive, hmap, Finset.card_image_of_injective _ (paperLabelEquiv n).injective,
    List.map_reverse, List.toFinset_reverse, hive]

def crosses {n : ℕ} (cutoff : ℕ) (xs : List (Fin n × Fin n)) : Prop :=
  ∃ a ∈ xs, decide (a.1.val < cutoff) ≠ decide (a.2.val < cutoff)

/-- The published length, transposition, endpoint and connectedness conditions
on a word written with one-based labels. -/
def PaperAccepts {n : ℕ} (std m : Perm (PaperLabel n)) (r : ℕ)
    (ys : List (PaperLabel n × PaperLabel n)) : Prop :=
  ys.length = r ∧ ys.Pairwise (fun a b ↦ a.2.val ≤ b.2.val) ∧
    (∀ a ∈ ys, paperStep a) ∧
    ((swaps ys).prod * m * (swaps ys).prod⁻¹ = std) ∧
    MulAction.IsPretransitive (generated std ys) (PaperLabel n)

/-- A transposition sequence can be given as a list of permutations, with
its canonical ordered endpoint representation. -/
noncomputable def paperPermWordsEquiv {n : ℕ} (std m : Perm (PaperLabel n)) (r : ℕ) :
    {ys // PaperAccepts std m r ys} ≃
      {ps : List (Perm (PaperLabel n)) // ∃ ys, PaperAccepts std m r ys ∧ swaps ys = ps} :=
  Equiv.ofBijective (fun ys ↦ ⟨swaps ys.val, ⟨ys.val, ys.property, rfl⟩⟩) (by
    constructor
    · intro ys zs he
      apply Subtype.ext
      exact paper_word_swaps_injective ys.property.2.2.1 zs.property.2.2.1
        (congrArg Subtype.val he)
    · rintro ⟨ps, ys, hy, hps⟩
      exact ⟨⟨ys, hy⟩, Subtype.ext hps⟩)

/-- Acceptance of a chronological word on the partner vectors. The crossing
condition is checked on the two initial components. -/
def ExecutionAccepts {n : ℕ} (std m : Perm (Fin n)) (cutoff r : ℕ)
    (xs : List (Fin n × Fin n)) : Prop :=
  xs.length = r ∧ xs.Pairwise (fun a b ↦ b.2.val ≤ a.2.val) ∧
    (∀ a ∈ xs, executionStep a) ∧ execute m xs = std ∧ crosses cutoff xs

private theorem paperOrder_accepts_iff {n : ℕ} (std m : Perm (Fin n)) (cutoff r : ℕ)
    (hconn : ∀ xs : List (Fin n × Fin n),
      (swaps xs).prod * m * (swaps xs).prod⁻¹ = std →
      (MulAction.IsPretransitive (generated std xs) (Fin n) ↔ crosses cutoff xs))
    (xs : List (Fin n × Fin n)) :
    PaperAccepts ((paperLabelEquiv n).permCongrHom std) ((paperLabelEquiv n).permCongrHom m)
        r (paperOrder n xs) ↔ ExecutionAccepts std m cutoff r xs := by
  simp only [PaperAccepts, ExecutionAccepts, paperOrder_length, paperOrder_pairwise_iff,
    paperOrder_steps_iff, paperOrder_endpoint_iff, paperOrder_connected_iff]
  have hiff (he : execute m xs = std) :
      MulAction.IsPretransitive (generated std xs) (Fin n) ↔ crosses cutoff xs := by
    have he' := (execute_eq_conj m xs).symm.trans he
    have hg := congrArg (fun H : Subgroup (Perm (Fin n)) ↦ MulAction.IsPretransitive H (Fin n))
      (generated_reverse std xs)
    apply (Iff.of_eq hg.symm).trans
    simpa only [crosses, List.mem_reverse] using hconn xs.reverse he'
  constructor
  · rintro ⟨hl, hm, hs, he, hc⟩
    exact ⟨hl, hm, hs, he, (hiff he).mp hc⟩
  · rintro ⟨hl, hm, hs, he, hc⟩
    exact ⟨hl, hm, hs, he, (hiff he).mpr hc⟩

theorem paper32_accepts_iff (xs : List (Fin 10 × Fin 10)) :
    PaperAccepts ((paperLabelEquiv 10).permCongrHom std5) ((paperLabelEquiv 10).permCongrHom mat5)
        9 (paperOrder 10 xs) ↔ ExecutionAccepts std5 mat5 6 9 xs :=
  paperOrder_accepts_iff std5 mat5 6 9 transitive_32 xs

theorem paper42_accepts_iff (xs : List (Fin 12 × Fin 12)) :
    PaperAccepts ((paperLabelEquiv 12).permCongrHom std6) ((paperLabelEquiv 12).permCongrHom mat6)
        10 (paperOrder 12 xs) ↔ ExecutionAccepts std6 mat6 8 10 xs :=
  paperOrder_accepts_iff std6 mat6 8 10 transitive_42 xs

/-- Connected, length-nine words in both presentations of the `(3,2)` input. -/
def connected32Equiv :
    {xs : List (Fin 10 × Fin 10) // ExecutionAccepts std5 mat5 6 9 xs} ≃
      {ys : List (PaperLabel 10 × PaperLabel 10) //
        PaperAccepts ((paperLabelEquiv 10).permCongrHom std5) ((paperLabelEquiv 10).permCongrHom mat5) 9 ys} :=
  (paperOrder 10).subtypeEquiv (fun xs ↦ (paper32_accepts_iff xs).symm)

/-- Connected, length-ten words in both presentations of the `(4,2)` input. -/
def connected42Equiv :
    {xs : List (Fin 12 × Fin 12) // ExecutionAccepts std6 mat6 8 10 xs} ≃
      {ys : List (PaperLabel 12 × PaperLabel 12) //
        PaperAccepts ((paperLabelEquiv 12).permCongrHom std6) ((paperLabelEquiv 12).permCongrHom mat6) 10 ys} :=
  (paperOrder 12).subtypeEquiv (fun xs ↦ (paper42_accepts_iff xs).symm)

end Hurwitz.MatchingWords
