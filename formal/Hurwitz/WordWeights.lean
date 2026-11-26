import Hurwitz.Charge
import Hurwitz.MatchingWords

/-! Comparing the flip exponent at each intermediate matching, including repeated swaps. -/
namespace Hurwitz.WordWeights
open Equiv Connectivity MatchingWords

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Execute one transposition at a time, taking its weight before the update. -/
def executionFlips (s m : Perm V) : List (V × V) → ℕ
  | [] => 0
  | a :: xs => Charge.flip s m a.1 a.2 + executionFlips s (rewire m a) xs

/-- The matching at a position of the paper's word is obtained from all factors
to its right, in the order of permutation multiplication. -/
def suffixMatching (m : Perm V) (ys : List (V × V)) : Perm V :=
  (swaps ys).prod * m * (swaps ys).prod⁻¹

def paperFlips (s m : Perm V) : List (V × V) → ℕ
  | [] => 0
  | a :: ys => Charge.flip s (suffixMatching m ys) a.1 a.2 + paperFlips s m ys

omit [Fintype V] in
theorem suffix_snoc (m : Perm V) (xs : List (V × V)) (a : V × V) :
    suffixMatching m (xs ++ [a]) = suffixMatching (rewire m a) xs := by
  simp only [suffixMatching, rewire, swaps, List.map_append, List.map_cons,
    List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one, mul_inv_rev]
  group

theorem paperFlips_snoc (s m : Perm V) (xs : List (V × V)) (a : V × V) :
    paperFlips s m (xs ++ [a]) = Charge.flip s m a.1 a.2 + paperFlips s (rewire m a) xs := by
  induction xs with
  | nil => simp [paperFlips, suffixMatching, swaps]
  | cons z xs ih =>
    simp only [List.cons_append, paperFlips, suffix_snoc, ih]
    omega

theorem reverse_flips (s m : Perm V) (xs : List (V × V)) :
    paperFlips s m xs.reverse = executionFlips s m xs := by
  induction xs generalizing m with
  | nil => rfl
  | cons a xs ih => rw [List.reverse_cons, paperFlips_snoc, ih, executionFlips]

variable {W : Type*} [Fintype W] [LinearOrder W]

omit [Fintype V] [Fintype W] in
private theorem perm_comm (e : V ≃o W) (r : Perm V) (x : V) :
    (e.toEquiv.permCongrHom r) (e x) = e (r x) := by
  change e (r (e.symm (e x))) = _
  simp

omit [Fintype V] [Fintype W] in
private theorem conjugated_suffix (e : V ≃o W) (m : Perm V) (ys : List (V × V)) :
    suffixMatching (e.toEquiv.permCongrHom m) (ys.map (e.toEquiv.prodCongr e.toEquiv)) =
      e.toEquiv.permCongrHom (suffixMatching m ys) := by
  simp only [suffixMatching, swaps_relabel, List.prod_hom, map_mul, map_inv]

theorem paperFlips_relabel (e : V ≃o W) (s m : Perm V) (ys : List (V × V)) :
    paperFlips (e.toEquiv.permCongrHom s) (e.toEquiv.permCongrHom m)
      (ys.map (e.toEquiv.prodCongr e.toEquiv)) = paperFlips s m ys := by
  induction ys with
  | nil => rfl
  | cons a ys ih =>
    simp only [List.map_cons, paperFlips]
    rw [ih, conjugated_suffix]
    congr 1
    exact Charge.flip_map s (suffixMatching m ys) _ _ e.toOrderEmbedding
      (perm_comm e s) (perm_comm e (suffixMatching m ys)) a.1 a.2

def paperOrderIso (n : ℕ) : Fin n ≃o PaperLabel n where
  toEquiv := paperLabelEquiv n
  map_rel_iff' := by
    intro a b
    change a.val + 1 ≤ b.val + 1 ↔ a.val ≤ b.val
    omega

theorem paperOrder_flips (n : ℕ) (s m : Perm (Fin n)) (xs : List (Fin n × Fin n)) :
    paperFlips ((paperLabelEquiv n).permCongrHom s) ((paperLabelEquiv n).permCongrHom m)
      (paperOrder n xs) = executionFlips s m xs :=
  (paperFlips_relabel (paperOrderIso n) s m xs.reverse).trans (reverse_flips s m xs)

theorem paperOrder_weight {R : Type*} [CommSemiring R] (b u : R) (n : ℕ)
    (s m : Perm (Fin n)) (xs : List (Fin n × Fin n)) :
    b ^ paperFlips ((paperLabelEquiv n).permCongrHom s) ((paperLabelEquiv n).permCongrHom m)
        (paperOrder n xs) * u ^ hive (paperOrder n xs) =
      b ^ executionFlips s m xs * u ^ hive xs := by
  rw [paperOrder_flips, paperOrder_hive]

section Enumeration
open scoped BigOperators

private theorem finite_words {A : Type*} [Fintype A] {ok : List A → Prop} {r : ℕ}
    (hlen : ∀ xs, ok xs → xs.length = r) : Finite {xs // ok xs} := by
  let code (w : {xs // ok xs}) : List.Vector A r := ⟨w.val, hlen w.val w.property⟩
  exact Finite.of_injective code (fun _ _ h => Subtype.ext (congrArg (fun v : List.Vector A r => v.val) h))

abbrev PaperWords (n : ℕ) (s m : Perm (PaperLabel n)) (r : ℕ) := {xs // PaperAccepts s m r xs}
abbrev ExecWords (n : ℕ) (s m : Perm (Fin n)) (cutoff r : ℕ) := {xs // ExecutionAccepts s m cutoff r xs}

noncomputable instance (n : ℕ) (s m : Perm (PaperLabel n)) (r : ℕ) : Fintype (PaperWords n s m r) := by
  letI : Finite (PaperWords n s m r) := finite_words (r := r) (fun _ h => h.1)
  exact Fintype.ofFinite _

noncomputable instance (n : ℕ) (s m : Perm (Fin n)) (cutoff r : ℕ) : Fintype (ExecWords n s m cutoff r) := by
  letI : Finite (ExecWords n s m cutoff r) := finite_words (r := r) (fun _ h => h.1)
  exact Fintype.ofFinite _

variable {R : Type*} [CommSemiring R]

/-- Raw sum in Proposition 4.18. The normalization is the product of the two parts. -/
noncomputable def paperSum (b u : R) (n : ℕ) (s m : Perm (Fin n)) (r : ℕ) : R :=
  let S := (paperLabelEquiv n).permCongrHom s
  let M := (paperLabelEquiv n).permCongrHom m
  ∑ w : PaperWords n S M r, b ^ paperFlips S M w.val * u ^ hive w.val

noncomputable def execSum (b u : R) (n : ℕ) (s m : Perm (Fin n)) (cutoff r : ℕ) : R :=
  ∑ w : ExecWords n s m cutoff r, b ^ executionFlips s m w.val * u ^ hive w.val

theorem raw32_eq_exec (b u : R) :
    paperSum b u 10 std5 mat5 9 = execSum b u 10 std5 mat5 6 9 := by
  unfold paperSum execSum
  rw [← connected32Equiv.sum_comp]
  exact Finset.sum_congr rfl (fun w _ => paperOrder_weight b u 10 std5 mat5 w.val)

theorem raw42_eq_exec (b u : R) :
    paperSum b u 12 std6 mat6 10 = execSum b u 12 std6 mat6 8 10 := by
  unfold paperSum execSum
  rw [← connected42Equiv.sum_comp]
  exact Finset.sum_congr rfl (fun w _ => paperOrder_weight b u 12 std6 mat6 w.val)

end Enumeration

#print axioms raw32_eq_exec
#print axioms raw42_eq_exec
#print axioms paperOrder_weight
end Hurwitz.WordWeights
