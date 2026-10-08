import VerifiedGarbage.Impl.Cast5.Tables
import VerifiedGarbage.Proof.Framework.ReadHalves

/-!
# CAST5: the tables' entries

Entry `e` of `table a b c d`, read as four dwords (`ent`) from memory holding
the table's quadwords (`Held`), is `a e, b e, c e, d e`.
-/

namespace VG.Proof.Cast5

open VG VG.Impl.Cast5

/-- Dword `k` of entry `i` of the table at `T`. -/
def ent (m : Mem) (T : Addr) (i k : Nat) : BitVec 32 :=
  m.readW (T + BitVec.ofNat 64 (16 * i + 4 * k)) 32

theorem flatMap_range_succ {α : Type} (f : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]


theorem getD_append' {α : Type} (l l' : List α) (n : Nat) (d : α) :
    (l ++ l').getD n d = if n < l.length then l.getD n d else l'.getD (n - l.length) d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : n < l.length
  · rw [ite_eq_left h, List.getElem?_append_left h]
  · rw [ite_eq_right h, List.getElem?_append_right (by omega)]

theorem pairs_length {α : Type} (f g : Nat → α) :
    ∀ n, ((List.range n).flatMap fun i => [f i, g i]).length = 2 * n
  | 0 => rfl
  | n + 1 => by
    rw [flatMap_range_succ, List.length_append, pairs_length f g n]
    simp only [List.length_cons, List.length_nil]
    omega

/-- Element `2 e` and `2 e + 1` of a list of pairs. -/
theorem pairs_getD {α : Type} (f g : Nat → α) (d : α) :
    ∀ n e, e < n → ((List.range n).flatMap fun i => [f i, g i]).getD (2 * e) d = f e ∧
      ((List.range n).flatMap fun i => [f i, g i]).getD (2 * e + 1) d = g e
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, e, h => by
    rw [flatMap_range_succ, getD_append', getD_append', pairs_length]
    by_cases he : e < n
    · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
      exact pairs_getD f g d n e he
    · have : e = n := by omega
      subst this
      rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.sub_self,
        show 2 * e + 1 - 2 * e = 1 by omega]
      exact ⟨rfl, rfl⟩

/-- Memory holding the quadwords `W` at `T`. -/
def Held (m : Mem) (T : Addr) (W : List (BitVec 64)) : Prop :=
  ∀ i < W.length, m.readW (T + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0

theorem table_length (a b c d : Byte → Spec.Cast5.Word) : (table a b c d).length = 512 := by
  unfold table
  rw [pairs_length]

theorem setWidth_append32 (x y : BitVec 32) : (x ++ y).setWidth 32 = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, decide_eq_true hi, Bool.true_and, ite_eq_left hi]

theorem extract_append32 (x y : BitVec 32) : (x ++ y).extractLsb' 32 32 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hi, Bool.true_and,
    ite_eq_right (by omega), Nat.add_sub_cancel_left]

/-- Dword `k` of entry `e` of `table a b c d`. -/
def tableEnt (a b c d : Byte → Spec.Cast5.Word) (e k : Nat) : Spec.Cast5.Word :=
  let x := BitVec.ofNat 8 e
  match k with | 0 => a x | 1 => b x | 2 => c x | _ => d x

theorem ent_table {m : Mem} {T : Addr} {a b c d : Byte → Spec.Cast5.Word}
    (h : Held m T (table a b c d)) {e k : Nat} (he : e < 256) (hk : k < 4) :
    ent m T e k = tableEnt a b c d e k := by
  have hp := pairs_getD (fun i => b (BitVec.ofNat 8 i) ++ a (BitVec.ofNat 8 i))
    (fun i => d (BitVec.ofNat 8 i) ++ c (BitVec.ofNat 8 i)) 0 256 e he
  have h0 := h (2 * e) (by rw [table_length]; omega)
  have h1 := h (2 * e + 1) (by rw [table_length]; omega)
  unfold table at h0 h1
  rw [hp.1] at h0
  rw [hp.2] at h1
  unfold ent tableEnt
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [show 16 * e + 4 * 0 = 8 * (2 * e) by omega, Mem.readW_lo32 h0, setWidth_append32]
    rfl
  · rw [show 16 * e + 4 * 1 = 8 * (2 * e) + 4 by omega, ← Offset.add_add, Mem.readW_hi32 h0,
      extract_append32]
    rfl
  · rw [show 16 * e + 4 * 2 = 8 * (2 * e + 1) by omega, Mem.readW_lo32 h1, setWidth_append32]
    rfl
  · rw [show 16 * e + 4 * 3 = 8 * (2 * e + 1) + 4 by omega, ← Offset.add_add, Mem.readW_hi32 h1,
      extract_append32]
    rfl

end VG.Proof.Cast5
