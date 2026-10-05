import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombWords
import VerifiedGarbage.Proof.Weierstrass.TCombLay
import VerifiedGarbage.Proof.Weierstrass.Words

/-!
# The comb from tables in memory on AArch64: the tables

The tables at `T` (`TblMem`): `ws.length` words, readable, word `i` at
`T + 8 i` the word `i` of `ws`; they survive a change of the working space
only (`TblMem.unch`). For the comb's words (`tcombWords`), the words of
entry `m` of table `j` are its coordinates in Montgomery form
(`tcombWords_x`, `tcombWords_y`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass

/-- The words `ws` at `T`, readable (in one region). -/
structure TblMem (s : State) (T : Addr) (ws : List (BitVec 64)) : Prop where
  rd : InRegions (s.rd ++ s.wr) T (8 * ws.length)
  val : ∀ i < ws.length, s.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = ws.getD i 0

/-- Element `q k + r` of a list of lists of `k` elements each. -/
theorem getD_flatMap_uniform {α β : Type} (f : α → List β) (k : Nat) (d : β) :
    ∀ (l : List α) (da : α), (∀ x ∈ l, (f x).length = k) → ∀ q < l.length, ∀ r < k,
      (l.flatMap f).getD (q * k + r) d = (f (l.getD q da)).getD r d
  | [], _, _, q, hq, _, _ => absurd hq (Nat.not_lt_zero _)
  | x :: l, da, h, q, hq, r, hr => by
    have hx := h x (List.mem_cons_self ..)
    rw [List.flatMap_cons]
    cases q with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.getD_cons_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
    | succ q =>
      simp only [List.getD_cons_succ, List.length_cons] at hq ⊢
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hx, Nat.succ_mul]; omega), hx,
        show (q + 1) * k + r - k = q * k + r by rw [Nat.succ_mul]; omega, ← List.getD_eq_getElem?_getD]
      exact getD_flatMap_uniform f k d l da (fun y hy => h y (List.mem_cons_of_mem _ hy)) q (by omega) r hr

/-- Word `i < 2n` of entry `m` of table `j`: its `x`'s words, then its `y`'s. -/
theorem tcombWords_getD {n R p H J : Nat} {tbl : List (List (Nat × Nat))} (hJ : tbl.length = J)
    (hH : ∀ j < J, (tbl.getD j []).length = H) {j m i : Nat} (hj : j < J) (hm : m < H) (hi : i < 2 * n) :
    (tcombWords n R p tbl).getD (j * (H * (2 * n)) + m * (2 * n) + i) 0 =
      if i < n then wordOf ((combAt tbl j m).1 * R % p) i else wordOf ((combAt tbl j m).2 * R % p) (i - n) := by
  unfold tcombWords
  rw [Nat.add_assoc, getD_flatMap_uniform _ (H * (2 * n)) 0 tbl [] (fun t ht => by
      obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem ht
      have := hH j' (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] at this
      simp only [Option.getD_some] at this
      rw [length_flatMap_uniform _ (2 * n) _ fun xy _ => tcombWords_entry_len n R p xy, this]) j
      (by omega) _ (by
      refine Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi _) ?_
      have := Nat.mul_le_mul_right (2 * n) (show m + 1 ≤ H from hm)
      rwa [Nat.succ_mul] at this)]
  rw [getD_flatMap_uniform _ (2 * n) 0 _ (0, 0) (fun xy _ => tcombWords_entry_len n R p xy) m
    (by rw [hH j hj]; exact hm) i hi]
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simp; exact h), List.getElem?_map, List.getElem?_range h]
    simp [h, combAt]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_map, List.length_map,
      List.length_range, List.getElem?_range (by omega)]
    simp [h, combAt]

/-- The tables survive a change of the memory that keeps their bytes and the
regions. -/
theorem TblMem.unch {s s' : State} {T : Addr} {ws : List (BitVec 64)} (h : TblMem s T ws)
    (hrd : s'.rd ++ s'.wr = s.rd ++ s.wr)
    (hm : ∀ i < ws.length, ∀ b < 8,
      s'.mem (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) =
        s.mem (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) :
    TblMem s' T ws :=
  ⟨hrd ▸ h.rd, fun i hi => by
    rw [← h.val i hi]; exact Mem.readW_congr fun b hb => hm i hi b (by omega)⟩

/-- The `x` and `y` of entry `m` of table `j`, in Montgomery form, at
`16 n m` and `16 n m + 8 n` bytes into the table, at `T + 16 n H j`. -/
theorem tbl_entry {s : State} {T : Addr} {n R p H J : Nat} {tbl : List (List (Nat × Nat))}
    (hT : TblMem s T (tcombWords n R p tbl)) (hJ : tbl.length = J)
    (hH : ∀ j < J, (tbl.getD j []).length = H) {j m : Nat} (hj : j < J) (hm : m < H)
    (hx : (combAt tbl j m).1 * R % p < 2 ^ (64 * n)) (hy : (combAt tbl j m).2 * R % p < 2 ^ (64 * n)) :
    wordsVal s.mem (T + BitVec.ofNat 64 (j * (16 * n * H))) (16 * n * m) n = (combAt tbl j m).1 * R % p ∧
    wordsVal s.mem (T + BitVec.ofNat 64 (j * (16 * n * H))) (16 * n * m + 8 * n) n =
      (combAt tbl j m).2 * R % p := by
  have hlen := tcombWords_length (n := n) (R := R) (p := p) hJ hH
  have hidx : ∀ i < 2 * n, j * (H * (2 * n)) + m * (2 * n) + i < J * (H * (2 * n)) := fun i hi => by
    have h1 : j * (H * (2 * n)) + m * (2 * n) + i < j * (H * (2 * n)) + H * (2 * n) := by
      have := Nat.mul_le_mul_right (2 * n) (show m + 1 ≤ H from hm)
      rw [Nat.succ_mul] at this; omega
    have h2 : j * (H * (2 * n)) + H * (2 * n) ≤ J * (H * (2 * n)) := by
      have := Nat.mul_le_mul_right (H * (2 * n)) (show j + 1 ≤ J from hj)
      rwa [Nat.succ_mul] at this
    omega
  have hw : ∀ i < 2 * n, word s.mem (T + BitVec.ofNat 64 (j * (16 * n * H))) (16 * n * m + 8 * i) =
      (tcombWords n R p tbl).getD (j * (H * (2 * n)) + m * (2 * n) + i) 0 := fun i hi => by
    rw [← hT.val _ (by rw [hlen]; exact hidx i hi), word, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2
    grind
  constructor
  · refine wordsVal_of_shifts _ _ _ _ _ hx fun i hi => ?_
    rw [hw i (by omega), tcombWords_getD hJ hH hj hm (by omega)]; simp only [hi, ↓reduceIte]; rfl
  · refine wordsVal_of_shifts _ _ _ _ _ hy fun i hi => ?_
    rw [show 16 * n * m + 8 * n + 8 * i = 16 * n * m + 8 * (n + i) by omega, hw (n + i) (by omega),
      tcombWords_getD hJ hH hj hm (by omega)]
    simp only [show ¬ n + i < n by omega, ↓reduceIte, Nat.add_sub_cancel_left]; rfl

end VG.Proof.Weierstrass.AArch64
