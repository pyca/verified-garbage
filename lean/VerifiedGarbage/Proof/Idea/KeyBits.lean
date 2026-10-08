import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Impl.Idea.Key

/-!
# IDEA key expansion, bit by bit

Target-independent facts for proving key expansion: bit `b` of subkey `n` is
bit `Impl.Idea.keyBit n b` of the key (`expandKey_getLsbD`), which is a bit of
one of the key's bytes (`keyValue_getLsbD`), at the bit `keyLoc` gives of one
of the key's quadwords in memory (`keyLoc_spec`); and a subkey's bits are bits
of a quadword of the schedule in memory (`scheduleAt_getLsbD`).
-/

namespace VG.Proof.Idea

open VG

theorem foldl_bytes_getLsbD (l : List (BitVec 8)) (acc : BitVec 128) (i : Nat) (hi : i < 128) :
    (l.foldl (fun (out : BitVec 128) (byte : BitVec 8) => (out <<< 8) ||| byte.zeroExtend 128) acc).getLsbD i =
      if i < 8 * l.length then (l.getD (l.length - 1 - i / 8) 0).getLsbD (i % 8)
      else acc.getLsbD (i - 8 * l.length) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_cons]
    by_cases h1 : i < 8 * xs.length
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
      congr 1
      rw [show xs.length + 1 - 1 - i / 8 = (xs.length - 1 - i / 8) + 1 by omega]
      simp
    · rw [ite_eq_right h1]
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
      by_cases h2 : i < 8 * (xs.length + 1)
      · rw [ite_eq_left h2, show xs.length + 1 - 1 - i / 8 = 0 by omega]
        simp only [List.getD_cons_zero]
        have : i - 8 * xs.length < 8 := by omega
        simp [this, show i - 8 * xs.length < 128 by omega, show i % 8 = i - 8 * xs.length by omega]
      · rw [ite_eq_right h2]
        simp [show ¬ (i - 8 * xs.length < 8) by omega, show i - 8 * xs.length < 128 by omega,
          show i - 8 * xs.length - 8 = i - 8 * (xs.length + 1) by omega]
        intro h
        rw [BitVec.getLsbD_of_ge x _ (by omega)] at h
        cases h

theorem keyValue_getLsbD (key : Vector Byte 16) {i : Nat} (hi : i < 128) :
    (Spec.Idea.keyValue key).getLsbD i = (key.getD (15 - i / 8) 0).getLsbD (i % 8) := by
  unfold Spec.Idea.keyValue
  rw [foldl_bytes_getLsbD _ _ _ hi]
  simp only [Vector.length_toList, show i < 8 * 16 from hi, ↓reduceIte]
  simp [Vector.getD, show 15 - i / 8 < 16 by omega]

theorem getD_lt {α : Type} {n : Nat} (v : Vector α n) (d : α) {i : Nat} (hi : i < n) :
    v.getD i d = v[i] := by
  simp [Vector.getD, hi]

theorem expandKey_getLsbD (key : Vector Byte 16) {n b : Nat} (hn : n < 52) (hb : b < 16) :
    ((Spec.Idea.expandKey key).getD n 0).getLsbD b =
      (Spec.Idea.keyValue key).getLsbD (Impl.Idea.keyBit n b) := by
  rw [getD_lt _ _ hn]
  simp only [Spec.Idea.expandKey, Vector.getElem_ofFn,
    BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_rotateLeft, Impl.Idea.keyBit]
  have h128 : 16 * (7 - n % 8) + b < 128 := by omega
  split
  · congr 1; omega
  · rw [decide_eq_true h128, Bool.true_and]
    congr 1; omega

theorem keyBit_lt (n b : Nat) : Impl.Idea.keyBit n b < 128 := by
  unfold Impl.Idea.keyBit; omega

theorem keyLoc_spec {i : Nat} (hi : i < 128) :
    (Impl.Idea.keyLoc i).1 < 2 ∧ (Impl.Idea.keyLoc i).2 < 64 ∧
      8 * (Impl.Idea.keyLoc i).1 + (Impl.Idea.keyLoc i).2 / 8 = 15 - i / 8 ∧
      (Impl.Idea.keyLoc i).2 % 8 = i % 8 := by
  simp only [Impl.Idea.keyLoc]
  omega

/-- Bit `t` of a little-endian quadword in memory. -/
theorem readW_getLsbD (m : Mem) (a : Addr) {t : Nat} (ht : t < 64) :
    (m.readW a 64).getLsbD t = (m (a + BitVec.ofNat 64 (t / 8))).getLsbD (t % 8) := by
  rw [← Mem.extractLsb'_read m a (n := 8) (j := t / 8) (by omega), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq, show t % 8 < 8 from Nat.mod_lt _ (by decide),
    decide_true, Bool.true_and]
  congr 1; omega

theorem keyAt_getD (m : Mem) (p : Addr) {k : Nat} (hk : k < 16) :
    (Spec.Idea.keyAt m p).getD k 0 = m (p + BitVec.ofNat 64 k) := by
  simp [Spec.Idea.keyAt, Vector.getD, hk]

/-- Bit `b` of subkey `n` is a bit of quadword `n / 4` of the schedule. -/
theorem scheduleAt_getLsbD (m : Mem) (p : Addr) {n b : Nat} (hn : n < 52) (hb : b < 16) :
    ((Spec.Idea.scheduleAt m p).getD n 0).getLsbD b =
      (m.readW (p + BitVec.ofNat 64 (8 * (n / 4))) 64).getLsbD (16 * (n % 4) + b) := by
  rw [scheduleAt_getD m p hn, readW_getLsbD _ _ (by omega), Offset.add_ofNat_add_ofNat,
    BitVec.getLsbD_append]
  by_cases h : b < 8
  · simp only [h, ↓reduceIte]
    rw [show 8 * (n / 4) + (16 * (n % 4) + b) / 8 = 2 * n by omega,
      show (16 * (n % 4) + b) % 8 = b by omega]
  · simp only [h, ↓reduceIte]
    rw [show 8 * (n / 4) + (16 * (n % 4) + b) / 8 = 2 * n + 1 by omega,
      show (16 * (n % 4) + b) % 8 = b - 8 by omega]

end VG.Proof.Idea
