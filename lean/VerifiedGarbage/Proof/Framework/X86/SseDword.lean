import VerifiedGarbage.Proof.Framework.X86.Sse

/-!
# x86 (32-bit): SSE2 operations doubleword by doubleword

The SSE2 instructions that compute on doublewords (`paddd`, `pxor`, `por`,
the shifts, `pshufd`), stated on one doubleword of their result; and the
rotation of each doubleword by 16 bits that `pshuflw` and `pshufhw` with
`0xb1` compute.
-/

namespace VG.X86

theorem cases4 {i : Nat} (hi : i < 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega

theorem dword_paddd (a b : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .paddd a b) i = dword a i + dword b i := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [XBinOp.eval]

theorem dword_pxor (a b : BitVec 128) (i : Nat) :
    dword (XBinOp.eval .pxor a b) i = dword a i ^^^ dword b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [XBinOp.eval, dword, hj]

theorem dword_por (a b : BitVec 128) (i : Nat) :
    dword (XBinOp.eval .por a b) i = dword a i ||| dword b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [XBinOp.eval, dword, hj]

theorem dword_pslld (a : BitVec 128) (n : BitVec 8) (hn : n.toNat < 32) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld a n) i = dword a i <<< n.toNat := by
  simp only [XShiftOp.eval, show ¬ 31 < n.toNat by omega, ite_false]
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp

theorem dword_psrld (a : BitVec 128) (n : BitVec 8) (hn : n.toNat < 32) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld a n) i = dword a i >>> n.toNat := by
  simp only [XShiftOp.eval, show ¬ 31 < n.toNat by omega, ite_false]
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp

theorem dword_shufDwords (a : BitVec 128) (o : BitVec 8) {i : Nat} (hi : i < 4) :
    dword (shufDwords a o) i = dword a (o.extractLsb' (2 * i) 2).toNat := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [shufDwords]

/-- `pshufd` with `0x55 * k` broadcasts doubleword `k`. -/
theorem dword_shufDwords_bcast (a : BitVec 128) {k i : Nat} (hk : k < 4) (hi : i < 4) :
    dword (shufDwords a (BitVec.ofNat 8 (0x55 * k))) i = dword a k := by
  rw [dword_shufDwords _ _ hi]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl

theorem punpckldq_eq (a b : BitVec 128) :
    XBinOp.eval .punpckldq a b = ofDwords (dword a 0) (dword b 0) (dword a 1) (dword b 1) := rfl

theorem punpckhdq_eq (a b : BitVec 128) :
    XBinOp.eval .punpckhdq a b = ofDwords (dword a 2) (dword b 2) (dword a 3) (dword b 3) := rfl

/-- A rotation as two shifts. -/
theorem shl_or_shr (x : BitVec 32) {k : Nat} (hk : 0 < k) (hk' : k < 32) :
    x <<< k ||| x >>> (32 - k) = x.rotateLeft k := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt hk']
  by_cases h : m < k
  · simp [h, hm]
  · rw [BitVec.getLsbD_of_ge x (32 - k + m) (by omega)]
    simp [h, hm]

/-! ## The rotation by 16 -/

theorem getLsbD_ofWords (f : Nat → BitVec 16) {k r : Nat} (hk : k < 8) (hr : r < 16) :
    (ofWords f).getLsbD (16 * k + r) = (f k).getLsbD r := by
  simp only [ofWords, getLsbD_append_block _ _ _ hr]
  match k, hk with
  | 0, _ => ?_
  | 1, _ => ?_
  | 2, _ => ?_
  | 3, _ => ?_
  | 4, _ => ?_
  | 5, _ => ?_
  | 6, _ => ?_
  | 7, _ => ?_
  | _ + 8, h => exact absurd h (by omega)
  all_goals
    simp only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add]

theorem getLsbD_word (x : BitVec 128) (k r : Nat) (hr : r < 16) :
    (word x k).getLsbD r = x.getLsbD (16 * k + r) := by
  simp [word, hr]

theorem word_ofWords (f : Nat → BitVec 16) {k : Nat} (hk : k < 8) : word (ofWords f) k = f k := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  rw [getLsbD_word _ _ _ hr, getLsbD_ofWords _ hk hr]

/-- `pshuflw` and `pshufhw` with `0xb1` swap the two words of each doubleword. -/
theorem word_rot16 (x : BitVec 128) {k : Nat} (hk : k < 8) :
    word (shufHighWords (shufLowWords x 0xb1) 0xb1) k = word x (k ^^^ 1) := by
  simp only [shufHighWords, word_ofWords _ hk]
  match k, hk with
  | 0, _ => ?_
  | 1, _ => ?_
  | 2, _ => ?_
  | 3, _ => ?_
  | 4, _ => ?_
  | 5, _ => ?_
  | 6, _ => ?_
  | 7, _ => ?_
  | _ + 8, h => exact absurd h (by omega)
  all_goals
    simp (disch := decide) only [↓reduceIte, Nat.reduceLT, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceAdd, BitVec.reduceExtractLsb', BitVec.reduceToNat, shufLowWords, word_ofWords]
    rfl

theorem getLsbD_rot16 (x : BitVec 128) {k r : Nat} (hk : k < 8) (hr : r < 16) :
    (shufHighWords (shufLowWords x 0xb1) 0xb1).getLsbD (16 * k + r) =
      x.getLsbD (16 * (k ^^^ 1) + r) := by
  rw [← getLsbD_word _ _ _ hr, word_rot16 _ hk, getLsbD_word _ _ _ hr]

theorem dword_rot16 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (shufHighWords (shufLowWords x 0xb1) 0xb1) i = (dword x i).rotateLeft 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [getLsbD_dword, BitVec.getLsbD_rotateLeft, decide_eq_true hm, Bool.true_and]
  by_cases h : m < 16
  · rw [show 32 * i + m = 16 * (2 * i) + m by omega, getLsbD_rot16 _ (by omega) h,
      show 16 % 32 = 16 from rfl, ite_eq_left h, getLsbD_dword, decide_eq_true (by omega), Bool.true_and]
    exact congrArg _ (by rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp <;> omega)
  · rw [show 32 * i + m = 16 * (2 * i + 1) + (m - 16) by omega, getLsbD_rot16 _ (by omega) (by omega),
      show 16 % 32 = 16 from rfl, ite_eq_right h, getLsbD_dword, decide_eq_true (by omega), Bool.true_and]
    exact congrArg _ (by rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp <;> omega)

/-! ## Little-endian reads and writes, byte by byte

As in `Proof/Framework/X86_64/Avx.lean` (a module of another target). -/

theorem readW_extract (m : Mem) (a : Addr) {w k n : Nat} (h : 8 * (k + n) ≤ w) :
    (m.readW a w).extractLsb' (8 * k) (8 * n) = m.readW (a + BitVec.ofNat 64 k) (8 * n) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and, decide_eq_true (show 8 * k + i < w by omega)]
  rw [getLsbD_read _ _ (by omega), getLsbD_read _ _ (by omega)]
  rw [show a + BitVec.ofNat 64 ((8 * k + i) / 8) = a + BitVec.ofNat 64 k + BitVec.ofNat 64 (i / 8) by
    rw [show (8 * k + i) / 8 = k + i / 8 by omega, BitVec.ofNat_add, BitVec.add_assoc]]
  exact congrArg _ (by omega)

theorem readW_writeW_inside (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) {k n : Nat}
    (h : 8 * (k + n) ≤ w) (hw : w < 2 ^ 64) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 k) (8 * n) = v.extractLsb' (8 * k) (8 * n) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  rw [getLsbD_read _ _ (by omega)]
  simp only [Mem.writeW, Mem.write]
  rw [show a + BitVec.ofNat 64 k + BitVec.ofNat 64 (i / 8) - a = BitVec.ofNat 64 (k + i / 8) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left]]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [show k + i / 8 < w / 8 by omega, ite_true, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth]
  rw [decide_eq_true (by omega), decide_eq_true (by omega), Bool.true_and, Bool.true_and]
  exact congrArg _ (by omega)

theorem readW_8 (m : Mem) (a : Addr) : m.readW a 8 = m a := by
  simp only [Mem.readW, Mem.read]
  ext i hi; simp only [BitVec.getElem_setWidth]; rw [BitVec.getLsbD_append]; simp [hi]

/-- Byte `k` of a read. -/
theorem byte_readW (m : Mem) (a : Addr) {w k : Nat} (h : 8 * (k + 1) ≤ w) :
    (m.readW a w).extractLsb' (8 * k) 8 = m (a + BitVec.ofNat 64 k) := by
  have e := readW_extract m a (k := k) (n := 1) h
  rw [Nat.mul_one] at e
  rw [e, readW_8]

/-- Byte `k` of a write. -/
theorem writeW_byte (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) {k : Nat} (h : 8 * (k + 1) ≤ w)
    (hw : w < 2 ^ 64) : (m.writeW a v) (a + BitVec.ofNat 64 k) = v.extractLsb' (8 * k) 8 := by
  have e := readW_writeW_inside m a v (k := k) (n := 1) h hw
  rw [Nat.mul_one, readW_8] at e
  exact e

/-- A byte outside a write. -/
theorem writeW_byte_off (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) (x : Addr)
    (h : w / 8 ≤ (x - a).toNat) : (m.writeW a v) x = m x := by
  simp only [Mem.writeW, Mem.write, show ¬ (x - a).toNat < w / 8 by omega, ite_false]

theorem extract_extract {w : Nat} (x : BitVec w) (a b c d : Nat) (h : c + d ≤ b) :
    (x.extractLsb' a b).extractLsb' c d = x.extractLsb' (a + c) d := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', decide_eq_true hi, decide_eq_true (show c + i < b by omega),
    Bool.true_and, Nat.add_assoc]

/-- Byte `t` of a 128-bit value: byte `t % 4` of doubleword `t / 4`. -/
theorem byte_dword (v : BitVec 128) (t : Nat) :
    v.extractLsb' (8 * t) 8 = (dword v (t / 4)).extractLsb' (8 * (t % 4)) 8 := by
  rw [dword, extract_extract _ _ _ _ _ (by omega), show 32 * (t / 4) + 8 * (t % 4) = 8 * t by omega]

end VG.X86
