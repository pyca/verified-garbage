module

public import VerifiedGarbage.Impl.Rc2.X86.Ssse3
public import VerifiedGarbage.Proof.Rc2.X86.PiLookup
import VerifiedGarbage.Proof.Rc2.Table
import VerifiedGarbage.Proof.Framework.X86.ByteLookup
import VerifiedGarbage.Proof.Framework.X86.ByteMap
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseWord
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Syms

/-!
# RC2 on x86: PITABLE read by `pshufb`

`Impl.Rc2.X86.Ssse3.piLookup` leaves PITABLE[EAX & 255] in EAX
(`piLookup_ok`), keeping memory, as the baseline's look-up does
(`piLookupSse_ok`), when EBP holds the address of the table.

The values the registers take are functions of the index (`evV`, `odV`,
`hiV`, then `pairV`, `quadV`, `octV`, `allV` and `resV`, as the code makes
them), and `resV_byte` is the look-up: byte 0 of `resV` is PITABLE's byte at
the index. The code is run once (`rows_ok`), to those values.
-/

@[expose] public section

namespace VG.Proof.Rc2.X86.Ssse3

open VG VG.X86 VG.X86.RegUpd VG.X86.ByteMap VG.X86.ByteLookup VG.Impl.Rc2.X86 VG.Impl.Rc2.X86.Ssse3
open VG.Impl.Rc2 (piSym piQuads piQuad)

/-! ## The table's rows -/

/-- Row `r` of the table, as `tb` loads it. -/
def row (r : Nat) : BitVec 128 := piQuads.getD (2 * r + 1) 0 ++ piQuads.getD (2 * r) 0

theorem row_byte {r c : Nat} (hr : r < 16) (hc : c < 16) :
    byte (row r) c = Spec.Rc2.piTable.getD (16 * r + c) 0 := by
  rw [row, byte_append _ _ hc, Proof.Rc2.piQuads_getD (by omega_using [hr]),
    Proof.Rc2.piQuads_getD (by omega_using [hr]), ← Proof.Rc2.piQuad_byte (by omega_using [hr, hc])]
  by_cases h : c < 8
  · rw [ite_eq_left h, show (16 * r + c) / 8 = 2 * r by omega_using [h],
      show (16 * r + c) % 8 = c % 8 by omega_using []]
  · rw [ite_eq_right h, show (16 * r + c) / 8 = 2 * r + 1 by omega_using [h, hc],
      show (16 * r + c) % 8 = c % 8 by omega_using []]

/-! ## The index vectors -/

/-- `xmm6`: the low nibble in byte 0, `0x80` in bytes 1 to 3. -/
def evV (a : BitVec 32) : BitVec 128 := (0 : BitVec 96) ++ (a &&& (15 : BitVec 32) ||| (0x80808000 : BitVec 32))

/-- `xmm7`: the low nibble in byte 1, `0x80` in bytes 0, 2 and 3. -/
def odV (a : BitVec 32) : BitVec 128 := (0 : BitVec 96) ++ (a &&& (15 : BitVec 32) ||| (0x80808000 : BitVec 32)).rotateRight 24

/-- `xmm5`: the high nibble in byte 0. -/
def hiV (a : BitVec 32) : BitVec 128 := (0 : BitVec 96) ++ (a >>> 4 &&& (15 : BitVec 32))

theorem lo_eq (a : BitVec 32) : a &&& (15 : BitVec 32) = BitVec.ofNat 32 (a.setWidth 8 &&& 0x0f#8).toNat := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (a &&& (15 : BitVec 32)).toNat = a.toNat % 16 := by
    rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 4
  have h2 : (a.setWidth 8 &&& 0x0f#8).toNat = a.toNat % 256 % 16 := by
    rw [BitVec.toNat_and, BitVec.toNat_setWidth]; exact Nat.and_two_pow_sub_one_eq_mod _ 4
  rw [h1, BitVec.toNat_ofNat, h2]
  omega_using []

theorem hi_eq (a : BitVec 32) : a >>> 4 &&& (15 : BitVec 32) = BitVec.ofNat 32 (a.setWidth 8 >>> 4).toNat := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (a >>> 4 &&& (15 : BitVec 32)).toNat = a.toNat / 16 % 16 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.and_two_pow_sub_one_eq_mod _ 4
  have h2 : (a.setWidth 8 >>> 4).toNat = a.toNat % 256 / 16 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
  rw [h1, BitVec.toNat_ofNat, h2]
  omega_using []

/-- What the look-up needs of the index vectors of a nibble. -/
theorem nibble_vec : ∀ n < 16,
    (byte ((0 : BitVec 96) ++ (BitVec.ofNat 32 n ||| (0x80808000 : BitVec 32))) 0).msb = false ∧
    ((byte ((0 : BitVec 96) ++ (BitVec.ofNat 32 n ||| (0x80808000 : BitVec 32))) 0).extractLsb' 0 4).toNat = n ∧
    (byte ((0 : BitVec 96) ++ (BitVec.ofNat 32 n ||| (0x80808000 : BitVec 32))) 1).msb = true ∧
    (byte ((0 : BitVec 96) ++ (BitVec.ofNat 32 n ||| (0x80808000 : BitVec 32)).rotateRight 24) 0).msb = true ∧
    (byte ((0 : BitVec 96) ++ (BitVec.ofNat 32 n ||| (0x80808000 : BitVec 32)).rotateRight 24) 1).msb = false ∧
    ((byte ((0 : BitVec 96) ++ (BitVec.ofNat 32 n ||| (0x80808000 : BitVec 32)).rotateRight 24) 1).extractLsb' 0 4).toNat = n ∧
    (byte ((0 : BitVec 96) ++ BitVec.ofNat 32 n) 0).msb = false ∧
    ((byte ((0 : BitVec 96) ++ BitVec.ofNat 32 n) 0).extractLsb' 0 4).toNat = n := by
  decide

/-! ## The rows' bytes, put together -/

/-- The OR of rows `2 k` and `2 k + 1` through their index vectors. -/
def pairV (a : BitVec 32) (k : Nat) : BitVec 128 :=
  XBinOp.eval .por (XBinOp.eval .pshufb (row (2 * k)) (evV a)) (XBinOp.eval .pshufb (row (2 * k + 1)) (odV a))

def quadV (a : BitVec 32) (k : Nat) : BitVec 128 := XBinOp.eval .punpcklwd (pairV a k) (pairV a (k + 1))

def octV (a : BitVec 32) (k : Nat) : BitVec 128 := XBinOp.eval .punpckldq (quadV a k) (quadV a (k + 2))

def allV (a : BitVec 32) : BitVec 128 := XBinOp.eval .punpcklqdq (octV a 0) (octV a 4)

def resV (a : BitVec 32) : BitVec 128 := XBinOp.eval .pshufb (allV a) (hiV a)

/-- The index's low nibble. -/
abbrev lo (a : BitVec 32) : Nat := (a.setWidth 8 &&& 0x0f#8).toNat

theorem lo_lt (a : BitVec 32) : lo a < 16 := (nibbles (a.setWidth 8)).2.2.2.2.2.2.1

theorem pair_byte (a : BitVec 32) (k : Nat) {j : Nat} (hj : j < 2) :
    byte (pairV a k) j = byte (row (2 * k + j)) (lo a) := by
  obtain ⟨e0, e0', e1, o0, o1, o1', -, -⟩ := nibble_vec (lo a) (lo_lt a)
  rw [pairV, show ∀ x y : BitVec 128, XBinOp.eval .por x y = x ||| y from fun _ _ => rfl, byte_or,
    byte_pshufb _ _ (by omega_using [hj]), byte_pshufb _ _ (by omega_using [hj]), evV, odV, lo_eq]
  rcases (by omega_using [hj] : j = 0 ∨ j = 1) with rfl | rfl
  · rw [e0, e0', o0]; simp
  · rw [e1, o1, o1']; simp

/-- A byte of a register is a byte of one of its words. -/
theorem byte_eq_word (v : BitVec 128) (i : Nat) : byte v i = (word v (i / 2)).extractLsb' (8 * (i % 2)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [byte, word, BitVec.getLsbD_extractLsb', hr, decide_true, Bool.true_and,
    show 8 * (i % 2) + r < 16 by omega_using [hr]]
  exact congrArg _ (by omega_using [])

theorem byte_punpcklwd (x y : BitVec 128) {i : Nat} (hi : i < 4) :
    byte (XBinOp.eval .punpcklwd x y) i = if i < 2 then byte x i else byte y (i - 2) := by
  rw [byte_eq_word, word_punpcklwd _ _ (by omega_using [hi])]
  by_cases h : i < 2
  · rw [ite_eq_left h, ite_eq_left (by omega_using [h]), byte_eq_word x,
      show i / 2 / 2 = i / 2 by omega_using [h]]
  · rw [ite_eq_right h, ite_eq_right (by omega_using [h, hi]), byte_eq_word y,
      show i / 2 / 2 = (i - 2) / 2 by omega_using [h, hi], show i % 2 = (i - 2) % 2 by omega_using [h]]

theorem byte_punpckldq (x y : BitVec 128) {i : Nat} (hi : i < 8) :
    byte (XBinOp.eval .punpckldq x y) i = if i < 4 then byte x i else byte y (i - 4) := by
  rw [punpckldq_eq, byte_eq_dword]
  by_cases h : i < 4
  · rw [ite_eq_left h, show i / 4 = 0 by omega_using [h], dword_ofDwords_0, byte_eq_dword x,
      show i / 4 = 0 by omega_using [h]]
  · rw [ite_eq_right h, show i / 4 = 1 by omega_using [h, hi], dword_ofDwords_1, byte_eq_dword y,
      show (i - 4) / 4 = 0 by omega_using [h, hi], show (i - 4) % 4 = i % 4 by omega_using [h]]

theorem quad_byte (a : BitVec 32) (k : Nat) {j : Nat} (hj : j < 4) :
    byte (quadV a k) j = byte (row (2 * k + j)) (lo a) := by
  rw [quadV, byte_punpcklwd _ _ hj]
  by_cases h : j < 2
  · rw [ite_eq_left h, pair_byte a k h]
  · rw [ite_eq_right h, pair_byte a (k + 1) (by omega_using [h, hj]),
      show 2 * (k + 1) + (j - 2) = 2 * k + j by omega_using [h]]

theorem oct_byte (a : BitVec 32) (k : Nat) {j : Nat} (hj : j < 8) :
    byte (octV a k) j = byte (row (2 * k + j)) (lo a) := by
  rw [octV, byte_punpckldq _ _ hj]
  by_cases h : j < 4
  · rw [ite_eq_left h, quad_byte a k h]
  · rw [ite_eq_right h, quad_byte a (k + 2) (by omega_using [h, hj]),
      show 2 * (k + 2) + (j - 4) = 2 * k + j by omega_using [h]]

theorem all_byte (a : BitVec 32) {j : Nat} (hj : j < 16) : byte (allV a) j = byte (row j) (lo a) := by
  rw [allV, byte_punpcklqdq _ _ hj]
  by_cases h : j < 8
  · rw [ite_eq_left h, oct_byte a 0 h, show 2 * 0 + j = j by omega_using []]
  · rw [ite_eq_right h, oct_byte a 4 (by omega_using [h, hj]), show 2 * 4 + (j - 8) = j by omega_using [h]]

/-- **The look-up.** -/
theorem resV_byte (a : BitVec 32) : byte (resV a) 0 = Spec.Rc2.pi (a.setWidth 8) := by
  obtain ⟨-, -, -, -, -, hl, ll, sum⟩ := nibbles (a.setWidth 8)
  obtain ⟨-, -, -, -, -, -, h0, h0'⟩ := nibble_vec _ hl
  rw [resV, byte_pshufb _ _ (by decide), hiV, hi_eq, h0, h0', ite_eq_right Bool.false_ne_true,
    all_byte a hl, row_byte hl ll, sum]
  rfl

theorem resV_dword (a : BitVec 32) : dword (resV a) 0 &&& 255 = (Spec.Rc2.pi (a.setWidth 8)).setWidth 32 := by
  rw [← resV_byte, byte_low _ (by decide : 0 < 4), idx_and255]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
    Nat.mul_zero, Nat.shiftRight_zero]

/-! ## The code -/

theorem syms_setXmm (s : State) (d : XReg) (v : BitVec 128) : (s.setXmm d v).syms = s.syms := rfl

theorem start_ok (s : State) :
    WP isa (.block start) s fun t =>
      t.xmm .xmm5 = hiV (s.gpr .eax) ∧ t.xmm .xmm6 = evV (s.gpr .eax) ∧ t.xmm .xmm7 = odV (s.gpr .eax) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold start
  lrun
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ne_eq, not_false_eq_true, xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, xmm_setFlags,
      xmm_arithFlags, gpr_setXmm, gpr_setReg, gpr_setFlags, gpr_arithFlags, mem_setXmm, mem_setReg,
      mem_setFlags, mem_arithFlags, rd_setXmm, rd_setReg, rd_setFlags, rd_arithFlags, wr_setXmm, wr_setReg,
      wr_setFlags, wr_arithFlags, reduceCtorEq]
  · rfl
  · rfl
  · rfl
  · intro r ha hb
    simp only [ha, hb, ite_false]

/-- The sixteen rows, read once. -/
theorem rows_ok (s : State) (a : BitVec 32) (hb : s.gpr .ebp = s.syms piSym) (h5 : s.xmm .xmm5 = hiV a)
    (h6 : s.xmm .xmm6 = evV a) (h7 : s.xmm .xmm7 = odV a) :
    WP isa (.block rows) s fun t =>
      t.xmm .xmm1 = resV a ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold rows octet quad pair tb
  lrun [memOp, syms_setXmm, hb, Proof.Rc2.piQuads_length, Nat.reduceDiv]
  refine ⟨?_, funext fun r => ?_, ?_, ?_, ?_⟩
  · simp only [xmm_setXmm_self, h5, h6, h7, resV, allV, octV, quadV, pairV, row, Nat.reduceMul, Nat.reduceAdd]
  · simp only [gpr_setXmm]
  · simp only [mem_setXmm]
  · simp only [rd_setXmm]
  · simp only [wr_setXmm]

/-- PITABLE[EAX & 255] into EAX, keeping memory; the table's address is in EBP. -/
theorem piLookup_ok (s : State) (hw : InRegions s.wr (addr (s.gpr .edi) 0) 16)
    (hb : s.gpr .ebp = s.syms piSym) :
    WP isa (.block Ssse3.piLookup) s fun t =>
      t.gpr .eax = (Spec.Rc2.pi ((s.gpr .eax).setWidth 8)).setWidth 32 ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [Ssse3.piLookup, List.append_assoc, WP.block_append_iff]
  refine VG.X86.WP.mono_syms (start_ok s) fun t ⟨t5, t6, t7, tg, tm, trd, twr⟩ ts => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rows_ok t (s.gpr .eax) (by rw [tg .ebp (by decide) (by decide), ts]; exact hb) t5 t6 t7)
    fun u ⟨u1, ug, um, urd, uwr⟩ => ?_
  have edi : u.gpr .edi = s.gpr .edi := by rw [ug]; exact tg .edi (by decide) (by decide)
  refine WP.mono (extract_ok u (by rw [uwr, twr, edi]; exact hw)) fun y ⟨y1, yg, ym, yrd, ywr⟩ =>
    ⟨?_, fun r ha hb' _ => ?_, ?_, ?_, ?_⟩
  · rw [y1, u1, resV_dword]
  · rw [yg r ha, ug, tg r ha hb']
  · rw [ym, um, tm]
  · rw [yrd, urd, trd]
  · rw [ywr, uwr, twr]

end VG.Proof.Rc2.X86.Ssse3
