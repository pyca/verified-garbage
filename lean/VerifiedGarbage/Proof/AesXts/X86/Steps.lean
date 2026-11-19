module

import VerifiedGarbage.Proof.AesXts.Alpha
import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Impl.AesXts.X86
public import VerifiedGarbage.Spec.Xts
import VerifiedGarbage.Proof.CmacAes.X86.Save
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword

/-!
# XTS-AES on x86: multiplication by `α`

`mulA` run once, with its memory as explicit writes (`alphaMem`): the
canonical words of `mulAlpha_words32` (`Proof/AesXts/Alpha.lean`), from
`add`, `adc`, `sbb`, `and` and `xor`.

`mulX` is the same product in an SSE register: `alphaX` of its 128-bit value,
whose 16 bytes (`bx`) are then `Spec.Xts.mulAlpha` of the bytes it had
(`bx_alphaX`). `mulX_val` is the value its instructions compute, doubleword
by doubleword (`dword_alphaX_0`, `dword_alphaX_succ`, and `mask32` for the
mask of the carried bit).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesXts.X86
open VG.Impl.CmacAes.X86 (at_)
open VG.Proof.CmacAes.X86 (ea_at')
open VG.Spec.Aes (bytesAt)
open VG.Spec.Xts (mulAlpha)

/-- The memory after `mulA` on the tweak at `Q`. -/
def alphaMem (m : Mem) (Q : Addr) : Mem :=
  let w (d : Nat) := m.readW (Q + BitVec.ofNat 64 d) 32
  (((m.writeW Q ((w 0 <<< 1) ^^^ (if (w 12).msb then (0x87 : BitVec 32) else 0))).writeW
      (Q + BitVec.ofNat 64 4) ((w 4 <<< 1) ||| (if (w 0).msb then (1 : BitVec 32) else 0))).writeW
      (Q + BitVec.ofNat 64 8) ((w 8 <<< 1) ||| (if (w 4).msb then (1 : BitVec 32) else 0))).writeW
      (Q + BitVec.ofNat 64 12) ((w 12 <<< 1) ||| (if (w 8).msb then (1 : BitVec 32) else 0))

theorem add_self (x : BitVec 32) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega_using []

theorem carry_self (x : BitVec 32) : decide (2 ^ 32 ≤ x.toNat + x.toNat) = x.msb := by
  rw [BitVec.msb_eq_decide]
  have := x.isLt
  simp only [decide_eq_decide]
  omega_using []

theorem carry_self_c (x : BitVec 32) (c : Bool) :
    decide (2 ^ 32 ≤ x.toNat + x.toNat + c.toNat) = x.msb := by
  rw [BitVec.msb_eq_decide]
  have := x.isLt
  have := c.toNat_le
  simp only [decide_eq_decide]
  omega_using [this]

theorem shl_add_bit (x : BitVec 32) (c : Bool) :
    (x <<< 1) + (BitVec.ofBool c).setWidth 32 = (x <<< 1) ||| (if c then (1 : BitVec 32) else 0) := by
  cases c
  · simp
  · apply BitVec.add_eq_or_of_and_eq_zero
    ext i hi
    simp
    omega_using []

theorem mask_87 (x : BitVec 32) (c : Bool) :
    (x - x - (BitVec.ofBool c).setWidth 32) &&& (135 : BitVec 32) = if c then (0x87 : BitVec 32) else 0 := by
  rw [BitVec.sub_self]
  cases c <;> decide

theorem mulA_ok (s : State) {Q : Addr} (hq : (s.gpr .ebx).setWidth 64 = Q) (hfit : (s.gpr .ebx).toNat + 16 ≤ 2 ^ 32)
    (hr : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 d) n)
    (hw : ∀ d n, d + n ≤ 16 → InRegions s.wr (Q + BitVec.ofNat 64 d) n) :
    ∃ s', runBlock isa mulA s = some s' ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → r ≠ .ebp → s'.gpr r = s.gpr r) ∧
      s'.mem = alphaMem s.mem Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a (d : Nat) (hd : d < 16) : addr (s.gpr .ebx) d = Q + BitVec.ofNat 64 d := by
    rw [addr_eq (by omega_using [hfit, hd]), hq]
  have a0 : addr (s.gpr .ebx) 0 = Q := by rw [a 0 (by decide)]; simp
  have r0 : InRegions (s.rd ++ s.wr) Q 4 := by simpa using hr 0 4 (by decide)
  have w0 : InRegions s.wr Q 4 := by simpa using hw 0 4 (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, mulA, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.store32, ea_at', execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, cf_setReg, cf_arithFlags, a0, a 4 (by decide), a 8 (by decide), a 12 (by decide),
      r0, hr 4 4 (by decide), hr 8 4 (by decide), hr 12 4 (by decide), w0, hw 4 4 (by decide),
      hw 8 4 (by decide), hw 12 4 (by decide)]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ h₃ h₄ h₅ => by simp [gpr_setReg, h₁, h₂, h₃, h₄, h₅], ?_, rfl, rfl⟩
  have e0 : Q + BitVec.ofNat 64 0 = Q := by simp
  simp only [alphaMem, e0, carry_self, carry_self_c, add_self, shl_add_bit, mask_87]

theorem alphaMem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 16⟩] m (alphaMem m Q) :=
  ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains_base Q (d := 0) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 4) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 8) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 12) (n := 4) (k := 16) (by decide) (by decide))

theorem alphaMem_bytes (m : Mem) (Q : Addr) : bytesAt (alphaMem m Q) Q 16 = Spec.Xts.mulAlpha (bytesAt m Q 16) := by
  have := AesXts.mulAlpha_words32 m Q
  have e0 : Q + BitVec.ofNat 64 0 = Q := by simp
  simp only [e0] at this
  simp only [alphaMem, e0]
  exact this

/-! ## In an SSE register -/

/-- The 16 bytes of a 128-bit value, the least significant first: the block a
16-byte load reads it from and a store writes it to. -/
def bx (x : BitVec 128) : List Byte := (List.range 16).map fun j => x.extractLsb' (8 * j) 8

/-- The block at `P`, loaded. -/
theorem bytesAt_bx (m : Mem) (P : Addr) : bytesAt m P 16 = bx (m.readW P 128) := AesXts.bytesAt_readW (k := 16) m P

/-- The block at `P`, stored. -/
theorem bytesAt_writeW_bx (m : Mem) (P : Addr) (v : BitVec 128) : bytesAt (m.writeW P v) P 16 = bx v :=
  AesXts.bytesAt_writeW (k := 16) m P v (by decide)

theorem bx_xor (a b : BitVec 128) : bx (a ^^^ b) = Spec.Cbc.xor (bx a) (bx b) := by
  simp only [bx, Spec.Cbc.xor, List.zipWith_map, List.zipWith_self, BitVec.extractLsb'_xor]

/-- `x ⊗ α`, of the tweak as a 128-bit integer, the first byte least
significant: shifted left by one bit, and XORed with `0x87` if the top bit
was set. -/
def alphaX (x : BitVec 128) : BitVec 128 := (x <<< 1) ^^^ (if x.msb then 0x87 else 0)

theorem bx_alphaX (x : BitVec 128) : bx (alphaX x) = mulAlpha (bx x) := by
  simp only [bx, List.range, List.range.loop, List.map]
  rw [AesXts.mulAlpha_16, alphaX, AesXts.msb_byte x 15 rfl]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (rw [AesXts.byte_shl_xor _ _ (by decide)]; rfl)

/-- All ones (`xmm6`). -/
def onesX : BitVec 128 := ofDwords 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
/-- The doublewords `0x87, 1, 1, 1` (`xmm7`). -/
def cX : BitVec 128 := ofDwords 0x87 1 1 1

theorem dword_pandn (a b : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .pandn a b) i = ~~~dword a i &&& dword b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [XBinOp.eval, dword, hj, show 32 * i + j < 128 by omega_arith]

/-- The top bit, shifted down. -/
theorem shr31 (x : BitVec 32) : x >>> 31 = if x.msb then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  by_cases h : x.msb
  · have h' := h; rw [BitVec.msb_eq_decide] at h'
    simp only [h, ↓reduceIte, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp at h'; show x.toNat / 2 ^ 31 = 1; omega_arith
  · have h' := h; rw [BitVec.msb_eq_decide] at h'
    simp only [h, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp at h'; show x.toNat / 2 ^ 31 = 0; omega_arith

/-- The top bit of `x` as a mask of `c`: all ones added to it, complemented. -/
theorem mask32 (x c : BitVec 32) : ~~~((x >>> 31) + 0xFFFFFFFF) &&& c = if x.msb then c else 0 := by
  rw [shr31]
  have e1 : ~~~((1 : BitVec 32) + 0xFFFFFFFF) = BitVec.allOnes 32 := by decide
  have e0 : ~~~((0 : BitVec 32) + 0xFFFFFFFF) = 0 := by decide
  by_cases h : x.msb
  · simp only [h, ↓reduceIte, e1, BitVec.allOnes_and]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, e0]; exact BitVec.zero_and

theorem msb_dword3 (x : BitVec 128) : x.msb = (dword x 3).msb := by
  simp only [BitVec.msb_eq_getLsbD_last, getLsbD_dword]; simp

theorem dword_alphaX_0 (x : BitVec 128) :
    dword (alphaX x) 0 = (dword x 0 <<< 1) ^^^ (if (dword x 3).msb then 0x87 else 0) := by
  rw [alphaX, msb_dword3]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h128 : i < 128 := by omega_arith
  have h1 : i - 1 < 32 := by omega_arith
  have k : (135#128).getLsbD i = (135#32).getLsbD i := rfl
  by_cases h : (dword x 3).msb
  · simp only [h, ↓reduceIte, getLsbD_dword, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
      Nat.mul_zero, Nat.zero_add, hi, h128, h1, decide_true, Bool.true_and]
    exact congrArg (fun b => (!decide (i < 1) && x.getLsbD (i - 1)) ^^ b) k
  · simp only [h, Bool.false_eq_true, ↓reduceIte, getLsbD_dword, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
      Nat.mul_zero, Nat.zero_add, hi, h128, h1, decide_true, Bool.true_and]
    rfl

theorem dword_alphaX_succ (x : BitVec 128) {j : Nat} (hj : j < 3) :
    dword (alphaX x) (j + 1) = (dword x (j + 1) <<< 1) ^^^ (if (dword x j).msb then 1 else 0) := by
  rw [alphaX]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h128 : 32 * (j + 1) + i < 128 := by omega_arith
  have k1 : (135#128).getLsbD (32 * (j + 1) + i) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 135 < 2 ^ 32) (Nat.pow_le_pow_right (by decide) (by omega_arith)))
  have hm : (dword x j).msb = x.getLsbD (32 * j + 31) := by
    simp only [BitVec.msb_eq_getLsbD_last, getLsbD_dword]; simp
  have hc : (if x.msb = true then (135 : BitVec 128) else 0).getLsbD (32 * (j + 1) + i) = false := by
    split
    · exact k1
    · simp
  simp only [getLsbD_dword, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, hi, h128, decide_true, Bool.true_and, hc,
    hm, Bool.xor_false]
  by_cases hi0 : i = 0
  · subst hi0
    have e : 32 * (j + 1) - 1 = 32 * j + 31 := by omega_arith
    cases hb : x.getLsbD (32 * j + 31) <;> simp [hb, e]
  · have e : 32 * (j + 1) + i - 1 = 32 * (j + 1) + (i - 1) := by omega_arith
    have h1 : i - 1 < 32 := by omega_arith
    have l : ¬ 32 * (j + 1) + i < 1 := by omega_arith
    have l' : ¬ i < 1 := by omega_arith
    cases hb : x.getLsbD (32 * j + 31) <;> simp [e, h1, l, l', hi0]

/-- What `mulX` computes is `x ⊗ α`. -/
theorem mulX_val (x : BitVec 128) :
    XBinOp.eval .pxor (XBinOp.eval .paddd x x)
      (XBinOp.eval .pandn (XBinOp.eval .paddd (XShiftOp.eval .psrld (shufDwords x 0x93) 31) onesX) cX) = alphaX x := by
  have s0 : ((0x93 : BitVec 8).extractLsb' (2 * 0) 2).toNat = 3 := rfl
  have s1 : ((0x93 : BitVec 8).extractLsb' (2 * 1) 2).toNat = 0 := rfl
  have s2 : ((0x93 : BitVec 8).extractLsb' (2 * 2) 2).toNat = 1 := rfl
  have s3 : ((0x93 : BitVec 8).extractLsb' (2 * 3) 2).toNat = 2 := rfl
  have n31 : (31 : BitVec 8).toNat = 31 := rfl
  apply ext_dword
  · rw [dword_pxor, dword_paddd _ _ (by decide), dword_pandn _ _ (by decide), dword_paddd _ _ (by decide),
      dword_psrld _ _ (by decide) (by decide), dword_shufDwords _ _ (by decide), s0, n31, onesX, cX, dword_ofDwords_0,
      dword_ofDwords_0, mask32, add_self, dword_alphaX_0]
  · rw [dword_pxor, dword_paddd _ _ (by decide), dword_pandn _ _ (by decide), dword_paddd _ _ (by decide),
      dword_psrld _ _ (by decide) (by decide), dword_shufDwords _ _ (by decide), s1, n31, onesX, cX, dword_ofDwords_1,
      dword_ofDwords_1, mask32, add_self, dword_alphaX_succ x (j := 0) (by decide)]
  · rw [dword_pxor, dword_paddd _ _ (by decide), dword_pandn _ _ (by decide), dword_paddd _ _ (by decide),
      dword_psrld _ _ (by decide) (by decide), dword_shufDwords _ _ (by decide), s2, n31, onesX, cX, dword_ofDwords_2,
      dword_ofDwords_2, mask32, add_self, dword_alphaX_succ x (j := 1) (by decide)]
  · rw [dword_pxor, dword_paddd _ _ (by decide), dword_pandn _ _ (by decide), dword_paddd _ _ (by decide),
      dword_psrld _ _ (by decide) (by decide), dword_shufDwords _ _ (by decide), s3, n31, onesX, cX, dword_ofDwords_3,
      dword_ofDwords_3, mask32, add_self, dword_alphaX_succ x (j := 2) (by decide)]

end VG.Proof.AesXts.X86
