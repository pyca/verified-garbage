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
import VerifiedGarbage.Proof.Framework.X86.SseWord

/-!
# XTS-AES on x86: multiplication by `α`

`mulA` run once, with its memory as explicit writes (`alphaMem`): the
canonical words of `mulAlpha_words32` (`Proof/AesXts/Alpha.lean`), from
`add`, `adc`, `sbb`, `and` and `xor`.

`mulX` is the same product in an SSE register: `alphaX` of its 128-bit value,
whose 16 bytes (`bx`) are then `Spec.Xts.mulAlpha` of the bytes it had
(`bx_alphaX`). `mulX_val` is the value its instructions compute, doubleword
by doubleword (`dword_alphaX_0`, `dword_alphaX_succ`, and `mask32` for the
mask of the carried bit). `mul8_val` is the value `mul8`'s instructions
compute: `alphaX` eight times.
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

/-! ## `α⁸`

`mul8` multiplies by `α⁸` at once. `x ⊗ αᵏ`, for `k ≤ 8`, is `x` shifted
left by `k` bits, XORed with the `k` bits shifted out times `0x87` without
carries (`jumpX`, `redX`), by induction on `k` (`jump_succ`: one more
`alphaX`, whose carried bit is bit `127 − k` of `x`, `jump_msb`); for
`k = 8` the bits shifted out are the top byte, which the quadword shifts of
`mul8` shift as 128-bit shifts would (`psllq_small`, checked for each
byte). -/

/-- The carry-less product of `h` and `0x87`. -/
def redX (h : BitVec 128) : BitVec 128 := h ^^^ (h <<< 1) ^^^ (h <<< 2) ^^^ (h <<< 7)

/-- `x ⊗ αᵏ`, for `k ≤ 8`: `x` shifted left by `k` bits, and the `k` bits shifted out times `0x87`. -/
def jumpX (k : Nat) (x : BitVec 128) : BitVec 128 := (x <<< k) ^^^ redX (x >>> (128 - k))

theorem redX_xor (u v : BitVec 128) : redX (u ^^^ v) = redX u ^^^ redX v := by
  simp only [redX, BitVec.shiftLeft_xor_distrib]; ac_rfl

theorem redX_shl (h : BitVec 128) : redX h <<< 1 = redX (h <<< 1) := by
  simp only [redX, BitVec.shiftLeft_xor_distrib, ← BitVec.shiftLeft_add]

theorem redX_bit (b : Bool) : redX (if b then 1 else 0) = if b then 0x87 else 0 := by
  cases b <;> decide

theorem jump_msb (x : BitVec 128) {k : Nat} (hk : k < 8) : (jumpX k x).msb = x.getLsbD (127 - k) := by
  simp only [jumpX, redX, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  have o (m : Nat) (hm : 120 ≤ m) : x.getLsbD (128 - k + m) = false := BitVec.getLsbD_of_ge _ _ (by omega_arith)
  simp [o, show ¬ 127 < k by omega_arith]

theorem shr_succ (x : BitVec 128) {k : Nat} (hk : k < 8) :
    x >>> (127 - k) = ((x >>> (128 - k)) <<< 1) ^^^ (if x.getLsbD (127 - k) then 1 else 0) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases hi0 : i = 0
  · subst hi0; cases hb : x.getLsbD (127 - k) <;> simp [hb]
  · have e : 128 - k + (i - 1) = 127 - k + i := by omega_arith
    cases hb : x.getLsbD (127 - k) <;> simp [hi, hi0, e, show ¬ i < 1 by omega_arith]

theorem jump_succ (x : BitVec 128) {k : Nat} (hk : k < 8) : alphaX (jumpX k x) = jumpX (k + 1) x := by
  rw [alphaX, jump_msb x hk, ← redX_bit]
  rw [jumpX, BitVec.shiftLeft_xor_distrib, ← BitVec.shiftLeft_add, redX_shl, BitVec.xor_assoc, ← redX_xor,
    ← shr_succ x hk, jumpX, show 128 - (k + 1) = 127 - k by omega_arith]

theorem jump_zero (x : BitVec 128) : jumpX 0 x = x := by
  have z : x >>> 128 = 0 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_of_ge _ _ (by omega_arith)]; simp
  simp [jumpX, redX, z]

theorem alphaX_iter (x : BitVec 128) : ∀ k, k ≤ 8 → Nat.repeat alphaX k x = jumpX k x
  | 0, _ => (jump_zero x).symm
  | k + 1, h => by
    show alphaX (Nat.repeat alphaX k x) = _
    rw [alphaX_iter x k (by omega_arith), jump_succ x (by omega_arith)]

theorem shr120 (x : BitVec 128) : x >>> 120 = (x.extractLsb' 120 8).setWidth 128 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and]
  by_cases h : i < 8
  · simp only [h, decide_true, Bool.true_and]
  · simp only [h, decide_false, Bool.false_and]; exact BitVec.getLsbD_of_ge _ _ (by omega_arith)

theorem psllq_small : ∀ b : BitVec 8,
    XShiftOp.eval .psllq (b.setWidth 128) 1 = b.setWidth 128 <<< 1 ∧
    XShiftOp.eval .psllq (b.setWidth 128 <<< 1) 1 = b.setWidth 128 <<< 2 ∧
    XShiftOp.eval .psllq (b.setWidth 128 <<< 2) 5 = b.setWidth 128 <<< 7 := by decide +kernel

/-- What `mul8` computes is `x ⊗ α⁸`. -/
theorem mul8_val (x : BitVec 128) :
    XBinOp.eval .pxor (XBinOp.eval .pxor (XBinOp.eval .pxor (XBinOp.eval .pxor (XShiftOp.eval .pslldq x 1)
      (XShiftOp.eval .psrldq x 15)) (XShiftOp.eval .psllq (XShiftOp.eval .psrldq x 15) 1))
      (XShiftOp.eval .psllq (XShiftOp.eval .psllq (XShiftOp.eval .psrldq x 15) 1) 1))
      (XShiftOp.eval .psllq (XShiftOp.eval .psllq (XShiftOp.eval .psllq (XShiftOp.eval .psrldq x 15) 1) 1) 5) =
      Nat.repeat alphaX 8 x := by
  obtain ⟨p1, p2, p3⟩ := psllq_small (x.extractLsb' 120 8)
  have eh : XShiftOp.eval .psrldq x 15 = (x.extractLsb' 120 8).setWidth 128 := shr120 x
  rw [eh, p1, p2, p3, ← shr120, alphaX_iter x 8 (by decide), jumpX, redX]
  show x <<< 8 ^^^ x >>> 120 ^^^ x >>> 120 <<< 1 ^^^ x >>> 120 <<< 2 ^^^ x >>> 120 <<< 7 = _
  ac_rfl

/-- The bytes of `x ⊗ α⁸`. -/
theorem bx_iter8 (x : BitVec 128) : bx (Nat.repeat alphaX 8 x) = Nat.repeat mulAlpha 8 (bx x) := by
  simp only [Nat.repeat, bx_alphaX]

/-! ## The carries ahead

`Impl.AesXts.X86AesNi.step` multiplies a tweak by `α` with the two carries of
its quadwords made from `Signs`: the top bits of the first tweak's quadwords,
one after the other, as the bits that the reductions change are far below
them (`jump_msb`, `jump_bit63`). -/

/-- `0x87` in the low quadword if `b`, and `1` in the high one if `c`. -/
def redBC (b c : Bool) : BitVec 128 := (if c then (1 : BitVec 64) else 0) ++ (if b then (0x87 : BitVec 64) else 0)

/-- The carries of the quadwords of `x ⊗ αᵏ`. -/
def carryOf (x : BitVec 128) (k : Nat) : BitVec 128 := redBC (x.getLsbD (127 - k)) (x.getLsbD (63 - k))

/-- The constant of the sign steps: `0x87` and `1` in the quadwords. -/
def signC : BitVec 128 := (1 : BitVec 64) ++ (0x87 : BitVec 64)

/-- `t`'s words 0 and 4 hold, from the sign bit down, the bits `127 - k` and
`63 - k` of `x` and those below them. -/
def Signs (x : BitVec 128) (k : Nat) (t : BitVec 128) : Prop :=
  word t 0 = word x 7 <<< k ∧ word t 4 = word x 3 <<< k

theorem wbit (x : BitVec 128) (i : Nat) {j : Nat} (hj : j < 16) : (word x i).getLsbD j = x.getLsbD (16 * i + j) := by
  simp [word, hj]

theorem sraw15 (w : BitVec 16) : w.sshiftRight 15 = if w.msb then BitVec.allOnes 16 else 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hl : (w.sshiftRight 15).getLsbD i = w.msb := by
    rw [BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last]
    by_cases h0 : i = 0
    · subst h0; simp
    · simp [show ¬ 16 ≤ i by omega_arith, show ¬ 15 + i < 16 by omega_arith]
  rw [hl]
  cases w.msb
  · simp
  · rw [ite_eq_left rfl, BitVec.getLsbD_allOnes]; simp [hi]

theorem wadd (w : BitVec 16) : w + w = w <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega_using []

theorem Signs.step {x t : BitVec 128} {k : Nat} (h : Signs x k t) : Signs x (k + 1) (XBinOp.eval .paddw t t) := by
  constructor
  · rw [word_paddw _ _ (by decide), h.1, wadd, ← BitVec.shiftLeft_add]
  · rw [word_paddw _ _ (by decide), h.2, wadd, ← BitVec.shiftLeft_add]

theorem hi16 (x : BitVec 128) (k : Nat) :
    (dword x k >>> (16 : BitVec 8).toNat).extractLsb' (16 * 0) 16 = word x (2 * k + 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [wbit x _ hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, getLsbD_dword]
  have e : 32 * k + ((16 : BitVec 8).toNat + (16 * 0 + i)) = 16 * (2 * k + 1) + i := by
    show 32 * k + (16 + (16 * 0 + i)) = _; omega_arith
  have l : (16 : BitVec 8).toNat + (16 * 0 + i) < 32 := by show 16 + (16 * 0 + i) < 32; omega_arith
  rw [e, decide_eq_true hi, decide_eq_true l, Bool.true_and, Bool.true_and]

theorem Signs.start (x : BitVec 128) : Signs x 0 (XShiftOp.eval .psrld (shufDwords x 0x5f) 16) := by
  have s0 : ((0x5f : BitVec 8).extractLsb' (2 * 0) 2).toNat = 3 := rfl
  have s2 : ((0x5f : BitVec 8).extractLsb' (2 * 2) 2).toNat = 1 := rfl
  constructor
  · rw [word_dword _ 0 0 (by decide), dword_psrld _ _ (by decide) (by decide), dword_shufDwords _ _ (by decide), s0,
      BitVec.shiftLeft_zero]
    exact hi16 x 3
  · rw [word_dword _ 2 0 (by decide), dword_psrld _ _ (by decide) (by decide), dword_shufDwords _ _ (by decide), s2,
      BitVec.shiftLeft_zero]
    exact hi16 x 1

theorem mask_words (b : BitVec 16) (c : BitVec 16) : (b.sshiftRight 15) &&& c = if b.msb then c else 0 := by
  rw [sraw15]; split
  · exact BitVec.allOnes_and
  · exact BitVec.zero_and

theorem word_signC : word signC 0 = 0x87 ∧ word signC 4 = 1 ∧
    ∀ i < 8, i ≠ 0 → i ≠ 4 → word signC i = 0 := by decide

theorem word_redBC : ∀ b c : Bool, word (redBC b c) 0 = (if b then 0x87 else 0) ∧ word (redBC b c) 4 = (if c then 1 else 0) ∧
    ∀ i < 8, i ≠ 0 → i ≠ 4 → word (redBC b c) i = 0 := by decide

theorem Signs.msb {x t : BitVec 128} {k : Nat} (h : Signs x k t) (hk : k < 16) :
    (word t 0).msb = x.getLsbD (127 - k) ∧ (word t 4).msb = x.getLsbD (63 - k) := by
  rw [h.1, h.2, BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_shiftLeft]
  have h1 : ¬ 15 < k := by omega_arith
  have e (i : Nat) : (word x i).getLsbD (16 - 1 - k) = x.getLsbD (16 * i + (15 - k)) := wbit x i (by omega_arith)
  rw [e, e, show 16 * 7 + (15 - k) = 127 - k by omega_arith, show 16 * 3 + (15 - k) = 63 - k by omega_arith]
  simp [h1]

theorem Signs.red {x t : BitVec 128} {k : Nat} (h : Signs x k t) (hk : k < 16) :
    XBinOp.eval .pand (XShiftOp.eval .psraw t 15) signC = carryOf x k := by
  have n15 : min (15 : BitVec 8).toNat 16 = 15 := rfl
  obtain ⟨m0, m4⟩ := h.msb hk
  obtain ⟨c0, c4, cz⟩ := word_signC
  rw [carryOf]
  obtain ⟨r0, r4, rz⟩ := word_redBC (x.getLsbD (127 - k)) (x.getLsbD (63 - k))
  apply ext_word; intro i hi
  rw [word_pand, word_psraw _ _ hi, n15]
  by_cases h0 : i = 0
  · subst h0; rw [c0, r0, mask_words, m0]
  by_cases h4 : i = 4
  · subst h4; rw [c4, r4, mask_words, m4]
  · rw [cz i hi h0 h4, rz i hi h0 h4]; exact BitVec.and_zero

theorem qadd (w : BitVec 64) : w + w = w <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega_using []

theorem paddq_red (x : BitVec 128) :
    XBinOp.eval .pxor (XBinOp.eval .paddq x x) (redBC x.msb (x.getLsbD 63)) = alphaX x := by
  show ((qword x 1 + qword x 1) ++ (qword x 0 + qword x 0)) ^^^ redBC x.msb (x.getLsbD 63) = _
  rw [qadd, qadd, alphaX, redBC]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft, qword, qword, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_extractLsb']
  have kb : ∀ (b : Bool) i, (if b = true then (135 : BitVec 128) else 0).getLsbD i =
      (if b = true then (135 : BitVec 64) else 0).getLsbD i := fun b i => by
    cases b
    · simp
    · exact rfl
  rw [kb]
  by_cases h : i < 64
  · have h1 : i - 1 < 64 := by omega_arith
    have h2 : 64 * 0 + (i - 1) = i - 1 := by omega_arith
    simp only [h, hi, h1, h2, ite_true, decide_true, Bool.true_and]
  · have z : (if x.msb = true then (135 : BitVec 64) else 0).getLsbD i = false := BitVec.getLsbD_of_ge _ _ (by omega_arith)
    have h1 : i - 64 < 64 := by omega_arith
    have h3 : i - 64 - 1 < 64 := by omega_arith
    rw [z]
    by_cases h0 : i = 64
    · subst h0; cases x.getLsbD 63 <;> simp
    · have e : 64 * 1 + (i - 64 - 1) = i - 1 := by omega_arith
      have l : ¬ i < 1 := by omega_arith
      have l' : ¬ i - 64 < 1 := by omega_arith
      have b1 : (if x.getLsbD 63 = true then (1 : BitVec 64) else 0).getLsbD (i - 64) = false := by
        cases x.getLsbD 63
        · simp
        · simp [show ¬ i - 64 = 0 by omega_arith]
      simp only [h, hi, h1, h3, e, l, l', b1, ite_false, decide_true, decide_false, Bool.true_and, Bool.not_false]

theorem jump_bit63 (x : BitVec 128) {k : Nat} (hk : k < 8) : (jumpX k x).getLsbD 63 = x.getLsbD (63 - k) := by
  simp only [jumpX, redX, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  have o (m : Nat) (hm : 56 ≤ m) : x.getLsbD (128 - k + m) = false := BitVec.getLsbD_of_ge _ _ (by omega_arith)
  simp [o, show ¬ 63 < k by omega_arith]

/-- The tweak after `k` steps, doubled with its carries. -/
theorem dbl_carry (x : BitVec 128) {k : Nat} (hk : k < 8) :
    XBinOp.eval .pxor (XBinOp.eval .paddq (Nat.repeat alphaX k x) (Nat.repeat alphaX k x)) (carryOf x k) =
      Nat.repeat alphaX (k + 1) x := by
  show _ = alphaX (Nat.repeat alphaX k x)
  rw [← paddq_red, alphaX_iter x k (by omega_arith), jump_msb x hk, jump_bit63 x hk, carryOf]

end VG.Proof.AesXts.X86
