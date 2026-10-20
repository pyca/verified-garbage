module

import VerifiedGarbage.Proof.AesXts.Alpha
public import VerifiedGarbage.Impl.AesXts.X86_64
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Spec.Xts
import VerifiedGarbage.Proof.AesCbc.X86_64.Block
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# XTS-AES on x86-64: the tweak in registers

The tweak is kept as two little-endian words, the low one in `rax` and the
high one in `rcx`, whose bytes are `le8 rax ++ le8 rcx` (`tw`). `ldT` loads
them (`ldT_ok`, `tw_ldT`), `stT` stores them (`stT_ok`, `bytesAt_store2`),
`xorT` XORs them into a block (`xorT_ok`, `xorRegMem_bytes`), and `mulA`
multiplies them by `α` (`mulA_ok`, `mulAlpha_le8`): the words of
`mulAlpha_words64` (`Proof/AesXts/Alpha.lean`), from `add`, `adc`, `sbb`,
`and` and `xor`.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesXts.X86_64
open VG.Impl.AesCbc.X86_64 (at_)
open VG.Proof.AesCbc.X86_64 (offset_nat)
open VG.Spec.Aes (bytesAt)

/-- The bytes of the tweak in the words `L` (low) and `H` (high). -/
abbrev tw (L H : BitVec 64) : List Byte := Proof.Cmac.le8 L ++ Proof.Cmac.le8 H

/-- The tweak times `α`, in words. -/
theorem mulAlpha_le8 (L H : BitVec 64) :
    tw ((L <<< 1) ^^^ (if H.msb then (0x87 : BitVec 64) else 0)) ((H <<< 1) ||| (if L.msb then (1 : BitVec 64) else 0)) =
      Spec.Xts.mulAlpha (tw L H) := by
  simp only [tw, Proof.Cmac.le8, List.range, List.range.loop, List.map, List.cons_append, List.nil_append]
  rw [AesXts.mulAlpha_16, AesXts.msb_byte H 7 rfl, AesXts.msb_byte L 7 rfl]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | rw [AesXts.byte_shl_xor _ _ (by decide)]; rfl
    | rw [AesXts.byte_shl _ _ (by decide)]; rfl

/-- The memory after `xorT` of the words `L` and `H` into the block at `P`. -/
def xorRegMem (m : Mem) (P : Addr) (L H : BitVec 64) : Mem :=
  let m₁ := m.writeW P (m.readW P 64 ^^^ L)
  m₁.writeW (P + BitVec.ofNat 64 8) (m₁.readW (P + BitVec.ofNat 64 8) 64 ^^^ H)

theorem xorRegMem_frame (m : Mem) (P : Addr) (L H : BitVec 64) : Frame [⟨P, 16⟩] m (xorRegMem m P L H) :=
  AesCbc.frame_store2 _ _ _

theorem xorRegMem_bytes (m : Mem) (P : Addr) (L H : BitVec 64) :
    bytesAt (xorRegMem m P L H) P 16 = Spec.Cbc.xor (bytesAt m P 16) (tw L H) := by
  rw [xorRegMem, Proof.Cmac.bytesAt_store2, AesCbc.readW8_store1, Proof.Cmac.le8_xor, Proof.Cmac.le8_xor,
    Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, Proof.Cmac.bytesAt_split m P]
  exact (Proof.Cmac.xor_append (by simp [Spec.Aes.bytesAt, Proof.Cmac.le8])).symm

/-- The words of the tweak at `Q`. -/
theorem tw_readW (m : Mem) (Q : Addr) :
    tw (m.readW Q 64) (m.readW (Q + BitVec.ofNat 64 8) 64) = bytesAt m Q 16 := by
  rw [tw, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, Proof.Cmac.bytesAt_split]

theorem add_self (x : BitVec 64) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem carry_self (x : BitVec 64) : decide (2 ^ 64 ≤ x.toNat + x.toNat) = x.msb := by
  rw [BitVec.msb_eq_decide]
  have := x.isLt
  simp only [decide_eq_decide]
  omega

theorem carry_self_c (x : BitVec 64) (c : Bool) :
    decide (2 ^ 64 ≤ x.toNat + x.toNat + c.toNat) = x.msb := by
  rw [BitVec.msb_eq_decide]
  have := x.isLt
  have := c.toNat_le
  simp only [decide_eq_decide]
  omega

theorem shl_add_bit (x : BitVec 64) (c : Bool) :
    (x <<< 1) + (BitVec.ofBool c).setWidth 64 = (x <<< 1) ||| (if c then (1 : BitVec 64) else 0) := by
  cases c
  · simp
  · apply BitVec.add_eq_or_of_and_eq_zero
    ext i hi
    simp
    omega

theorem mask_87 (x : BitVec 64) (c : Bool) :
    (x - x - (BitVec.ofBool c).setWidth 64) &&& BitVec.signExtend 64 (135 : BitVec 32) =
      if c then (0x87 : BitVec 64) else 0 := by
  rw [BitVec.sub_self]
  cases c <;> decide

theorem ldT_ok (s : State) {Q : Addr} (hq : s.gpr .r12 = Q)
    (r0 : InRegions (s.rd ++ s.wr) Q 8) (r8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa ldT s = some s' ∧ (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.gpr .rax = s.mem.readW Q 64 ∧ s'.gpr .rcx = s.mem.readW (Q + BitVec.ofNat 64 8) 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, ldT, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.ea, offset_nat, Option.map_some, gpr_setReg, mem_setReg, rd_setReg,
      wr_setReg, hq, BitVec.add_zero, r0, r8]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ => ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, h₁, h₂]
  · simp [gpr_setReg]
  · simp [gpr_setReg]

theorem stT_ok (s : State) {Q : Addr} (hq : s.gpr .r12 = Q)
    (w0 : InRegions s.wr Q 8) (w8 : InRegions s.wr (Q + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa stT s = some s' ∧ (∀ r, s'.gpr r = s.gpr r) ∧
      s'.mem = (s.mem.writeW Q (s.gpr .rax)).writeW (Q + BitVec.ofNat 64 8) (s.gpr .rcx) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [↓reduceIte, stT, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      State.store64, State.ea, offset_nat, hq, BitVec.add_zero, w0, w8]
    rfl, ?_⟩
  exact ⟨fun _ => rfl, rfl, rfl, rfl⟩

theorem xorT_ok (s : State) {P : Addr} (hp : s.gpr .r13 = P)
    (r0 : InRegions (s.rd ++ s.wr) P 8) (r8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr P 8) (w8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa xorT s = some s' ∧ (∀ r, r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = xorRegMem s.mem P (s.gpr .rax) (s.gpr .rcx) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, xorT, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.store64, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, hp, BitVec.add_zero, r0, r8, w0, w8]
    rfl, ?_⟩
  refine ⟨fun r h₁ => ?_, rfl, rfl, rfl⟩
  simp [gpr_setReg, h₁]

theorem mulA_ok (s : State) :
    ∃ s', runBlock isa mulA s = some s' ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.gpr .rax = (s.gpr .rax <<< 1) ^^^ (if (s.gpr .rcx).msb then (0x87 : BitVec 64) else 0) ∧
      s'.gpr .rcx = (s.gpr .rcx <<< 1) ||| (if (s.gpr .rax).msb then (1 : BitVec 64) else 0) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, mulA, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, cf_setReg, cf_arithFlags]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ h₃ => ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, h₁, h₂, h₃]
  · simp only [gpr_setReg, ↓reduceIte, carry_self, add_self, mask_87]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, carry_self, carry_self_c, add_self,
      shl_add_bit]

end VG.Proof.AesXts.X86_64
