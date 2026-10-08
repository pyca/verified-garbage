import VerifiedGarbage.Proof.AesXts.Alpha
import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Impl.AesXts.X86_64

/-!
# XTS-AES on x86-64: multiplication by `α`

`mulA` run once, with its memory as explicit writes (`alphaMem`): the
canonical words of `mulAlpha_words64` (`Proof/AesXts/Alpha.lean`), from
`add`, `adc`, `sbb`, `and` and `xor`.
-/

namespace VG.Proof.AesXts.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesXts.X86_64
open VG.Impl.AesCbc.X86_64 (at_)
open VG.Proof.AesCbc.X86_64 (offset_nat)
open VG.Spec.Aes (bytesAt)

/-- The memory after `mulA` on the tweak at `Q`. -/
def alphaMem (m : Mem) (Q : Addr) : Mem :=
  (m.writeW Q ((m.readW Q 64 <<< 1) ^^^
      (if (m.readW (Q + BitVec.ofNat 64 8) 64).msb then (0x87 : BitVec 64) else 0))).writeW
    (Q + BitVec.ofNat 64 8) ((m.readW (Q + BitVec.ofNat 64 8) 64 <<< 1) |||
      (if (m.readW Q 64).msb then (1 : BitVec 64) else 0))

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

theorem mulA_ok (s : State) {Q : Addr} (hq : s.gpr .r12 = Q)
    (r0 : InRegions (s.rd ++ s.wr) Q 8) (r8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Q 8) (w8 : InRegions s.wr (Q + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa mulA s = some s' ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = alphaMem s.mem Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, mulA, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.store64, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, cf_setReg, cf_arithFlags, hq, BitVec.add_zero, r0, r8, w0, w8]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ h₃ => ?_, ?_, rfl, rfl⟩
  · simp [gpr_setReg, h₁, h₂, h₃]
  · simp only [alphaMem, carry_self, carry_self_c, add_self, shl_add_bit, mask_87]

theorem alphaMem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 16⟩] m (alphaMem m Q) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains_base Q (d := 0) (n := 8) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 8) (n := 8) (k := 16) (by decide) (by decide))

theorem alphaMem_bytes (m : Mem) (Q : Addr) : bytesAt (alphaMem m Q) Q 16 = Spec.Xts.mulAlpha (bytesAt m Q 16) :=
  AesXts.mulAlpha_words64 m Q

end VG.Proof.AesXts.X86_64
