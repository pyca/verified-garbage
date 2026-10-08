import VerifiedGarbage.Proof.AesXts.Alpha
import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.AesCbc.X86.Body
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Impl.AesXts.X86

/-!
# XTS-AES on x86: multiplication by `α`

`mulA` run once, with its memory as explicit writes (`alphaMem`): the
canonical words of `mulAlpha_words32` (`Proof/AesXts/Alpha.lean`), from
`add`, `adc`, `sbb`, `and` and `xor`.
-/

namespace VG.Proof.AesXts.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesXts.X86
open VG.Impl.CmacAes.X86 (at_)
open VG.Proof.CmacAes.X86 (ea_at')
open VG.Spec.Aes (bytesAt)

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
  omega

theorem carry_self (x : BitVec 32) : decide (2 ^ 32 ≤ x.toNat + x.toNat) = x.msb := by
  rw [BitVec.msb_eq_decide]
  have := x.isLt
  simp only [decide_eq_decide]
  omega

theorem carry_self_c (x : BitVec 32) (c : Bool) :
    decide (2 ^ 32 ≤ x.toNat + x.toNat + c.toNat) = x.msb := by
  rw [BitVec.msb_eq_decide]
  have := x.isLt
  have := c.toNat_le
  simp only [decide_eq_decide]
  omega

theorem shl_add_bit (x : BitVec 32) (c : Bool) :
    (x <<< 1) + (BitVec.ofBool c).setWidth 32 = (x <<< 1) ||| (if c then (1 : BitVec 32) else 0) := by
  cases c
  · simp
  · apply BitVec.add_eq_or_of_and_eq_zero
    ext i hi
    simp
    omega

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
    rw [addr_eq (by omega), hq]
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

end VG.Proof.AesXts.X86
