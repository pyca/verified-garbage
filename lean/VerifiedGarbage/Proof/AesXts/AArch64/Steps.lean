import VerifiedGarbage.Proof.AesXts.Alpha
import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.AesCbc.AArch64.Body
import VerifiedGarbage.Impl.AesXts.AArch64

/-!
# XTS-AES on AArch64: multiplication by `α`

`mulA` run once, with its memory as explicit writes (`alphaMem`): the
canonical words of `mulAlpha_words64` (`Proof/AesXts/Alpha.lean`), from
`adds`, `adcs`, `csel` and `eor`.
-/

namespace VG.Proof.AesXts.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesXts.AArch64
open VG.Spec.Aes (bytesAt)

/-- The memory after `mulA` on the tweak at `Q`. -/
def alphaMem (m : Mem) (Q : Addr) : Mem :=
  (m.writeW Q ((m.readW Q 64 <<< 1) ^^^
      (if (m.readW (Q + BitVec.ofNat 64 8) 64).msb then (0x87 : BitVec 64) else 0))).writeW
    (Q + BitVec.ofNat 64 8) ((m.readW (Q + BitVec.ofNat 64 8) 64 <<< 1) |||
      (if (m.readW Q 64).msb then (1 : BitVec 64) else 0))

theorem carry_c (x : BitVec 64) (c : Bool) : decide (2 ^ 64 ≤ x.toNat + x.toNat + c.toNat) = x.msb := by
  rw [BitVec.msb_eq_decide]
  have := x.isLt
  have := c.toNat_le
  simp only [decide_eq_decide]
  omega

theorem add_bit (x : BitVec 64) (c : Bool) :
    x + x + BitVec.ofNat 64 c.toNat = (x <<< 1) ||| (if c then (1 : BitVec 64) else 0) := by
  have e : x + x = x <<< 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega
  rw [e]
  cases c
  · simp
  · apply BitVec.add_eq_or_of_and_eq_zero
    ext i hi
    simp
    omega

theorem or_zero' (x : BitVec 64) : x ||| (0 : BitVec 64) = x := BitVec.or_zero

theorem sel_87 (c : Bool) :
    (if c = true then BitVec.setWidth 64 (135 : BitVec 16) <<< 0 else BitVec.setWidth 64 (0 : BitVec 16) <<< 0) =
      if c then (0x87 : BitVec 64) else 0 := by
  cases c <;> rfl

theorem mulA_ok (s : State) {Q : Addr} (hq : s.gpr .x21 = Q)
    (r0 : InRegions (s.rd ++ s.wr) Q 8) (r8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Q 8) (w8 : InRegions s.wr (Q + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa mulA s = some s' ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = alphaMem s.mem Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [mulA, gpr_addWithCarry, c_addWithCarry, c_write, mem_addWithCarry, rd_addWithCarry,
    wr_addWithCarry, sp_addWithCarry, hq, r0, r8, w0, w8], ?_⟩
  refine ⟨fun r h₁ h₂ h₃ h₄ => by simp [gpr_write, gpr_addWithCarry, h₁, h₂, h₃, h₄], rfl, ?_, rfl, rfl⟩
  simp only [alphaMem, Mem.writeW, Mem.readW, BitVec.setWidth_eq, carry_c, add_bit, sel_87, Bool.false_eq_true,
    ↓reduceIte, or_zero']

theorem alphaMem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 16⟩] m (alphaMem m Q) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains_base Q (d := 0) (n := 8) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 8) (n := 8) (k := 16) (by decide) (by decide))

theorem alphaMem_bytes (m : Mem) (Q : Addr) : bytesAt (alphaMem m Q) Q 16 = Spec.Xts.mulAlpha (bytesAt m Q 16) :=
  AesXts.mulAlpha_words64 m Q

end VG.Proof.AesXts.AArch64
