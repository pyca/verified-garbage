import VerifiedGarbage.Proof.AesXts.Alpha
import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.AesCbc.Arm.Body
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Impl.AesXts.Arm

/-!
# XTS-AES on ARMv7: multiplication by `α`

`mulA` run once, with its memory as explicit writes (`alphaMem`): the
canonical words of `mulAlpha_words32` (`Proof/AesXts/Alpha.lean`), from
shifted-register operands, `sub`, `and`, `eor` and `orr`.
-/

namespace VG.Proof.AesXts.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesXts.Arm
open VG.Spec.Aes (bytesAt)

/-- The memory after `mulA` on the tweak at `Q`. -/
def alphaMem (m : Mem) (Q : Addr) : Mem :=
  let w (d : Nat) := m.readW (Q + BitVec.ofNat 64 d) 32
  (((m.writeW Q ((w 0 <<< 1) ^^^ (if (w 12).msb then (0x87 : BitVec 32) else 0))).writeW
      (Q + BitVec.ofNat 64 4) ((w 4 <<< 1) ||| (if (w 0).msb then (1 : BitVec 32) else 0))).writeW
      (Q + BitVec.ofNat 64 8) ((w 8 <<< 1) ||| (if (w 4).msb then (1 : BitVec 32) else 0))).writeW
      (Q + BitVec.ofNat 64 12) ((w 12 <<< 1) ||| (if (w 8).msb then (1 : BitVec 32) else 0))

theorem ushr31 (x : BitVec 32) : x >>> 31 = if x.msb then (1 : BitVec 32) else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
  have := x.isLt
  by_cases h : 2 ^ 31 ≤ x.toNat
  · rw [decide_eq_true h]; show _ = 1; omega
  · rw [decide_eq_false h]; show _ = 0; omega

theorem mask_87 (x : BitVec 32) :
    (0 - (if x.msb then (1 : BitVec 32) else 0)) &&& (0x87 : BitVec 32) = if x.msb then (0x87 : BitVec 32) else 0 := by
  cases x.msb <;> decide

theorem mulA_ok (s : State) {Q : Addr} (hq : State.addr (s.gpr .r6) = Q)
    (hfit : (s.gpr .r6).toNat + 16 ≤ 2 ^ 32)
    (hr : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 d) n)
    (hw : ∀ d n, d + n ≤ 16 → InRegions s.wr (Q + BitVec.ofNat 64 d) n) :
    ∃ s', runBlock isa mulA s = some s' ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = alphaMem s.mem Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a (d : Nat) (hd : d < 16) : State.addr (s.gpr .r6 + BitVec.ofNat 32 d) = Q + BitVec.ofNat 64 d := by
    rw [addr_add (by omega), hq]
  have a0 : State.addr (s.gpr .r6 + BitVec.ofNat 32 0) = Q := by rw [a 0 (by decide)]; simp
  have r0 : InRegions (s.rd ++ s.wr) Q 4 := by simpa using hr 0 4 (by decide)
  have w0 : InRegions s.wr Q 4 := by simpa using hw 0 4 (by decide)
  have i0 (t : State) : (Op2.imm 0).eval t = some 0 := Proof.MdStream.Arm.op2_imm (by decide)
  have i87 (t : State) : (Op2.imm 0x87).eval t = some 0x87 := Proof.MdStream.Arm.op2_imm (by decide)
  have l1 (t : State) (r : Reg) : (Op2.shifted r .lsl 1).eval t = some (t.gpr r <<< 1) :=
    Proof.MdStream.Arm.op2_lsl (by decide)
  have r31 (t : State) (r : Reg) : (Op2.shifted r .lsr 31).eval t = some (t.gpr r >>> 31) :=
    Proof.MdStream.Arm.op2_lsr (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, mulA, runBlock_cons, runStep_some, runBlock_nil, exec,
      i0, i87, l1, r31, Proof.MdStream.Arm.op2_reg, State.load32, State.store32, Option.map_some, Nat.reduceLT,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, a0, a 4 (by decide), a 8 (by decide), a 12 (by decide),
      r0, hr 4 4 (by decide), hr 8 4 (by decide), hr 12 4 (by decide), w0, hw 4 4 (by decide),
      hw 8 4 (by decide), hw 12 4 (by decide)]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ h₃ h₄ h₅ h₆ => by simp [gpr_setReg, h₁, h₂, h₃, h₄, h₅, h₆], rfl, ?_, rfl, rfl⟩
  have e0 : Q + BitVec.ofNat 64 0 = Q := by simp
  simp only [alphaMem, e0, ushr31, mask_87]

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

end VG.Proof.AesXts.Arm
