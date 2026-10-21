module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TablePointer
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveControl
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Bind the compact table cursor and initialize the sieve's public flag. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

theorem sieveInit_ok {s : State} {dst base : BitVec 32} {n : Nat} (h : SieveContext dst base n s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInit s
      (SieveInv s dst base n (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)) 0) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInit
  refine WP.seq (WP.mono (tablePointer_ok s base n h.widthBound
    (by simpa only [BitVec.add_zero] using h.read.frame.read (d := 0) (by decide))
    (h.read.frame.read (by decide)) h.savedBase h.read.width) ?_)
  rintro u ⟨⟨ptr, memory⟩, rest⟩
  have ctx := h.after_memory memory rest
  refine WP.mono (sieveInitTail_ok u ctx.read.frame.space) ?_
  rintro t ⟨⟨cursor, count, memT⟩, restT⟩
  have changed : Frame [sieveLocal u.sp] u.mem t.mem := by
    rw [memT]
    exact sieveLocal_frame u 0#32
  have finalCtx := ctx.after_frame changed restT
  have bytes := ctx.bytes_after changed
  rw [memory] at bytes
  have total : Rest sieveRegs s t := (rest.mono (by simp [sieveRegs])).trans (restT.mono (by simp [sieveRegs]))
  refine ⟨finalCtx, by decide, ?_, count, ?_, ?_, ?_, total⟩
  · simpa only [Nat.mul_zero, Nat.add_zero] using cursor.trans ptr
  · rw [restT.sp, memT, Mem.readW_writeW_self32]
    rfl
  · rw [bytes]
  · rwa [memory, rest.sp] at changed

end VG.Proof.Ffdh.Arm.ParameterCandidate
