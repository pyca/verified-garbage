module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.FinishHead
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Return the candidate status and write a complete u64 entropy count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm

theorem finish_ok (s : State) (usedPtr : BitVec 32) (status count : Nat)
    (statusBound : status ≤ 2) (countBound : count < 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 32#32)) 4)
    (pointer : s.mem.readW (State.addr (s.sp + 32#32)) 32 = usedPtr)
    (output : OutputBuffer usedPtr 8 s) (value : s.gpr .r3 = BitVec.ofNat 32 count) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.finish status)) s fun t =>
      t.gpr .r0 = BitVec.ofNat 32 status ∧
      Spec.Rsa.wordsAt t.mem (State.addr usedPtr) 1 = [BitVec.ofNat 64 count] ∧
      Frame [⟨State.addr usedPtr, 8⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2] s t := by
  have write0 : InRegions s.wr (State.addr usedPtr) 4 := by
    simpa only [BitVec.add_zero] using
      CallLay.inRegions_sub output.writable (off := 0) (by decide : 0 + 4 ≤ 8) (by decide)
  have write4 : InRegions s.wr (off (State.addr usedPtr) 4) 4 :=
    CallLay.inRegions_sub output.writable (by decide : 4 + 4 ≤ 8) (by decide)
  have addr4 : State.addr (usedPtr + 4#32) = off (State.addr usedPtr) 4 :=
    VG.Arm.addr_add (by have := output.fits; omega)
  have enc : encodable (BitVec.ofNat 32 status) = true := encodable_byte (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : status < 2 ^ 32)]
    omega)
  have run : WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.finish status)) s fun t =>
      (t.gpr .r0 = BitVec.ofNat 32 status ∧
        t.mem = (s.mem.writeW (State.addr usedPtr) (BitVec.ofNat 32 count)).writeW
          (off (State.addr usedPtr) 4) (0 : BitVec 32)) ∧ Rest [.r0, .r1, .r2] s t := by
    refine withRest_all [.r0, .r1, .r2] ?_ (by rfl) (by rfl)
    unfold VG.Impl.Ffdh.Arm.ParameterCandidate.finish
    ffrun [BitVec.add_zero, read, pointer, write0, write4, addr4, value, enc]
  refine WP.mono run ?_
  rintro t ⟨⟨result, memory⟩, rest⟩
  refine ⟨result, ?_, ?_, rest⟩
  · rw [memory]
    exact VG.Proof.Ffdh.Arm.KeySearch.usedMem_words s.mem usedPtr count countBound
  · rw [memory]
    exact VG.Proof.Ffdh.Arm.KeySearch.usedMem_frame s.mem usedPtr (BitVec.ofNat 32 count)

end VG.Proof.Ffdh.Arm.ParameterCandidate
