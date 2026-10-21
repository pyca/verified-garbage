module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhasePieces
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Compose the native policy setup for q and p. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Proof.Bignum.Arm (Workspace)

theorem phaseHead_ok (q : Bool) (s : State) {bits : Nat} (lower : 512 ≤ bits) (upper : bits ≤ 8192)
    (space : Workspace s s.sp 72)
    (value : s.mem.readW (State.addr (s.sp + 24#32)) 32 = BitVec.ofNat 32 bits) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseHead q)) s fun t =>
      (t.mem = phaseMemory s q bits) ∧ Rest [.r1, .r3, .r4, .r5, .r12] s t := by
  have read24 : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 24#32)) 4 := by
    rw [VG.Arm.addr_add (by have := space.nowrap; omega)]
    exact space.read (by decide)
  have writes (d : Nat) (bound : d + 4 ≤ 72) : InRegions s.wr (State.addr (s.sp + BitVec.ofNat 32 d)) 4 := by
    rw [VG.Arm.addr_add (by have := space.nowrap; omega)]
    exact space.write bound
  have phasePositive : 0 < phaseBits q bits := by cases q <;> simp [phaseBits] <;> omega
  have phaseBound : phaseBits q bits ≤ 8192 := by cases q <;> simp [phaseBits] <;> omega
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.phaseHead
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (phaseBitHead_ok q s (by omega) read24 (writes 44 (by decide)) value) ?_
  rintro u ⟨⟨bitValue, memU⟩, restU⟩
  rw [WP.block_append_iff]
  refine WP.mono (phaseWidth_ok u phaseBound bitValue (by rw [restU.wr, restU.sp]; exact writes 48 (by decide))) ?_
  rintro v ⟨memV, restV⟩
  rw [WP.block_append_iff]
  have stable : v.gpr .r3 = BitVec.ofNat 32 (phaseBits q bits) := (restV.gpr .r3 (by simp)).trans bitValue
  refine WP.mono (phaseChecks_ok v phasePositive phaseBound stable (by
    rw [restV.wr, restU.wr, restV.sp, restU.sp]; exact writes 52 (by decide))) ?_
  rintro w ⟨memW, restW⟩
  refine WP.mono (phasePassed_ok w (by
    rw [restW.wr, restV.wr, restU.wr, restW.sp, restV.sp, restU.sp]; exact writes 56 (by decide))) ?_
  rintro t ⟨memT, restT⟩
  refine ⟨?_, (restU.mono (by simp)).trans ((restV.mono (by simp)).trans
    ((restW.mono (by simp)).trans (restT.mono (by simp))))⟩
  rw [memT, memW, memV, memU, restW.sp, restV.sp, restU.sp]
  rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
