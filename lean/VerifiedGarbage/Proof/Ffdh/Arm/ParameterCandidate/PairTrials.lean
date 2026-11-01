module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveContext
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairEntry
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairTrialSmall
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SievePolicy
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Each prime rejects p or p-1 before the sieve advances to its next entry. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)

theorem pairTrials_ok {s : State} {dst base : BitVec 32} {n value i : Nat}
    (ctx : SieveContext dst base n s) (more : i<trialCount n)
    (cursor : s.gpr .r10=base+BitVec.ofNat 32 (Proof.Rsa.Mont.arrAt ((n+7)/8) 34+4*i))
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)=value) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.pairTrials s fun t =>
      t.z=(value%VG.Impl.RsaKeyGen.tabEntry i==0 ||
        (VG.Impl.RsaKeyGen.tabEntry i-1+value)%VG.Impl.RsaKeyGen.tabEntry i==0) ∧
      t.mem=s.mem ∧ Rest [.r0,.r1,.r2,.r3,.r4,.r5,.r6,.r7,.r8] s t := by
  have bound := trialCount_bound n
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.pairTrials
  rw [WP.seq_iff]
  refine WP.mono (pairEntry_ok ctx more cursor) ?_
  rintro u ⟨⟨prime,memU⟩,restU⟩
  have ctxU := ctx.after_memory memU restU
  refine WP.mono (trialPair_ok u dst ctxU.read.positive ctxU.read.countFits ctxU.read.bufferFits
    (by omega : i<1024) prime (ctxU.read.frame.read (by decide)) (ctxU.read.frame.read (by decide))
    ctxU.read.out ctxU.read.width ctxU.read.readable) ?_
  rintro t ⟨flag,memory,rest⟩
  refine ⟨?_,memory.trans memU,(restU.mono (by simp)).trans rest⟩
  rwa [memU,number,←Bool.beq_eq_decide_eq,←Bool.beq_eq_decide_eq] at flag

end VG.Proof.Ffdh.Arm.ParameterCandidate
