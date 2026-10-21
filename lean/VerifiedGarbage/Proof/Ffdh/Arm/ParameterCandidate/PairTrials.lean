module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveContext
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairEntry
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialSmall
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialOffset
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
    (cursor : s.gpr .r10=base+BitVec.ofNat 32 (Spec.Rsa.Mont.arrAt ((n+7)/8) 34+4*i))
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)=value) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.pairTrials s fun t =>
      t.z=(value%VG.Impl.RsaKeyGen.tabEntry i==0 ||
        (VG.Impl.RsaKeyGen.tabEntry i-1+value)%VG.Impl.RsaKeyGen.tabEntry i==0) ∧
      t.mem=s.mem ∧ Rest [.r0,.r1,.r2,.r3,.r4,.r5,.r6,.r7] s t := by
  have bound := trialCount_bound n
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.pairTrials VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (pairEntry_ok ctx more cursor) ?_)
  rintro u ⟨⟨prime,memU⟩,restU⟩
  have ctxU := ctx.after_memory memU restU
  refine WP.seq (WP.mono (trialSmall_ok u dst ctxU.read.positive ctxU.read.countFits ctxU.read.bufferFits
    (by omega : i<1024) prime (ctxU.read.frame.read (by decide)) (ctxU.read.frame.read (by decide))
    ctxU.read.out ctxU.read.width ctxU.read.readable) ?_)
  rintro v ⟨flag,memV,restV⟩
  have ctxV := ctxU.after_memory memV restV
  rw [memU,number,←Bool.beq_eq_decide_eq] at flag
  have through : Rest [.r0,.r1,.r2,.r3,.r4,.r5,.r6,.r7] s v :=
    (restU.mono (by simp)).trans restV
  cases hit : (value%VG.Impl.RsaKeyGen.tabEntry i==0) with
  | true =>
    refine WP.seq (WP.ite true (by change some v.z=some true; rw [flag,hit]) ?_ (by intro h; cases h))
    intro _
    refine WP.block_nil (WP.block_nil ⟨?_,memV.trans memU,through⟩)
    rw [flag,hit]
    rfl
  | false =>
    refine WP.seq (WP.ite false (by change some v.z=some false; rw [flag,hit]) (by intro h; cases h) ?_)
    intro _
    rw [WP.seq_iff]
    have cursorV : v.gpr .r10=base+BitVec.ofNat 32 (Spec.Rsa.Mont.arrAt ((n+7)/8) 34+4*i) :=
      (through.gpr .r10 (by simp)).trans cursor
    refine WP.mono (pairEntry_ok ctxV more cursorV) ?_
    rintro a ⟨⟨primeA,memA⟩,restA⟩
    have ctxA := ctxV.after_memory memA restA
    refine WP.mono (trialOffset_value_ok a dst ctxA.read.positive ctxA.read.countFits ctxA.read.bufferFits
      (by omega : i<1024) primeA (ctxA.read.frame.read (by decide)) (ctxA.read.frame.read (by decide))
      ctxA.read.out ctxA.read.width ctxA.read.readable) ?_
    rintro t ⟨_,_,_,_,_,flagT,memT,restT⟩
    rw [memA,memV,memU,number,←Bool.beq_eq_decide_eq] at flagT
    refine WP.block_nil ⟨?_,memT.trans (memA.trans (memV.trans memU)),
      (through.trans (restA.mono (by simp))).trans restT⟩
    simpa only [hit,Bool.false_or] using flagT

end VG.Proof.Ffdh.Arm.ParameterCandidate
