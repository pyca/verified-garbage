module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialValue
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairTrialLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairTrialFlag
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialStart
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialOctets
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialFlag
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Simultaneous p and p-1 trial division through the shared RSA reducer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Impl.Ffdh.Arm.ParameterCandidate

private theorem reducedFlag {acc value divisor j : Nat}
    (odd : divisor%2=1) (bound : acc<2*divisor) (db : divisor<8162)
    (congruence : acc*2^(16*j)%divisor=value%divisor) :
    ((BitVec.ofNat 32 acc==0)||(BitVec.ofNat 32 acc==BitVec.ofNat 32 divisor))=decide (value%divisor=0) := by
  rw [ofNat_beq_zero (by omega : acc<2^32),ofNat_beq_eq (by omega : acc<2^32) (by omega : divisor<2^32),
    ←Bool.decide_or]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using (trialDigit_divides odd bound congruence).symm

theorem trialPair_ok (s : State) (dst : BitVec 32) {n prime : Nat}
    (positive : 0<n) (fits : n<2^32) (bufferFits : dst.toNat+n≤2^32)
    (primeBound : prime<1024)
    (divisor : s.gpr .r7=BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime))
    (readOut : InRegions (s.rd++s.wr) (State.addr (s.sp+4)) 4)
    (readWidth : InRegions (s.rd++s.wr) (State.addr (s.sp+12)) 4)
    (out : s.mem.readW (State.addr (s.sp+4)) 32=dst)
    (width : s.mem.readW (State.addr (s.sp+12)) 32=BitVec.ofNat 32 n)
    (read : TrialReadable s (dst+BitVec.ofNat 32 n) n) :
    WP isa trialPair s fun t =>
      t.z=(decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)%VG.Impl.RsaKeyGen.tabEntry prime=0) ||
        decide ((VG.Impl.RsaKeyGen.tabEntry prime-1+Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n))%
          VG.Impl.RsaKeyGen.tabEntry prime=0)) ∧ t.mem=s.mem ∧
      Rest [.r0,.r1,.r2,.r3,.r4,.r5,.r6,.r7,.r8] s t := by
  have facts := VG.Proof.RsaKeyGen.tabEntry_facts primeBound
  unfold trialPair
  refine WP.seq (WP.mono (trialStart_ok s dst n readOut readWidth out width) ?_)
  rintro u ⟨⟨ptr,cnt,zero,div,inverse,mem⟩,rest⟩
  unfold trialPairInit
  refine WP.seq (wp_dp (op2_imm (by decide)) fun w init => WP.block_nil ?_)
  have kept : Rest [.r0,.r1,.r2,.r3,.r4,.r5,.r6,.r7,.r8] s w :=
    (rest.mono (by simp)).trans (init.rest (by simp))
  have ptrW : w.gpr .r0=dst+BitVec.ofNat 32 n := (init.other .r0 (by decide)).trans ptr
  have cntW : w.gpr .r1=BitVec.ofNat 32 n := (init.other .r1 (by decide)).trans cnt
  have accA : w.gpr .r2=BitVec.ofNat 32 0 := (init.other .r2 (by decide)).trans zero
  have accB : w.gpr .r8=BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime-1) := by
    rw [init.gpr,dpVal,div,divisor]
    exact BitVec.ofNat_sub_ofNat_of_le _ 1 (by decide) (by omega)
  have divW : w.gpr .r3=BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime) :=
    (init.other .r3 (by decide)).trans (div.trans divisor)
  have memW : w.mem=s.mem := init.mem.trans mem
  have readable : TrialReadable w (w.gpr .r0) n := by
    rw [ptrW]
    intro i hi
    rw [kept.rd,kept.wr]
    exact read i hi
  have inv : (w.gpr .r4).toNat=(VG.Proof.RsaKeyGen.ninv (BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime))).toNat := by
    rw [init.other .r4 (by decide),inverse,divisor]
  refine WP.seq (WP.mono (trialPairLoop_ok w positive fits cntW readable accA (by omega) accB (by omega)
    divW facts.2 inv (VG.Proof.RsaKeyGen.ninv_tab primeBound)) ?_)
  rintro v ⟨a,b,j,ab,bb,av,bv,congA,congB,_,memory,keep⟩
  have inputValue : trialValue w.mem (w.gpr .r0) n=Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) := by
    rw [memW,ptrW,trialValue_octets,trialBytes_at _ _ fits bufferFits]
  rw [inputValue,Nat.zero_add] at congA
  rw [inputValue] at congB
  have divV : v.gpr .r3=BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime) :=
    (keep.gpr .r3 (by simp)).trans divW
  refine WP.mono (trialPairFlag_ok v) ?_
  rintro t ⟨flag,memT,restT⟩
  refine ⟨?_,memT.trans (memory.trans memW),kept.trans ((keep.mono (by simp)).trans (restT.mono (by simp)))⟩
  rw [flag,av,bv,divV,reducedFlag facts.1 ab facts.2.2 congA,reducedFlag facts.1 bb facts.2.2 congB]


end VG.Proof.Ffdh.Arm.ParameterCandidate
