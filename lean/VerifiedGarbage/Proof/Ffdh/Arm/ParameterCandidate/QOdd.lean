module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ReadContext
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.QOddLow
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResidueBytes
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

theorem qOdd_ok {s : State} {dst : BitVec 32} {n : Nat} (h : ReadContext dst n s)
    (odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)%2=1) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.qOdd) s fun t =>
      t.z=decide (((Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)-1)/2)%2=1) ∧
      t.mem=s.mem ∧ Rest [.r2,.r4,.r5] s t := by
  refine WP.mono (qOddLow_ok s dst n (h.frame.read (by decide)) (h.frame.read (by decide))
    h.out h.width (h.readable.low h.positive)) ?_
  rintro t ⟨⟨flag,memory⟩,rest⟩
  have last := candidate_mod8_last s.mem (State.addr dst) h.positive
  rw [←h.lastAddress] at last
  have low : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)%4 =
      (s.mem (State.addr (dst+BitVec.ofNat 32 n-1))).toNat%4 := by omega
  refine ⟨flag.trans (decide_eq_decide.mpr ?_),memory,rest⟩
  rw [←low]
  omega

end VG.Proof.Ffdh.Arm.ParameterCandidate
