module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.HeaderCT
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.HeaderCT
meta import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter generation on x86-64: timing of the outer-frame link -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Impl.Rsa.X86_64.Crt (sLink)

structure LinkPublic where
  B : Addr
  wr : List Region

def LinkHeader (p : LinkPublic) (s : State) : Prop :=
  InnerKW p.B p.wr ∧ HP (off p.B 256) p.wr [(sLink, p.B)] s

private theorem link_ct {c : Prog isa} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (innerT [] [sLink]) c hc).isSome = true) :
    RelCT isa (Two LinkHeader) c fun _ _ => True :=
  inner_ct LinkPublic.B LinkPublic.wr [sLink] (fun p => [(sLink, p.B)]) [] (by decide)
    (fun _ => rfl) (fun _ _ h => h) (pins_nil _) h

theorem drawHead_ct : RelCT isa (Two LinkHeader) (.block drawHead) fun _ _ => True := link_ct (by taint_decide)
theorem drawShort_ct : RelCT isa (Two LinkHeader) (.block drawShort) fun _ _ => True := link_ct (by taint_decide)
theorem drawSetup_ct : RelCT isa (Two LinkHeader) (.block drawSetup) fun _ _ => True := link_ct (by taint_decide)
theorem drawFinish_ct : RelCT isa (Two LinkHeader) (.block drawFinish) fun _ _ => True := link_ct (by taint_decide)
theorem roundPass_ct : RelCT isa (Two LinkHeader) (.block roundPass) fun _ _ => True := link_ct (by taint_decide)
theorem roundFail_ct : RelCT isa (Two LinkHeader) (.block roundFail) fun _ _ => True := link_ct (by taint_decide)
theorem roundInit_ct : RelCT isa (Two LinkHeader) (.block roundInit) fun _ _ => True := link_ct (by taint_decide)
theorem statusTest_ct : RelCT isa (Two LinkHeader) (.block statusTest) fun _ _ => True := link_ct (by taint_decide)
theorem statusMore_ct : RelCT isa (Two LinkHeader) (.block statusMore) fun _ _ => True := link_ct (by taint_decide)
theorem leaveStatus_ct : RelCT isa (Two LinkHeader) leaveStatus fun _ _ => True := link_ct (by taint_decide)
theorem innerReject_ct : RelCT isa (Two LinkHeader) (innerStatus 2) fun _ _ => True := link_ct (by taint_decide)

theorem drawLoadTail_ct : RelCT isa (Two LinkHeader)
    (.block [.mov .rax (.mem (VG.Impl.Bignum.X86_64.hdr sLink)),
      .mov .rsi (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax oOut)),
      .mov .rcx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax oWitnessLen))]) fun _ _ => True := link_ct (by taint_decide)

theorem loadOutputHead_ct : RelCT isa (Two LinkHeader)
    (.block [.mov .rax (.mem (VG.Impl.Bignum.X86_64.hdr sLink)),
      .mov .rsi (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax oOut)),
      .mov .rcx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax oLen))]) fun _ _ => True := link_ct (by taint_decide)

theorem generatorHead_ct : RelCT isa (Two LinkHeader)
    (.block [.mov .rax (.mem (VG.Impl.Bignum.X86_64.hdr sLink)),
      .mov .rdx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax oGen))]) fun _ _ => True := link_ct (by taint_decide)

theorem leave_ct : RelCT isa (Two LinkHeader) (.block [VG.Impl.Rsa.X86_64.Crt.leave]) fun _ _ => True :=
  link_ct (by taint_decide)

end VG.Proof.Ffdh.X86_64.ParameterCandidate
