module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT

/-! Fixed stack loads in the candidate's public policy and reducer setup. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm

theorem trialStart_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialStart) (fun s t => s.sp = t.sp) :=
  stackOnly_ct _ (by decide)

theorem initialRoom_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom) (fun s t => s.sp = t.sp) :=
  stackOnly_ct _ (by decide)

theorem witnessRoom_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessRoom) (fun s t => s.sp = t.sp) :=
  stackOnly_ct _ (by decide)

theorem drawArgs_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.drawArgs) (fun s t => s.sp = t.sp) :=
  stackOnly_ct _ (by decide)

theorem halveHead_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block [.ldrSp .r0 4, .ldrSp .lr 12, .mov .r2 (.imm 0)]) (fun s t => s.sp = t.sp) :=
  stackOnly_ct _ (by decide)

end VG.Proof.Ffdh.Arm.ParameterCandidate
