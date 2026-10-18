module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStages
public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeTiming

/-! # Public stack addresses suffice for every verifier straight-line fragment -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Recover VG.Proof.Dsa.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (test0 stackAt statusOffset)

theorem encArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block encArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem pubArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block pubArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem cmpArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block cmpArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem restore_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block VG.Impl.RsaPkcs1Sig.X86.Sign.restore)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem save_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.store (stackAt statusOffset) .eax])
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem releaseArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block releaseArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem return_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.mov .eax (.reg .ebx)])
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem length_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block lenCheck)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem zeroArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp]))
    (.block [.mov .esi (.mem (VG.Impl.RsaPkcs1Sig.X86.Verify.incoming 0)),
      .mov .ecx (.mem (VG.Impl.RsaPkcs1Sig.X86.Verify.incoming 1)), .mov .eax (.imm 0)])
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem cmp_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .eax])) (.block test0)
    (VG.X86.Taint.Agree (τr [.esp, .eax])) := checkedBlockInvariant rfl rfl

end VG.Proof.RsaPkcs1Sig.X86.Rcv
