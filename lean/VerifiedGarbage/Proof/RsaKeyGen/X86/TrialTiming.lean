module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Trial
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # A trial-reduction step does not leak its candidate or remainder -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Trial
open VG VG.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Trial

def publicRegs : VG.X86.Taint.T := { regs := .ofList [.ebx, .esi, .edi], flags := false }

theorem redc32_relCT : RelCT isa (VG.X86.Taint.Agree publicRegs) (.block redc32)
    (VG.X86.Taint.Agree publicRegs) := checkedBlockInvariant rfl rfl

theorem finish_relCT : RelCT isa (VG.X86.Taint.Agree publicRegs) (.block finish)
    (VG.X86.Taint.Agree publicRegs) := checkedBlockInvariant rfl rfl

end VG.Proof.RsaKeyGen.X86.Trial
