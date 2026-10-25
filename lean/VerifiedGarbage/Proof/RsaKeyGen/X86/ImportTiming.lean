module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Import
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # The import's address trace depends only on pointers and the public word count -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Import
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Import

def publicState : VG.X86.Taint.T := τr [.esp, .edi, .esi, .ebx, .ecx]

theorem code_trace : RelCT isa (VG.X86.Taint.Agree publicState) code (VG.X86.Taint.Agree publicState) :=
  checkedProgramChange (τ' := { publicState with flags := true })
    (hint := VG.Taint.hintOf taint publicState code) (by kernel_rfl) (by kernel_rfl)

end VG.Proof.RsaKeyGen.X86.Import
