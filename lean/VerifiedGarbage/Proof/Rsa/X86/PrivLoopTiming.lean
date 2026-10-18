module

public import VerifiedGarbage.Impl.Rsa.X86.PrivChecked
public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Comparison and candidate erasure disclose only public addresses and length -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Dsa.X86

def loopTaint : VG.X86.Taint.T := τr [.esp, .esi, .edi, .ecx]

theorem compareBytes_relCT : RelCT isa (VG.X86.Taint.Agree loopTaint) compareBytes
    (VG.X86.Taint.Agree loopTaint) := by
  apply checkedProgramChange (hint := VG.Taint.hintOf taint loopTaint compareBytes) rfl
  rfl

theorem releaseLoop_relCT : RelCT isa (VG.X86.Taint.Agree loopTaint) releaseLoop
    (VG.X86.Taint.Agree loopTaint) := by
  apply checkedProgramChange (hint := VG.Taint.hintOf taint loopTaint releaseLoop) rfl
  rfl

end VG.Proof.Rsa.X86.PrivChecked
