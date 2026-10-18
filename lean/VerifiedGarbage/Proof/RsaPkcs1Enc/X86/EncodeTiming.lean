module

public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Encrypt
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Encrypt
meta import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # Byte-loop traces disclose only public pointers and lengths -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86
open VG VG.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaPkcs1Enc.X86

def copyTaint : VG.X86.Taint.T := { regs := .ofList [.edi, .esi, .ebp], flags := false }
def maskTaint : VG.X86.Taint.T := { regs := .ofList [.esi, .ecx], flags := false }

theorem head_relCT : RelCT isa (VG.X86.Taint.Agree copyTaint) (.block head)
    (VG.X86.Taint.Agree copyTaint) := checkedBlockInvariant rfl rfl

theorem padding_relCT : RelCT isa (VG.X86.Taint.Agree copyTaint)
    (.seq (.block head) psLoop) (fun _ _ => True) := by
  apply RelCT.seq head_relCT
  apply RelCT.taint (A := taint) copyTaint (fun _ _ h => h)
  taint_decide

theorem message_relCT : RelCT isa (VG.X86.Taint.Agree copyTaint) message (fun _ _ => True) := by
  apply RelCT.taint (A := taint) copyTaint (fun _ _ h => h)
  taint_decide

theorem mask_relCT : RelCT isa (VG.X86.Taint.Agree maskTaint) maskLoop (fun _ _ => True) := by
  apply RelCT.taint (A := taint) maskTaint (fun _ _ h => h)
  taint_decide

theorem messageArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
    (.block Encrypt.messageArgs) (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl

theorem start_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block Encrypt.start)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem callArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block Encrypt.callArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem maskArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block Encrypt.maskArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem wipeArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block Encrypt.wipeArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

end VG.Proof.RsaPkcs1Enc.X86
