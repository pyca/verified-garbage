module

public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Decrypt
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Decrypt
meta import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # Secret data never controls implicit rejection's byte-loop traces -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def scanTaint : VG.X86.Taint.T := { regs := .ofList [.esi, .ecx, .edi], flags := false }
def alTaint : VG.X86.Taint.T := { regs := .ofList [.esi, .ecx], flags := false }
def selectTaint : VG.X86.Taint.T := { regs := .ofList [.esp, .esi, .edi, .ecx, .ebp], flags := false }
def maskTaint : VG.X86.Taint.T := { regs := .ofList [.eax, .ecx], flags := false }

theorem scan_relCT : RelCT isa (VG.X86.Taint.Agree scanTaint) scanLoop (fun _ _ => True) := by
  apply RelCT.taint (A := taint) scanTaint (fun _ _ h => h)
  taint_decide

theorem al_relCT : RelCT isa (VG.X86.Taint.Agree alTaint) alLoop (fun _ _ => True) := by
  apply RelCT.taint (A := taint) alTaint (fun _ _ h => h)
  taint_decide

theorem select_relCT : RelCT isa (VG.X86.Taint.Agree selectTaint) selLoop (fun _ _ => True) := by
  apply RelCT.taint (A := taint) selectTaint (fun _ _ h => h)
  taint_decide

theorem mask_relCT : RelCT isa (VG.X86.Taint.Agree maskTaint) maskLoop (fun _ _ => True) := by
  apply RelCT.taint (A := taint) maskTaint (fun _ _ h => h)
  taint_decide

theorem privateArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block privArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem validCalc_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .esi])) (.block validCalc)
    (VG.X86.Taint.Agree (τr [.esp, .esi])) := checkedBlockInvariant rfl rfl

end VG.Proof.RsaPkcs1Enc.X86.Dec
