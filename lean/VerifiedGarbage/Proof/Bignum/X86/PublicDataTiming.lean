module

public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Proof.Bignum.X86.ReverseTiming
public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Data conversion, comparison and masking traces depend only on addresses -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86
open VG.Proof.Mont.X86.Dynamic

def loadTaint : VG.X86.Taint.T :=
  { regs := .ofList [.edi, .esp, .esi, .ecx], flags := false }

def storeTaint : VG.X86.Taint.T :=
  { regs := .ofList [.edi, .esp, .ebx, .ecx], flags := false }

theorem loadBE_relCT (n out : Nat) :
    RelCT isa (VG.X86.Taint.Agree loadTaint) (loadBE n out)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply erased_relCT (loadBE n out) (loadBE 1 0)
    (VG.Taint.hintOf taint loadTaint (loadBE 1 0)) rfl rfl rfl
  rfl

theorem storeBE_relCT (src : Nat) :
    RelCT isa (VG.X86.Taint.Agree storeTaint) (storeBE src)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply erased_relCT (storeBE src) (storeBE 0)
    (VG.Taint.hintOf taint storeTaint (storeBE 0)) rfl rfl rfl
  rfl

theorem inputCompare_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (PublicContext.inputCompare n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply erased_relCT (PublicContext.inputCompare n) (PublicContext.inputCompare 1)
    (VG.Taint.hintOf taint (workspaceTaint false) (PublicContext.inputCompare 1)) rfl rfl rfl
  rfl

theorem maskResult_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (PublicFn.maskResult n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply erased_relCT (PublicFn.maskResult n) (PublicFn.maskResult 1)
    (VG.Taint.hintOf taint (workspaceTaint false) (PublicFn.maskResult 1)) rfl rfl rfl
  rfl

end VG.Proof.Bignum.X86
