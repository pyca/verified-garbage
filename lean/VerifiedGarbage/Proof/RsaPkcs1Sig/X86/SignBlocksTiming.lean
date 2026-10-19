module
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Sign

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Cast5.X86.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Weierstrass
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Sign
meta import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
meta import VerifiedGarbage.Proof.Cast5.X86.Run
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Weierstrass

/-! # Taint checks for argument setup, clearing, and register restoration -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Sign VG.Proof.Dsa.X86

theorem encArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block encArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem callArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block callArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem restore_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block restore)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

def clearTaint : VG.X86.Taint.T := { regs := .ofList [.esi, .ecx], flags := false }

theorem clear_relCT : RelCT isa (VG.X86.Taint.Agree clearTaint)
    (.loop (.block VG.Impl.Bignum.X86.PublicFn.clearStep) .ne) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) clearTaint (fun _ _ h => h)
  taint_decide

theorem wipeArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp]))
    (.block [.mov .ebx (.reg .eax), .mov .eax (.imm 0), .mov .esi (.reg .esp),
      .alu .add .esi (.imm (BitVec.ofNat 32 emOffset)), .mov .ecx (.mem (incoming 3))])
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem return_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.mov .eax (.reg .ebx)])
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem zeroArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp]))
    (.block [.mov .esi (.mem (incoming 0)), .mov .ecx (.mem (incoming 1)), .mov .eax (.imm 0)])
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

end VG.Proof.RsaPkcs1Sig.X86.Sgn
