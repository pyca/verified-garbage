module

public import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.X86.Ecb
public import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
meta import VerifiedGarbage.Impl.TripleDes.X86.Ecb
meta import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.Impl.TripleDes.X86

def keyTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [384, 512],
    argLen := 20, argBases := [(12, 0), (16, 1)] }
def ecbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 1024],
    argLen := 20, argBases := [(8, 0), (16, 1)], room := 16 }

/-! ECB calls the bitsliced functions (`Impl/TripleDes/X86/Bitsliced.lean`),
once each, whose code the analysis runs as it is. -/

theorem expandKey_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree keyTaint s₁ s₂) :
    ConstantTime isa pre pub Key.expandKey :=
  VG.Taint.constantTime (A := taint) keyTaint h (by taint_decide)

theorem ecbEncrypt_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree ecbTaint s₁ s₂) :
    ConstantTime isa pre pub Ecb.encrypt :=
  VG.Taint.constantTime (A := taint) ecbTaint h (by taint_decide)

theorem ecbDecrypt_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree ecbTaint s₁ s₂) :
    ConstantTime isa pre pub Ecb.decrypt :=
  VG.Taint.constantTime (A := taint) ecbTaint h (by taint_decide)

end VG.Proof.TripleDes.X86
