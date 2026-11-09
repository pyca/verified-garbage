module

public import VerifiedGarbage.Proof.Rsa.X86.InvTimeBase
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Rsa.X86.InvDispatch
import VerifiedGarbage.Proof.Rsa.X86.InvChoice
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base

/-! # Relating public length comparisons in the inverse dispatcher -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvTiming
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.CrtValuesRt VG.Proof.Rsa.X86.KeyRt

 def Pair (args : Nat → BitVec 32) (base : Addr) (size len P Q P' Q' : Nat) (sp : BitVec 32) (s t : State) : Prop :=
  (InvInput args base size len P Q s ∧ Public args base size sp s) ∧
  (InvInput args base size len P' Q' t ∧ Public args base size sp t)
end VG.Proof.Rsa.X86.InvTiming
