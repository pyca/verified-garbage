module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentBranch
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Public exponent branches compose with secret native arithmetic -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Key

theorem key_public_trace {c : Prog isa} (H : KeyPublic c) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint true)) c
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  obtain ⟨hint, out, checked, lower⟩ := H
  exact checkedProgramChange checked lower

end VG.Proof.RsaKeyGen.X86.Key
