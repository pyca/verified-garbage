module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionGeometry
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Rsa.X86.DivCopy
import VerifiedGarbage.Impl.Mont.X86
import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Mont.X86.Instr
/-! # Load the native division bank without clearing its temporary arrays -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure DivisionInputs (Z n src divisor : Nat) : Prop where
  source_bound : src + 4 * n ≤ Z
  divisor_bound : divisor + 4 * n ≤ Z
  source_outside : src + 4 * n ≤ hdr ∨ arr n 4 ≤ src
  divisor_outside : divisor + 4 * n ≤ hdr ∨ arr n 4 ≤ divisor

end VG.Proof.RsaKeyGen.X86.Key
