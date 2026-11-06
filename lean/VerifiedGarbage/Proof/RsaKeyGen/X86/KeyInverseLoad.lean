module

public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.DivCopy
public import VerifiedGarbage.Impl.Rsa.X86.Inverse

/-! # Load an independent prime-width or two-word inverse workspace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure InverseLayout (Z n src mo : Nat) : Prop where
  source_bound : src + 4 * n ≤ Z
  modulus_bound : mo + 4 * n ≤ Z
  source_outside : src + 4 * n ≤ hdr ∨ arr n 15 ≤ src
  modulus_outside : mo + 4 * n ≤ hdr ∨ arr n 15 ≤ mo

end VG.Proof.RsaKeyGen.X86.Key
