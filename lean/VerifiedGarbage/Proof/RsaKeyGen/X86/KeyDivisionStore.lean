module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionGeometry
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.DivCopy
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32

/-! # Export native division results to persistent workspace arrays -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure DivisionOutputs (Z n quotient remainder : Nat) : Prop where
  quotient_bound : quotient + 4 * n ≤ Z
  remainder_bound : remainder + 4 * n ≤ Z
  quotient_outside : quotient + 4 * n ≤ hdr ∨ arr n 4 ≤ quotient
  remainder_outside : remainder + 4 * n ≤ hdr ∨ arr n 4 ≤ remainder
  separate : quotient + 4 * n ≤ remainder ∨ remainder + 4 * n ≤ quotient

end VG.Proof.RsaKeyGen.X86.Key
