module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Secp256k1
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Secp256k1Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Secp256k1.X86.Law

/-! # SEC 1 point conversion with Secp256k1's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedSecp256k1.X86

open VG.Proof.Secp256k1.X86 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.Secp256k1.code
    verified := Proof.EcKey.Compressed.X86.Secp256k1.verified hasLaw.inv },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.Secp256k1Decompress.code
    verified := Proof.EcKey.Compressed.X86.Secp256k1Decompress.verified hasLaw.law hasLaw.inv }]

end VG.Artifacts.EcCompressedSecp256k1.X86
