module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P192.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
public import VerifiedGarbage.Spec.EcKey.P192
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.EcdhLit
public import VerifiedGarbage.Proof.P192.RISCV64.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P192.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P192.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P192.Lit

/-! # P-192 public keys (FIPS 186-5 §A.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcP192.RISCV64

open VG.Proof.P192.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact RISCV64.target (RISCV64.Scrub.withScrub {
    code := Impl.EcKey.Compressed.RISCV64.compressP192
    verified := Proof.EcKey.Compressed.RISCV64.P192.compress_verified }
    (Proof.EcKey.RISCV64.Scrub.compressOut _ _ [])),
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact RISCV64.target (RISCV64.Scrub.withScrub {
    code := Impl.EcKey.Compressed.RISCV64.decompressP192
    verified := Proof.EcKey.Compressed.RISCV64.P192.decompress_verified hasLaw.law }
    (Proof.EcKey.RISCV64.Scrub.decompressOut _ _ [])),
  Spec.EcKey.P192.publicKeyApi.artifact RISCV64.target (RISCV64.Scrub.withScrub {
    code := Impl.Ecdh.RISCV64.publicKeyP192
    verified := Proof.Ecdh.RISCV64.P192.pk_verified hasLaw.law }
    (Proof.EcKey.RISCV64.Scrub.publicKeyOut _ _ []))]

end VG.Artifacts.EcP192.RISCV64
