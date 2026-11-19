module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P256.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
public import VerifiedGarbage.Spec.EcKey.P256
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.EcdhLit
public import VerifiedGarbage.Proof.P256.RISCV64.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P256.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P256.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P256.Lit
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved

/-! # P-256 public keys (FIPS 186-5 §A.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcP256.RISCV64

open VG.Proof.P256.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.EcKey.Compressed.RISCV64.compressP256
    verified := Proof.EcKey.Compressed.RISCV64.P256.compress_verified }
    (Proof.EcKey.RISCV64.Scrub.compressOut _ _ [])),
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.EcKey.Compressed.RISCV64.decompressP256
    verified := Proof.EcKey.Compressed.RISCV64.P256.decompress_verified hasLaw.law }
    (Proof.EcKey.RISCV64.Scrub.decompressOut _ _ [])),
  Spec.EcKey.P256.publicKeyApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Ecdh.RISCV64.publicKeyP256
    verified := Proof.Ecdh.RISCV64.P256.pk_verified hasLaw.law }
    (Proof.EcKey.RISCV64.Scrub.publicKeyOut _ _ Impl.Ecdsa.RISCV64.Comb.p256CombConsts))]

end VG.Artifacts.EcP256.RISCV64
