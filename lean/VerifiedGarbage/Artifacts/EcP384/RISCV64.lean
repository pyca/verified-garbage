module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P384.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
public import VerifiedGarbage.Spec.EcKey.P384
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.EcdhLit
public import VerifiedGarbage.Proof.P384.RISCV64.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P384.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P384.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P384.Lit
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved

/-! # P-384 public keys (FIPS 186-5 §A.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcP384.RISCV64

open VG.Proof.P384.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.EcKey.Compressed.RISCV64.compressP384
    verified := Proof.EcKey.Compressed.RISCV64.P384.compress_verified }
    (Proof.EcKey.RISCV64.Scrub.compressOut _ _ [])),
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.EcKey.Compressed.RISCV64.decompressP384
    verified := Proof.EcKey.Compressed.RISCV64.P384.decompress_verified hasLaw.law }
    (Proof.EcKey.RISCV64.Scrub.decompressOut _ _ [])),
  Spec.EcKey.P384.publicKeyApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Ecdh.RISCV64.publicKeyP384
    verified := Proof.Ecdh.RISCV64.P384.pk_verified hasLaw.law }
    (Proof.EcKey.RISCV64.Scrub.publicKeyOut _ _ Impl.Ecdsa.RISCV64.Comb.p384CombConsts))]

end VG.Artifacts.EcP384.RISCV64
