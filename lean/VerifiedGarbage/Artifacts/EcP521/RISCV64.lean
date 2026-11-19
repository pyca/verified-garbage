module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P521.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
public import VerifiedGarbage.Spec.EcKey.P521
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.EcdhLit
public import VerifiedGarbage.Proof.P521.RISCV64.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P521.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P521.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P521.Lit
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved

/-! # P-521 public keys (FIPS 186-5 §A.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcP521.RISCV64

open VG.Proof.P521.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.EcKey.Compressed.RISCV64.compressP521
    verified := Proof.EcKey.Compressed.RISCV64.P521.compress_verified }
    (Proof.EcKey.RISCV64.Scrub.compressOut _ _ [])),
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.EcKey.Compressed.RISCV64.decompressP521
    verified := Proof.EcKey.Compressed.RISCV64.P521.decompress_verified hasLaw.law }
    (Proof.EcKey.RISCV64.Scrub.decompressOut _ _ [])),
  Spec.EcKey.P521.publicKeyApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Ecdh.RISCV64.publicKeyP521
    verified := Proof.Ecdh.RISCV64.P521.pk_verified hasLaw.law }
    (Proof.EcKey.RISCV64.Scrub.publicKeyOut _ _ Impl.Ecdsa.RISCV64.CombU.p521CombConsts))]

end VG.Artifacts.EcP521.RISCV64
