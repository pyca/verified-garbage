module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.P256.RISCV64
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.PublicKeyVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.EcdhLit
import VerifiedGarbage.Proof.P256.RISCV64.Law
import VerifiedGarbage.Impl.EcKey.Compressed.P256.RISCV64
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P256.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P256.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-256 public keys (FIPS 186-5 §A.2) on RISC-V -/

namespace VG.Artifacts.EcP256.RISCV64

open VG.Proof.P256.RISCV64 (hasLaw)

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.compressP256
    verified := Proof.EcKey.Compressed.RISCV64.P256.compress_scrubbed },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.decompressP256
    verified := Proof.EcKey.Compressed.RISCV64.P256.decompress_scrubbed hasLaw.law },
  Spec.EcKey.P256.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.publicKeyP256
    verified := Proof.Ecdh.RISCV64.P256.publicKey_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcP256.RISCV64
