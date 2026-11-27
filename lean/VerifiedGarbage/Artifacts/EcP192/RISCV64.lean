module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P192
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.P192.RISCV64
import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.PublicKeyVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.EcdhLit
import VerifiedGarbage.Proof.P192.RISCV64.Law
import VerifiedGarbage.Impl.EcKey.Compressed.P192.RISCV64
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P192.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P192.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-192 public keys (FIPS 186-5 §A.2) on RISC-V -/

namespace VG.Artifacts.EcP192.RISCV64

open VG.Proof.P192.RISCV64 (hasLaw)

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.compressP192
    verified := Proof.EcKey.Compressed.RISCV64.P192.compress_scrubbed },
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.decompressP192
    verified := Proof.EcKey.Compressed.RISCV64.P192.decompress_scrubbed hasLaw.law },
  Spec.EcKey.P192.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.publicKeyP192
    verified := Proof.Ecdh.RISCV64.P192.publicKey_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcP192.RISCV64
