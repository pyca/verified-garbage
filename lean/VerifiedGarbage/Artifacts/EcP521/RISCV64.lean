module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P521
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.P521.RISCV64
import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.PublicKeyVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.EcdhLit
import VerifiedGarbage.Proof.P521.RISCV64.Law
import VerifiedGarbage.Impl.EcKey.Compressed.P521.RISCV64
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P521.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P521.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-521 public keys (FIPS 186-5 §A.2) on RISC-V -/

namespace VG.Artifacts.EcP521.RISCV64

open VG.Proof.P521.RISCV64 (hasLaw)

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.compressP521
    verified := Proof.EcKey.Compressed.RISCV64.P521.compress_scrubbed },
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.decompressP521
    verified := Proof.EcKey.Compressed.RISCV64.P521.decompress_scrubbed hasLaw.law },
  Spec.EcKey.P521.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.publicKeyP521
    verified := Proof.Ecdh.RISCV64.P521.publicKey_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcP521.RISCV64
